const std = @import("std");
const security = @import("security.zig");

pub const WalError = error{
    IoFailed,
    Corrupted,
    SegmentTooSmall,
    SegmentTooLarge,
    BadVersion,
    BadMagic,
    UnknownRecordKind,
    Closed,
} || security.SecurityError || std.mem.Allocator.Error;

pub const WAL_MAGIC: [4]u8 = .{ 'R', 'W', 'A', 'L' };
pub const WAL_VERSION: u32 = 1;
pub const SEGMENT_HEADER_SIZE: usize = 32;
pub const RECORD_HEADER_SIZE: usize = 24;

pub const RecordKind = enum(u16) {
    invalid = 0,
    forward_step = 1,
    backward_step = 2,
    apply_update = 3,
    snapshot_marker = 4,
    config_change = 5,
    layer_reseed = 6,
};

pub const RecordHeader = struct {
    kind: RecordKind,
    sequence: u64,
    timestamp_ns: u64,
    payload_len: u32,
    crc32: u32,

    pub fn writeBytes(self: RecordHeader, dest: []u8) WalError!void {
        if (dest.len < RECORD_HEADER_SIZE) return WalError.SegmentTooSmall;
        std.mem.writeIntLittle(u16, dest[0..2], @intFromEnum(self.kind));
        std.mem.writeIntLittle(u16, dest[2..4], 0);
        std.mem.writeIntLittle(u64, dest[4..12], self.sequence);
        std.mem.writeIntLittle(u64, dest[12..20], self.timestamp_ns);
        std.mem.writeIntLittle(u32, dest[20..24], self.payload_len);
    }

    pub fn readBytes(src: []const u8) WalError!RecordHeader {
        if (src.len < RECORD_HEADER_SIZE) return WalError.SegmentTooSmall;
        const k = std.mem.readIntLittle(u16, src[0..2]);
        if (k > @intFromEnum(RecordKind.layer_reseed)) return WalError.UnknownRecordKind;
        return .{
            .kind = @enumFromInt(k),
            .sequence = std.mem.readIntLittle(u64, src[4..12]),
            .timestamp_ns = std.mem.readIntLittle(u64, src[12..20]),
            .payload_len = std.mem.readIntLittle(u32, src[20..24]),
            .crc32 = 0,
        };
    }
};

pub const SegmentHeader = struct {
    magic: [4]u8 = WAL_MAGIC,
    version: u32 = WAL_VERSION,
    segment_index: u64,
    created_ns: u64,
    record_count: u64,

    pub fn writeBytes(self: SegmentHeader, dest: []u8) WalError!void {
        if (dest.len < SEGMENT_HEADER_SIZE) return WalError.SegmentTooSmall;
        @memcpy(dest[0..4], &self.magic);
        std.mem.writeIntLittle(u32, dest[4..8], self.version);
        std.mem.writeIntLittle(u64, dest[8..16], self.segment_index);
        std.mem.writeIntLittle(u64, dest[16..24], self.created_ns);
        std.mem.writeIntLittle(u64, dest[24..32], self.record_count);
    }

    pub fn readBytes(src: []const u8) WalError!SegmentHeader {
        if (src.len < SEGMENT_HEADER_SIZE) return WalError.SegmentTooSmall;
        var m: [4]u8 = undefined;
        @memcpy(&m, src[0..4]);
        if (!std.mem.eql(u8, &m, &WAL_MAGIC)) return WalError.BadMagic;
        const v = std.mem.readIntLittle(u32, src[4..8]);
        if (v != WAL_VERSION) return WalError.BadVersion;
        return .{
            .magic = WAL_MAGIC,
            .version = v,
            .segment_index = std.mem.readIntLittle(u64, src[8..16]),
            .created_ns = std.mem.readIntLittle(u64, src[16..24]),
            .record_count = std.mem.readIntLittle(u64, src[24..32]),
        };
    }
};

pub const Record = struct {
    header: RecordHeader,
    payload: []u8,
};

pub const WriteAheadLog = struct {
    allocator: std.mem.Allocator,
    dir: std.fs.Dir,
    sub_path: []u8,
    file: ?std.fs.File,
    sequence: u64,
    record_count: u64,
    bytes_written: usize,
    closed: bool,

    pub fn create(allocator: std.mem.Allocator, dir: std.fs.Dir, sub_path: []const u8, segment_index: u64) WalError!WriteAheadLog {
        const owned_path = try allocator.dupe(u8, sub_path);
        errdefer allocator.free(owned_path);
        var file = dir.createFile(sub_path, .{ .truncate = true, .read = true }) catch return WalError.IoFailed;
        errdefer file.close();
        var hdr = SegmentHeader{
            .magic = WAL_MAGIC,
            .version = WAL_VERSION,
            .segment_index = segment_index,
            .created_ns = @intCast(std.time.nanoTimestamp()),
            .record_count = 0,
        };
        var hdr_bytes: [SEGMENT_HEADER_SIZE]u8 = undefined;
        try hdr.writeBytes(&hdr_bytes);
        file.writeAll(&hdr_bytes) catch return WalError.IoFailed;
        file.sync() catch return WalError.IoFailed;
        return .{
            .allocator = allocator,
            .dir = dir,
            .sub_path = owned_path,
            .file = file,
            .sequence = 0,
            .record_count = 0,
            .bytes_written = SEGMENT_HEADER_SIZE,
            .closed = false,
        };
    }

    pub fn append(self: *WriteAheadLog, kind: RecordKind, payload: []const u8) WalError!u64 {
        if (self.closed) return WalError.Closed;
        const file = self.file orelse return WalError.Closed;
        if (payload.len > std.math.maxInt(u32)) return WalError.SegmentTooLarge;
        self.sequence +%= 1;
        const crc = security.Crc32.computeBytes(payload);
        var hdr = RecordHeader{
            .kind = kind,
            .sequence = self.sequence,
            .timestamp_ns = @intCast(std.time.nanoTimestamp()),
            .payload_len = @intCast(payload.len),
            .crc32 = crc,
        };
        var hdr_bytes: [RECORD_HEADER_SIZE]u8 = undefined;
        try hdr.writeBytes(&hdr_bytes);
        var crc_buf: [4]u8 = undefined;
        std.mem.writeIntLittle(u32, &crc_buf, crc);
        file.writeAll(&hdr_bytes) catch return WalError.IoFailed;
        file.writeAll(&crc_buf) catch return WalError.IoFailed;
        if (payload.len > 0) file.writeAll(payload) catch return WalError.IoFailed;
        file.sync() catch return WalError.IoFailed;
        self.record_count += 1;
        self.bytes_written += RECORD_HEADER_SIZE + 4 + payload.len;
        try self.refreshHeader();
        return self.sequence;
    }

    fn refreshHeader(self: *WriteAheadLog) WalError!void {
        const file = self.file orelse return WalError.Closed;
        var hdr = SegmentHeader{
            .segment_index = 0,
            .created_ns = 0,
            .record_count = self.record_count,
        };
        var buf: [SEGMENT_HEADER_SIZE]u8 = undefined;
        try hdr.writeBytes(&buf);
        var existing: [SEGMENT_HEADER_SIZE]u8 = undefined;
        file.seekTo(0) catch return WalError.IoFailed;
        const n = file.readAll(&existing) catch return WalError.IoFailed;
        if (n == SEGMENT_HEADER_SIZE) {
            std.mem.writeIntLittle(u64, existing[24..32], self.record_count);
            file.seekTo(0) catch return WalError.IoFailed;
            file.writeAll(&existing) catch return WalError.IoFailed;
            file.sync() catch return WalError.IoFailed;
            file.seekFromEnd(0) catch return WalError.IoFailed;
        }
    }

    pub fn close(self: *WriteAheadLog) void {
        if (self.closed) return;
        if (self.file) |*f| {
            f.sync() catch {};
            f.close();
        }
        self.file = null;
        self.closed = true;
    }

    pub fn deinit(self: *WriteAheadLog) void {
        self.close();
        self.allocator.free(self.sub_path);
    }

    pub fn bytesUsed(self: *const WriteAheadLog) usize {
        return self.bytes_written;
    }
};

pub const Replay = struct {
    allocator: std.mem.Allocator,
    bytes: []u8,
    cursor: usize,
    header: SegmentHeader,

    pub fn open(allocator: std.mem.Allocator, dir: std.fs.Dir, sub_path: []const u8) WalError!Replay {
        const file = dir.openFile(sub_path, .{}) catch return WalError.IoFailed;
        defer file.close();
        const stat = file.stat() catch return WalError.IoFailed;
        const bytes = try allocator.alloc(u8, @intCast(stat.size));
        errdefer allocator.free(bytes);
        const n = file.readAll(bytes) catch return WalError.IoFailed;
        if (n != bytes.len) return WalError.IoFailed;
        if (bytes.len < SEGMENT_HEADER_SIZE) return WalError.Corrupted;
        const hdr = try SegmentHeader.readBytes(bytes[0..SEGMENT_HEADER_SIZE]);
        return .{
            .allocator = allocator,
            .bytes = bytes,
            .cursor = SEGMENT_HEADER_SIZE,
            .header = hdr,
        };
    }

    pub fn deinit(self: *Replay) void {
        self.allocator.free(self.bytes);
    }

    pub fn next(self: *Replay) WalError!?Record {
        if (self.cursor + RECORD_HEADER_SIZE + 4 > self.bytes.len) return null;
        var hdr = try RecordHeader.readBytes(self.bytes[self.cursor .. self.cursor + RECORD_HEADER_SIZE]);
        const crc = std.mem.readIntLittle(u32, self.bytes[self.cursor + RECORD_HEADER_SIZE .. self.cursor + RECORD_HEADER_SIZE + 4][0..4]);
        hdr.crc32 = crc;
        const payload_start = self.cursor + RECORD_HEADER_SIZE + 4;
        const payload_end = payload_start + hdr.payload_len;
        if (payload_end > self.bytes.len) return WalError.Corrupted;
        const payload = self.bytes[payload_start..payload_end];
        if (security.Crc32.computeBytes(payload) != crc) return WalError.Corrupted;
        self.cursor = payload_end;
        return Record{ .header = hdr, .payload = payload };
    }

    pub fn rewind(self: *Replay) void {
        self.cursor = SEGMENT_HEADER_SIZE;
    }
};

test "wal append and replay" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var wal = try WriteAheadLog.create(alloc, tmp_dir.dir, "test.wal", 1);
    defer wal.deinit();
    const a = "step-1";
    const b = "step-2";
    _ = try wal.append(.forward_step, a);
    _ = try wal.append(.backward_step, b);
    wal.close();
    var rep = try Replay.open(alloc, tmp_dir.dir, "test.wal");
    defer rep.deinit();
    try std.testing.expectEqual(@as(u64, 2), rep.header.record_count);
    var rec1 = try rep.next();
    try std.testing.expect(rec1 != null);
    try std.testing.expectEqualStrings(a, rec1.?.payload);
    var rec2 = try rep.next();
    try std.testing.expect(rec2 != null);
    try std.testing.expectEqualStrings(b, rec2.?.payload);
    try std.testing.expectEqual(@as(?Record, null), try rep.next());
}

test "wal corrupt detection" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var wal = try WriteAheadLog.create(alloc, tmp_dir.dir, "bad.wal", 0);
    _ = try wal.append(.forward_step, "data");
    wal.deinit();
    var f = try tmp_dir.dir.openFile("bad.wal", .{ .mode = .read_write });
    try f.seekTo(SEGMENT_HEADER_SIZE + RECORD_HEADER_SIZE + 4 + 1);
    try f.writeAll(&[_]u8{0xFF});
    f.close();
    var rep = try Replay.open(alloc, tmp_dir.dir, "bad.wal");
    defer rep.deinit();
    try std.testing.expectError(WalError.Corrupted, rep.next());
}
