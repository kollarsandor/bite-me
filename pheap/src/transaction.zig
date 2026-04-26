const std = @import("std");
const security = @import("security.zig");
const header_mod = @import("header.zig");
const schema = @import("schema.zig");
const snapshot_mod = @import("../c/snapshot.zig");

pub const TransactionError = error{
    NotInProgress,
    AlreadyComitted,
    AlreadyAborted,
    IoFailed,
    HashMismatch,
} || snapshot_mod.SnapshotError || std.mem.Allocator.Error;

pub const TransactionState = enum(u8) {
    idle = 0,
    in_progress = 1,
    committing = 2,
    committed = 3,
    aborted = 4,
};

pub const SaveTransaction = struct {
    allocator: std.mem.Allocator,
    dir: std.fs.Dir,
    final_path: []u8,
    temp_path: []u8,
    backup_path: []u8,
    state: TransactionState,
    bytes_written: usize,
    crc_computed: u32,

    pub fn begin(allocator: std.mem.Allocator, dir: std.fs.Dir, final_name: []const u8) TransactionError!SaveTransaction {
        const final_owned = try allocator.dupe(u8, final_name);
        errdefer allocator.free(final_owned);
        const temp = try std.fmt.allocPrint(allocator, "{s}.tmp", .{final_name});
        errdefer allocator.free(temp);
        const backup = try std.fmt.allocPrint(allocator, "{s}.bak", .{final_name});
        errdefer allocator.free(backup);
        return .{
            .allocator = allocator,
            .dir = dir,
            .final_path = final_owned,
            .temp_path = temp,
            .backup_path = backup,
            .state = .in_progress,
            .bytes_written = 0,
            .crc_computed = 0,
        };
    }

    pub fn deinit(self: *SaveTransaction) void {
        self.allocator.free(self.final_path);
        self.allocator.free(self.temp_path);
        self.allocator.free(self.backup_path);
    }

    pub fn write(self: *SaveTransaction, bytes: []const u8) TransactionError!void {
        if (self.state != .in_progress) return TransactionError.NotInProgress;
        var file = self.dir.createFile(self.temp_path, .{ .truncate = true }) catch return TransactionError.IoFailed;
        defer file.close();
        file.writeAll(bytes) catch return TransactionError.IoFailed;
        file.sync() catch return TransactionError.IoFailed;
        self.bytes_written = bytes.len;
        self.crc_computed = security.Crc32.computeBytes(bytes);
    }

    pub fn commit(self: *SaveTransaction) TransactionError!void {
        if (self.state != .in_progress) return TransactionError.NotInProgress;
        self.state = .committing;
        if (self.dir.access(self.final_path, .{})) |_| {
            self.dir.deleteFile(self.backup_path) catch {};
            self.dir.rename(self.final_path, self.backup_path) catch return TransactionError.IoFailed;
        } else |_| {}
        self.dir.rename(self.temp_path, self.final_path) catch return TransactionError.IoFailed;
        var dirfile = self.dir.openFile(".", .{}) catch null;
        if (dirfile) |*f| {
            f.sync() catch {};
            f.close();
        }
        self.state = .committed;
    }

    pub fn abort(self: *SaveTransaction) void {
        if (self.state == .committed) return;
        self.dir.deleteFile(self.temp_path) catch {};
        self.state = .aborted;
    }

    pub fn restoreBackup(self: *SaveTransaction) TransactionError!void {
        if (self.dir.access(self.backup_path, .{})) |_| {
            self.dir.deleteFile(self.final_path) catch {};
            self.dir.rename(self.backup_path, self.final_path) catch return TransactionError.IoFailed;
        } else |_| return TransactionError.IoFailed;
    }
};

pub const SnapshotTransaction = struct {
    allocator: std.mem.Allocator,
    save: SaveTransaction,
    snapshot: snapshot_mod.SavedModelSnapshot,
    payload: []u8,

    pub fn begin(
        allocator: std.mem.Allocator,
        dir: std.fs.Dir,
        final_name: []const u8,
        snapshot: snapshot_mod.SavedModelSnapshot,
    ) TransactionError!SnapshotTransaction {
        var save = try SaveTransaction.begin(allocator, dir, final_name);
        errdefer save.deinit();
        const payload = try snapshot.writeBytes(allocator);
        errdefer allocator.free(payload);
        try save.write(payload);
        return .{
            .allocator = allocator,
            .save = save,
            .snapshot = snapshot,
            .payload = payload,
        };
    }

    pub fn commit(self: *SnapshotTransaction) TransactionError!void {
        try self.save.commit();
    }

    pub fn abort(self: *SnapshotTransaction) void {
        self.save.abort();
    }

    pub fn deinit(self: *SnapshotTransaction) void {
        self.allocator.free(self.payload);
        self.save.deinit();
    }

    pub fn checksum(self: *const SnapshotTransaction) u32 {
        return self.save.crc_computed;
    }

    pub fn bytesWritten(self: *const SnapshotTransaction) usize {
        return self.save.bytes_written;
    }
};

pub fn writeAtomic(allocator: std.mem.Allocator, dir: std.fs.Dir, final_name: []const u8, payload: []const u8) TransactionError!void {
    var tx = try SaveTransaction.begin(allocator, dir, final_name);
    defer tx.deinit();
    errdefer tx.abort();
    try tx.write(payload);
    try tx.commit();
}

test "atomic write rename" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const data = [_]u8{ 0xCA, 0xFE, 0xBA, 0xBE, 0x00, 0x01, 0x02, 0x03 };
    try writeAtomic(alloc, tmp_dir.dir, "model.rsf", &data);
    var f = try tmp_dir.dir.openFile("model.rsf", .{});
    defer f.close();
    var buf: [8]u8 = undefined;
    const n = try f.readAll(&buf);
    try std.testing.expectEqual(@as(usize, 8), n);
    try std.testing.expectEqualSlices(u8, &data, &buf);
}

test "abort cleans temp" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var tx = try SaveTransaction.begin(alloc, tmp_dir.dir, "broken.rsf");
    defer tx.deinit();
    const data = [_]u8{0xAA} ** 32;
    try tx.write(&data);
    tx.abort();
    try std.testing.expectError(error.FileNotFound, tmp_dir.dir.access("broken.rsf.tmp", .{}));
}
