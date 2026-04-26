const std = @import("std");
const rsf = @import("../pheap/src/api.zig");

pub const PersistenceError = error{
    EmptyPayload,
    NoSnapshot,
    NotOpen,
    InvalidPath,
    PayloadTooSmall,
    PayloadMismatch,
    InvalidWorldSize,
    InvalidRank,
} || rsf.transaction.TransactionError || rsf.wal.WalError || rsf.repair_mod.RepairError || rsf.recovery.RecoveryError || std.mem.Allocator.Error;

pub const LoadResult = struct {
    payload: []u8,
    used_backup: bool,
    bytes: usize,
    crc32: u32,

    pub fn deinit(self: *LoadResult, allocator: std.mem.Allocator) void {
        if (self.payload.len > 0) allocator.free(self.payload);
        self.payload = &[_]u8{};
        self.bytes = 0;
        self.crc32 = 0;
    }
};

pub const StepRecordKind = rsf.wal.RecordKind;

pub const SaveResult = struct {
    bytes_written: usize,
    crc32: u32,
    snapshot_marker_sequence: ?u64,
};

pub const ClusterAggregateReport = struct {
    ranks_processed: u32,
    ranks_present: u32,
    total_records: usize,
    bytes_written: usize,
    output_path: []const u8,
};

pub const OwnedRecord = struct {
    header: rsf.wal.RecordHeader,
    payload: []u8,
};

pub const CheckpointStore = struct {
    allocator: std.mem.Allocator,
    dir: std.fs.Dir,
    primary_name: []u8,
    backup_name: []u8,
    wal_name: []u8,
    cluster_wal_name: []u8,
    wal: ?rsf.wal.WriteAheadLog,
    wal_segment: u64,
    rank: u32,
    world_size: u32,
    open: bool,

    const Self = @This();

    pub fn openAt(allocator: std.mem.Allocator, dir: std.fs.Dir, basename: []const u8) PersistenceError!Self {
        return openWithRank(allocator, dir, basename, 0, 1);
    }

    pub fn openWithRank(
        allocator: std.mem.Allocator,
        dir: std.fs.Dir,
        basename: []const u8,
        rank: u32,
        world_size: u32,
    ) PersistenceError!Self {
        if (basename.len == 0) return PersistenceError.InvalidPath;
        if (world_size == 0) return PersistenceError.InvalidWorldSize;
        if (rank >= world_size) return PersistenceError.InvalidRank;
        const primary = try allocator.dupe(u8, basename);
        errdefer allocator.free(primary);
        const backup = try std.fmt.allocPrint(allocator, "{s}.bak", .{basename});
        errdefer allocator.free(backup);
        const wal_name = try std.fmt.allocPrint(allocator, "{s}.rank{d}.wal", .{ basename, rank });
        errdefer allocator.free(wal_name);
        const cluster_name = try std.fmt.allocPrint(allocator, "{s}.cluster.wal", .{basename});
        errdefer allocator.free(cluster_name);
        return .{
            .allocator = allocator,
            .dir = dir,
            .primary_name = primary,
            .backup_name = backup,
            .wal_name = wal_name,
            .cluster_wal_name = cluster_name,
            .wal = null,
            .wal_segment = 0,
            .rank = rank,
            .world_size = world_size,
            .open = true,
        };
    }

    pub fn close(self: *Self) void {
        if (!self.open) return;
        if (self.wal) |*w| w.deinit();
        self.wal = null;
        self.allocator.free(self.primary_name);
        self.allocator.free(self.backup_name);
        self.allocator.free(self.wal_name);
        self.allocator.free(self.cluster_wal_name);
        self.open = false;
    }

    fn nextSegmentIndex(self: *Self) u64 {
        const ts: u64 = @intCast(std.time.nanoTimestamp());
        var seg = self.wal_segment;
        if (seg == 0) seg = ts;
        seg +%= 1;
        if (seg == 0) seg = 1;
        self.wal_segment = seg;
        return seg;
    }

    fn ensureWal(self: *Self) PersistenceError!void {
        if (!self.open) return PersistenceError.NotOpen;
        if (self.wal != null) return;
        const seg = self.nextSegmentIndex();
        const w = try rsf.wal.WriteAheadLog.create(self.allocator, self.dir, self.wal_name, seg);
        self.wal = w;
    }

    pub fn save(self: *Self, payload: []const u8) PersistenceError!SaveResult {
        if (!self.open) return PersistenceError.NotOpen;
        if (payload.len == 0) return PersistenceError.EmptyPayload;
        var tx = try rsf.transaction.SaveTransaction.begin(self.allocator, self.dir, self.primary_name);
        defer tx.deinit();
        errdefer tx.abort();
        try tx.write(payload);
        try tx.commit();
        const written = tx.bytes_written;
        const crc = tx.crc_computed;
        var marker_seq: ?u64 = null;
        try self.ensureWal();
        if (self.wal) |*w| {
            var marker_buf: [24]u8 = undefined;
            std.mem.writeIntLittle(u64, marker_buf[0..8], @as(u64, @intCast(written)));
            std.mem.writeIntLittle(u32, marker_buf[8..12], crc);
            std.mem.writeIntLittle(u64, marker_buf[12..20], @as(u64, @intCast(std.time.nanoTimestamp())));
            std.mem.writeIntLittle(u32, marker_buf[20..24], self.rank);
            marker_seq = try w.append(.snapshot_marker, &marker_buf);
        }
        return .{
            .bytes_written = written,
            .crc32 = crc,
            .snapshot_marker_sequence = marker_seq,
        };
    }

    fn readWholeFile(self: *Self, name: []const u8) PersistenceError!?LoadResult {
        const file = self.dir.openFile(name, .{}) catch return null;
        defer file.close();
        const stat = file.stat() catch return null;
        if (stat.size == 0) return null;
        const buf = try self.allocator.alloc(u8, @intCast(stat.size));
        errdefer self.allocator.free(buf);
        const n = file.readAll(buf) catch {
            self.allocator.free(buf);
            return null;
        };
        if (n != buf.len) {
            self.allocator.free(buf);
            return PersistenceError.PayloadMismatch;
        }
        return LoadResult{
            .payload = buf,
            .used_backup = false,
            .bytes = buf.len,
            .crc32 = rsf.security.Crc32.computeBytes(buf),
        };
    }

    pub fn load(self: *Self) PersistenceError!LoadResult {
        if (!self.open) return PersistenceError.NotOpen;
        if (try self.readWholeFile(self.primary_name)) |result| {
            var owned = result;
            owned.used_backup = false;
            return owned;
        }
        if (try self.readWholeFile(self.backup_name)) |result| {
            var owned = result;
            owned.used_backup = true;
            return owned;
        }
        return PersistenceError.NoSnapshot;
    }

    pub fn recordStep(self: *Self, kind: rsf.wal.RecordKind, payload: []const u8) PersistenceError!u64 {
        try self.ensureWal();
        const w = if (self.wal) |*ww| ww else return PersistenceError.NotOpen;
        return try w.append(kind, payload);
    }

    pub fn closeWal(self: *Self) void {
        if (self.wal) |*w| w.deinit();
        self.wal = null;
    }

    pub fn replay(self: *Self, applier: rsf.recovery.WalApplier) PersistenceError!usize {
        if (!self.open) return PersistenceError.NotOpen;
        self.closeWal();
        const exists_blk = blk: {
            self.dir.access(self.wal_name, .{}) catch break :blk false;
            break :blk true;
        };
        if (!exists_blk) return 0;
        var rec = try rsf.recovery.WalRecovery.init(self.allocator, self.dir, self.wal_name);
        defer rec.deinit();
        return try rec.replay(applier);
    }

    pub fn truncateWal(self: *Self) PersistenceError!void {
        if (!self.open) return PersistenceError.NotOpen;
        self.closeWal();
        self.dir.deleteFile(self.wal_name) catch {};
    }

    pub fn repairCheckpoint(self: *Self) PersistenceError!rsf.RepairReport {
        if (!self.open) return PersistenceError.NotOpen;
        var rep = try rsf.repair_mod.Repairer.init(self.allocator, self.dir, self.primary_name);
        defer rep.deinit();
        return try rep.repair();
    }

    pub fn bytesUsedByWal(self: *const Self) usize {
        if (self.wal) |w| return w.bytesUsed();
        return 0;
    }

    pub fn primaryPath(self: *const Self) []const u8 {
        return self.primary_name;
    }

    pub fn backupPath(self: *const Self) []const u8 {
        return self.backup_name;
    }

    pub fn walPath(self: *const Self) []const u8 {
        return self.wal_name;
    }

    pub fn clusterWalPath(self: *const Self) []const u8 {
        return self.cluster_wal_name;
    }

    pub fn rankIndex(self: *const Self) u32 {
        return self.rank;
    }

    pub fn worldSize(self: *const Self) u32 {
        return self.world_size;
    }

    fn lessByTimestamp(_: void, a: OwnedRecord, b: OwnedRecord) bool {
        if (a.header.timestamp_ns == b.header.timestamp_ns) {
            return a.header.sequence < b.header.sequence;
        }
        return a.header.timestamp_ns < b.header.timestamp_ns;
    }

    pub fn aggregateClusterWal(self: *Self) PersistenceError!ClusterAggregateReport {
        if (!self.open) return PersistenceError.NotOpen;
        if (self.world_size == 0) return PersistenceError.InvalidWorldSize;
        self.closeWal();

        var collected = std.ArrayList(OwnedRecord).init(self.allocator);
        defer {
            for (collected.items) |rec| {
                self.allocator.free(rec.payload);
            }
            collected.deinit();
        }

        var ranks_present: u32 = 0;
        var rank_idx: u32 = 0;
        while (rank_idx < self.world_size) : (rank_idx += 1) {
            const rank_wal = try std.fmt.allocPrint(self.allocator, "{s}.rank{d}.wal", .{ self.primary_name, rank_idx });
            defer self.allocator.free(rank_wal);
            self.dir.access(rank_wal, .{}) catch continue;
            ranks_present += 1;
            var rep = try rsf.wal.Replay.open(self.allocator, self.dir, rank_wal);
            defer rep.deinit();
            while (true) {
                const maybe = try rep.next();
                if (maybe) |rec| {
                    const payload_owned = try self.allocator.dupe(u8, rec.payload);
                    errdefer self.allocator.free(payload_owned);
                    try collected.append(.{ .header = rec.header, .payload = payload_owned });
                } else break;
            }
        }

        std.sort.heap(OwnedRecord, collected.items, {}, lessByTimestamp);

        self.dir.deleteFile(self.cluster_wal_name) catch {};
        const seg = self.nextSegmentIndex();
        var w = try rsf.wal.WriteAheadLog.create(self.allocator, self.dir, self.cluster_wal_name, seg);
        defer w.deinit();
        for (collected.items) |rec| {
            _ = try w.append(rec.header.kind, rec.payload);
        }

        const total_records = collected.items.len;
        const bytes_written = w.bytesUsed();

        return .{
            .ranks_processed = self.world_size,
            .ranks_present = ranks_present,
            .total_records = total_records,
            .bytes_written = bytes_written,
            .output_path = self.cluster_wal_name,
        };
    }

    pub fn replayClusterWal(self: *Self, applier: rsf.recovery.WalApplier) PersistenceError!usize {
        if (!self.open) return PersistenceError.NotOpen;
        const exists_blk = blk: {
            self.dir.access(self.cluster_wal_name, .{}) catch break :blk false;
            break :blk true;
        };
        if (!exists_blk) return 0;
        var rec = try rsf.recovery.WalRecovery.init(self.allocator, self.dir, self.cluster_wal_name);
        defer rec.deinit();
        return try rec.replay(applier);
    }

    pub fn truncateClusterWal(self: *Self) PersistenceError!void {
        if (!self.open) return PersistenceError.NotOpen;
        self.dir.deleteFile(self.cluster_wal_name) catch {};
    }

    pub fn truncateAllRankWals(self: *Self) PersistenceError!void {
        if (!self.open) return PersistenceError.NotOpen;
        if (self.world_size == 0) return PersistenceError.InvalidWorldSize;
        self.closeWal();
        var rank_idx: u32 = 0;
        while (rank_idx < self.world_size) : (rank_idx += 1) {
            const rank_wal = try std.fmt.allocPrint(self.allocator, "{s}.rank{d}.wal", .{ self.primary_name, rank_idx });
            defer self.allocator.free(rank_wal);
            self.dir.deleteFile(rank_wal) catch {};
        }
    }
};

const TestApplierState = struct {
    seen: usize = 0,
    last_kind: ?rsf.wal.RecordKind = null,
    fn apply(ctx_ptr: *anyopaque, rec: rsf.wal.Record) anyerror!void {
        const self: *TestApplierState = @ptrCast(@alignCast(ctx_ptr));
        self.seen += 1;
        self.last_kind = rec.header.kind;
    }
};

test "checkpoint store atomic save and load" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var store = try CheckpointStore.openAt(alloc, tmp_dir.dir, "model.rsf");
    defer store.close();
    const payload = [_]u8{ 0xCA, 0xFE, 0xBA, 0xBE, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77 };
    const save_res = try store.save(&payload);
    try std.testing.expectEqual(@as(usize, payload.len), save_res.bytes_written);
    var loaded = try store.load();
    defer loaded.deinit(alloc);
    try std.testing.expect(!loaded.used_backup);
    try std.testing.expectEqualSlices(u8, &payload, loaded.payload);
    try std.testing.expectEqual(save_res.crc32, loaded.crc32);
}

test "checkpoint store backup fallback after deleting primary" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var store = try CheckpointStore.openAt(alloc, tmp_dir.dir, "model.rsf");
    defer store.close();
    const payload_a = [_]u8{ 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 };
    _ = try store.save(&payload_a);
    const payload_b = [_]u8{ 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10 };
    _ = try store.save(&payload_b);
    try tmp_dir.dir.deleteFile("model.rsf");
    var loaded = try store.load();
    defer loaded.deinit(alloc);
    try std.testing.expect(loaded.used_backup);
    try std.testing.expectEqualSlices(u8, &payload_a, loaded.payload);
}

test "checkpoint store wal append and replay" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var store = try CheckpointStore.openAt(alloc, tmp_dir.dir, "training.rsf");
    defer store.close();
    _ = try store.recordStep(.forward_step, "fwd-1");
    _ = try store.recordStep(.backward_step, "bwd-1");
    _ = try store.recordStep(.apply_update, "upd-1");
    var state = TestApplierState{};
    const applier = rsf.recovery.WalApplier{
        .context = &state,
        .apply_fn = TestApplierState.apply,
    };
    const replayed = try store.replay(applier);
    try std.testing.expectEqual(@as(usize, 3), replayed);
    try std.testing.expectEqual(@as(usize, 3), state.seen);
    try std.testing.expectEqual(rsf.wal.RecordKind.apply_update, state.last_kind.?);
    try store.truncateWal();
    var state2 = TestApplierState{};
    const applier2 = rsf.recovery.WalApplier{
        .context = &state2,
        .apply_fn = TestApplierState.apply,
    };
    const replayed2 = try store.replay(applier2);
    try std.testing.expectEqual(@as(usize, 0), replayed2);
}

test "checkpoint store repair reports backup and primary" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 8, .layers = 1 };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    var snap = try model.snapshot();
    defer snap.deinit();
    const payload = try snap.writeBytes(alloc);
    defer alloc.free(payload);
    var store = try CheckpointStore.openAt(alloc, tmp_dir.dir, "model.rsf");
    defer store.close();
    _ = try store.save(payload);
    _ = try store.save(payload);
    const report = try store.repairCheckpoint();
    try std.testing.expect(report.primary_valid);
    try std.testing.expect(report.backup_valid);
    try std.testing.expect(!report.repaired_from_backup);
}

test "checkpoint store rank aware wal naming" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var store = try CheckpointStore.openWithRank(alloc, tmp_dir.dir, "model.rsf", 2, 4);
    defer store.close();
    _ = try store.recordStep(.forward_step, "rank2-fwd");
    try std.testing.expectEqualStrings("model.rsf.rank2.wal", store.walPath());
    try std.testing.expectEqualStrings("model.rsf.cluster.wal", store.clusterWalPath());
    try std.testing.expectEqual(@as(u32, 2), store.rankIndex());
    try std.testing.expectEqual(@as(u32, 4), store.worldSize());
    _ = try tmp_dir.dir.access("model.rsf.rank2.wal", .{});
}

test "checkpoint store openWithRank rejects invalid configurations" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    try std.testing.expectError(PersistenceError.InvalidPath, CheckpointStore.openWithRank(alloc, tmp_dir.dir, "", 0, 1));
    try std.testing.expectError(PersistenceError.InvalidWorldSize, CheckpointStore.openWithRank(alloc, tmp_dir.dir, "x", 0, 0));
    try std.testing.expectError(PersistenceError.InvalidRank, CheckpointStore.openWithRank(alloc, tmp_dir.dir, "x", 4, 4));
}

test "aggregate cluster wal merges all ranks in timestamp order" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const world_size: u32 = 3;
    var stores: [3]CheckpointStore = undefined;
    var rr: u32 = 0;
    while (rr < world_size) : (rr += 1) {
        stores[rr] = try CheckpointStore.openWithRank(alloc, tmp_dir.dir, "model.rsf", rr, world_size);
    }
    defer {
        var idx: u32 = 0;
        while (idx < world_size) : (idx += 1) {
            stores[idx].close();
        }
    }
    _ = try stores[0].recordStep(.forward_step, "r0-a");
    std.time.sleep(1_000_000);
    _ = try stores[1].recordStep(.forward_step, "r1-a");
    std.time.sleep(1_000_000);
    _ = try stores[2].recordStep(.forward_step, "r2-a");
    std.time.sleep(1_000_000);
    _ = try stores[0].recordStep(.apply_update, "r0-b");
    std.time.sleep(1_000_000);
    _ = try stores[1].recordStep(.apply_update, "r1-b");
    var aggregator = try CheckpointStore.openWithRank(alloc, tmp_dir.dir, "model.rsf", 0, world_size);
    defer aggregator.close();
    const report = try aggregator.aggregateClusterWal();
    try std.testing.expectEqual(@as(u32, 3), report.ranks_processed);
    try std.testing.expectEqual(@as(u32, 3), report.ranks_present);
    try std.testing.expectEqual(@as(usize, 5), report.total_records);
    try std.testing.expect(report.bytes_written > 0);
    try std.testing.expectEqualStrings("model.rsf.cluster.wal", report.output_path);
    var state = TestApplierState{};
    const applier = rsf.recovery.WalApplier{
        .context = &state,
        .apply_fn = TestApplierState.apply,
    };
    const replayed = try aggregator.replayClusterWal(applier);
    try std.testing.expectEqual(@as(usize, 5), replayed);
    try std.testing.expectEqual(rsf.wal.RecordKind.apply_update, state.last_kind.?);
    try aggregator.truncateAllRankWals();
    try aggregator.truncateClusterWal();
    try std.testing.expectError(error.FileNotFound, tmp_dir.dir.access("model.rsf.cluster.wal", .{}));
}

test "aggregate cluster wal handles missing rank files gracefully" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var store0 = try CheckpointStore.openWithRank(alloc, tmp_dir.dir, "model.rsf", 0, 4);
    defer store0.close();
    var store2 = try CheckpointStore.openWithRank(alloc, tmp_dir.dir, "model.rsf", 2, 4);
    defer store2.close();
    _ = try store0.recordStep(.forward_step, "r0");
    _ = try store2.recordStep(.forward_step, "r2");
    var aggregator = try CheckpointStore.openWithRank(alloc, tmp_dir.dir, "model.rsf", 0, 4);
    defer aggregator.close();
    const report = try aggregator.aggregateClusterWal();
    try std.testing.expectEqual(@as(u32, 4), report.ranks_processed);
    try std.testing.expectEqual(@as(u32, 2), report.ranks_present);
    try std.testing.expectEqual(@as(usize, 2), report.total_records);
}
