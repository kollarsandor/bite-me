const std = @import("std");
const security = @import("security.zig");
const header_mod = @import("header.zig");
const schema = @import("schema.zig");
const wal_mod = @import("wal.zig");
const transaction_mod = @import("transaction.zig");
const snapshot_mod = @import("../c/snapshot.zig");
const pheap_core = @import("../c/pheap.zig");

pub const RecoveryError = error{
    NoSnapshotFound,
    AllSnapshotsCorrupted,
    WalReplayFailed,
    InconsistentState,
    IoFailed,
} || snapshot_mod.SnapshotError || wal_mod.WalError || transaction_mod.TransactionError || std.mem.Allocator.Error;

pub const RecoveryReport = struct {
    primary_loaded: bool,
    backup_used: bool,
    wal_records_replayed: usize,
    final_step: u64,
    bytes_loaded: usize,
};

pub const SnapshotRecovery = struct {
    allocator: std.mem.Allocator,
    dir: std.fs.Dir,
    primary: []u8,
    backup: []u8,

    pub fn init(allocator: std.mem.Allocator, dir: std.fs.Dir, primary_name: []const u8, backup_name: []const u8) !SnapshotRecovery {
        const primary_owned = try allocator.dupe(u8, primary_name);
        errdefer allocator.free(primary_owned);
        const backup_owned = try allocator.dupe(u8, backup_name);
        errdefer allocator.free(backup_owned);
        return .{
            .allocator = allocator,
            .dir = dir,
            .primary = primary_owned,
            .backup = backup_owned,
        };
    }

    pub fn deinit(self: *SnapshotRecovery) void {
        self.allocator.free(self.primary);
        self.allocator.free(self.backup);
    }

    pub fn loadInto(self: *SnapshotRecovery, core: *pheap_core.RSFCore) RecoveryError!RecoveryReport {
        var report = RecoveryReport{
            .primary_loaded = false,
            .backup_used = false,
            .wal_records_replayed = 0,
            .final_step = 0,
            .bytes_loaded = 0,
        };
        if (snapshot_mod.readSnapshotFromFile(self.allocator, self.dir, self.primary)) |loaded_const| {
            var loaded = loaded_const;
            defer loaded.deinit();
            try loaded.restore(core);
            report.primary_loaded = true;
            report.final_step = loaded.global_step;
            report.bytes_loaded = self.statSize(self.primary);
            return report;
        } else |_| {}
        if (snapshot_mod.readSnapshotFromFile(self.allocator, self.dir, self.backup)) |loaded_const| {
            var loaded = loaded_const;
            defer loaded.deinit();
            try loaded.restore(core);
            report.backup_used = true;
            report.final_step = loaded.global_step;
            report.bytes_loaded = self.statSize(self.backup);
            return report;
        } else |_| return RecoveryError.AllSnapshotsCorrupted;
    }

    fn statSize(self: *SnapshotRecovery, name: []const u8) usize {
        const f = self.dir.openFile(name, .{}) catch return 0;
        defer f.close();
        const s = f.stat() catch return 0;
        return @intCast(s.size);
    }
};

pub const WalRecovery = struct {
    allocator: std.mem.Allocator,
    dir: std.fs.Dir,
    sub_path: []u8,

    pub fn init(allocator: std.mem.Allocator, dir: std.fs.Dir, sub_path: []const u8) !WalRecovery {
        const owned = try allocator.dupe(u8, sub_path);
        return .{
            .allocator = allocator,
            .dir = dir,
            .sub_path = owned,
        };
    }

    pub fn deinit(self: *WalRecovery) void {
        self.allocator.free(self.sub_path);
    }

    pub fn replay(self: *WalRecovery, applier: WalApplier) RecoveryError!usize {
        var rep = wal_mod.Replay.open(self.allocator, self.dir, self.sub_path) catch |e| switch (e) {
            error.IoFailed => return 0,
            else => return RecoveryError.WalReplayFailed,
        };
        defer rep.deinit();
        var processed: usize = 0;
        while (true) {
            const maybe = rep.next() catch return RecoveryError.WalReplayFailed;
            if (maybe) |rec| {
                applier.apply(rec) catch return RecoveryError.WalReplayFailed;
                processed += 1;
            } else break;
        }
        return processed;
    }

    pub fn truncate(self: *WalRecovery) RecoveryError!void {
        self.dir.deleteFile(self.sub_path) catch return RecoveryError.IoFailed;
    }
};

pub const WalApplier = struct {
    context: *anyopaque,
    apply_fn: *const fn (ctx: *anyopaque, rec: wal_mod.Record) anyerror!void,

    pub fn apply(self: WalApplier, rec: wal_mod.Record) anyerror!void {
        try self.apply_fn(self.context, rec);
    }
};

pub const RecoveryPlan = struct {
    snapshot: SnapshotRecovery,
    wal: WalRecovery,

    pub fn init(allocator: std.mem.Allocator, dir: std.fs.Dir) !RecoveryPlan {
        return .{
            .snapshot = try SnapshotRecovery.init(allocator, dir, "model.rsf", "model.rsf.bak"),
            .wal = try WalRecovery.init(allocator, dir, "model.wal"),
        };
    }

    pub fn deinit(self: *RecoveryPlan) void {
        self.snapshot.deinit();
        self.wal.deinit();
    }

    pub fn run(self: *RecoveryPlan, core: *pheap_core.RSFCore, applier: WalApplier) RecoveryError!RecoveryReport {
        var report = self.snapshot.loadInto(core) catch RecoveryReport{
            .primary_loaded = false,
            .backup_used = false,
            .wal_records_replayed = 0,
            .final_step = 0,
            .bytes_loaded = 0,
        };
        const replayed = try self.wal.replay(applier);
        report.wal_records_replayed = replayed;
        return report;
    }
};

const NoopContext = struct {
    counter: usize = 0,
    fn apply(self_ptr: *anyopaque, rec: wal_mod.Record) !void {
        const self: *NoopContext = @ptrCast(@alignCast(self_ptr));
        _ = rec;
        self.counter += 1;
    }
};

test "wal recovery replays records" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var wal = try wal_mod.WriteAheadLog.create(alloc, tmp_dir.dir, "rec.wal", 1);
    _ = try wal.append(.forward_step, "abc");
    _ = try wal.append(.backward_step, "xyz");
    _ = try wal.append(.apply_update, "upd");
    wal.deinit();
    var rec = try WalRecovery.init(alloc, tmp_dir.dir, "rec.wal");
    defer rec.deinit();
    var ctx: NoopContext = .{};
    const applier = WalApplier{ .context = &ctx, .apply_fn = NoopContext.apply };
    const n = try rec.replay(applier);
    try std.testing.expectEqual(@as(usize, 3), n);
    try std.testing.expectEqual(@as(usize, 3), ctx.counter);
}

test "snapshot recovery falls back to backup" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 1 };
    const core = try pheap_core.RSFCore.init(alloc, cfg);
    defer core.destroy();
    var snap = try snapshot_mod.SavedModelSnapshot.capture(alloc, core);
    defer snap.deinit();
    try snapshot_mod.writeSnapshotToFile(&snap, alloc, tmp_dir.dir, "model.rsf.bak");
    var rec = try SnapshotRecovery.init(alloc, tmp_dir.dir, "model.rsf", "model.rsf.bak");
    defer rec.deinit();
    const c2 = try pheap_core.RSFCore.init(alloc, cfg);
    defer c2.destroy();
    const report = try rec.loadInto(c2);
    try std.testing.expect(report.backup_used);
    try std.testing.expect(!report.primary_loaded);
}
