const std = @import("std");

pub const security = @import("security.zig");
pub const schema = @import("schema.zig");
pub const header = @import("header.zig");
pub const concurrency = @import("concurrency.zig");
pub const gc = @import("gc.zig");
pub const gpu = @import("gpu.zig");
pub const transaction = @import("transaction.zig");
pub const wal = @import("wal.zig");
pub const recovery = @import("recovery.zig");
pub const allocator_mod = @import("../c/allocator.zig");
pub const pointer_mod = @import("../c/pointer.zig");
pub const pheap_core = @import("../c/pheap.zig");
pub const snapshot_mod = @import("../c/snapshot.zig");
pub const repair_mod = @import("../c/repair.zig");

pub const RSFConfig = schema.RSFConfig;
pub const TrainerConfig = schema.TrainerConfig;
pub const ModelMetadata = schema.ModelMetadata;
pub const RSFCore = pheap_core.RSFCore;
pub const LayerCore = pheap_core.LayerCore;
pub const SavedModelSnapshot = snapshot_mod.SavedModelSnapshot;
pub const Header = header.Header;
pub const GpuContext = gpu.Context;
pub const GpuBackend = gpu.Backend;
pub const Repairer = repair_mod.Repairer;
pub const RepairReport = repair_mod.RepairReport;

pub const RSFError = error{
    NotInitialized,
    InvalidHandle,
    DimensionMismatch,
    PendingDelete,
    NoSnapshotFound,
} || pheap_core.CoreError || gpu.GpuError || schema.SchemaError || header.HeaderError || snapshot_mod.SnapshotError || repair_mod.RepairError || transaction.TransactionError || recovery.RecoveryError || std.mem.Allocator.Error;

pub const RSF = struct {
    allocator: std.mem.Allocator,
    core: ?*RSFCore,
    backend: GpuBackend,
    gpu_ctx: GpuContext,

    pub fn create(allocator: std.mem.Allocator, cfg: RSFConfig) RSFError!RSF {
        const core = try RSFCore.init(allocator, cfg);
        const ctx = GpuContext.init(allocator, .{ .backend = .cpu });
        return .{
            .allocator = allocator,
            .core = core,
            .backend = .cpu,
            .gpu_ctx = ctx,
        };
    }

    pub fn destroy(self: *RSF) void {
        self.gpu_ctx.deinit();
        if (self.core) |c| c.destroy();
        self.core = null;
    }

    pub fn config(self: *const RSF) RSFError!RSFConfig {
        const c = self.core orelse return RSFError.NotInitialized;
        return c.config;
    }

    pub fn metadata(self: *const RSF) RSFError!*ModelMetadata {
        const c = self.core orelse return RSFError.NotInitialized;
        return &c.metadata;
    }

    pub fn forward(self: *RSF, x1: []const f32, x2: []const f32, y1: []f32, y2: []f32) RSFError!void {
        const c = self.core orelse return RSFError.NotInitialized;
        var rg = concurrency.acquireRead(&c.lock);
        defer rg.release();
        try self.gpu_ctx.forward(c, 0, x1, x2, y1, y2);
        var idx: usize = 1;
        while (idx < c.layers.len) : (idx += 1) {
            try self.gpu_ctx.forward(c, idx, y1, y2, y1, y2);
        }
    }

    pub fn inverse(self: *RSF, y1: []const f32, y2: []const f32, x1: []f32, x2: []f32) RSFError!void {
        const c = self.core orelse return RSFError.NotInitialized;
        var rg = concurrency.acquireRead(&c.lock);
        defer rg.release();
        var i: usize = c.layers.len;
        while (i > 0) {
            i -= 1;
            if (i == c.layers.len - 1) {
                try self.gpu_ctx.inverse(c, i, y1, y2, x1, x2);
            } else {
                try self.gpu_ctx.inverse(c, i, x1, x2, x1, x2);
            }
        }
    }

    pub fn backward(self: *RSF, y1: []const f32, y2: []const f32, dy1: []const f32, dy2: []const f32, dx1: []f32, dx2: []f32) RSFError!void {
        const c = self.core orelse return RSFError.NotInitialized;
        var wg = concurrency.acquireWrite(&c.lock);
        defer wg.release();
        var i: usize = c.layers.len;
        var current_y1 = y1;
        var current_y2 = y2;
        var current_dy1 = dy1;
        var current_dy2 = dy2;
        while (i > 0) {
            i -= 1;
            try self.gpu_ctx.backward(c, i, current_y1, current_y2, current_dy1, current_dy2, dx1, dx2);
            current_y1 = dx1;
            current_y2 = dx2;
            current_dy1 = dx1;
            current_dy2 = dx2;
        }
    }

    pub fn applyMomentum(self: *RSF, lr: f32, momentum: f32) RSFError!void {
        const c = self.core orelse return RSFError.NotInitialized;
        var wg = concurrency.acquireWrite(&c.lock);
        defer wg.release();
        try c.applyMomentumStep(lr, momentum);
    }

    pub fn clipGradients(self: *RSF, threshold: f32) RSFError!void {
        const c = self.core orelse return RSFError.NotInitialized;
        var wg = concurrency.acquireWrite(&c.lock);
        defer wg.release();
        c.clipGradientsL2(threshold);
    }

    pub fn snapshot(self: *RSF) RSFError!SavedModelSnapshot {
        const c = self.core orelse return RSFError.NotInitialized;
        var rg = concurrency.acquireRead(&c.lock);
        defer rg.release();
        return try snapshot_mod.SavedModelSnapshot.capture(self.allocator, c);
    }

    pub fn restoreFromSnapshot(self: *RSF, snap: *const SavedModelSnapshot) RSFError!void {
        const c = self.core orelse return RSFError.NotInitialized;
        var wg = concurrency.acquireWrite(&c.lock);
        defer wg.release();
        try snap.restore(c);
    }

    pub fn save(self: *RSF, dir: std.fs.Dir, name: []const u8) RSFError!void {
        var snap = try self.snapshot();
        defer snap.deinit();
        var tx = try transaction.SnapshotTransaction.begin(self.allocator, dir, name, snap);
        defer tx.deinit();
        errdefer tx.abort();
        try tx.commit();
    }

    pub fn load(self: *RSF, dir: std.fs.Dir, name: []const u8) RSFError!void {
        var snap = try snapshot_mod.readSnapshotFromFile(self.allocator, dir, name);
        defer snap.deinit();
        try self.restoreFromSnapshot(&snap);
    }

    pub fn repair(self: *RSF, dir: std.fs.Dir, name: []const u8) RSFError!RepairReport {
        var rep = try Repairer.init(self.allocator, dir, name);
        defer rep.deinit();
        return try rep.repair();
    }

    pub fn step(self: *RSF, x1: []const f32, x2: []const f32, t1: []const f32, t2: []const f32, lr: f32, momentum: f32) RSFError!f32 {
        const c = self.core orelse return RSFError.NotInitialized;
        const half = c.config.dim / 2;
        const y1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(y1);
        const y2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(y2);
        const dx1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(dx1);
        const dx2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(dx2);
        try self.forward(x1, x2, y1, y2);
        var dy1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(dy1);
        var dy2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(dy2);
        const inv_n: f32 = 2.0 / @as(f32, @floatFromInt(half));
        var loss: f32 = 0.0;
        for (0..half) |i| {
            const e1 = y1[i] - t1[i];
            const e2 = y2[i] - t2[i];
            dy1[i] = inv_n * e1;
            dy2[i] = inv_n * e2;
            loss += e1 * e1 + e2 * e2;
        }
        loss /= @as(f32, @floatFromInt(half));
        try self.backward(y1, y2, dy1, dy2, dx1, dx2);
        try self.applyMomentum(lr, momentum);
        return loss;
    }

    pub fn statsSnapshot(self: *const RSF) gpu.ExecutionStats {
        return self.gpu_ctx.stats;
    }
};

test "rsf create destroy" {
    const alloc = std.testing.allocator;
    const cfg = RSFConfig{ .dim = 8, .layers = 1 };
    var model = try RSF.create(alloc, cfg);
    defer model.destroy();
    const c = try model.config();
    try std.testing.expectEqual(@as(usize, 8), c.dim);
}

test "rsf forward inverse roundtrip" {
    const alloc = std.testing.allocator;
    const cfg = RSFConfig{ .dim = 8, .layers = 1 };
    var model = try RSF.create(alloc, cfg);
    defer model.destroy();
    const half = cfg.dim / 2;
    const x1 = try alloc.alloc(f32, half);
    defer alloc.free(x1);
    const x2 = try alloc.alloc(f32, half);
    defer alloc.free(x2);
    const y1 = try alloc.alloc(f32, half);
    defer alloc.free(y1);
    const y2 = try alloc.alloc(f32, half);
    defer alloc.free(y2);
    const r1 = try alloc.alloc(f32, half);
    defer alloc.free(r1);
    const r2 = try alloc.alloc(f32, half);
    defer alloc.free(r2);
    for (0..half) |i| {
        x1[i] = @as(f32, @floatFromInt(i)) * 0.05;
        x2[i] = @as(f32, @floatFromInt(i)) * -0.07;
    }
    try model.forward(x1, x2, y1, y2);
    try model.inverse(y1, y2, r1, r2);
    for (0..half) |i| {
        try std.testing.expectApproxEqAbs(x1[i], r1[i], 1.0e-3);
        try std.testing.expectApproxEqAbs(x2[i], r2[i], 1.0e-3);
    }
}

test "rsf step decreases loss" {
    const alloc = std.testing.allocator;
    const cfg = RSFConfig{ .dim = 8, .layers = 1 };
    var model = try RSF.create(alloc, cfg);
    defer model.destroy();
    const half = cfg.dim / 2;
    const x1 = try alloc.alloc(f32, half);
    defer alloc.free(x1);
    const x2 = try alloc.alloc(f32, half);
    defer alloc.free(x2);
    const t1 = try alloc.alloc(f32, half);
    defer alloc.free(t1);
    const t2 = try alloc.alloc(f32, half);
    defer alloc.free(t2);
    for (0..half) |i| {
        x1[i] = 0.1;
        x2[i] = 0.2;
        t1[i] = 0.5;
        t2[i] = -0.3;
    }
    var prev: f32 = std.math.inf(f32);
    var iter: usize = 0;
    while (iter < 10) : (iter += 1) {
        const loss = try model.step(x1, x2, t1, t2, 0.05, 0.9);
        if (iter > 0) try std.testing.expect(loss <= prev + 1.0e-3);
        prev = loss;
    }
}

test "rsf save and load" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = RSFConfig{ .dim = 8, .layers = 2 };
    var model_a = try RSF.create(alloc, cfg);
    defer model_a.destroy();
    try model_a.save(tmp_dir.dir, "model.rsf");
    var model_b = try RSF.create(alloc, cfg);
    defer model_b.destroy();
    try model_b.load(tmp_dir.dir, "model.rsf");
    var snap_a = try model_a.snapshot();
    defer snap_a.deinit();
    var snap_b = try model_b.snapshot();
    defer snap_b.deinit();
    try std.testing.expectApproxEqAbs(@as(f32, 0.0), snap_a.diffNorm(&snap_b), 1.0e-5);
}

test "rsf repair after corruption" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = RSFConfig{ .dim = 8, .layers = 1 };
    var model = try RSF.create(alloc, cfg);
    defer model.destroy();
    try model.save(tmp_dir.dir, "model.rsf");
    var f = try tmp_dir.dir.openFile("model.rsf", .{ .mode = .read_write });
    try f.seekTo(40);
    try f.writeAll(&[_]u8{ 0xFF, 0xFF, 0xFF, 0xFF });
    f.close();
    try tmp_dir.dir.copyFile("model.rsf", tmp_dir.dir, "model.rsf.bak", .{});
    try model.save(tmp_dir.dir, "model.rsf");
    const report = try model.repair(tmp_dir.dir, "model.rsf");
    try std.testing.expect(report.primary_valid);
}
