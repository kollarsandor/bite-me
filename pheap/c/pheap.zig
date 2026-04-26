const std = @import("std");
const schema = @import("../src/schema.zig");
const security = @import("../src/security.zig");
const concurrency = @import("../src/concurrency.zig");
const allocator_mod = @import("allocator.zig");

pub const CoreError = error{
    DimensionMismatch,
    LayerIndexOutOfBounds,
    NonFiniteValue,
    PendingDelete,
    NotInitialized,
    Underflow,
} || allocator_mod.AllocError || schema.SchemaError || security.SecurityError;

pub const LayerCore = struct {
    half_dim: usize,
    w_s: []align(64) f32,
    w_t: []align(64) f32,
    b_s: []align(64) f32,
    b_t: []align(64) f32,
    grad_w_s: []align(64) f32,
    grad_w_t: []align(64) f32,
    grad_b_s: []align(64) f32,
    grad_b_t: []align(64) f32,
    vel_w_s: []align(64) f32,
    vel_w_t: []align(64) f32,
    vel_b_s: []align(64) f32,
    vel_b_t: []align(64) f32,
    allocator: std.mem.Allocator,

    pub fn init(child: std.mem.Allocator, half: usize, seed: u64, layer_index: usize) CoreError!LayerCore {
        const matrix_len = std.math.mul(usize, half, half) catch return CoreError.SizeOverflow;
        var lc = LayerCore{
            .half_dim = half,
            .w_s = try allocator_mod.allocAlignedF32(child, matrix_len, 64),
            .w_t = try allocator_mod.allocAlignedF32(child, matrix_len, 64),
            .b_s = try allocator_mod.allocAlignedF32(child, half, 64),
            .b_t = try allocator_mod.allocAlignedF32(child, half, 64),
            .grad_w_s = try allocator_mod.allocAlignedF32(child, matrix_len, 64),
            .grad_w_t = try allocator_mod.allocAlignedF32(child, matrix_len, 64),
            .grad_b_s = try allocator_mod.allocAlignedF32(child, half, 64),
            .grad_b_t = try allocator_mod.allocAlignedF32(child, half, 64),
            .vel_w_s = try allocator_mod.allocAlignedF32(child, matrix_len, 64),
            .vel_w_t = try allocator_mod.allocAlignedF32(child, matrix_len, 64),
            .vel_b_s = try allocator_mod.allocAlignedF32(child, half, 64),
            .vel_b_t = try allocator_mod.allocAlignedF32(child, half, 64),
            .allocator = child,
        };
        const seed_s = seed ^ (0x9E3779B97F4A7C15 *% layer_index) ^ 0x12345;
        const seed_t = seed ^ (0x9E3779B97F4A7C15 *% (layer_index + 1)) ^ 0x67890;
        fillXavier(lc.w_s, half, half, seed_s);
        fillXavier(lc.w_t, half, half, seed_t);
        return lc;
    }

    pub fn deinit(self: *LayerCore) void {
        self.allocator.free(self.w_s);
        self.allocator.free(self.w_t);
        self.allocator.free(self.b_s);
        self.allocator.free(self.b_t);
        self.allocator.free(self.grad_w_s);
        self.allocator.free(self.grad_w_t);
        self.allocator.free(self.grad_b_s);
        self.allocator.free(self.grad_b_t);
        self.allocator.free(self.vel_w_s);
        self.allocator.free(self.vel_w_t);
        self.allocator.free(self.vel_b_s);
        self.allocator.free(self.vel_b_t);
        self.* = undefined;
    }

    pub fn zeroGradients(self: *LayerCore) void {
        @memset(self.grad_w_s, 0.0);
        @memset(self.grad_w_t, 0.0);
        @memset(self.grad_b_s, 0.0);
        @memset(self.grad_b_t, 0.0);
    }

    pub fn zeroVelocities(self: *LayerCore) void {
        @memset(self.vel_w_s, 0.0);
        @memset(self.vel_w_t, 0.0);
        @memset(self.vel_b_s, 0.0);
        @memset(self.vel_b_t, 0.0);
    }
};

fn fillXavier(buf: []f32, fan_in: usize, fan_out: usize, seed: u64) void {
    const limit = @sqrt(6.0 / @as(f32, @floatFromInt(fan_in + fan_out)));
    var state = security.xoshiroSeed(seed);
    for (buf) |*v| {
        const u = security.uniformF32FromU64(security.xoshiroNext(&state));
        v.* = (2.0 * u - 1.0) * limit;
    }
}

fn matvec(out: []f32, w: []const f32, x: []const f32, rows: usize, cols: usize) void {
    var i: usize = 0;
    while (i < rows) : (i += 1) {
        var acc: f32 = 0.0;
        const base = i * cols;
        var j: usize = 0;
        while (j < cols) : (j += 1) {
            acc += w[base + j] * x[j];
        }
        out[i] = acc;
    }
}

fn matvecTranspose(out: []f32, w: []const f32, x: []const f32, rows: usize, cols: usize) void {
    @memset(out, 0.0);
    var i: usize = 0;
    while (i < rows) : (i += 1) {
        const xi = x[i];
        const base = i * cols;
        var j: usize = 0;
        while (j < cols) : (j += 1) {
            out[j] += w[base + j] * xi;
        }
    }
}

fn outerAccum(target: []f32, a: []const f32, b: []const f32) void {
    const rows = a.len;
    const cols = b.len;
    var i: usize = 0;
    while (i < rows) : (i += 1) {
        const ai = a[i];
        const base = i * cols;
        var j: usize = 0;
        while (j < cols) : (j += 1) {
            target[base + j] += ai * b[j];
        }
    }
}

fn clipScalar(x: f32, lo: f32, hi: f32) f32 {
    if (x < lo) return lo;
    if (x > hi) return hi;
    return x;
}

pub const RSFCore = struct {
    config: schema.RSFConfig,
    layers: []LayerCore,
    metadata: schema.ModelMetadata,
    refcount: concurrency.RefCounter,
    pending_delete: std.atomic.Atomic(bool),
    lock: concurrency.RwLock,
    allocator: std.mem.Allocator,
    scratch_a: []align(64) f32,
    scratch_b: []align(64) f32,
    scratch_pre: []align(64) f32,
    scratch_dpre: []align(64) f32,
    scratch_dy1: []align(64) f32,
    scratch_x1: []align(64) f32,
    scratch_x2: []align(64) f32,

    pub fn init(child: std.mem.Allocator, config: schema.RSFConfig) CoreError!*RSFCore {
        try config.validate();
        const half = config.dim / 2;
        const self = try child.create(RSFCore);
        errdefer child.destroy(self);
        self.* = RSFCore{
            .config = config,
            .layers = try child.alloc(LayerCore, config.layers),
            .metadata = schema.ModelMetadata.init("rsf"),
            .refcount = concurrency.RefCounter.init(1),
            .pending_delete = std.atomic.Atomic(bool).init(false),
            .lock = .{},
            .allocator = child,
            .scratch_a = try allocator_mod.allocAlignedF32(child, half, 64),
            .scratch_b = try allocator_mod.allocAlignedF32(child, half, 64),
            .scratch_pre = try allocator_mod.allocAlignedF32(child, half, 64),
            .scratch_dpre = try allocator_mod.allocAlignedF32(child, half, 64),
            .scratch_dy1 = try allocator_mod.allocAlignedF32(child, half, 64),
            .scratch_x1 = try allocator_mod.allocAlignedF32(child, half, 64),
            .scratch_x2 = try allocator_mod.allocAlignedF32(child, half, 64),
        };
        var i: usize = 0;
        errdefer {
            var j: usize = 0;
            while (j < i) : (j += 1) self.layers[j].deinit();
            child.free(self.layers);
            child.free(self.scratch_a);
            child.free(self.scratch_b);
            child.free(self.scratch_pre);
            child.free(self.scratch_dpre);
            child.free(self.scratch_dy1);
            child.free(self.scratch_x1);
            child.free(self.scratch_x2);
        }
        while (i < config.layers) : (i += 1) {
            self.layers[i] = try LayerCore.init(child, half, config.seed, i);
        }
        return self;
    }

    pub fn destroy(self: *RSFCore) void {
        for (self.layers) |*lc| lc.deinit();
        self.allocator.free(self.layers);
        self.allocator.free(self.scratch_a);
        self.allocator.free(self.scratch_b);
        self.allocator.free(self.scratch_pre);
        self.allocator.free(self.scratch_dpre);
        self.allocator.free(self.scratch_dy1);
        self.allocator.free(self.scratch_x1);
        self.allocator.free(self.scratch_x2);
        const a = self.allocator;
        a.destroy(self);
    }

    pub fn acquire(self: *RSFCore) u64 {
        return self.refcount.acquire();
    }

    pub fn release(self: *RSFCore) bool {
        const remaining = self.refcount.release();
        if (remaining == 0 and self.pending_delete.load(.Acquire)) {
            self.destroy();
            return true;
        }
        return false;
    }

    pub fn markPendingDelete(self: *RSFCore) void {
        self.pending_delete.store(true, .Release);
    }

    pub fn forwardLayer(
        self: *RSFCore,
        layer_index: usize,
        x1: []const f32,
        x2: []const f32,
        y1: []f32,
        y2: []f32,
    ) CoreError!void {
        if (layer_index >= self.layers.len) return CoreError.LayerIndexOutOfBounds;
        const half = self.config.dim / 2;
        if (x1.len != half or x2.len != half or y1.len != half or y2.len != half) {
            return CoreError.DimensionMismatch;
        }
        try security.ensureFiniteF32(x1);
        try security.ensureFiniteF32(x2);
        const lc = &self.layers[layer_index];
        matvec(self.scratch_pre, lc.w_s, x2, half, half);
        var i: usize = 0;
        while (i < half) : (i += 1) {
            const pre = self.scratch_pre[i] + lc.b_s[i];
            const scale = std.math.exp(clipScalar(pre, self.config.clip_min, self.config.clip_max));
            y1[i] = x1[i] * scale;
        }
        matvec(self.scratch_a, lc.w_t, y1, half, half);
        i = 0;
        while (i < half) : (i += 1) {
            y2[i] = x2[i] + self.scratch_a[i] + lc.b_t[i];
        }
        try security.ensureFiniteF32(y1);
        try security.ensureFiniteF32(y2);
    }

    pub fn inverseLayer(
        self: *RSFCore,
        layer_index: usize,
        y1: []const f32,
        y2: []const f32,
        x1: []f32,
        x2: []f32,
    ) CoreError!void {
        if (layer_index >= self.layers.len) return CoreError.LayerIndexOutOfBounds;
        const half = self.config.dim / 2;
        if (y1.len != half or y2.len != half or x1.len != half or x2.len != half) {
            return CoreError.DimensionMismatch;
        }
        const lc = &self.layers[layer_index];
        matvec(self.scratch_a, lc.w_t, y1, half, half);
        var i: usize = 0;
        while (i < half) : (i += 1) {
            x2[i] = y2[i] - self.scratch_a[i] - lc.b_t[i];
        }
        matvec(self.scratch_pre, lc.w_s, x2, half, half);
        i = 0;
        while (i < half) : (i += 1) {
            const pre = self.scratch_pre[i] + lc.b_s[i];
            const scale = std.math.exp(clipScalar(pre, self.config.clip_min, self.config.clip_max));
            x1[i] = y1[i] / scale;
        }
        try security.ensureFiniteF32(x1);
        try security.ensureFiniteF32(x2);
    }

    pub fn backwardLayer(
        self: *RSFCore,
        layer_index: usize,
        y1: []const f32,
        y2: []const f32,
        dy1: []const f32,
        dy2: []const f32,
        dx1: []f32,
        dx2: []f32,
    ) CoreError!void {
        if (layer_index >= self.layers.len) return CoreError.LayerIndexOutOfBounds;
        const half = self.config.dim / 2;
        if (y1.len != half or y2.len != half or dy1.len != half or dy2.len != half) {
            return CoreError.DimensionMismatch;
        }
        if (dx1.len != half or dx2.len != half) return CoreError.DimensionMismatch;
        const lc = &self.layers[layer_index];
        matvec(self.scratch_a, lc.w_t, y1, half, half);
        var i: usize = 0;
        while (i < half) : (i += 1) {
            self.scratch_x2[i] = y2[i] - self.scratch_a[i] - lc.b_t[i];
        }
        matvec(self.scratch_pre, lc.w_s, self.scratch_x2, half, half);
        i = 0;
        while (i < half) : (i += 1) {
            self.scratch_pre[i] += lc.b_s[i];
        }
        i = 0;
        while (i < half) : (i += 1) {
            const pre = self.scratch_pre[i];
            const scale = std.math.exp(clipScalar(pre, self.config.clip_min, self.config.clip_max));
            self.scratch_b[i] = scale;
            self.scratch_x1[i] = y1[i] / scale;
        }
        i = 0;
        while (i < half) : (i += 1) {
            lc.grad_b_t[i] += dy2[i];
        }
        outerAccum(lc.grad_w_t, dy2, y1);
        matvecTranspose(self.scratch_dy1, lc.w_t, dy2, half, half);
        i = 0;
        while (i < half) : (i += 1) {
            self.scratch_dy1[i] += dy1[i];
        }
        i = 0;
        while (i < half) : (i += 1) {
            const draw = self.scratch_dy1[i] * self.scratch_x1[i];
            const pre = self.scratch_pre[i];
            const clipped = pre <= self.config.clip_min or pre >= self.config.clip_max;
            self.scratch_dpre[i] = if (clipped) 0.0 else draw * self.scratch_b[i];
            lc.grad_b_s[i] += self.scratch_dpre[i];
        }
        outerAccum(lc.grad_w_s, self.scratch_dpre, self.scratch_x2);
        matvecTranspose(self.scratch_a, lc.w_s, self.scratch_dpre, half, half);
        i = 0;
        while (i < half) : (i += 1) {
            dx2[i] = dy2[i] + self.scratch_a[i];
            dx1[i] = self.scratch_dy1[i] * self.scratch_b[i];
        }
        try security.ensureFiniteF32(dx1);
        try security.ensureFiniteF32(dx2);
    }

    pub fn applyMomentumStep(self: *RSFCore, lr: f32, momentum: f32) CoreError!void {
        try security.validateLearningRate(lr);
        try security.validateMomentum(momentum);
        for (self.layers) |*lc| {
            applyOne(lc.w_s, lc.grad_w_s, lc.vel_w_s, lr, momentum);
            applyOne(lc.w_t, lc.grad_w_t, lc.vel_w_t, lr, momentum);
            applyOne(lc.b_s, lc.grad_b_s, lc.vel_b_s, lr, momentum);
            applyOne(lc.b_t, lc.grad_b_t, lc.vel_b_t, lr, momentum);
            lc.zeroGradients();
        }
        self.metadata.incStep();
    }

    fn applyOne(weights: []f32, grads: []f32, velocities: []f32, lr: f32, momentum: f32) void {
        var i: usize = 0;
        while (i < weights.len) : (i += 1) {
            const v = momentum * velocities[i] + grads[i];
            velocities[i] = v;
            weights[i] -= lr * v;
        }
    }

    pub fn clipGradientsL2(self: *RSFCore, threshold: f32) void {
        if (threshold <= 0.0) return;
        var sq: f32 = 0.0;
        for (self.layers) |*lc| {
            for (lc.grad_w_s) |v| sq += v * v;
            for (lc.grad_w_t) |v| sq += v * v;
            for (lc.grad_b_s) |v| sq += v * v;
            for (lc.grad_b_t) |v| sq += v * v;
        }
        const norm = @sqrt(sq);
        if (norm <= threshold) return;
        const scale = threshold / norm;
        for (self.layers) |*lc| {
            for (lc.grad_w_s) |*v| v.* *= scale;
            for (lc.grad_w_t) |*v| v.* *= scale;
            for (lc.grad_b_s) |*v| v.* *= scale;
            for (lc.grad_b_t) |*v| v.* *= scale;
        }
    }

    pub fn forwardChain(self: *RSFCore, x1: []const f32, x2: []const f32, y1: []f32, y2: []f32) CoreError!void {
        const half = self.config.dim / 2;
        if (x1.len != half or x2.len != half or y1.len != half or y2.len != half) {
            return CoreError.DimensionMismatch;
        }
        var a = try self.allocator.alloc(f32, half);
        defer self.allocator.free(a);
        var b = try self.allocator.alloc(f32, half);
        defer self.allocator.free(b);
        @memcpy(a, x1);
        @memcpy(b, x2);
        var idx: usize = 0;
        while (idx < self.layers.len) : (idx += 1) {
            try self.forwardLayer(idx, a, b, y1, y2);
            scatterPair(y1, y2, a, b);
        }
        @memcpy(y1, a);
        @memcpy(y2, b);
    }

    pub fn inverseChain(self: *RSFCore, y1: []const f32, y2: []const f32, x1: []f32, x2: []f32) CoreError!void {
        const half = self.config.dim / 2;
        if (y1.len != half or y2.len != half or x1.len != half or x2.len != half) {
            return CoreError.DimensionMismatch;
        }
        var a = try self.allocator.alloc(f32, half);
        defer self.allocator.free(a);
        var b = try self.allocator.alloc(f32, half);
        defer self.allocator.free(b);
        @memcpy(a, y1);
        @memcpy(b, y2);
        var i: usize = self.layers.len;
        while (i > 0) {
            i -= 1;
            scatterInversePair(a, b, x1, x2);
            try self.inverseLayer(i, x1, x2, a, b);
        }
        @memcpy(x1, a);
        @memcpy(x2, b);
    }
};

pub fn scatterPair(in1: []const f32, in2: []const f32, out1: []f32, out2: []f32) void {
    const factor: f32 = 0.7071067811865475;
    var i: usize = 0;
    while (i < in1.len) : (i += 1) {
        out1[i] = (in1[i] + in2[i]) * factor;
        out2[i] = (in1[i] - in2[i]) * factor;
    }
}

pub fn scatterInversePair(in1: []const f32, in2: []const f32, out1: []f32, out2: []f32) void {
    const factor: f32 = 0.7071067811865475;
    var i: usize = 0;
    while (i < in1.len) : (i += 1) {
        out1[i] = (in1[i] + in2[i]) * factor;
        out2[i] = (in1[i] - in2[i]) * factor;
    }
}

pub fn oftbForward(in1: []f32, in2: []f32, scratch: []f32) void {
    const factor: f32 = 0.7071067811865475;
    @memcpy(scratch, in1);
    var i: usize = 0;
    while (i < in1.len) : (i += 1) {
        in1[i] = in1[i] + in2[i] * factor;
    }
    i = 0;
    while (i < in2.len) : (i += 1) {
        in2[i] = in2[i] + scratch[i] * factor * 0.5;
    }
}

pub fn oftbBackward(in1: []f32, in2: []f32, scratch: []f32) void {
    const factor: f32 = 0.7071067811865475;
    @memcpy(scratch, in1);
    var i: usize = 0;
    while (i < in2.len) : (i += 1) {
        in2[i] = in2[i] - scratch[i] * factor * 0.5;
    }
    i = 0;
    while (i < in1.len) : (i += 1) {
        in1[i] = in1[i] - in2[i] * factor;
    }
}

test "core forward inverse roundtrip" {
    const alloc = std.testing.allocator;
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 1 };
    const core = try RSFCore.init(alloc, cfg);
    defer core.destroy();
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
        x1[i] = @as(f32, @floatFromInt(i)) * 0.1;
        x2[i] = @as(f32, @floatFromInt(i)) * 0.05 - 0.2;
    }
    try core.forwardLayer(0, x1, x2, y1, y2);
    try core.inverseLayer(0, y1, y2, r1, r2);
    for (0..half) |i| {
        try std.testing.expectApproxEqAbs(x1[i], r1[i], 1.0e-4);
        try std.testing.expectApproxEqAbs(x2[i], r2[i], 1.0e-4);
    }
}

test "core backward shapes" {
    const alloc = std.testing.allocator;
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 1 };
    const core = try RSFCore.init(alloc, cfg);
    defer core.destroy();
    const half = cfg.dim / 2;
    const x1 = try alloc.alloc(f32, half);
    defer alloc.free(x1);
    const x2 = try alloc.alloc(f32, half);
    defer alloc.free(x2);
    const y1 = try alloc.alloc(f32, half);
    defer alloc.free(y1);
    const y2 = try alloc.alloc(f32, half);
    defer alloc.free(y2);
    const dy1 = try alloc.alloc(f32, half);
    defer alloc.free(dy1);
    const dy2 = try alloc.alloc(f32, half);
    defer alloc.free(dy2);
    const dx1 = try alloc.alloc(f32, half);
    defer alloc.free(dx1);
    const dx2 = try alloc.alloc(f32, half);
    defer alloc.free(dx2);
    for (0..half) |i| {
        x1[i] = 0.01 * @as(f32, @floatFromInt(i + 1));
        x2[i] = 0.02 * @as(f32, @floatFromInt(i + 1));
        dy1[i] = 0.5;
        dy2[i] = -0.25;
    }
    try core.forwardLayer(0, x1, x2, y1, y2);
    try core.backwardLayer(0, y1, y2, dy1, dy2, dx1, dx2);
}

test "scatter inverts itself" {
    const data = [_]f32{ 1.0, -2.5, 3.25, 0.0, 4.5, -1.5, 2.0, 0.75 };
    var a: [8]f32 = undefined;
    var b: [8]f32 = undefined;
    var sa: [8]f32 = undefined;
    var sb: [8]f32 = undefined;
    @memcpy(&a, &data);
    @memcpy(&b, &data);
    scatterPair(&a, &b, &sa, &sb);
    var ra: [8]f32 = undefined;
    var rb: [8]f32 = undefined;
    scatterInversePair(&sa, &sb, &ra, &rb);
    for (0..8) |i| {
        try std.testing.expectApproxEqAbs(a[i], ra[i], 1.0e-5);
        try std.testing.expectApproxEqAbs(b[i], rb[i], 1.0e-5);
    }
}
