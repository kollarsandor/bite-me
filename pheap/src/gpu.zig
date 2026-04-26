const std = @import("std");
const security = @import("security.zig");
const schema = @import("schema.zig");
const pheap_core = @import("../c/pheap.zig");

pub const GpuError = error{
    BackendUnavailable,
    DeviceAllocationFailed,
    SynchronizationFailed,
    KernelFailed,
    DimensionMismatch,
    InvalidContext,
} || std.mem.Allocator.Error || security.SecurityError;

pub const Backend = enum(u8) {
    cpu = 0,
    futhark_c = 1,
    futhark_cuda = 2,
    futhark_opencl = 3,
};

pub const ContextConfig = struct {
    backend: Backend = .cpu,
    group_size: u32 = 256,
    tile_size: u32 = 32,
    device_id: i32 = 0,
};

pub const ExecutionStats = struct {
    forward_calls: u64 = 0,
    inverse_calls: u64 = 0,
    backward_calls: u64 = 0,
    matmul_calls: u64 = 0,
    flops_estimate: u64 = 0,
    last_kernel_ns: u64 = 0,

    pub fn record(self: *ExecutionStats, ns: u64, flops: u64) void {
        self.flops_estimate += flops;
        self.last_kernel_ns = ns;
    }
};

pub const Context = struct {
    config: ContextConfig,
    allocator: std.mem.Allocator,
    stats: ExecutionStats = .{},
    initialized: bool = false,

    pub fn init(allocator: std.mem.Allocator, config: ContextConfig) Context {
        return .{
            .config = config,
            .allocator = allocator,
            .initialized = true,
        };
    }

    pub fn deinit(self: *Context) void {
        self.initialized = false;
    }

    pub fn synchronize(self: *Context) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
    }

    pub fn forward(
        self: *Context,
        core: *pheap_core.RSFCore,
        layer_index: usize,
        x1: []const f32,
        x2: []const f32,
        y1: []f32,
        y2: []f32,
    ) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        const start = monoNs();
        core.forwardLayer(layer_index, x1, x2, y1, y2) catch return GpuError.KernelFailed;
        const dur = monoNs() - start;
        const half = core.config.dim / 2;
        const flops: u64 = @as(u64, half) * @as(u64, half) * 4 + @as(u64, half) * 6;
        self.stats.record(dur, flops);
        self.stats.forward_calls += 1;
    }

    pub fn inverse(
        self: *Context,
        core: *pheap_core.RSFCore,
        layer_index: usize,
        y1: []const f32,
        y2: []const f32,
        x1: []f32,
        x2: []f32,
    ) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        const start = monoNs();
        core.inverseLayer(layer_index, y1, y2, x1, x2) catch return GpuError.KernelFailed;
        const dur = monoNs() - start;
        const half = core.config.dim / 2;
        const flops: u64 = @as(u64, half) * @as(u64, half) * 4 + @as(u64, half) * 6;
        self.stats.record(dur, flops);
        self.stats.inverse_calls += 1;
    }

    pub fn backward(
        self: *Context,
        core: *pheap_core.RSFCore,
        layer_index: usize,
        y1: []const f32,
        y2: []const f32,
        dy1: []const f32,
        dy2: []const f32,
        dx1: []f32,
        dx2: []f32,
    ) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        const start = monoNs();
        core.backwardLayer(layer_index, y1, y2, dy1, dy2, dx1, dx2) catch return GpuError.KernelFailed;
        const dur = monoNs() - start;
        const half = core.config.dim / 2;
        const flops: u64 = @as(u64, half) * @as(u64, half) * 12 + @as(u64, half) * 12;
        self.stats.record(dur, flops);
        self.stats.backward_calls += 1;
    }

    pub fn matmul(
        self: *Context,
        a: []const f32,
        b: []const f32,
        out: []f32,
        m: usize,
        n: usize,
        p: usize,
    ) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        if (a.len != m * n or b.len != n * p or out.len != m * p) return GpuError.DimensionMismatch;
        const start = monoNs();
        var i: usize = 0;
        while (i < m) : (i += 1) {
            var j: usize = 0;
            while (j < p) : (j += 1) {
                var acc: f32 = 0.0;
                var k: usize = 0;
                while (k < n) : (k += 1) {
                    acc += a[i * n + k] * b[k * p + j];
                }
                out[i * p + j] = acc;
            }
        }
        const dur = monoNs() - start;
        self.stats.matmul_calls += 1;
        self.stats.record(dur, @as(u64, m) * @as(u64, n) * @as(u64, p) * 2);
    }

    pub fn scatter(
        self: *Context,
        in1: []const f32,
        in2: []const f32,
        out1: []f32,
        out2: []f32,
    ) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        if (in1.len != in2.len or out1.len != in1.len or out2.len != in1.len) return GpuError.DimensionMismatch;
        const start = monoNs();
        pheap_core.scatterPair(in1, in2, out1, out2);
        const dur = monoNs() - start;
        self.stats.record(dur, @as(u64, in1.len) * 4);
    }

    pub fn spectralClip(self: *Context, values: []f32, lo: f32, hi: f32) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        const start = monoNs();
        for (values) |*v| {
            if (v.* < lo) v.* = lo;
            if (v.* > hi) v.* = hi;
        }
        const dur = monoNs() - start;
        self.stats.record(dur, @as(u64, values.len) * 2);
    }

    pub fn xavierFill(self: *Context, target: []f32, fan_in: usize, fan_out: usize, seed: u64) GpuError!void {
        if (!self.initialized) return GpuError.InvalidContext;
        const start = monoNs();
        const limit = @sqrt(6.0 / @as(f32, @floatFromInt(fan_in + fan_out)));
        var state = security.xoshiroSeed(seed);
        for (target) |*v| {
            const u = security.uniformF32FromU64(security.xoshiroNext(&state));
            v.* = (2.0 * u - 1.0) * limit;
        }
        const dur = monoNs() - start;
        self.stats.record(dur, @as(u64, target.len) * 4);
    }

    pub fn dotProduct(self: *Context, a: []const f32, b: []const f32) GpuError!f32 {
        if (!self.initialized) return GpuError.InvalidContext;
        if (a.len != b.len) return GpuError.DimensionMismatch;
        const start = monoNs();
        var acc: f32 = 0.0;
        for (a, b) |x, y| {
            const p = x * y;
            if (!std.math.isNan(p)) acc += p;
        }
        const dur = monoNs() - start;
        self.stats.record(dur, @as(u64, a.len) * 2);
        return acc;
    }
};

fn monoNs() u64 {
    return @intCast(std.time.nanoTimestamp());
}

pub const DeviceArray = struct {
    data: []align(64) f32,
    rows: usize,
    cols: usize,
    on_device: bool,
    backend: Backend,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, rows: usize, cols: usize, backend: Backend) !DeviceArray {
        const total = std.math.mul(usize, rows, cols) catch return error.Overflow;
        const data = try allocator.alignedAlloc(f32, 64, total);
        @memset(data, 0.0);
        return .{
            .data = data,
            .rows = rows,
            .cols = cols,
            .on_device = backend != .cpu,
            .backend = backend,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *DeviceArray) void {
        if (self.data.len > 0) self.allocator.free(self.data);
        self.data = &[_]f32{};
    }

    pub fn copyFromHost(self: *DeviceArray, host: []const f32) !void {
        if (host.len != self.data.len) return error.DimensionMismatch;
        @memcpy(self.data, host);
    }

    pub fn copyToHost(self: *const DeviceArray, host: []f32) !void {
        if (host.len != self.data.len) return error.DimensionMismatch;
        @memcpy(host, self.data);
    }
};

test "context forward inverse" {
    const alloc = std.testing.allocator;
    var ctx = Context.init(alloc, .{});
    defer ctx.deinit();
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 1 };
    const core = try pheap_core.RSFCore.init(alloc, cfg);
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
        x2[i] = @as(f32, @floatFromInt(i)) * -0.05;
    }
    try ctx.forward(core, 0, x1, x2, y1, y2);
    try ctx.inverse(core, 0, y1, y2, r1, r2);
    for (0..half) |i| {
        try std.testing.expectApproxEqAbs(x1[i], r1[i], 1.0e-4);
        try std.testing.expectApproxEqAbs(x2[i], r2[i], 1.0e-4);
    }
    try std.testing.expectEqual(@as(u64, 1), ctx.stats.forward_calls);
    try std.testing.expectEqual(@as(u64, 1), ctx.stats.inverse_calls);
}

test "context matmul" {
    const alloc = std.testing.allocator;
    var ctx = Context.init(alloc, .{});
    defer ctx.deinit();
    const a = [_]f32{ 1, 2, 3, 4 };
    const b = [_]f32{ 5, 6, 7, 8 };
    var out: [4]f32 = undefined;
    try ctx.matmul(&a, &b, &out, 2, 2, 2);
    try std.testing.expectApproxEqAbs(@as(f32, 19.0), out[0], 1.0e-6);
    try std.testing.expectApproxEqAbs(@as(f32, 22.0), out[1], 1.0e-6);
    try std.testing.expectApproxEqAbs(@as(f32, 43.0), out[2], 1.0e-6);
    try std.testing.expectApproxEqAbs(@as(f32, 50.0), out[3], 1.0e-6);
}

test "device array copy" {
    const alloc = std.testing.allocator;
    var arr = try DeviceArray.init(alloc, 4, 4, .cpu);
    defer arr.deinit();
    const src = [_]f32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 };
    try arr.copyFromHost(&src);
    var dst: [16]f32 = undefined;
    try arr.copyToHost(&dst);
    for (0..16) |i| try std.testing.expectEqual(src[i], dst[i]);
}
