const std = @import("std");
const api = @import("api.zig");

pub const BenchError = error{
    InvalidConfig,
    AllocationFailed,
} || api.RSFError;

pub const BenchConfig = struct {
    dim: usize = 64,
    layers: usize = 4,
    iterations: usize = 100,
    warmup: usize = 10,
    learning_rate: f32 = 1.0e-3,
    momentum: f32 = 0.9,
    seed: u64 = 0xA5A5A5A5,
};

pub const BenchResult = struct {
    label: []const u8,
    iterations: usize,
    total_ns: u64,
    min_ns: u64,
    max_ns: u64,
    mean_ns: f64,
    p50_ns: u64,
    p99_ns: u64,
    throughput_per_sec: f64,
};

pub const Benchmark = struct {
    allocator: std.mem.Allocator,
    config: BenchConfig,

    pub fn init(allocator: std.mem.Allocator, config: BenchConfig) Benchmark {
        return .{ .allocator = allocator, .config = config };
    }

    pub fn forwardOnly(self: *Benchmark) BenchError!BenchResult {
        const cfg = api.RSFConfig{
            .dim = self.config.dim,
            .layers = self.config.layers,
            .seed = self.config.seed,
        };
        var model = try api.RSF.create(self.allocator, cfg);
        defer model.destroy();
        const half = cfg.dim / 2;
        const x1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(x1);
        const x2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(x2);
        const y1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(y1);
        const y2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(y2);
        for (0..half) |i| {
            const f = @as(f32, @floatFromInt(i)) * 0.01;
            x1[i] = f;
            x2[i] = -f;
        }
        var i: usize = 0;
        while (i < self.config.warmup) : (i += 1) {
            try model.forward(x1, x2, y1, y2);
        }
        return try self.measure("forward", self.config.iterations, struct {
            ctx: *api.RSF,
            x1: []const f32,
            x2: []const f32,
            y1: []f32,
            y2: []f32,
            fn step(s: *@This()) BenchError!void {
                try s.ctx.forward(s.x1, s.x2, s.y1, s.y2);
            }
        }, .{ .ctx = &model, .x1 = x1, .x2 = x2, .y1 = y1, .y2 = y2 });
    }

    pub fn inverseOnly(self: *Benchmark) BenchError!BenchResult {
        const cfg = api.RSFConfig{
            .dim = self.config.dim,
            .layers = self.config.layers,
            .seed = self.config.seed,
        };
        var model = try api.RSF.create(self.allocator, cfg);
        defer model.destroy();
        const half = cfg.dim / 2;
        const y1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(y1);
        const y2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(y2);
        const r1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(r1);
        const r2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(r2);
        for (0..half) |i| {
            const f = @as(f32, @floatFromInt(i)) * 0.01;
            y1[i] = f;
            y2[i] = -f;
        }
        var i: usize = 0;
        while (i < self.config.warmup) : (i += 1) {
            try model.inverse(y1, y2, r1, r2);
        }
        return try self.measure("inverse", self.config.iterations, struct {
            ctx: *api.RSF,
            y1: []const f32,
            y2: []const f32,
            r1: []f32,
            r2: []f32,
            fn step(s: *@This()) BenchError!void {
                try s.ctx.inverse(s.y1, s.y2, s.r1, s.r2);
            }
        }, .{ .ctx = &model, .y1 = y1, .y2 = y2, .r1 = r1, .r2 = r2 });
    }

    pub fn trainingStep(self: *Benchmark) BenchError!BenchResult {
        const cfg = api.RSFConfig{
            .dim = self.config.dim,
            .layers = self.config.layers,
            .seed = self.config.seed,
        };
        var model = try api.RSF.create(self.allocator, cfg);
        defer model.destroy();
        const half = cfg.dim / 2;
        const x1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(x1);
        const x2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(x2);
        const t1 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(t1);
        const t2 = try self.allocator.alloc(f32, half);
        defer self.allocator.free(t2);
        for (0..half) |i| {
            x1[i] = @as(f32, @floatFromInt(i)) * 0.01;
            x2[i] = @as(f32, @floatFromInt(i)) * -0.01;
            t1[i] = 0.0;
            t2[i] = 0.0;
        }
        var i: usize = 0;
        while (i < self.config.warmup) : (i += 1) {
            _ = try model.step(x1, x2, t1, t2, self.config.learning_rate, self.config.momentum);
        }
        return try self.measure("step", self.config.iterations, struct {
            ctx: *api.RSF,
            x1: []const f32,
            x2: []const f32,
            t1: []const f32,
            t2: []const f32,
            lr: f32,
            mom: f32,
            fn step(s: *@This()) BenchError!void {
                _ = try s.ctx.step(s.x1, s.x2, s.t1, s.t2, s.lr, s.mom);
            }
        }, .{
            .ctx = &model,
            .x1 = x1,
            .x2 = x2,
            .t1 = t1,
            .t2 = t2,
            .lr = self.config.learning_rate,
            .mom = self.config.momentum,
        });
    }

    fn measure(self: *Benchmark, label: []const u8, iters: usize, comptime State: type, init_state: State) BenchError!BenchResult {
        var samples = try self.allocator.alloc(u64, iters);
        defer self.allocator.free(samples);
        var state = init_state;
        var i: usize = 0;
        var total: u64 = 0;
        var min_v: u64 = std.math.maxInt(u64);
        var max_v: u64 = 0;
        while (i < iters) : (i += 1) {
            const start = std.time.nanoTimestamp();
            try state.step();
            const dur: u64 = @intCast(std.time.nanoTimestamp() - start);
            samples[i] = dur;
            total += dur;
            if (dur < min_v) min_v = dur;
            if (dur > max_v) max_v = dur;
        }
        std.sort.heap(u64, samples, {}, std.sort.asc(u64));
        const p50 = samples[iters / 2];
        const p99_idx = if (iters >= 100) (iters * 99) / 100 else iters - 1;
        const p99 = samples[p99_idx];
        const mean: f64 = @as(f64, @floatFromInt(total)) / @as(f64, @floatFromInt(iters));
        const throughput: f64 = if (mean > 0.0) 1.0e9 / mean else 0.0;
        return BenchResult{
            .label = label,
            .iterations = iters,
            .total_ns = total,
            .min_ns = min_v,
            .max_ns = max_v,
            .mean_ns = mean,
            .p50_ns = p50,
            .p99_ns = p99,
            .throughput_per_sec = throughput,
        };
    }
};

pub fn printResult(writer: anytype, result: BenchResult) !void {
    try writer.print("{s:<10} iters={d:<6} mean={d:>10.1}ns min={d:>10}ns max={d:>10}ns p50={d:>10}ns p99={d:>10}ns throughput={d:>12.1}/s\n", .{
        result.label,
        result.iterations,
        result.mean_ns,
        result.min_ns,
        result.max_ns,
        result.p50_ns,
        result.p99_ns,
        result.throughput_per_sec,
    });
}

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const args = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, args);
    var dim: usize = 64;
    var layers: usize = 4;
    var iters: usize = 100;
    var warmup: usize = 10;
    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const arg = args[i];
        if (std.mem.eql(u8, arg, "--dim") and i + 1 < args.len) {
            dim = try std.fmt.parseInt(usize, args[i + 1], 10);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--layers") and i + 1 < args.len) {
            layers = try std.fmt.parseInt(usize, args[i + 1], 10);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--iters") and i + 1 < args.len) {
            iters = try std.fmt.parseInt(usize, args[i + 1], 10);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--warmup") and i + 1 < args.len) {
            warmup = try std.fmt.parseInt(usize, args[i + 1], 10);
            i += 1;
        }
    }
    const cfg = BenchConfig{
        .dim = dim,
        .layers = layers,
        .iterations = iters,
        .warmup = warmup,
    };
    var bench = Benchmark.init(alloc, cfg);
    const stdout = std.io.getStdOut().writer();
    try stdout.print("RSF benchmark: dim={d} layers={d} iters={d} warmup={d}\n", .{ dim, layers, iters, warmup });
    const fwd = try bench.forwardOnly();
    try printResult(stdout, fwd);
    const inv = try bench.inverseOnly();
    try printResult(stdout, inv);
    const train = try bench.trainingStep();
    try printResult(stdout, train);
}

test "benchmark forward small" {
    const alloc = std.testing.allocator;
    var bench = Benchmark.init(alloc, .{ .dim = 8, .layers = 1, .iterations = 10, .warmup = 2 });
    const r = try bench.forwardOnly();
    try std.testing.expectEqual(@as(usize, 10), r.iterations);
    try std.testing.expect(r.total_ns > 0);
}
