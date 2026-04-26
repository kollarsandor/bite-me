const std = @import("std");
const rsf = @import("rsf");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const args = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, args);
    if (args.len < 2) {
        const stderr = std.io.getStdErr().writer();
        try stderr.print("Usage: rsf-inspect <model.rsf> [--dump-layer N]\n", .{});
        return;
    }
    const path = args[1];
    var dump_layer: ?usize = null;
    var i: usize = 2;
    while (i < args.len) : (i += 1) {
        if (std.mem.eql(u8, args[i], "--dump-layer") and i + 1 < args.len) {
            dump_layer = try std.fmt.parseInt(usize, args[i + 1], 10);
            i += 1;
        }
    }
    const dir = std.fs.cwd();
    const file = try dir.openFile(path, .{});
    defer file.close();
    const stat = try file.stat();
    const bytes = try alloc.alloc(u8, @intCast(stat.size));
    const n = try file.readAll(bytes);
    if (n != bytes.len) {
        return error.ShortRead;
    }
    var snap = try rsf.snapshot_mod.SavedModelSnapshot.readBytes(alloc, bytes);
    defer snap.deinit();
    const stdout = std.io.getStdOut().writer();
    try stdout.print("RSF model file: {s}\n", .{path});
    try stdout.print("  size: {d} bytes\n", .{stat.size});
    try stdout.print("  dim: {d}\n", .{snap.config.dim});
    try stdout.print("  layers: {d}\n", .{snap.config.layers});
    try stdout.print("  clip range: [{d:.4}, {d:.4}]\n", .{ snap.config.clip_min, snap.config.clip_max });
    try stdout.print("  learning rate: {d:.6}\n", .{snap.config.learning_rate});
    try stdout.print("  momentum: {d:.6}\n", .{snap.config.momentum});
    try stdout.print("  seed: 0x{x}\n", .{snap.config.seed});
    try stdout.print("  global step: {d}\n", .{snap.global_step});
    try stdout.print("  parameters per layer: {d}\n", .{snap.config.paramsPerLayer()});
    try stdout.print("  total parameters: {d}\n", .{snap.config.totalParams()});
    var li: usize = 0;
    while (li < snap.layer_data.len) : (li += 1) {
        const slice = snap.layer_data[li];
        const half = snap.config.dim / 2;
        const matrix_len = half * half;
        const w_s = slice[0..matrix_len];
        const w_t = slice[matrix_len .. 2 * matrix_len];
        const b_s = slice[2 * matrix_len .. 2 * matrix_len + half];
        const b_t = slice[2 * matrix_len + half .. 2 * matrix_len + 2 * half];
        const norm_s = frobeniusNorm(w_s);
        const norm_t = frobeniusNorm(w_t);
        const bs_norm = frobeniusNorm(b_s);
        const bt_norm = frobeniusNorm(b_t);
        try stdout.print("  layer[{d:>3}]: |Ws|={d:>10.4} |Wt|={d:>10.4} |bs|={d:>10.4} |bt|={d:>10.4}\n", .{ li, norm_s, norm_t, bs_norm, bt_norm });
        if (dump_layer) |target| {
            if (target == li) {
                try stdout.print("    Ws[0..min(8,n)]: ", .{});
                try printSample(stdout, w_s);
                try stdout.print("\n    Wt[0..min(8,n)]: ", .{});
                try printSample(stdout, w_t);
                try stdout.print("\n    bs: ", .{});
                try printSample(stdout, b_s);
                try stdout.print("\n    bt: ", .{});
                try printSample(stdout, b_t);
                try stdout.print("\n", .{});
            }
        }
    }
}

fn frobeniusNorm(slice: []const f32) f32 {
    var acc: f32 = 0.0;
    for (slice) |v| acc += v * v;
    return @sqrt(acc);
}

fn printSample(writer: anytype, slice: []const f32) !void {
    const limit = @min(slice.len, 8);
    try writer.print("[", .{});
    for (slice[0..limit], 0..) |v, idx| {
        if (idx > 0) try writer.print(", ", .{});
        try writer.print("{d:.4}", .{v});
    }
    if (slice.len > limit) try writer.print(", ...", .{});
    try writer.print("]", .{});
}
