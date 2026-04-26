const std = @import("std");
const rsf = @import("rsf");

const Command = enum {
    info,
    init,
    train,
    inspect,
    save,
    load,
    repair,
    forward,
    invert,
    help,
};

const Args = struct {
    command: Command,
    path: ?[]const u8 = null,
    dim: usize = 64,
    layers: usize = 4,
    seed: u64 = 0xC0FFEE,
    learning_rate: f32 = 1.0e-3,
    momentum: f32 = 0.9,
    steps: usize = 100,
};

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const argv = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, argv);
    const stdout = std.io.getStdOut().writer();
    const stderr = std.io.getStdErr().writer();
    if (argv.len < 2) {
        try printUsage(stdout);
        return;
    }
    const args = parseArgs(argv) catch |err| {
        try stderr.print("Argument parse error: {s}\n", .{@errorName(err)});
        try printUsage(stderr);
        return;
    };
    switch (args.command) {
        .help => try printUsage(stdout),
        .info => try cmdInfo(stdout, alloc, args),
        .init => try cmdInit(stdout, alloc, args),
        .train => try cmdTrain(stdout, alloc, args),
        .inspect => try cmdInspect(stdout, alloc, args),
        .save => try cmdSave(stdout, alloc, args),
        .load => try cmdLoad(stdout, alloc, args),
        .repair => try cmdRepair(stdout, alloc, args),
        .forward => try cmdForward(stdout, alloc, args),
        .invert => try cmdInvert(stdout, alloc, args),
    }
}

fn parseArgs(argv: [][:0]u8) !Args {
    var args = Args{ .command = .help };
    if (argv.len < 2) return args;
    args.command = parseCommand(argv[1]) orelse return error.UnknownCommand;
    var i: usize = 2;
    while (i < argv.len) : (i += 1) {
        const arg = argv[i];
        if (std.mem.eql(u8, arg, "--path") and i + 1 < argv.len) {
            args.path = argv[i + 1];
            i += 1;
        } else if (std.mem.eql(u8, arg, "--dim") and i + 1 < argv.len) {
            args.dim = try std.fmt.parseInt(usize, argv[i + 1], 10);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--layers") and i + 1 < argv.len) {
            args.layers = try std.fmt.parseInt(usize, argv[i + 1], 10);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--seed") and i + 1 < argv.len) {
            args.seed = try std.fmt.parseInt(u64, argv[i + 1], 0);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--lr") and i + 1 < argv.len) {
            args.learning_rate = try std.fmt.parseFloat(f32, argv[i + 1]);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--momentum") and i + 1 < argv.len) {
            args.momentum = try std.fmt.parseFloat(f32, argv[i + 1]);
            i += 1;
        } else if (std.mem.eql(u8, arg, "--steps") and i + 1 < argv.len) {
            args.steps = try std.fmt.parseInt(usize, argv[i + 1], 10);
            i += 1;
        }
    }
    return args;
}

fn parseCommand(name: []const u8) ?Command {
    if (std.mem.eql(u8, name, "info")) return .info;
    if (std.mem.eql(u8, name, "init")) return .init;
    if (std.mem.eql(u8, name, "train")) return .train;
    if (std.mem.eql(u8, name, "inspect")) return .inspect;
    if (std.mem.eql(u8, name, "save")) return .save;
    if (std.mem.eql(u8, name, "load")) return .load;
    if (std.mem.eql(u8, name, "repair")) return .repair;
    if (std.mem.eql(u8, name, "forward")) return .forward;
    if (std.mem.eql(u8, name, "invert")) return .invert;
    if (std.mem.eql(u8, name, "help")) return .help;
    return null;
}

fn printUsage(writer: anytype) !void {
    try writer.print("rsf - Reversible Scatter Flow runtime\n", .{});
    try writer.print("\nUsage:\n", .{});
    try writer.print("  rsf info\n", .{});
    try writer.print("  rsf init    --path <file> [--dim D] [--layers L] [--seed S]\n", .{});
    try writer.print("  rsf train   --path <file> [--steps N] [--lr R] [--momentum M]\n", .{});
    try writer.print("  rsf inspect --path <file>\n", .{});
    try writer.print("  rsf save    --path <file>\n", .{});
    try writer.print("  rsf load    --path <file>\n", .{});
    try writer.print("  rsf repair  --path <file>\n", .{});
    try writer.print("  rsf forward --path <file>\n", .{});
    try writer.print("  rsf invert  --path <file>\n", .{});
}

fn cmdInfo(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    _ = alloc;
    _ = args;
    try writer.print("rsf {s}\n", .{rsfVersion()});
    try writer.print("  bijective coupling layers with O(1) backward memory\n", .{});
    try writer.print("  scatter mixing factor 1/sqrt(2) ~= 0.7071068\n", .{});
    try writer.print("  default clip range [-5, 5]\n", .{});
    try writer.print("  Futhark kernels: c/compute.fut\n", .{});
}

fn cmdInit(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    const cfg = rsf.RSFConfig{
        .dim = args.dim,
        .layers = args.layers,
        .seed = args.seed,
        .learning_rate = args.learning_rate,
        .momentum = args.momentum,
    };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    try model.save(std.fs.cwd(), path);
    try writer.print("initialised RSF model at '{s}': dim={d} layers={d}\n", .{ path, args.dim, args.layers });
}

fn cmdTrain(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    var cfg = rsf.RSFConfig{
        .dim = args.dim,
        .layers = args.layers,
        .seed = args.seed,
        .learning_rate = args.learning_rate,
        .momentum = args.momentum,
    };
    var loaded_opt: ?rsf.snapshot_mod.SavedModelSnapshot = null;
    if (rsf.snapshot_mod.readSnapshotFromFile(alloc, std.fs.cwd(), path)) |loaded_const| {
        loaded_opt = loaded_const;
        cfg = loaded_const.config;
    } else |_| {}
    defer if (loaded_opt) |*ld| ld.deinit();
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    if (loaded_opt) |*ld| try model.restoreFromSnapshot(ld);
    const half = cfg.dim / 2;
    const x1 = try alloc.alloc(f32, half);
    defer alloc.free(x1);
    const x2 = try alloc.alloc(f32, half);
    defer alloc.free(x2);
    const t1 = try alloc.alloc(f32, half);
    defer alloc.free(t1);
    const t2 = try alloc.alloc(f32, half);
    defer alloc.free(t2);
    var seed_state = rsf.security.xoshiroSeed(args.seed);
    for (0..half) |i| {
        x1[i] = rsf.security.uniformF32FromU64(rsf.security.xoshiroNext(&seed_state)) * 0.5;
        x2[i] = rsf.security.uniformF32FromU64(rsf.security.xoshiroNext(&seed_state)) * 0.5;
        t1[i] = rsf.security.uniformF32FromU64(rsf.security.xoshiroNext(&seed_state));
        t2[i] = rsf.security.uniformF32FromU64(rsf.security.xoshiroNext(&seed_state));
    }
    var step_idx: usize = 0;
    var last_loss: f32 = 0.0;
    while (step_idx < args.steps) : (step_idx += 1) {
        last_loss = try model.step(x1, x2, t1, t2, args.learning_rate, args.momentum);
        if (step_idx % 10 == 0 or step_idx + 1 == args.steps) {
            try writer.print("step {d:>5}: loss={d:.6}\n", .{ step_idx, last_loss });
        }
    }
    try model.save(std.fs.cwd(), path);
    try writer.print("trained {d} steps, final loss={d:.6}, saved to '{s}'\n", .{ args.steps, last_loss, path });
}

fn cmdInspect(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    var snap = try rsf.snapshot_mod.readSnapshotFromFile(alloc, std.fs.cwd(), path);
    defer snap.deinit();
    try writer.print("model: {s}\n", .{path});
    try writer.print("  dim={d} layers={d} step={d}\n", .{ snap.config.dim, snap.config.layers, snap.global_step });
    for (snap.layer_data, 0..) |slice, idx| {
        var sq: f32 = 0.0;
        for (slice) |v| sq += v * v;
        try writer.print("  layer[{d}] |w| = {d:.4}\n", .{ idx, @sqrt(sq) });
    }
}

fn cmdSave(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    const cfg = rsf.RSFConfig{ .dim = args.dim, .layers = args.layers, .seed = args.seed };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    try model.save(std.fs.cwd(), path);
    try writer.print("saved fresh RSF model to '{s}'\n", .{path});
}

fn cmdLoad(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    var snap = try rsf.snapshot_mod.readSnapshotFromFile(alloc, std.fs.cwd(), path);
    defer snap.deinit();
    var model = try rsf.RSF.create(alloc, snap.config);
    defer model.destroy();
    try model.restoreFromSnapshot(&snap);
    try writer.print("loaded model '{s}': dim={d} layers={d}\n", .{ path, snap.config.dim, snap.config.layers });
}

fn cmdRepair(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    var rep = try rsf.repair_mod.Repairer.init(alloc, std.fs.cwd(), path);
    defer rep.deinit();
    const report = try rep.repair();
    try writer.print("repair '{s}': primary_valid={} backup_valid={} repaired_from_backup={} promoted_temp={} bytes_total={d}\n", .{
        path,
        report.primary_valid,
        report.backup_valid,
        report.repaired_from_backup,
        report.promoted_temp,
        report.bytes_total,
    });
}

fn cmdForward(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    var snap = try rsf.snapshot_mod.readSnapshotFromFile(alloc, std.fs.cwd(), path);
    defer snap.deinit();
    var model = try rsf.RSF.create(alloc, snap.config);
    defer model.destroy();
    try model.restoreFromSnapshot(&snap);
    const half = snap.config.dim / 2;
    const x1 = try alloc.alloc(f32, half);
    defer alloc.free(x1);
    const x2 = try alloc.alloc(f32, half);
    defer alloc.free(x2);
    const y1 = try alloc.alloc(f32, half);
    defer alloc.free(y1);
    const y2 = try alloc.alloc(f32, half);
    defer alloc.free(y2);
    for (0..half) |i| {
        x1[i] = @as(f32, @floatFromInt(i)) * 0.01;
        x2[i] = @as(f32, @floatFromInt(i)) * -0.01;
    }
    try model.forward(x1, x2, y1, y2);
    try writer.print("forward output:\n  y1=", .{});
    try printSlice(writer, y1);
    try writer.print("\n  y2=", .{});
    try printSlice(writer, y2);
    try writer.print("\n", .{});
}

fn cmdInvert(writer: anytype, alloc: std.mem.Allocator, args: Args) !void {
    const path = args.path orelse return error.MissingPath;
    var snap = try rsf.snapshot_mod.readSnapshotFromFile(alloc, std.fs.cwd(), path);
    defer snap.deinit();
    var model = try rsf.RSF.create(alloc, snap.config);
    defer model.destroy();
    try model.restoreFromSnapshot(&snap);
    const half = snap.config.dim / 2;
    const y1 = try alloc.alloc(f32, half);
    defer alloc.free(y1);
    const y2 = try alloc.alloc(f32, half);
    defer alloc.free(y2);
    const x1 = try alloc.alloc(f32, half);
    defer alloc.free(x1);
    const x2 = try alloc.alloc(f32, half);
    defer alloc.free(x2);
    for (0..half) |i| {
        y1[i] = @as(f32, @floatFromInt(i)) * 0.01;
        y2[i] = @as(f32, @floatFromInt(i)) * -0.01;
    }
    try model.inverse(y1, y2, x1, x2);
    try writer.print("inverse output:\n  x1=", .{});
    try printSlice(writer, x1);
    try writer.print("\n  x2=", .{});
    try printSlice(writer, x2);
    try writer.print("\n", .{});
}

fn printSlice(writer: anytype, slice: []const f32) !void {
    const limit = @min(slice.len, 8);
    try writer.print("[", .{});
    for (slice[0..limit], 0..) |v, idx| {
        if (idx > 0) try writer.print(", ", .{});
        try writer.print("{d:.5}", .{v});
    }
    if (slice.len > limit) try writer.print(", ...", .{});
    try writer.print("]", .{});
}

fn rsfVersion() []const u8 {
    return "0.4.0";
}
