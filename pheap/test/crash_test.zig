const std = @import("std");
const rsf = @import("rsf");

test "snapshot survives partial primary corruption with backup intact" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 16, .layers = 2 };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    try model.save(tmp_dir.dir, "ckpt.rsf");
    try tmp_dir.dir.copyFile("ckpt.rsf", tmp_dir.dir, "ckpt.rsf.bak", .{});
    var f = try tmp_dir.dir.openFile("ckpt.rsf", .{ .mode = .read_write });
    try f.seekTo(48);
    try f.writeAll(&[_]u8{ 0xDE, 0xAD, 0xBE, 0xEF });
    f.close();
    const report = try model.repair(tmp_dir.dir, "ckpt.rsf");
    try std.testing.expect(report.primary_valid);
    try std.testing.expect(report.repaired_from_backup);
    var loaded = try rsf.snapshot_mod.readSnapshotFromFile(alloc, tmp_dir.dir, "ckpt.rsf");
    defer loaded.deinit();
    try std.testing.expectEqual(cfg.dim, loaded.config.dim);
}

test "save abort leaves no temp file" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 8, .layers = 1 };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    var snap = try model.snapshot();
    defer snap.deinit();
    var tx = try rsf.transaction.SnapshotTransaction.begin(alloc, tmp_dir.dir, "abort.rsf", snap);
    defer tx.deinit();
    tx.abort();
    try std.testing.expectError(error.FileNotFound, tmp_dir.dir.access("abort.rsf.tmp", .{}));
    try std.testing.expectError(error.FileNotFound, tmp_dir.dir.access("abort.rsf", .{}));
}

test "wal recovery after simulated crash" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var w = try rsf.wal.WriteAheadLog.create(alloc, tmp_dir.dir, "crash.wal", 1);
    _ = try w.append(.forward_step, "fwd-1");
    _ = try w.append(.backward_step, "bwd-1");
    _ = try w.append(.apply_update, "upd-1");
    w.deinit();
    var rep = try rsf.wal.Replay.open(alloc, tmp_dir.dir, "crash.wal");
    defer rep.deinit();
    var counts: usize = 0;
    while (true) {
        const m = try rep.next();
        if (m) |_| counts += 1 else break;
    }
    try std.testing.expectEqual(@as(usize, 3), counts);
}

test "round trip after train then save then load" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 8, .layers = 1 };
    var model_a = try rsf.RSF.create(alloc, cfg);
    defer model_a.destroy();
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
        x1[i] = 0.05;
        x2[i] = -0.05;
        t1[i] = 0.5;
        t2[i] = -0.5;
    }
    var iter: usize = 0;
    while (iter < 5) : (iter += 1) {
        _ = try model_a.step(x1, x2, t1, t2, 0.01, 0.5);
    }
    try model_a.save(tmp_dir.dir, "trained.rsf");
    var model_b = try rsf.RSF.create(alloc, cfg);
    defer model_b.destroy();
    try model_b.load(tmp_dir.dir, "trained.rsf");
    var snap_a = try model_a.snapshot();
    defer snap_a.deinit();
    var snap_b = try model_b.snapshot();
    defer snap_b.deinit();
    try std.testing.expectApproxEqAbs(@as(f32, 0.0), snap_a.diffNorm(&snap_b), 1.0e-4);
}

test "double save keeps backup" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 8, .layers = 1 };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    try model.save(tmp_dir.dir, "twice.rsf");
    try model.save(tmp_dir.dir, "twice.rsf");
    try tmp_dir.dir.access("twice.rsf", .{});
    try tmp_dir.dir.access("twice.rsf.bak", .{});
}

test "repair fails when both files missing" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 8, .layers = 1 };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    try std.testing.expectError(rsf.repair_mod.RepairError.NotRepairable, model.repair(tmp_dir.dir, "missing.rsf"));
}

test "wal corrupted record detected" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    var w = try rsf.wal.WriteAheadLog.create(alloc, tmp_dir.dir, "corrupt.wal", 0);
    _ = try w.append(.forward_step, "payload-data-here");
    w.deinit();
    var f = try tmp_dir.dir.openFile("corrupt.wal", .{ .mode = .read_write });
    try f.seekTo(rsf.wal.SEGMENT_HEADER_SIZE + rsf.wal.RECORD_HEADER_SIZE + 4 + 5);
    try f.writeAll(&[_]u8{ 0xFF, 0xFF });
    f.close();
    var rep = try rsf.wal.Replay.open(alloc, tmp_dir.dir, "corrupt.wal");
    defer rep.deinit();
    try std.testing.expectError(rsf.wal.WalError.Corrupted, rep.next());
}

test "header version rejected" {
    const alloc = std.testing.allocator;
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();
    const cfg = rsf.RSFConfig{ .dim = 8, .layers = 1 };
    var model = try rsf.RSF.create(alloc, cfg);
    defer model.destroy();
    try model.save(tmp_dir.dir, "ver.rsf");
    var f = try tmp_dir.dir.openFile("ver.rsf", .{ .mode = .read_write });
    try f.seekTo(4);
    try f.writeAll(&[_]u8{ 0xEE, 0xEE, 0xEE, 0xEE });
    f.close();
    try std.testing.expectError(rsf.header.HeaderError.UnsupportedVersion, rsf.snapshot_mod.readSnapshotFromFile(alloc, tmp_dir.dir, "ver.rsf"));
}
