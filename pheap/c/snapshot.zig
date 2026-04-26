const std = @import("std");
const schema = @import("../src/schema.zig");
const security = @import("../src/security.zig");
const header_mod = @import("../src/header.zig");
const pheap_core = @import("pheap.zig");

pub const SnapshotError = error{
    PayloadCorrupted,
    HeaderMismatch,
    LayerCountMismatch,
    BufferOverflow,
    IoFailed,
    ChecksumMismatch,
} || header_mod.HeaderError || security.SecurityError || std.mem.Allocator.Error;

pub const SavedModelSnapshot = struct {
    config: schema.RSFConfig,
    metadata: schema.ModelMetadata,
    global_step: u64,
    layer_data: [][]f32,
    allocator: std.mem.Allocator,

    pub fn capture(allocator: std.mem.Allocator, core: *pheap_core.RSFCore) SnapshotError!SavedModelSnapshot {
        const half = core.config.dim / 2;
        const matrix_len = half * half;
        const params_per_layer = 2 * matrix_len + 2 * half;
        var snap = SavedModelSnapshot{
            .config = core.config,
            .metadata = core.metadata,
            .global_step = core.metadata.global_step,
            .layer_data = try allocator.alloc([]f32, core.layers.len),
            .allocator = allocator,
        };
        errdefer {
            for (snap.layer_data, 0..) |slice, i| {
                if (slice.len > 0) allocator.free(slice);
                snap.layer_data[i] = &[_]f32{};
            }
            allocator.free(snap.layer_data);
        }
        for (core.layers, 0..) |*lc, i| {
            const buf = try allocator.alloc(f32, params_per_layer);
            @memcpy(buf[0..matrix_len], lc.w_s);
            @memcpy(buf[matrix_len .. 2 * matrix_len], lc.w_t);
            @memcpy(buf[2 * matrix_len .. 2 * matrix_len + half], lc.b_s);
            @memcpy(buf[2 * matrix_len + half .. 2 * matrix_len + 2 * half], lc.b_t);
            snap.layer_data[i] = buf;
        }
        return snap;
    }

    pub fn deinit(self: *SavedModelSnapshot) void {
        for (self.layer_data) |slice| {
            if (slice.len > 0) self.allocator.free(slice);
        }
        self.allocator.free(self.layer_data);
        self.layer_data = &[_][]f32{};
    }

    pub fn restore(self: *const SavedModelSnapshot, core: *pheap_core.RSFCore) SnapshotError!void {
        if (!core.config.equals(self.config)) return SnapshotError.HeaderMismatch;
        if (self.layer_data.len != core.layers.len) return SnapshotError.LayerCountMismatch;
        const half = core.config.dim / 2;
        const matrix_len = half * half;
        for (core.layers, 0..) |*lc, i| {
            const buf = self.layer_data[i];
            if (buf.len != 2 * matrix_len + 2 * half) return SnapshotError.PayloadCorrupted;
            try security.ensureFiniteF32(buf);
            @memcpy(lc.w_s, buf[0..matrix_len]);
            @memcpy(lc.w_t, buf[matrix_len .. 2 * matrix_len]);
            @memcpy(lc.b_s, buf[2 * matrix_len .. 2 * matrix_len + half]);
            @memcpy(lc.b_t, buf[2 * matrix_len + half .. 2 * matrix_len + 2 * half]);
            lc.zeroGradients();
            lc.zeroVelocities();
        }
        core.metadata = self.metadata;
        core.metadata.global_step = self.global_step;
    }

    pub fn writeBytes(self: *const SavedModelSnapshot, allocator: std.mem.Allocator) SnapshotError![]u8 {
        const half = self.config.dim / 2;
        const matrix_len = half * half;
        const params_per_layer = 2 * matrix_len + 2 * half;
        const payload_bytes: usize = self.layer_data.len * params_per_layer * @sizeOf(f32);
        const total: usize = header_mod.HEADER_SIZE + payload_bytes + @sizeOf(u32);
        const out = try allocator.alloc(u8, total);
        errdefer allocator.free(out);
        var hdr = header_mod.Header.fromConfig(self.config, self.global_step);
        try hdr.writeBytes(out[0..header_mod.HEADER_SIZE]);
        var cursor: usize = header_mod.HEADER_SIZE;
        for (self.layer_data) |slice| {
            const bytes = std.mem.sliceAsBytes(slice);
            @memcpy(out[cursor .. cursor + bytes.len], bytes);
            cursor += bytes.len;
        }
        const crc = security.Crc32.computeBytes(out[header_mod.HEADER_SIZE..cursor]);
        std.mem.writeIntLittle(u32, out[cursor .. cursor + 4][0..4], crc);
        return out;
    }

    pub fn readBytes(allocator: std.mem.Allocator, bytes: []const u8) SnapshotError!SavedModelSnapshot {
        if (bytes.len < header_mod.HEADER_SIZE + 4) return SnapshotError.PayloadCorrupted;
        const hdr = try header_mod.Header.readBytes(bytes[0..header_mod.HEADER_SIZE]);
        const cfg = try hdr.toConfig();
        const half = cfg.dim / 2;
        const matrix_len = half * half;
        const params_per_layer = 2 * matrix_len + 2 * half;
        const expected_payload = cfg.layers * params_per_layer * @sizeOf(f32);
        if (bytes.len < header_mod.HEADER_SIZE + expected_payload + 4) return SnapshotError.PayloadCorrupted;
        const payload_end: usize = header_mod.HEADER_SIZE + expected_payload;
        const stored_crc = std.mem.readIntLittle(u32, bytes[payload_end .. payload_end + 4][0..4]);
        const computed_crc = security.Crc32.computeBytes(bytes[header_mod.HEADER_SIZE..payload_end]);
        if (stored_crc != computed_crc) return SnapshotError.ChecksumMismatch;
        var snap = SavedModelSnapshot{
            .config = cfg,
            .metadata = schema.ModelMetadata.init("rsf"),
            .global_step = hdr.global_step,
            .layer_data = try allocator.alloc([]f32, cfg.layers),
            .allocator = allocator,
        };
        errdefer {
            for (snap.layer_data) |slice| {
                if (slice.len > 0) allocator.free(slice);
            }
            allocator.free(snap.layer_data);
        }
        var cursor: usize = header_mod.HEADER_SIZE;
        for (0..cfg.layers) |i| {
            const buf = try allocator.alloc(f32, params_per_layer);
            const dst_bytes = std.mem.sliceAsBytes(buf);
            @memcpy(dst_bytes, bytes[cursor .. cursor + dst_bytes.len]);
            try security.ensureFiniteF32(buf);
            snap.layer_data[i] = buf;
            cursor += dst_bytes.len;
        }
        snap.metadata.global_step = hdr.global_step;
        return snap;
    }

    pub fn diffNorm(self: *const SavedModelSnapshot, other: *const SavedModelSnapshot) f32 {
        if (!self.config.equals(other.config)) return std.math.floatMax(f32);
        if (self.layer_data.len != other.layer_data.len) return std.math.floatMax(f32);
        var sq: f32 = 0.0;
        for (self.layer_data, other.layer_data) |a, b| {
            if (a.len != b.len) return std.math.floatMax(f32);
            for (a, b) |x, y| {
                const d = x - y;
                sq += d * d;
            }
        }
        return @sqrt(sq);
    }
};

pub fn writeSnapshotToFile(snapshot: *const SavedModelSnapshot, allocator: std.mem.Allocator, dir: std.fs.Dir, sub_path: []const u8) SnapshotError!void {
    const bytes = try snapshot.writeBytes(allocator);
    defer allocator.free(bytes);
    var file = dir.createFile(sub_path, .{ .truncate = true }) catch return SnapshotError.IoFailed;
    defer file.close();
    file.writeAll(bytes) catch return SnapshotError.IoFailed;
    file.sync() catch return SnapshotError.IoFailed;
}

pub fn readSnapshotFromFile(allocator: std.mem.Allocator, dir: std.fs.Dir, sub_path: []const u8) SnapshotError!SavedModelSnapshot {
    const file = dir.openFile(sub_path, .{}) catch return SnapshotError.IoFailed;
    defer file.close();
    const stat = file.stat() catch return SnapshotError.IoFailed;
    if (stat.size == 0) return SnapshotError.PayloadCorrupted;
    const bytes = allocator.alloc(u8, @intCast(stat.size)) catch return SnapshotError.IoFailed;
    defer allocator.free(bytes);
    const read_n = file.readAll(bytes) catch return SnapshotError.IoFailed;
    if (read_n != bytes.len) return SnapshotError.IoFailed;
    return try SavedModelSnapshot.readBytes(allocator, bytes);
}

test "snapshot roundtrip via bytes" {
    const alloc = std.testing.allocator;
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 2 };
    const core = try pheap_core.RSFCore.init(alloc, cfg);
    defer core.destroy();
    var snap = try SavedModelSnapshot.capture(alloc, core);
    defer snap.deinit();
    const bytes = try snap.writeBytes(alloc);
    defer alloc.free(bytes);
    var loaded = try SavedModelSnapshot.readBytes(alloc, bytes);
    defer loaded.deinit();
    try std.testing.expect(snap.config.equals(loaded.config));
    try std.testing.expectEqual(@as(usize, snap.layer_data.len), loaded.layer_data.len);
    const dn = snap.diffNorm(&loaded);
    try std.testing.expectApproxEqAbs(@as(f32, 0.0), dn, 1.0e-5);
}

test "snapshot restore" {
    const alloc = std.testing.allocator;
    const cfg = schema.RSFConfig{ .dim = 8, .layers = 1 };
    const c1 = try pheap_core.RSFCore.init(alloc, cfg);
    defer c1.destroy();
    var snap = try SavedModelSnapshot.capture(alloc, c1);
    defer snap.deinit();
    const c2 = try pheap_core.RSFCore.init(alloc, cfg);
    defer c2.destroy();
    try snap.restore(c2);
    var snap2 = try SavedModelSnapshot.capture(alloc, c2);
    defer snap2.deinit();
    try std.testing.expectApproxEqAbs(@as(f32, 0.0), snap.diffNorm(&snap2), 1.0e-5);
}
