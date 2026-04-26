const std = @import("std");
const security = @import("security.zig");
const schema = @import("schema.zig");

pub const HeaderError = error{
    MagicMismatch,
    UnsupportedVersion,
    HeaderTooSmall,
    ChecksumMismatch,
    DimensionInvalid,
    LayerCountInvalid,
    ClipRangeInvalid,
    InvalidGradientPolicy,
    BufferTooSmall,
    WriteFailed,
} || security.SecurityError || schema.SchemaError;

pub const MAGIC: [4]u8 = .{ 'R', 'S', 'F', '0' };
pub const VERSION: u32 = 4;
pub const HEADER_SIZE: usize = 72;

pub const Header = struct {
    magic: [4]u8 = MAGIC,
    version: u32 = VERSION,
    dim: u64,
    layers: u64,
    clip_min: f32,
    clip_max: f32,
    grad_policy: u8,
    reserved: [7]u8 = [_]u8{0} ** 7,
    learning_rate: f32,
    momentum: f32,
    seed: u64,
    global_step: u64,
    crc32: u32 = 0,

    pub fn fromConfig(cfg: schema.RSFConfig, global_step: u64) Header {
        return Header{
            .magic = MAGIC,
            .version = VERSION,
            .dim = cfg.dim,
            .layers = cfg.layers,
            .clip_min = cfg.clip_min,
            .clip_max = cfg.clip_max,
            .grad_policy = @intFromEnum(cfg.gradient_policy),
            .reserved = [_]u8{0} ** 7,
            .learning_rate = cfg.learning_rate,
            .momentum = cfg.momentum,
            .seed = cfg.seed,
            .global_step = global_step,
            .crc32 = 0,
        };
    }

    pub fn toConfig(self: Header) HeaderError!schema.RSFConfig {
        if (self.grad_policy > 1) return HeaderError.InvalidGradientPolicy;
        const cfg = schema.RSFConfig{
            .dim = @intCast(self.dim),
            .layers = @intCast(self.layers),
            .clip_min = self.clip_min,
            .clip_max = self.clip_max,
            .learning_rate = self.learning_rate,
            .momentum = self.momentum,
            .seed = self.seed,
            .gradient_policy = @enumFromInt(self.grad_policy),
        };
        try cfg.validate();
        return cfg;
    }

    pub fn writeBytes(self: *Header, dest: []u8) HeaderError!void {
        if (dest.len < HEADER_SIZE) return HeaderError.BufferTooSmall;
        var buf = dest[0..HEADER_SIZE];
        @memcpy(buf[0..4], &self.magic);
        std.mem.writeIntLittle(u32, buf[4..8], self.version);
        std.mem.writeIntLittle(u64, buf[8..16], self.dim);
        std.mem.writeIntLittle(u64, buf[16..24], self.layers);
        std.mem.writeIntLittle(u32, buf[24..28], @as(u32, @bitCast(self.clip_min)));
        std.mem.writeIntLittle(u32, buf[28..32], @as(u32, @bitCast(self.clip_max)));
        buf[32] = self.grad_policy;
        @memcpy(buf[33..40], &self.reserved);
        std.mem.writeIntLittle(u32, buf[40..44], @as(u32, @bitCast(self.learning_rate)));
        std.mem.writeIntLittle(u32, buf[44..48], @as(u32, @bitCast(self.momentum)));
        std.mem.writeIntLittle(u64, buf[48..56], self.seed);
        std.mem.writeIntLittle(u64, buf[56..64], self.global_step);
        @memset(buf[64..68], 0);
        const crc_region = buf[0 .. HEADER_SIZE - 4];
        const crc = security.Crc32.computeBytes(crc_region);
        self.crc32 = crc;
        std.mem.writeIntLittle(u32, buf[HEADER_SIZE - 4 .. HEADER_SIZE][0..4], crc);
    }

    pub fn readBytes(src: []const u8) HeaderError!Header {
        if (src.len < HEADER_SIZE) return HeaderError.HeaderTooSmall;
        const buf = src[0..HEADER_SIZE];
        var magic_buf: [4]u8 = undefined;
        @memcpy(&magic_buf, buf[0..4]);
        if (!std.mem.eql(u8, &magic_buf, &MAGIC)) return HeaderError.MagicMismatch;
        const version = std.mem.readIntLittle(u32, buf[4..8]);
        if (version != VERSION) return HeaderError.UnsupportedVersion;
        var reserved: [7]u8 = undefined;
        @memcpy(&reserved, buf[33..40]);
        const stored_crc = std.mem.readIntLittle(u32, buf[HEADER_SIZE - 4 .. HEADER_SIZE][0..4]);
        const computed_crc = security.Crc32.computeBytes(buf[0 .. HEADER_SIZE - 4]);
        if (stored_crc != computed_crc) return HeaderError.ChecksumMismatch;
        return Header{
            .magic = MAGIC,
            .version = version,
            .dim = std.mem.readIntLittle(u64, buf[8..16]),
            .layers = std.mem.readIntLittle(u64, buf[16..24]),
            .clip_min = @bitCast(std.mem.readIntLittle(u32, buf[24..28])),
            .clip_max = @bitCast(std.mem.readIntLittle(u32, buf[28..32])),
            .grad_policy = buf[32],
            .reserved = reserved,
            .learning_rate = @bitCast(std.mem.readIntLittle(u32, buf[40..44])),
            .momentum = @bitCast(std.mem.readIntLittle(u32, buf[44..48])),
            .seed = std.mem.readIntLittle(u64, buf[48..56]),
            .global_step = std.mem.readIntLittle(u64, buf[56..64]),
            .crc32 = stored_crc,
        };
    }

    pub fn toBytes(self: *Header) [HEADER_SIZE]u8 {
        var buf: [HEADER_SIZE]u8 = undefined;
        self.writeBytes(&buf) catch unreachable;
        return buf;
    }
};

pub const PayloadDescriptor = struct {
    s_weight_offset: u64,
    t_weight_offset: u64,
    s_bias_offset: u64,
    t_bias_offset: u64,
    layer_stride: u64,

    pub fn forConfig(cfg: schema.RSFConfig) PayloadDescriptor {
        const half = cfg.dim / 2;
        const matrix_bytes: u64 = @intCast(half * half * @sizeOf(f32));
        const bias_bytes: u64 = @intCast(half * @sizeOf(f32));
        return PayloadDescriptor{
            .s_weight_offset = 0,
            .t_weight_offset = matrix_bytes,
            .s_bias_offset = 2 * matrix_bytes,
            .t_bias_offset = 2 * matrix_bytes + bias_bytes,
            .layer_stride = 2 * matrix_bytes + 2 * bias_bytes,
        };
    }
};

test "header roundtrip" {
    const cfg = schema.RSFConfig{ .dim = 64, .layers = 4 };
    var hdr = Header.fromConfig(cfg, 17);
    var buf: [HEADER_SIZE]u8 = undefined;
    try hdr.writeBytes(&buf);
    const restored = try Header.readBytes(&buf);
    try std.testing.expectEqual(cfg.dim, restored.dim);
    try std.testing.expectEqual(cfg.layers, restored.layers);
    try std.testing.expectEqual(cfg.clip_min, restored.clip_min);
    try std.testing.expectEqual(cfg.clip_max, restored.clip_max);
    try std.testing.expectEqual(@as(u64, 17), restored.global_step);
}

test "header rejects bad magic" {
    var buf = [_]u8{0} ** HEADER_SIZE;
    try std.testing.expectError(HeaderError.MagicMismatch, Header.readBytes(&buf));
}

test "header rejects bad crc" {
    const cfg = schema.RSFConfig{ .dim = 32, .layers = 2 };
    var hdr = Header.fromConfig(cfg, 0);
    var buf: [HEADER_SIZE]u8 = undefined;
    try hdr.writeBytes(&buf);
    buf[20] ^= 0xFF;
    try std.testing.expectError(HeaderError.ChecksumMismatch, Header.readBytes(&buf));
}

test "payload descriptor" {
    const cfg = schema.RSFConfig{ .dim = 64, .layers = 2 };
    const desc = PayloadDescriptor.forConfig(cfg);
    try std.testing.expectEqual(@as(u64, 32 * 32 * 4), desc.t_weight_offset);
    try std.testing.expectEqual(@as(u64, 2 * 32 * 32 * 4 + 2 * 32 * 4), desc.layer_stride);
}
