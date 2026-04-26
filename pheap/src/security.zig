const std = @import("std");

pub const SecurityError = error{
    NonFiniteValue,
    ChecksumMismatch,
    ClipRangeInvalid,
    DimensionInvalid,
    LayerCountInvalid,
    BufferTooSmall,
    AlignmentInvalid,
    ParameterOutOfRange,
};

extern "c" fn rsf_crc32_init() u32;
extern "c" fn rsf_crc32_update(crc: u32, data: ?*const anyopaque, length: usize) u32;
extern "c" fn rsf_crc32_finish(crc: u32) u32;
extern "c" fn rsf_crc32_compute(data: ?*const anyopaque, length: usize) u32;
extern "c" fn rsf_finite_f32_slice(data: [*]const f32, length: usize) c_int;
extern "c" fn rsf_finite_f64_slice(data: [*]const f64, length: usize) c_int;

pub const Crc32 = struct {
    state: u32,

    pub fn init() Crc32 {
        return .{ .state = rsf_crc32_init() };
    }

    pub fn update(self: *Crc32, bytes: []const u8) void {
        if (bytes.len == 0) return;
        self.state = rsf_crc32_update(self.state, bytes.ptr, bytes.len);
    }

    pub fn finish(self: *Crc32) u32 {
        return rsf_crc32_finish(self.state);
    }

    pub fn computeBytes(bytes: []const u8) u32 {
        if (bytes.len == 0) return rsf_crc32_compute(null, 0);
        return rsf_crc32_compute(bytes.ptr, bytes.len);
    }

    pub fn computeF32(values: []const f32) u32 {
        const bytes = std.mem.sliceAsBytes(values);
        return computeBytes(bytes);
    }
};

pub fn ensureFiniteF32(values: []const f32) SecurityError!void {
    if (values.len == 0) return;
    if (rsf_finite_f32_slice(values.ptr, values.len) == 0) {
        return SecurityError.NonFiniteValue;
    }
}

pub fn ensureFiniteF64(values: []const f64) SecurityError!void {
    if (values.len == 0) return;
    if (rsf_finite_f64_slice(values.ptr, values.len) == 0) {
        return SecurityError.NonFiniteValue;
    }
}

pub fn validateClipRange(clip_min: f32, clip_max: f32) SecurityError!void {
    if (!std.math.isFinite(clip_min) or !std.math.isFinite(clip_max)) {
        return SecurityError.ClipRangeInvalid;
    }
    if (clip_min >= clip_max) return SecurityError.ClipRangeInvalid;
    if (clip_min < -20.0 or clip_max > 20.0) return SecurityError.ClipRangeInvalid;
}

pub fn validateDimension(dim: usize) SecurityError!void {
    if (dim == 0) return SecurityError.DimensionInvalid;
    if (dim % 2 != 0) return SecurityError.DimensionInvalid;
    if (dim > 1 << 22) return SecurityError.DimensionInvalid;
}

pub fn validateLayerCount(layers: usize) SecurityError!void {
    if (layers == 0) return SecurityError.LayerCountInvalid;
    if (layers > 1024) return SecurityError.LayerCountInvalid;
}

pub fn validateLearningRate(lr: f32) SecurityError!void {
    if (!std.math.isFinite(lr)) return SecurityError.ParameterOutOfRange;
    if (lr <= 0.0 or lr > 10.0) return SecurityError.ParameterOutOfRange;
}

pub fn validateMomentum(m: f32) SecurityError!void {
    if (!std.math.isFinite(m)) return SecurityError.ParameterOutOfRange;
    if (m < 0.0 or m >= 1.0) return SecurityError.ParameterOutOfRange;
}

pub fn requireMinLength(buffer: []const u8, required: usize) SecurityError!void {
    if (buffer.len < required) return SecurityError.BufferTooSmall;
}

pub fn requireAlignment(comptime T: type, ptr: *const T) SecurityError!void {
    const addr = @intFromPtr(ptr);
    if (addr % @alignOf(T) != 0) return SecurityError.AlignmentInvalid;
}

pub fn xoshiroNext(state: *[4]u64) u64 {
    const result = std.math.rotl(u64, state[1] *% 5, 7) *% 9;
    const t = state[1] << 17;
    state[2] ^= state[0];
    state[3] ^= state[1];
    state[1] ^= state[2];
    state[0] ^= state[3];
    state[2] ^= t;
    state[3] = std.math.rotl(u64, state[3], 45);
    return result;
}

pub fn xoshiroSeed(seed: u64) [4]u64 {
    var s = [_]u64{ 0, 0, 0, 0 };
    var z = seed +% 0x9E3779B97F4A7C15;
    inline for (0..4) |i| {
        z = (z ^ (z >> 30)) *% 0xBF58476D1CE4E5B9;
        z = (z ^ (z >> 27)) *% 0x94D049BB133111EB;
        s[i] = z ^ (z >> 31);
    }
    return s;
}

pub fn uniformF32FromU64(raw: u64) f32 {
    const mantissa: u32 = @truncate(raw >> 40);
    const denom: f32 = 16777216.0;
    return @as(f32, @floatFromInt(mantissa)) / denom;
}

test "crc32 deterministic" {
    const bytes = [_]u8{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const a = Crc32.computeBytes(&bytes);
    const b = Crc32.computeBytes(&bytes);
    try std.testing.expectEqual(a, b);
}

test "validate clip range" {
    try validateClipRange(-5.0, 5.0);
    try std.testing.expectError(SecurityError.ClipRangeInvalid, validateClipRange(5.0, -5.0));
    try std.testing.expectError(SecurityError.ClipRangeInvalid, validateClipRange(-100.0, 100.0));
}

test "validate dimension" {
    try validateDimension(64);
    try std.testing.expectError(SecurityError.DimensionInvalid, validateDimension(0));
    try std.testing.expectError(SecurityError.DimensionInvalid, validateDimension(7));
}

test "ensure finite" {
    const ok = [_]f32{ 0.0, 1.0, -1.0, 3.14 };
    try ensureFiniteF32(&ok);
    const bad = [_]f32{ 0.0, std.math.nan(f32), 1.0 };
    try std.testing.expectError(SecurityError.NonFiniteValue, ensureFiniteF32(&bad));
}

test "xoshiro deterministic" {
    var s1 = xoshiroSeed(42);
    var s2 = xoshiroSeed(42);
    try std.testing.expectEqual(xoshiroNext(&s1), xoshiroNext(&s2));
    try std.testing.expectEqual(xoshiroNext(&s1), xoshiroNext(&s2));
}
