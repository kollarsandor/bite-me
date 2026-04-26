const std = @import("std");
const security = @import("security.zig");

pub const SchemaError = error{
    DimensionInvalid,
    LayerCountInvalid,
    ClipRangeInvalid,
    ParameterOutOfRange,
    LayerIndexOutOfBounds,
    InvalidGradientPolicy,
} || security.SecurityError;

pub const GradientPolicy = enum(u8) {
    sum = 0,
    mean = 1,
};

pub const RSFConfig = struct {
    dim: usize,
    layers: usize,
    clip_min: f32 = -5.0,
    clip_max: f32 = 5.0,
    learning_rate: f32 = 1.0e-3,
    momentum: f32 = 0.9,
    seed: u64 = 0x12345678ABCDEF01,
    gradient_policy: GradientPolicy = .sum,

    pub fn validate(self: RSFConfig) SchemaError!void {
        try security.validateDimension(self.dim);
        try security.validateLayerCount(self.layers);
        try security.validateClipRange(self.clip_min, self.clip_max);
        try security.validateLearningRate(self.learning_rate);
        try security.validateMomentum(self.momentum);
    }

    pub fn paramsPerLayer(self: RSFConfig) usize {
        const half = self.dim / 2;
        const w = half * half;
        return 2 * w + 2 * half;
    }

    pub fn totalParams(self: RSFConfig) usize {
        return self.layers * self.paramsPerLayer();
    }

    pub fn matrixElems(self: RSFConfig) usize {
        const half = self.dim / 2;
        return half * half;
    }

    pub fn biasElems(self: RSFConfig) usize {
        return self.dim / 2;
    }

    pub fn equals(a: RSFConfig, b: RSFConfig) bool {
        return a.dim == b.dim and a.layers == b.layers and
            a.clip_min == b.clip_min and a.clip_max == b.clip_max and
            a.learning_rate == b.learning_rate and a.momentum == b.momentum and
            a.seed == b.seed and a.gradient_policy == b.gradient_policy;
    }
};

pub const LayerConfig = struct {
    index: usize,
    half_dim: usize,
    clip_min: f32,
    clip_max: f32,

    pub fn fromModel(cfg: RSFConfig, layer_index: usize) SchemaError!LayerConfig {
        if (layer_index >= cfg.layers) return SchemaError.LayerIndexOutOfBounds;
        return LayerConfig{
            .index = layer_index,
            .half_dim = cfg.dim / 2,
            .clip_min = cfg.clip_min,
            .clip_max = cfg.clip_max,
        };
    }
};

pub const TrainerConfig = struct {
    learning_rate: f32 = 1.0e-3,
    momentum: f32 = 0.9,
    batch_size: usize = 32,
    max_epochs: usize = 10,
    grad_clip_l2: f32 = 1.0,
    weight_decay: f32 = 0.0,

    pub fn validate(self: TrainerConfig) SchemaError!void {
        try security.validateLearningRate(self.learning_rate);
        try security.validateMomentum(self.momentum);
        if (self.batch_size == 0) return SchemaError.ParameterOutOfRange;
        if (self.max_epochs == 0) return SchemaError.ParameterOutOfRange;
        if (!std.math.isFinite(self.grad_clip_l2) or self.grad_clip_l2 <= 0.0) {
            return SchemaError.ParameterOutOfRange;
        }
        if (!std.math.isFinite(self.weight_decay) or self.weight_decay < 0.0) {
            return SchemaError.ParameterOutOfRange;
        }
    }
};

pub const ScatterConfig = struct {
    factor: f32 = 0.7071067811865475,
    enable_oftb: bool = true,

    pub fn validate(self: ScatterConfig) SchemaError!void {
        if (!std.math.isFinite(self.factor) or self.factor <= 0.0 or self.factor > 2.0) {
            return SchemaError.ParameterOutOfRange;
        }
    }
};

pub const ModelMetadata = struct {
    name_buf: [64]u8,
    name_len: usize,
    created_unix_ms: i64,
    updated_unix_ms: i64,
    global_step: u64,

    pub fn init(initial_name: []const u8) ModelMetadata {
        var meta = ModelMetadata{
            .name_buf = [_]u8{0} ** 64,
            .name_len = 0,
            .created_unix_ms = std.time.milliTimestamp(),
            .updated_unix_ms = std.time.milliTimestamp(),
            .global_step = 0,
        };
        const copy_len = @min(initial_name.len, meta.name_buf.len);
        @memcpy(meta.name_buf[0..copy_len], initial_name[0..copy_len]);
        meta.name_len = copy_len;
        return meta;
    }

    pub fn name(self: *const ModelMetadata) []const u8 {
        return self.name_buf[0..self.name_len];
    }

    pub fn touch(self: *ModelMetadata) void {
        self.updated_unix_ms = std.time.milliTimestamp();
    }

    pub fn incStep(self: *ModelMetadata) void {
        self.global_step +%= 1;
        self.touch();
    }
};

test "config validate" {
    const cfg = RSFConfig{ .dim = 64, .layers = 4 };
    try cfg.validate();
    try std.testing.expectEqual(@as(usize, 32 * 32 * 2 + 32 * 2), cfg.paramsPerLayer());
    try std.testing.expectEqual(@as(usize, 4 * (32 * 32 * 2 + 32 * 2)), cfg.totalParams());
}

test "config rejects odd dim" {
    const cfg = RSFConfig{ .dim = 7, .layers = 1 };
    try std.testing.expectError(SchemaError.DimensionInvalid, cfg.validate());
}

test "trainer validate" {
    const tcfg = TrainerConfig{};
    try tcfg.validate();
    const bad = TrainerConfig{ .learning_rate = 0.0 };
    try std.testing.expectError(SchemaError.ParameterOutOfRange, bad.validate());
}

test "metadata roundtrip" {
    var m = ModelMetadata.init("rsf-experiment");
    try std.testing.expectEqualStrings("rsf-experiment", m.name());
    m.incStep();
    try std.testing.expectEqual(@as(u64, 1), m.global_step);
}
