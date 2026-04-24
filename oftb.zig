const std = @import("std");
const Allocator = std.mem.Allocator;
const Tensor = @import("../core/tensor.zig").Tensor;

pub const OFTB = struct {
    fractal_scale: f32,
    dim: usize,

    pub fn init(d: usize) OFTB {
        return OFTB{
            .fractal_scale = 0.70710678,
            .dim = d,
        };
    }

    pub fn forwardInPlace(self: *const OFTB, x: *Tensor) void {
        if (x.data.len < self.dim * 2) return;
        const half = self.dim;
        const x1 = x.data[0..half];
        const x2 = x.data[half .. half * 2];

        var mix_buf: [16384]f32 = undefined;
        if (half > mix_buf.len) return;

        var i: usize = 0;
        while (i < half) : (i += 1) {
            mix_buf[i] = x1[i];
        }

        i = 0;
        while (i < half) : (i += 1) {
            x1[i] += x2[i] * self.fractal_scale;
        }

        i = 0;
        while (i < half) : (i += 1) {
            x2[i] += mix_buf[i] * self.fractal_scale * 0.5;
        }
    }

    pub fn backwardInPlace(self: *const OFTB, grad: []f32) void {
        if (grad.len < self.dim * 2) return;
        const half = self.dim;
        const g1 = grad[0..half];
        const g2 = grad[half .. half * 2];

        var buf: [16384]f32 = undefined;
        if (half > buf.len) return;

        var i: usize = 0;
        while (i < half) : (i += 1) {
            buf[i] = g2[i];
        }

        i = 0;
        while (i < half) : (i += 1) {
            g2[i] += g1[i] * self.fractal_scale;
        }

        i = 0;
        while (i < half) : (i += 1) {
            g1[i] += buf[i] * self.fractal_scale * 0.5;
        }
    }
};
