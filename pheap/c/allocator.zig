const std = @import("std");
const security = @import("../src/security.zig");

pub const AllocError = error{
    OutOfMemory,
    AlignmentInvalid,
    SizeOverflow,
    DoubleFree,
    UnknownPointer,
} || std.mem.Allocator.Error;

pub const Tensor1D = struct {
    data: []align(64) f32,
    owned: bool,

    pub fn init(allocator: std.mem.Allocator, len: usize) AllocError!Tensor1D {
        const data = try allocator.alignedAlloc(f32, 64, len);
        @memset(data, 0.0);
        return .{ .data = data, .owned = true };
    }

    pub fn fromSlice(slice: []align(64) f32) Tensor1D {
        return .{ .data = slice, .owned = false };
    }

    pub fn deinit(self: *Tensor1D, allocator: std.mem.Allocator) void {
        if (self.owned and self.data.len > 0) {
            allocator.free(self.data);
        }
        self.data = &[_]f32{};
        self.owned = false;
    }

    pub fn fillZero(self: *Tensor1D) void {
        @memset(self.data, 0.0);
    }

    pub fn copyFrom(self: *Tensor1D, src: []const f32) AllocError!void {
        if (src.len != self.data.len) return AllocError.SizeOverflow;
        @memcpy(self.data, src);
    }
};

pub const Tensor2D = struct {
    data: []align(64) f32,
    rows: usize,
    cols: usize,
    owned: bool,

    pub fn init(allocator: std.mem.Allocator, rows: usize, cols: usize) AllocError!Tensor2D {
        const total = std.math.mul(usize, rows, cols) catch return AllocError.SizeOverflow;
        const data = try allocator.alignedAlloc(f32, 64, total);
        @memset(data, 0.0);
        return .{ .data = data, .rows = rows, .cols = cols, .owned = true };
    }

    pub fn deinit(self: *Tensor2D, allocator: std.mem.Allocator) void {
        if (self.owned and self.data.len > 0) {
            allocator.free(self.data);
        }
        self.data = &[_]f32{};
        self.rows = 0;
        self.cols = 0;
        self.owned = false;
    }

    pub fn at(self: *Tensor2D, r: usize, c: usize) *f32 {
        return &self.data[r * self.cols + c];
    }

    pub fn row(self: *Tensor2D, r: usize) []f32 {
        return self.data[r * self.cols .. (r + 1) * self.cols];
    }

    pub fn rowConst(self: *const Tensor2D, r: usize) []const f32 {
        return self.data[r * self.cols .. (r + 1) * self.cols];
    }

    pub fn fillZero(self: *Tensor2D) void {
        @memset(self.data, 0.0);
    }

    pub fn copyFrom(self: *Tensor2D, src: []const f32) AllocError!void {
        if (src.len != self.data.len) return AllocError.SizeOverflow;
        @memcpy(self.data, src);
    }

    pub fn xavierFill(self: *Tensor2D, fan_in: usize, fan_out: usize, seed: u64) void {
        const limit = @sqrt(6.0 / @as(f32, @floatFromInt(fan_in + fan_out)));
        var state = security.xoshiroSeed(seed);
        for (self.data) |*v| {
            const u = security.uniformF32FromU64(security.xoshiroNext(&state));
            v.* = (2.0 * u - 1.0) * limit;
        }
    }

    pub fn frobeniusNorm(self: *const Tensor2D) f32 {
        var acc: f32 = 0.0;
        for (self.data) |v| acc += v * v;
        return @sqrt(acc);
    }
};

pub const TrackingAllocator = struct {
    backing: std.mem.Allocator,
    allocations: std.AutoHashMap(usize, AllocRecord),
    bytes_in_flight: usize = 0,
    high_water: usize = 0,
    mutex: std.Thread.Mutex = .{},

    const AllocRecord = struct {
        size: usize,
        alignment: u29,
    };

    pub fn init(backing: std.mem.Allocator, child_allocator: std.mem.Allocator) TrackingAllocator {
        return .{
            .backing = backing,
            .allocations = std.AutoHashMap(usize, AllocRecord).init(child_allocator),
        };
    }

    pub fn deinit(self: *TrackingAllocator) void {
        self.allocations.deinit();
    }

    pub fn allocator(self: *TrackingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = vtableAlloc,
                .resize = vtableResize,
                .free = vtableFree,
            },
        };
    }

    fn vtableAlloc(ctx: *anyopaque, len: usize, ptr_align: u8, ret_addr: usize) ?[*]u8 {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.mutex.lock();
        defer self.mutex.unlock();
        const ptr = self.backing.rawAlloc(len, ptr_align, ret_addr) orelse return null;
        const key = @intFromPtr(ptr);
        self.allocations.put(key, .{ .size = len, .alignment = @as(u29, ptr_align) }) catch {
            self.backing.rawFree(ptr[0..len], ptr_align, ret_addr);
            return null;
        };
        self.bytes_in_flight += len;
        if (self.bytes_in_flight > self.high_water) self.high_water = self.bytes_in_flight;
        return ptr;
    }

    fn vtableResize(ctx: *anyopaque, buf: []u8, buf_align: u8, new_len: usize, ret_addr: usize) bool {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.mutex.lock();
        defer self.mutex.unlock();
        if (!self.backing.rawResize(buf, buf_align, new_len, ret_addr)) return false;
        const key = @intFromPtr(buf.ptr);
        if (self.allocations.getPtr(key)) |rec| {
            self.bytes_in_flight = self.bytes_in_flight + new_len - rec.size;
            rec.size = new_len;
            if (self.bytes_in_flight > self.high_water) self.high_water = self.bytes_in_flight;
        }
        return true;
    }

    fn vtableFree(ctx: *anyopaque, buf: []u8, buf_align: u8, ret_addr: usize) void {
        const self: *TrackingAllocator = @ptrCast(@alignCast(ctx));
        self.mutex.lock();
        defer self.mutex.unlock();
        const key = @intFromPtr(buf.ptr);
        if (self.allocations.fetchRemove(key)) |kv| {
            self.bytes_in_flight -= kv.value.size;
        }
        self.backing.rawFree(buf, buf_align, ret_addr);
    }

    pub fn snapshot(self: *TrackingAllocator) MemoryReport {
        self.mutex.lock();
        defer self.mutex.unlock();
        return .{
            .live_bytes = self.bytes_in_flight,
            .live_allocations = self.allocations.count(),
            .high_water_bytes = self.high_water,
        };
    }
};

pub const MemoryReport = struct {
    live_bytes: usize,
    live_allocations: usize,
    high_water_bytes: usize,
};

pub fn allocAlignedF32(allocator: std.mem.Allocator, len: usize, comptime alignment: u29) AllocError![]align(alignment) f32 {
    if (alignment == 0 or (alignment & (alignment - 1)) != 0) return AllocError.AlignmentInvalid;
    const data = try allocator.alignedAlloc(f32, alignment, len);
    @memset(data, 0.0);
    return data;
}

pub fn freeAlignedF32(allocator: std.mem.Allocator, comptime alignment: u29, slice: []align(alignment) f32) void {
    allocator.free(slice);
}

test "tensor1d basic" {
    const alloc = std.testing.allocator;
    var t = try Tensor1D.init(alloc, 16);
    defer t.deinit(alloc);
    try std.testing.expectEqual(@as(usize, 16), t.data.len);
    try std.testing.expectEqual(@as(f32, 0.0), t.data[7]);
    t.data[3] = 5.5;
    try std.testing.expectEqual(@as(f32, 5.5), t.data[3]);
}

test "tensor2d at and row" {
    const alloc = std.testing.allocator;
    var t = try Tensor2D.init(alloc, 4, 8);
    defer t.deinit(alloc);
    t.at(2, 3).* = 9.0;
    try std.testing.expectEqual(@as(f32, 9.0), t.row(2)[3]);
}

test "tensor2d xavier fill" {
    const alloc = std.testing.allocator;
    var t = try Tensor2D.init(alloc, 8, 8);
    defer t.deinit(alloc);
    t.xavierFill(8, 8, 0xDEADBEEF);
    var any_nonzero = false;
    for (t.data) |v| {
        if (v != 0.0) any_nonzero = true;
        try std.testing.expect(v <= 1.0 and v >= -1.0);
    }
    try std.testing.expect(any_nonzero);
}

test "tracking allocator counts" {
    var tracker = TrackingAllocator.init(std.testing.allocator, std.testing.allocator);
    defer tracker.deinit();
    const alloc = tracker.allocator();
    const a = try alloc.alloc(u8, 128);
    const r1 = tracker.snapshot();
    try std.testing.expectEqual(@as(usize, 128), r1.live_bytes);
    alloc.free(a);
    const r2 = tracker.snapshot();
    try std.testing.expectEqual(@as(usize, 0), r2.live_bytes);
    try std.testing.expectEqual(@as(usize, 128), r2.high_water_bytes);
}
