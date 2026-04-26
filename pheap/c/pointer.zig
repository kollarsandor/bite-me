const std = @import("std");
const security = @import("../src/security.zig");

pub const PointerError = error{
    NullPointer,
    AlignmentInvalid,
    SizeOverflow,
    OutOfMemory,
    UnsupportedAlignment,
} || std.mem.Allocator.Error;

pub const PinnedBuffer = struct {
    data: []align(64) u8,
    backing: []align(64) u8,
    pinned: bool,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator, length: usize) PointerError!PinnedBuffer {
        const bytes = try allocator.alignedAlloc(u8, 64, length);
        @memset(bytes, 0);
        return .{
            .data = bytes,
            .backing = bytes,
            .pinned = true,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *PinnedBuffer) void {
        if (self.backing.len > 0) self.allocator.free(self.backing);
        self.data = self.backing[0..0];
        self.backing = self.backing[0..0];
        self.pinned = false;
    }

    pub fn asF32(self: *PinnedBuffer) []f32 {
        const bytes = self.data;
        const ptr: [*]f32 = @ptrCast(@alignCast(bytes.ptr));
        return ptr[0 .. bytes.len / @sizeOf(f32)];
    }

    pub fn asU8(self: *PinnedBuffer) []u8 {
        return self.data;
    }
};

pub const DevicePointer = struct {
    address: usize,
    length: usize,
    device_id: i32,
    owned: bool,

    pub fn init(host: *anyopaque, length: usize, device_id: i32) DevicePointer {
        return .{
            .address = @intFromPtr(host),
            .length = length,
            .device_id = device_id,
            .owned = false,
        };
    }

    pub fn isNull(self: DevicePointer) bool {
        return self.address == 0 or self.length == 0;
    }

    pub fn rawPointer(self: DevicePointer) ?*anyopaque {
        if (self.address == 0) return null;
        return @ptrFromInt(self.address);
    }
};

pub const HandleKind = enum(u8) {
    invalid = 0,
    layer_state = 1,
    activation_buffer = 2,
    gradient_buffer = 3,
    velocity_buffer = 4,
    snapshot = 5,
    wal_segment = 6,
};

pub const Handle = packed struct(u64) {
    generation: u32,
    index: u24,
    kind: u8,

    pub fn invalid() Handle {
        return .{ .generation = 0, .index = 0, .kind = @intFromEnum(HandleKind.invalid) };
    }

    pub fn isValid(self: Handle) bool {
        return self.kind != @intFromEnum(HandleKind.invalid);
    }

    pub fn pack(self: Handle) u64 {
        return @bitCast(self);
    }

    pub fn unpack(raw: u64) Handle {
        return @bitCast(raw);
    }
};

pub const HandleRegistry = struct {
    allocator: std.mem.Allocator,
    slots: std.ArrayList(Slot),
    free_indices: std.ArrayList(u24),
    mutex: std.Thread.Mutex = .{},

    const Slot = struct {
        generation: u32,
        kind: HandleKind,
        payload: ?*anyopaque,
        live: bool,
    };

    pub fn init(allocator: std.mem.Allocator) HandleRegistry {
        return .{
            .allocator = allocator,
            .slots = std.ArrayList(Slot).init(allocator),
            .free_indices = std.ArrayList(u24).init(allocator),
        };
    }

    pub fn deinit(self: *HandleRegistry) void {
        self.slots.deinit();
        self.free_indices.deinit();
    }

    pub fn alloc(self: *HandleRegistry, kind: HandleKind, payload: ?*anyopaque) !Handle {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.free_indices.popOrNull()) |idx| {
            const slot = &self.slots.items[idx];
            slot.generation +%= 1;
            slot.kind = kind;
            slot.payload = payload;
            slot.live = true;
            return Handle{
                .generation = slot.generation,
                .index = idx,
                .kind = @intFromEnum(kind),
            };
        }
        const idx_value: u24 = @intCast(self.slots.items.len);
        try self.slots.append(.{
            .generation = 1,
            .kind = kind,
            .payload = payload,
            .live = true,
        });
        return Handle{
            .generation = 1,
            .index = idx_value,
            .kind = @intFromEnum(kind),
        };
    }

    pub fn release(self: *HandleRegistry, handle: Handle) bool {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (handle.index >= self.slots.items.len) return false;
        const slot = &self.slots.items[handle.index];
        if (!slot.live or slot.generation != handle.generation) return false;
        slot.live = false;
        slot.payload = null;
        self.free_indices.append(handle.index) catch return false;
        return true;
    }

    pub fn lookup(self: *HandleRegistry, handle: Handle) ?*anyopaque {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (handle.index >= self.slots.items.len) return null;
        const slot = &self.slots.items[handle.index];
        if (!slot.live or slot.generation != handle.generation) return null;
        if (@intFromEnum(slot.kind) != handle.kind) return null;
        return slot.payload;
    }

    pub fn liveCount(self: *HandleRegistry) usize {
        self.mutex.lock();
        defer self.mutex.unlock();
        var count: usize = 0;
        for (self.slots.items) |s| {
            if (s.live) count += 1;
        }
        return count;
    }
};

test "pinned buffer" {
    const alloc = std.testing.allocator;
    var pb = try PinnedBuffer.init(alloc, 128);
    defer pb.deinit();
    try std.testing.expectEqual(@as(usize, 128), pb.asU8().len);
    const f = pb.asF32();
    try std.testing.expectEqual(@as(usize, 32), f.len);
    f[0] = 1.5;
    try std.testing.expectEqual(@as(f32, 1.5), pb.asF32()[0]);
}

test "handle registry alloc release" {
    const alloc = std.testing.allocator;
    var reg = HandleRegistry.init(alloc);
    defer reg.deinit();
    const h1 = try reg.alloc(.layer_state, @ptrFromInt(0xCAFE0001));
    try std.testing.expect(h1.isValid());
    try std.testing.expect(reg.release(h1));
    try std.testing.expect(!reg.release(h1));
    const h2 = try reg.alloc(.snapshot, @ptrFromInt(0xCAFE0002));
    try std.testing.expectEqual(h1.index, h2.index);
    try std.testing.expect(h2.generation > h1.generation);
}

test "handle pack roundtrip" {
    const h = Handle{ .generation = 7, .index = 42, .kind = 3 };
    const restored = Handle.unpack(h.pack());
    try std.testing.expectEqual(h.generation, restored.generation);
    try std.testing.expectEqual(h.index, restored.index);
    try std.testing.expectEqual(h.kind, restored.kind);
}
