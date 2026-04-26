const std = @import("std");
const concurrency = @import("concurrency.zig");
const pheap_core = @import("../c/pheap.zig");

pub const GcError = error{
    PendingDelete,
    AlreadyDeleted,
    InvalidHandle,
};

pub const CoreEntry = struct {
    core: ?*pheap_core.RSFCore,
    refcount: concurrency.RefCounter,
    pending_delete: std.atomic.Atomic(bool),
    creation_step: u64,

    pub fn alive(self: *const CoreEntry) bool {
        return self.core != null and !self.pending_delete.load(.Acquire);
    }
};

pub const CoreRegistry = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayList(*CoreEntry),
    free_indices: std.ArrayList(usize),
    mutex: std.Thread.Mutex = .{},
    creation_counter: std.atomic.Atomic(u64),

    pub fn init(allocator: std.mem.Allocator) CoreRegistry {
        return .{
            .allocator = allocator,
            .entries = std.ArrayList(*CoreEntry).init(allocator),
            .free_indices = std.ArrayList(usize).init(allocator),
            .creation_counter = std.atomic.Atomic(u64).init(0),
        };
    }

    pub fn deinit(self: *CoreRegistry) void {
        for (self.entries.items) |entry| {
            if (entry.core) |c| c.destroy();
            self.allocator.destroy(entry);
        }
        self.entries.deinit();
        self.free_indices.deinit();
    }

    pub fn registerCore(self: *CoreRegistry, core: *pheap_core.RSFCore) !usize {
        self.mutex.lock();
        defer self.mutex.unlock();
        const step = self.creation_counter.fetchAdd(1, .AcqRel);
        if (self.free_indices.popOrNull()) |idx| {
            const entry = self.entries.items[idx];
            entry.core = core;
            entry.refcount = concurrency.RefCounter.init(1);
            entry.pending_delete.store(false, .Release);
            entry.creation_step = step;
            return idx;
        }
        const entry = try self.allocator.create(CoreEntry);
        entry.* = .{
            .core = core,
            .refcount = concurrency.RefCounter.init(1),
            .pending_delete = std.atomic.Atomic(bool).init(false),
            .creation_step = step,
        };
        try self.entries.append(entry);
        return self.entries.items.len - 1;
    }

    pub fn acquire(self: *CoreRegistry, index: usize) GcError!*pheap_core.RSFCore {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (index >= self.entries.items.len) return GcError.InvalidHandle;
        const entry = self.entries.items[index];
        if (entry.pending_delete.load(.Acquire)) return GcError.PendingDelete;
        const c = entry.core orelse return GcError.AlreadyDeleted;
        _ = entry.refcount.acquire();
        return c;
    }

    pub fn release(self: *CoreRegistry, index: usize) GcError!void {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (index >= self.entries.items.len) return GcError.InvalidHandle;
        const entry = self.entries.items[index];
        if (entry.core == null) return GcError.AlreadyDeleted;
        const remaining = entry.refcount.release();
        if (remaining == 0 and entry.pending_delete.load(.Acquire)) {
            self.collectLocked(index);
        }
    }

    pub fn markDelete(self: *CoreRegistry, index: usize) GcError!void {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (index >= self.entries.items.len) return GcError.InvalidHandle;
        const entry = self.entries.items[index];
        if (entry.core == null) return GcError.AlreadyDeleted;
        entry.pending_delete.store(true, .Release);
        if (entry.refcount.current() == 0) {
            self.collectLocked(index);
        }
    }

    pub fn collectAll(self: *CoreRegistry) usize {
        self.mutex.lock();
        defer self.mutex.unlock();
        var collected: usize = 0;
        for (self.entries.items, 0..) |entry, idx| {
            if (entry.pending_delete.load(.Acquire) and entry.refcount.current() == 0 and entry.core != null) {
                self.collectLocked(idx);
                collected += 1;
            }
        }
        return collected;
    }

    fn collectLocked(self: *CoreRegistry, index: usize) void {
        const entry = self.entries.items[index];
        if (entry.core) |c| c.destroy();
        entry.core = null;
        entry.pending_delete.store(false, .Release);
        self.free_indices.append(index) catch {};
    }

    pub fn liveCount(self: *CoreRegistry) usize {
        self.mutex.lock();
        defer self.mutex.unlock();
        var count: usize = 0;
        for (self.entries.items) |entry| {
            if (entry.alive()) count += 1;
        }
        return count;
    }

    pub fn pendingCount(self: *CoreRegistry) usize {
        self.mutex.lock();
        defer self.mutex.unlock();
        var count: usize = 0;
        for (self.entries.items) |entry| {
            if (entry.pending_delete.load(.Acquire) and entry.core != null) count += 1;
        }
        return count;
    }
};

test "registry register and acquire" {
    const alloc = std.testing.allocator;
    var reg = CoreRegistry.init(alloc);
    defer reg.deinit();
    const cfg = @import("schema.zig").RSFConfig{ .dim = 8, .layers = 1 };
    const core = try pheap_core.RSFCore.init(alloc, cfg);
    const idx = try reg.registerCore(core);
    const c2 = try reg.acquire(idx);
    try std.testing.expectEqual(core, c2);
    try reg.release(idx);
    try reg.markDelete(idx);
    try reg.release(idx);
    try std.testing.expectEqual(@as(usize, 0), reg.liveCount());
}

test "registry double release" {
    const alloc = std.testing.allocator;
    var reg = CoreRegistry.init(alloc);
    defer reg.deinit();
    const cfg = @import("schema.zig").RSFConfig{ .dim = 8, .layers = 1 };
    const core = try pheap_core.RSFCore.init(alloc, cfg);
    const idx = try reg.registerCore(core);
    try reg.markDelete(idx);
    try reg.release(idx);
    try std.testing.expectError(GcError.AlreadyDeleted, reg.release(idx));
}
