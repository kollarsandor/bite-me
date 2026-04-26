const std = @import("std");

pub const ConcurrencyError = error{
    AlreadyHeld,
    NotHeld,
    PendingDelete,
    InvalidState,
};

pub const RwLock = struct {
    inner: std.Thread.RwLock = .{},
    readers: std.atomic.Atomic(usize) = std.atomic.Atomic(usize).init(0),
    writer_active: std.atomic.Atomic(bool) = std.atomic.Atomic(bool).init(false),

    pub fn lockShared(self: *RwLock) void {
        self.inner.lockShared();
        _ = self.readers.fetchAdd(1, .Monotonic);
    }

    pub fn unlockShared(self: *RwLock) void {
        _ = self.readers.fetchSub(1, .Monotonic);
        self.inner.unlockShared();
    }

    pub fn lockExclusive(self: *RwLock) void {
        self.inner.lock();
        self.writer_active.store(true, .Release);
    }

    pub fn unlockExclusive(self: *RwLock) void {
        self.writer_active.store(false, .Release);
        self.inner.unlock();
    }

    pub fn tryLockExclusive(self: *RwLock) bool {
        if (!self.inner.tryLock()) return false;
        self.writer_active.store(true, .Release);
        return true;
    }

    pub fn currentReaders(self: *const RwLock) usize {
        return self.readers.load(.Monotonic);
    }

    pub fn writerActive(self: *const RwLock) bool {
        return self.writer_active.load(.Acquire);
    }
};

pub const ReadGuard = struct {
    lock: *RwLock,
    released: bool = false,

    pub fn release(self: *ReadGuard) void {
        if (self.released) return;
        self.released = true;
        self.lock.unlockShared();
    }
};

pub const WriteGuard = struct {
    lock: *RwLock,
    released: bool = false,

    pub fn release(self: *WriteGuard) void {
        if (self.released) return;
        self.released = true;
        self.lock.unlockExclusive();
    }
};

pub fn acquireRead(lock: *RwLock) ReadGuard {
    lock.lockShared();
    return ReadGuard{ .lock = lock };
}

pub fn acquireWrite(lock: *RwLock) WriteGuard {
    lock.lockExclusive();
    return WriteGuard{ .lock = lock };
}

pub const RefCounter = struct {
    value: std.atomic.Atomic(u64),

    pub fn init(start: u64) RefCounter {
        return .{ .value = std.atomic.Atomic(u64).init(start) };
    }

    pub fn acquire(self: *RefCounter) u64 {
        return self.value.fetchAdd(1, .AcqRel) + 1;
    }

    pub fn release(self: *RefCounter) u64 {
        const prev = self.value.fetchSub(1, .AcqRel);
        return prev - 1;
    }

    pub fn current(self: *const RefCounter) u64 {
        return self.value.load(.Acquire);
    }
};

pub const Semaphore = struct {
    permits: std.atomic.Atomic(i64),
    mutex: std.Thread.Mutex = .{},
    cond: std.Thread.Condition = .{},

    pub fn init(initial: i64) Semaphore {
        return .{ .permits = std.atomic.Atomic(i64).init(initial) };
    }

    pub fn acquire(self: *Semaphore) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        while (self.permits.load(.Acquire) <= 0) {
            self.cond.wait(&self.mutex);
        }
        _ = self.permits.fetchSub(1, .AcqRel);
    }

    pub fn release(self: *Semaphore) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        _ = self.permits.fetchAdd(1, .AcqRel);
        self.cond.signal();
    }

    pub fn tryAcquire(self: *Semaphore) bool {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.permits.load(.Acquire) <= 0) return false;
        _ = self.permits.fetchSub(1, .AcqRel);
        return true;
    }
};

pub const Latch = struct {
    flag: std.atomic.Atomic(bool),
    mutex: std.Thread.Mutex = .{},
    cond: std.Thread.Condition = .{},

    pub fn init() Latch {
        return .{ .flag = std.atomic.Atomic(bool).init(false) };
    }

    pub fn signal(self: *Latch) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        self.flag.store(true, .Release);
        self.cond.broadcast();
    }

    pub fn wait(self: *Latch) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        while (!self.flag.load(.Acquire)) {
            self.cond.wait(&self.mutex);
        }
    }

    pub fn isSet(self: *const Latch) bool {
        return self.flag.load(.Acquire);
    }
};

pub const SpinLock = struct {
    flag: std.atomic.Atomic(bool) = std.atomic.Atomic(bool).init(false),

    pub fn lock(self: *SpinLock) void {
        while (self.flag.swap(true, .Acquire)) {
            std.atomic.spinLoopHint();
        }
    }

    pub fn tryLock(self: *SpinLock) bool {
        return !self.flag.swap(true, .Acquire);
    }

    pub fn unlock(self: *SpinLock) void {
        self.flag.store(false, .Release);
    }
};

test "rwlock shared and exclusive" {
    var lock = RwLock{};
    var rg = acquireRead(&lock);
    try std.testing.expectEqual(@as(usize, 1), lock.currentReaders());
    rg.release();
    var wg = acquireWrite(&lock);
    try std.testing.expect(lock.writerActive());
    wg.release();
}

test "ref counter acquire release" {
    var rc = RefCounter.init(0);
    try std.testing.expectEqual(@as(u64, 1), rc.acquire());
    try std.testing.expectEqual(@as(u64, 2), rc.acquire());
    try std.testing.expectEqual(@as(u64, 1), rc.release());
    try std.testing.expectEqual(@as(u64, 0), rc.release());
}

test "semaphore basic" {
    var sem = Semaphore.init(2);
    sem.acquire();
    sem.acquire();
    try std.testing.expect(!sem.tryAcquire());
    sem.release();
    try std.testing.expect(sem.tryAcquire());
}

test "latch signal" {
    var latch = Latch.init();
    try std.testing.expect(!latch.isSet());
    latch.signal();
    latch.wait();
    try std.testing.expect(latch.isSet());
}
