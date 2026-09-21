//! The io_uring FILE-LOADER backend (Linux): ONE ring thread instead of a thread per
//! in-flight read. Same contract as the thread-pool backend — `submit` from a prover worker,
//! `land` + `Engine.externalEnd` when the file is in — so `ParseTask`, `Context` and the
//! engine know nothing about it (see `Loader.zig`).
//!
//! PROTOCOL per file (all completions reaped by the ring thread):
//!   1. the WORKER submits a `statx` (size only) — the one thing it cannot know up front is
//!      how big a buffer the read needs;
//!   2. on the statx completion the RING THREAD allocates the exact buffer and submits a
//!      LINKED chain `openat_direct` → `read` (fixed file) → `close_direct`: the kernel runs
//!      the three in order and cancels the rest of the chain if one fails, so a load is one
//!      submission and the ring thread never blocks in an `open`;
//!   3. when the chain's three completions are in, the ring thread publishes the result on
//!      the task and retires the engine's external count — the wake.
//!
//! THREADS. `IoUring` is not thread-safe. The SQ side (`get_sqe` + `submit`) is shared by the
//! workers and the ring thread and is guarded by `sq_lock`; the CQ side (`copy_cqes`) is the
//! ring thread's alone. The kernel allows a submit `enter` and a wait `enter` concurrently,
//! which is exactly the split.
//!
//! FALLBACK. `openat_direct`/`close_direct` need kernel 5.15, and the ring itself is refused
//! under seccomp and in some containers. `init` PROBES both with a real chain on "/" and
//! fails cleanly; the caller then uses the thread-pool backend, silently. A submission the
//! ring cannot take (`slots` loads in flight) is `error.Unavailable` → the worker reads
//! inline, the same fallback the pool has.
//!
//! ALLOCATION. Source bytes are durable → `ctx.arena` (thread-safe bump), sized exactly by
//! statx. A literate `.md`'s raw bytes are transient → `gpa`, freed once extracted. The
//! per-load record lives on `ctx.arena` (a few hundred bytes per file; the arena is never
//! reset anyway, and a pointer-stable record is what `user_data` carries).

const std = @import("std");
const builtin = @import("builtin");
const linux = std.os.linux;
const IoUring = linux.IoUring;
const Context = @import("../Context.zig");
const Engine = @import("../Engine.zig");
const ParseTask = @import("ParseTask.zig");
const literate = @import("../literate.zig");

const Ring = @This();

/// Submission-queue depth. A load needs at most 4 SQEs and the queue is flushed under the
/// lock after every batch, so this bounds nothing but a single batch.
const entries: u16 = 256;
/// The registered (direct) file table — one slot per in-flight load, so also the in-flight
/// ceiling; beyond it a submission is refused and read inline.
const slots: u32 = 256;

/// The Context's `Io` — only for `sq_lock` (its Threaded backend makes it a futex).
io: std.Io,
gpa: std.mem.Allocator,
ring: IoUring,
/// Guards the SQ side and the counters below.
sq_lock: std.Io.Mutex = .init,
/// Loads submitted and not yet landed (≤ `slots`).
in_flight: u32 = 0,
/// `drain` was called: refuse new loads; the ring thread exits once `in_flight` is 0.
stopping: bool = false,
/// Direct-file slots not in use. RING THREAD ONLY (slots are claimed when the chain is
/// built and released when it completes, both on that thread).
free_slots: [slots]u32 = undefined,
free_len: u32 = slots,
thread: ?std.Thread = null,

/// One file in flight. Its address, with the op in the low bits, is the `user_data` every
/// completion carries back.
const Load = struct {
    ctx: *Context,
    engine: *Engine,
    task: *ParseTask,
    waiter: Engine.TaskIndex,
    path: [:0]const u8,
    md: bool,
    statx: linux.Statx = undefined,
    /// `--io-delay`: the linked timeout's duration (must outlive its completion)
    delay: linux.kernel_timespec = .{ .sec = 0, .nsec = 0 },
    slot: u32 = 0,
    buf: []u8 = &.{},
    /// chain completions still expected
    pending: u8 = 0,
    len: usize = 0,
    err: ?anyerror = null,
};

const Op = enum(u3) { statx = 1, open = 2, read = 3, close = 4, delay = 5, stop = 7 };

fn tag(load: *Load, op: Op) u64 {
    comptime std.debug.assert(@alignOf(Load) >= 8); // the low three bits are free for `op`
    return @intFromPtr(load) | @intFromEnum(op);
}

fn lock(self: *Ring) void {
    self.sq_lock.lockUncancelable(self.io);
}

fn unlock(self: *Ring) void {
    self.sq_lock.unlock(self.io);
}

/// Set up the ring, register the slot table, PROBE the direct-file ops, and start the ring
/// thread. Any refusal is `error.Unavailable` — the caller falls back to the thread pool.
pub fn init(gpa: std.mem.Allocator, io: std.Io) error{Unavailable}!*Ring {
    const self = gpa.create(Ring) catch return error.Unavailable;
    errdefer gpa.destroy(self);
    self.* = .{ .io = io, .gpa = gpa, .ring = IoUring.init(entries, 0) catch return error.Unavailable };
    errdefer self.ring.deinit();
    for (&self.free_slots, 0..) |*s, i| s.* = @intCast(i);
    // a SPARSE table: every entry -1, filled by `openat_direct` as loads run
    self.ring.register_files(&([_]linux.fd_t{-1} ** slots)) catch return error.Unavailable;
    try self.probe();
    self.thread = std.Thread.spawn(.{}, threadMain, .{self}) catch return error.Unavailable;
    return self;
}

/// One real chain against "/" — `openat_direct` into slot 0, linked `close_direct` — waited
/// synchronously. A kernel without direct files answers EINVAL/EOPNOTSUPP here rather than
/// on the first user file, where it would read as "file not found".
fn probe(self: *Ring) error{Unavailable}!void {
    const dir: [:0]const u8 = "/";
    const o = self.ring.openat_direct(1, linux.AT.FDCWD, dir.ptr, .{ .ACCMODE = .RDONLY, .DIRECTORY = true }, 0, 0) catch return error.Unavailable;
    o.flags |= linux.IOSQE_IO_LINK;
    _ = self.ring.close_direct(2, 0) catch return error.Unavailable;
    _ = self.ring.submit_and_wait(2) catch return error.Unavailable;
    var cqes: [2]linux.io_uring_cqe = undefined;
    var got: u32 = 0;
    while (got < 2) {
        const n = self.ring.copy_cqes(cqes[got..], 1) catch return error.Unavailable;
        got += n;
    }
    for (cqes) |c| if (c.res < 0) return error.Unavailable;
}

/// Hand `task`'s file to the ring: the worker submits the statx and returns; everything
/// else happens on the ring thread. `error.Unavailable` = nothing submitted, nothing owed.
pub fn submit(self: *Ring, ctx: *Context, engine: *Engine, task: *ParseTask, waiter: Engine.TaskIndex) error{Unavailable}!void {
    const path = ctx.files.get(@intFromEnum(task.file_id)).path;
    const load = ctx.arena.create(Load) catch return error.Unavailable;
    load.* = .{
        .ctx = ctx,
        .engine = engine,
        .task = task,
        .waiter = waiter,
        .path = ctx.arena.dupeZ(u8, path) catch return error.Unavailable,
        .md = std.mem.endsWith(u8, path, ".md"),
    };
    engine.externalBegin(); // BEFORE the hand-off (see Engine.externalBegin)
    self.lock();
    defer self.unlock();
    if (self.stopping or self.in_flight >= slots) {
        engine.externalCancel();
        return error.Unavailable;
    }
    _ = self.ring.statx(tag(load, .statx), linux.AT.FDCWD, load.path, 0, .{ .SIZE = true }, &load.statx) catch {
        engine.externalCancel(); // no SQE was queued
        return error.Unavailable;
    };
    self.flushLocked();
    self.in_flight += 1;
}

/// Push the queued SQEs to the kernel. Under `sq_lock`. A transient refusal (the kernel out
/// of request resources, a signal) is retried — the ring thread is reaping concurrently, so
/// resources free up — and a persistent one is a broken ring, which no fallback can mend:
/// the queued SQEs cannot be un-queued and their loads would never land.
fn flushLocked(self: *Ring) void {
    var tries: u32 = 0;
    while (true) : (tries += 1) {
        _ = self.ring.submit() catch |e| {
            if (tries < 100_000) {
                std.atomic.spinLoopHint();
                continue;
            }
            std.debug.panic("io_uring submit failed persistently: {s}", .{@errorName(e)});
        };
        return;
    }
}

/// The ring thread: reap completions until told to stop and nothing is in flight.
fn threadMain(self: *Ring) void {
    var cqes: [64]linux.io_uring_cqe = undefined;
    while (true) {
        const n = self.ring.copy_cqes(&cqes, 1) catch continue; // EINTR and friends: wait again
        for (cqes[0..n]) |cqe| self.complete(cqe);
        self.lock();
        const done = self.stopping and self.in_flight == 0;
        self.unlock();
        if (done) return;
    }
}

fn complete(self: *Ring, cqe: linux.io_uring_cqe) void {
    const op: Op = @enumFromInt(@as(u3, @truncate(cqe.user_data)));
    if (op == .stop) return; // the drain's wake-up NOP; the loop re-checks its exit condition
    const load: *Load = @ptrFromInt(cqe.user_data & ~@as(u64, 7));
    switch (op) {
        .statx => {
            if (cqe.res < 0) return self.finish(load, errorOf(cqe));
            const size: usize = @intCast(load.statx.size);
            if (size == 0) return self.finish(load, null); // nothing to read, nothing to open
            load.buf = (if (load.md) self.gpa.alloc(u8, size) else load.ctx.arena.alloc(u8, size)) catch
                return self.finish(load, error.OutOfMemory);
            self.free_len -= 1; // never empty: in_flight ≤ slots
            load.slot = self.free_slots[self.free_len];
            self.lock();
            defer self.unlock();
            // The chain. The SQ is empty under the lock (every batch is flushed before the
            // lock is dropped), so its four SQEs always fit.
            load.pending = 3;
            const delay_ns = load.ctx.verify.io_delay_ns;
            if (delay_ns != 0) {
                // `--io-delay`: a timeout LINKED ahead of the open, so the simulated latency
                // is spent by the kernel, not a thread. Expiry must count as success or it
                // would break the link (`ETIME_SUCCESS`, kernel 5.16).
                load.delay = .{ .sec = @intCast(delay_ns / std.time.ns_per_s), .nsec = @intCast(delay_ns % std.time.ns_per_s) };
                const t = self.ring.timeout(tag(load, .delay), &load.delay, 0, linux.IORING_TIMEOUT_ETIME_SUCCESS) catch unreachable;
                t.flags |= linux.IOSQE_IO_LINK;
                load.pending = 4;
            }
            // (no CLOEXEC: a direct descriptor never enters the fd table, and the kernel
            // answers EINVAL to the flag — found by the probe)
            const o = self.ring.openat_direct(tag(load, .open), linux.AT.FDCWD, load.path.ptr, .{ .ACCMODE = .RDONLY }, 0, load.slot) catch unreachable;
            o.flags |= linux.IOSQE_IO_LINK;
            const r = self.ring.read(tag(load, .read), @intCast(load.slot), .{ .buffer = load.buf }, 0) catch unreachable;
            r.flags |= linux.IOSQE_FIXED_FILE | linux.IOSQE_IO_LINK;
            _ = self.ring.close_direct(tag(load, .close), load.slot) catch unreachable;
            self.flushLocked();
        },
        .delay => {
            // an expired timeout answers ETIME even under `ETIME_SUCCESS` — the flag keeps the
            // LINK alive, it does not change the timeout's own result (probed)
            if (cqe.res < 0 and cqe.err() != .TIME and load.err == null) load.err = errorOf(cqe);
            self.step(load);
        },
        .open => {
            if (cqe.res < 0 and load.err == null) load.err = errorOf(cqe);
            self.step(load);
        },
        .read => {
            // a chain broken by the open answers ECANCELED here: the open's error is the one
            // to keep. A short read is the file having shrunk since statx; the bytes are what
            // they are.
            if (cqe.res < 0) {
                if (load.err == null and cqe.err() != .CANCELED) load.err = errorOf(cqe);
            } else load.len = @intCast(cqe.res);
            self.step(load);
        },
        .close => self.step(load), // its result is immaterial: the slot is free either way
        .stop => unreachable,
    }
}

fn step(self: *Ring, load: *Load) void {
    load.pending -= 1;
    if (load.pending != 0) return;
    self.free_slots[self.free_len] = load.slot;
    self.free_len += 1;
    self.finish(load, load.err);
}

/// Publish the outcome on the task and wake it. Ring thread only.
fn finish(self: *Ring, load: *Load, err: ?anyerror) void {
    if (err) |e| {
        load.task.land(.{ .failed = e });
    } else if (load.md) {
        const extracted = literate.extract(load.ctx.arena, load.buf[0..load.len]);
        if (extracted) |src| load.task.land(.{ .bytes = src }) else |e| load.task.land(.{ .failed = e });
    } else {
        load.task.land(.{ .bytes = load.buf[0..load.len] });
    }
    if (load.md and load.buf.len != 0) self.gpa.free(load.buf);
    self.lock();
    self.in_flight -= 1;
    self.unlock();
    load.engine.externalEnd(load.waiter);
}

fn errorOf(cqe: linux.io_uring_cqe) anyerror {
    return switch (cqe.err()) {
        .NOENT, .NOTDIR => error.FileNotFound,
        .ACCES, .PERM => error.AccessDenied,
        .ISDIR => error.IsDir,
        else => error.ReadFailed,
    };
}

/// Barrier: refuse new loads, wake the ring thread, and join it once every load in flight
/// has landed. Called with no worker running (nothing submits after it).
pub fn drain(self: *Ring) void {
    const t = self.thread orelse return;
    self.lock();
    self.stopping = true;
    _ = self.ring.nop(@intFromEnum(Op.stop)) catch unreachable; // the SQ is empty under the lock
    self.flushLocked();
    self.unlock();
    t.join();
    self.thread = null;
}

pub fn deinit(self: *Ring) void {
    self.drain(); // idempotent: a joined thread is null
    self.ring.deinit();
    const gpa = self.gpa;
    gpa.destroy(self);
}
