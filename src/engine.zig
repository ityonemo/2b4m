//! The demand-driven task engine — FRAMEWORK ONLY (first slice).
//!
//! This is the strangler entry point for the execution refactor (see the plan file
//! ok-claude-can-you-wondrous-pine.md). It provides a task queue + worker loop with
//! the CONCURRENCY AFFORDANCES (a mutex around shared queue/counter state, an atomic
//! stop flag) baked in, but runs SINGLE-THREADED for now — so adding multi-core
//! work-stealing later is a wiring change, not a rewrite.
//!
//! A `Task` is an opaque payload the caller supplies together with a `run` function
//! (a closure over the caller's context). The engine owns scheduling: it pulls a task
//! off the run queue, runs it (the task may `rack` more tasks via the handle it is
//! given), and repeats until QUIESCENT — the race-free termination condition
//! `completed == racked` (the "in/out counter"). Normal termination is quiescence,
//! NOT a shutdown task; the stop flag is the affordance for future abnormal teardown.
//!
//! NOT here yet (later slices): the parked queue / suspend / resume, cycle detection,
//! and real multi-threading. Only the parse task — which never suspends — runs on it.

const std = @import("std");

/// A minimal test-and-set spinlock — the CONCURRENCY AFFORDANCE for shared engine
/// state. Single-threaded now, so lock/unlock are uncontended atomic ops; the value is
/// that the critical sections are MARKED. When real multi-threading lands, swap this for
/// `std.Io.Mutex` (futex-blocking, needs an `Io` handle) or per-core work-stealing
/// deques — the lock/unlock CALL SITES stay identical. (Zig 0.16 moved the blocking
/// mutex under `std.Io`; a self-contained spinlock avoids threading an `Io` handle
/// through the engine before we actually spawn threads.)
pub const SpinLock = struct {
    locked: std.atomic.Value(bool) = .init(false),
    pub fn lock(self: *SpinLock) void {
        while (self.locked.swap(true, .acquire)) {
            std.atomic.spinLoopHint();
        }
    }
    pub fn unlock(self: *SpinLock) void {
        self.locked.store(false, .release);
    }
};

/// The engine, generic over the task payload `T` and the task error set `E`. `Ctx` is
/// the caller's context (e.g. the loader) threaded to each task's `run`.
pub fn Engine(comptime Ctx: type, comptime T: type, comptime E: type) type {
    return struct {
        const Self = @This();

        /// A unit of work: an opaque payload plus the function that runs it. `run`
        /// receives the caller ctx, the payload, and a `*Handle` it can use to rack
        /// further tasks (the demand edges). It may return an error (fatal → the
        /// engine stops).
        pub const Task = struct {
            payload: T,
            run: *const fn (ctx: *Ctx, payload: T, h: *Handle) E!void,
        };

        /// The scheduling handle handed to a running task: the ONLY way to rack more
        /// work. Keeps the `racked` counter and the queue in lockstep under the mutex.
        pub const Handle = struct {
            engine: *Self,
            pub fn rack(self: *Handle, task: Task) E!void {
                try self.engine.rack(task);
            }
        };

        arena: std.mem.Allocator,
        ctx: *Ctx,

        /// AFFORDANCE: guards the run queue + counters. One worker never contends;
        /// multi-core stealing later takes this lock (or replaces it with per-core
        /// deques). Present from day one so the shared-state shape is correct.
        mutex: SpinLock = .{},
        run_queue: std.ArrayList(Task) = .empty,

        /// the in/out counter — the race-free "done" detector. `racked` bumps on every
        /// rack; `completed` bumps as each task finishes. Quiescent ⇔ equal.
        racked: usize = 0,
        completed: usize = 0,

        /// AFFORDANCE: abnormal/early teardown. Checked at the top of the loop; unused
        /// in the single-threaded happy path (quiescence ends the loop). No poison-pill
        /// delivery yet (that wakes OTHER blocked workers — a multi-worker concern).
        should_stop: std.atomic.Value(bool) = .init(false),

        pub fn init(arena: std.mem.Allocator, ctx: *Ctx) Self {
            return .{ .arena = arena, .ctx = ctx };
        }

        /// Rack a task: bump `racked`, push to the run queue. Mutex-guarded. `E` must
        /// include `error{OutOfMemory}` (the queue append can OOM).
        pub fn rack(self: *Self, task: Task) E!void {
            self.mutex.lock();
            defer self.mutex.unlock();
            self.racked += 1;
            try self.run_queue.append(self.arena, task);
        }

        /// Pull the next runnable task, or null if the run queue is empty. Mutex-guarded.
        fn pull(self: *Self) ?Task {
            self.mutex.lock();
            defer self.mutex.unlock();
            if (self.run_queue.items.len == 0) return null;
            return self.run_queue.pop();
        }

        /// Run the worker loop to QUIESCENCE (single-threaded). Returns when the run
        /// queue is drained and `completed == racked`. A task error stops the engine
        /// and propagates. The stop flag also ends the loop (affordance).
        pub fn run(self: *Self) E!void {
            while (!self.should_stop.load(.acquire)) {
                const task = self.pull() orelse break; // run queue empty ⇒ quiescent
                var handle: Handle = .{ .engine = self };
                try task.run(self.ctx, task.payload, &handle);
                self.mutex.lock();
                self.completed += 1;
                self.mutex.unlock();
            }
        }
    };
}

test "engine runs racked tasks to quiescence, tasks can rack more" {
    const Counter = struct { total: usize = 0 };
    const E = Engine(Counter, u32, error{OutOfMemory});
    const runFn = struct {
        fn run(ctx: *Counter, payload: u32, h: *E.Handle) error{OutOfMemory}!void {
            ctx.total += payload;
            // fan out: a task of value N racks N/2 (a shrinking tree) to exercise
            // dynamic racking + quiescence.
            if (payload > 1) try h.rack(.{ .payload = payload / 2, .run = @This().run });
        }
    }.run;

    var ctx: Counter = .{};
    var e = E.init(std.testing.allocator, &ctx);
    defer e.run_queue.deinit(std.testing.allocator);
    try e.rack(.{ .payload = 8, .run = runFn });
    try e.run();
    // 8 + 4 + 2 + 1 = 15; and racked == completed at quiescence.
    try std.testing.expectEqual(@as(usize, 15), ctx.total);
    try std.testing.expectEqual(e.racked, e.completed);
}
