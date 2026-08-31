//! The demand-driven task engine — FRAMEWORK ONLY (first slice).
//!
//! This FILE IS the engine struct (capitalized-file = top-level-struct convention):
//! `const Engine = @import("Engine.zig")` yields the type directly, and its fields +
//! methods live at file top level; the helper types (SpinLock, Task, Handle) are nested
//! pub decls. Task PAYLOADS live under `src/Engine/` (ParseTask now, re-exported here).
//!
//! This is the strangler entry point for the execution refactor (see the plan file
//! ok-claude-can-you-wondrous-pine.md). It provides a task queue + worker loop with
//! the CONCURRENCY AFFORDANCES (a mutex around shared queue/counter state, an atomic
//! stop flag) baked in, but runs SINGLE-THREADED for now — so adding multi-core
//! work-stealing later is a wiring change, not a rewrite.
//!
//! CONCRETE, not generic. The engine owns exactly the task shapes bpa's checker needs
//! (today: parse; later: prove). A `Task` is a payload plus a `run` function closing
//! over the `Context` context. The engine pulls a task off the run queue, runs it (the
//! task may `rack` more tasks via the handle it is given), and repeats until QUIESCENT
//! — the race-free termination condition `completed == racked` (the "in/out counter").
//! Normal termination is quiescence, NOT a shutdown task; the stop flag is the
//! affordance for future abnormal teardown.
//!
//! NOT here yet (later slices): the parked queue / suspend / resume, cycle detection,
//! and real multi-threading. Only the parse task — which never suspends — runs on it.
//! When `prove` lands, `Task.payload` grows into a union the engine can inspect (to
//! compute a memo key and decide suspension) — the reason this is concrete, not generic.

const std = @import("std");
const Context = @import("Context.zig");

const Engine = @This();

/// Task types (all payloads live under `src/Engine/`). `parse` produces ASTs + follows
/// imports (transitional); `prove` is racked by the parse scan per theorem — a NO-OP for
/// now. The engine treats both uniformly via type-erased payloads (see `Task`).
pub const ParseTask = @import("Engine/ParseTask.zig");
pub const ProveTask = @import("Engine/ProveTask.zig");

arena: std.mem.Allocator,
ctx: *Context,

/// AFFORDANCE: guards the run queue + counters. One worker never contends; multi-core
/// stealing later takes this lock (or replaces it with per-core deques). Present from
/// day one so the shared-state shape is correct.
mutex: SpinLock = .{},
run_queue: std.ArrayList(Task) = .empty,

/// the in/out counter — the race-free "done" detector. `racked` bumps on every rack;
/// `completed` bumps as each task finishes. Quiescent ⇔ equal.
racked: usize = 0,
completed: usize = 0,

/// AFFORDANCE: abnormal/early teardown. Checked at the top of the loop; unused in the
/// single-threaded happy path (quiescence ends the loop). No poison-pill delivery yet
/// (that wakes OTHER blocked workers — a multi-worker concern).
should_stop: std.atomic.Value(bool) = .init(false),

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

/// A unit of work: a TYPE-ERASED payload pointer plus the function that runs it. The
/// engine is task-type-AGNOSTIC — it never inspects the payload; it just calls `run`,
/// which casts the pointer back to its concrete type. Each task type (see `src/Engine/`)
/// owns a `new(arena, payload)` that arena-allocates the payload (so it outlives the
/// queue slot) and bundles the matching typed `run`. Adding a task type touches ZERO
/// lines here. `run` may return an allocation error (fatal → the engine stops).
///
/// When suspend/parking lands, the engine's inspection needs (a memo key, a can-suspend
/// flag) become explicit FIELDS here — not knowledge of the payload's concrete type.
pub const Task = struct {
    payload: *anyopaque,
    run: *const fn (ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void,
};

/// The scheduling handle handed to a running task: the ONLY way to rack more work. Keeps
/// the `racked` counter and the queue in lockstep under the mutex.
pub const Handle = struct {
    engine: *Engine,
    pub fn rack(self: *Handle, task: Task) std.mem.Allocator.Error!void {
        try self.engine.rack(task);
    }
};

pub fn init(arena: std.mem.Allocator, ctx: *Context) Engine {
    return .{ .arena = arena, .ctx = ctx };
}

/// Rack a task: bump `racked`, push to the run queue. Mutex-guarded.
pub fn rack(self: *Engine, task: Task) std.mem.Allocator.Error!void {
    self.mutex.lock();
    defer self.mutex.unlock();
    self.racked += 1;
    try self.run_queue.append(self.arena, task);
}

/// Pull the next runnable task, or null if the run queue is empty. Mutex-guarded.
fn pull(self: *Engine) ?Task {
    self.mutex.lock();
    defer self.mutex.unlock();
    if (self.run_queue.items.len == 0) return null;
    return self.run_queue.pop();
}

/// Run the worker loop to QUIESCENCE (single-threaded). Returns when the run queue is
/// drained and `completed == racked`. A task error stops the engine and propagates. The
/// stop flag also ends the loop (affordance).
pub fn run(self: *Engine) std.mem.Allocator.Error!void {
    while (!self.should_stop.load(.acquire)) {
        const task = self.pull() orelse break; // run queue empty ⇒ quiescent
        var handle: Handle = .{ .engine = self };
        try task.run(self.ctx, task.payload, &handle);
        self.mutex.lock();
        self.completed += 1;
        self.mutex.unlock();
    }
}

pub fn deinit(self: *Engine) void {
    self.run_queue.deinit(self.arena);
}

test "engine runs racked tasks to quiescence, tasks can rack more" {
    // Pure-scheduling test: the run fn exercises the queue + in/out counter WITHOUT
    // touching the Context ctx (an undefined ctx pointer is fine — we test scheduling).
    // The payload is a type-erased `*u32` the run fn casts back — mirroring how a real
    // task type casts its own payload.
    const S = struct {
        var total: usize = 0;
        fn run(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx; // never dereferenced
            const n: *u32 = @ptrCast(@alignCast(payload));
            total += n.*;
            // fan out: a task of value N racks N/2 (a shrinking tree) to exercise dynamic
            // racking + quiescence. The child payload is arena-allocated so it outlives
            // the queue slot (the discipline every real task type follows via `new`).
            if (n.* > 1) {
                const child = try h.engine.arena.create(u32);
                child.* = n.* / 2;
                try h.rack(.{ .payload = child, .run = &@This().run });
            }
        }
    };
    S.total = 0;

    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var e = Engine.init(arena_state.allocator(), undefined);
    const seed = try arena_state.allocator().create(u32);
    seed.* = 8;
    try e.rack(.{ .payload = seed, .run = &S.run });
    try e.run();
    // 8 + 4 + 2 + 1 = 15; and racked == completed at quiescence.
    try std.testing.expectEqual(@as(usize, 15), S.total);
    try std.testing.expectEqual(e.racked, e.completed);
}
