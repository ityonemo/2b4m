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

/// The parse task payload — the sole task shape today (all task payloads live under
/// `src/Engine/`). `ProveTask` etc. join it there; `Task.payload` becomes a union.
pub const ParseTask = @import("Engine/ParseTask.zig");

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

/// A unit of work: an opaque payload plus the function that runs it. `run` receives the
/// `Context` context, the payload, and a `*Handle` it can use to rack further tasks (the
/// demand edges). It may return an allocation error (fatal → the engine stops).
///
/// TODO(prove-slice): `payload` becomes a `union(enum) { parse: ParseTask, prove: … }`
/// so the engine can key/suspend on the variant; for now the sole shape is parse.
pub const Task = struct {
    payload: ParseTask,
    run: *const fn (ctx: *Context, payload: ParseTask, h: *Handle) std.mem.Allocator.Error!void,
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
    // touching the Context ctx (it only reads/writes a counter smuggled through a global),
    // so an undefined ctx pointer is fine — we test scheduling, not parsing.
    const S = struct {
        var total: usize = 0;
        fn run(ctx: *Context, payload: ParseTask, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx; // never dereferenced
            const n = @intFromEnum(payload.file_id);
            total += n;
            // fan out: a task of value N racks N/2 (a shrinking tree) to exercise
            // dynamic racking + quiescence.
            if (n > 1) try h.rack(.{ .payload = .{ .file_id = @enumFromInt(n / 2), .source = "", .path = "" }, .run = &@This().run });
        }
    };
    S.total = 0;

    var e = Engine.init(std.testing.allocator, undefined);
    defer e.deinit();
    try e.rack(.{ .payload = .{ .file_id = @enumFromInt(8), .source = "", .path = "" }, .run = &S.run });
    try e.run();
    // 8 + 4 + 2 + 1 = 15; and racked == completed at quiescence.
    try std.testing.expectEqual(@as(usize, 15), S.total);
    try std.testing.expectEqual(e.racked, e.completed);
}
