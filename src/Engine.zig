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

/// A stable handle to a racked task — its slot in the append-only `tasks` table. Distinct
/// id space from `InternPool.Index` (tasks are mutable, transient scheduler state; the
/// pool is immutable/eternal). Used to wait on / park on a specific task.
pub const TaskIndex = enum(u32) { _ };

/// A suspended task + the task it is blocked on (its wake trigger + the cycle-detection
/// edge).
const Parked = struct { task: TaskIndex, blocked_on: TaskIndex };

/// Task types (all payloads live under `src/Engine/`). `parse` produces ASTs + follows
/// imports (transitional); `prove` is racked by the parse scan per theorem — a NO-OP for
/// now. The engine treats both uniformly via type-erased payloads (see `Task`).
pub const ParseTask = @import("Engine/ParseTask.zig");
pub const ProveTask = @import("Engine/ProveTask.zig");
pub const FetchTask = @import("Engine/FetchTask.zig");
pub const ModelTask = @import("Engine/ModelTask.zig");

arena: std.mem.Allocator,
ctx: *Context,

/// AFFORDANCE: guards the task table, run queue + counters. One worker never contends;
/// multi-core stealing later takes this lock (or replaces it with per-core deques).
/// Present from day one so the shared-state shape is correct.
mutex: SpinLock = .{},
/// The task TABLE — append-only; a task's `TaskIndex` is its slot here, a STABLE handle
/// that outlives its time in the run queue (so a suspended task can be waited on / parked
/// on by `TaskIndex`, and FactKV can record "task T is proving this"). The run queue holds
/// INDICES into this table, not tasks.
tasks: std.ArrayList(Task) = .empty,
run_queue: std.ArrayList(TaskIndex) = .empty,
/// `--trace-facts` lifecycle tracing. Held HERE (not read off `ctx`) because the pure
/// scheduling unit test builds an Engine over an undefined Context; `Context.loadRoots`
/// sets it from `verify` before the run.
trace: bool = false,
/// `--chaos`: when set, `pull` takes a RANDOM runnable task rather than the top of the
/// stack, so a run explores a different interleaving. Deterministic per seed. Held here
/// (like `trace`) so the scheduling unit tests can drive it without a Context. See
/// `Verify.chaos_seed` for why this exists — it is how the determinism contract is tested.
chaos: ?std.Random.DefaultPrng = null,
/// SUSPENDED tasks, each tagged with the `blocked_on` task it waits on. Cores never pull
/// from here. When a task completes, everything parked blocked-on IT moves to the run
/// queue (`wake`). The parked set also doubles (later) as the cycle/wedge registry: run
/// queue empty + parked non-empty + nothing finishing = stuck. Detector deferred; the
/// `blocked_on` edge it will walk is recorded here from day one.
parked: std.ArrayList(Parked) = .empty,

/// The in/out counters, read TOGETHER under `mutex` to decide termination. `racked` bumps
/// on every rack, `completed` as each task finishes, `in_flight` while a task is popped but
/// not yet resolved (parked or completed).
///
/// They are a CONSISTENT SNAPSHOT, not three independent numbers: making them separate
/// atomics would let a reader observe a combination that never existed — `in_flight` already
/// decremented while the children that task racked are not yet in `racked` — which reads as
/// a false wedge. So they stay under the engine lock and the predicate is evaluated there.
racked: usize = 0,
completed: usize = 0,
in_flight: usize = 0,

/// Set when a task returns an error (or a caller asks for early teardown): every worker
/// checks it at the top of its loop and exits, so one worker's failure does not leave the
/// others running against a Context the caller is about to tear down.
should_stop: std.atomic.Value(bool) = .init(false),
/// The error that set `should_stop`, re-raised by `run` once the loop exits. Only OOM can
/// realistically land here — a failed PROOF is a diagnostic in the sink, not an error — but
/// an OOM under workers must not leave anyone waiting on a condition nobody will signal.
failure: ?std.mem.Allocator.Error = null,

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
    /// The running task's OWN index — so it can claim itself in FactKV (record "task
    /// `self_index` is proving this") and hand others something to suspend on.
    self_index: TaskIndex,
    /// Set by `suspendOn`: the task this run is blocked on. null ⇒ the task COMPLETED
    /// this run; non-null ⇒ SUSPENDED, park it blocked-on that TaskIndex. The engine reads
    /// this after `run` returns. (`run` stays `void` — suspension is a control signal, not
    /// a return value; a task's actual output lives in the Context it mutates.)
    blocked_on: ?TaskIndex = null,

    /// Rack a child task; discards its `TaskIndex` (fire-and-forget — the common case).
    pub fn rack(self: *Handle, task: Task) std.mem.Allocator.Error!void {
        const idx = try self.engine.rack(task);
        self.engine.traceLifecycle("rack", idx, self.self_index);
    }
    /// Rack a child and KEEP its `TaskIndex` — for a task that will `suspendOn` the child.
    pub fn rackIndexed(self: *Handle, task: Task) std.mem.Allocator.Error!TaskIndex {
        const idx = try self.engine.rack(task);
        self.engine.traceLifecycle("rack", idx, self.self_index);
        return idx;
    }
    /// Signal that this run is SUSPENDED, blocked on task `t`. The engine parks this task;
    /// when `t` completes it is moved back to the run queue and its `run` re-enters (it
    /// resumes from its own saved state — held in the Context / its payload).
    pub fn suspendOn(self: *Handle, t: TaskIndex) void {
        self.blocked_on = t;
    }
};

pub fn init(arena: std.mem.Allocator, ctx: *Context) Engine {
    return .{ .arena = arena, .ctx = ctx };
}

/// Rack a task: append it to the task table (assigning its stable `TaskIndex`), bump
/// `racked`, push the index to the run queue. Returns the `TaskIndex`. Mutex-guarded.
pub fn rack(self: *Engine, task: Task) std.mem.Allocator.Error!TaskIndex {
    self.mutex.lock();
    defer self.mutex.unlock();
    const index: TaskIndex = @enumFromInt(self.tasks.items.len);
    try self.tasks.append(self.arena, task);
    self.racked += 1;
    try self.run_queue.append(self.arena, index);
    return index;
}

/// What a worker should do next.
const Next = union(enum) {
    /// run this task (already counted `in_flight`)
    run: TaskIndex,
    /// nothing runnable and nothing in flight: the run is over (quiescent or wedged)
    done,
    /// nothing runnable, but a task IS in flight and may yet rack more work — wait
    wait,
};

/// Claim the next runnable task, or say why there is none. Mutex-guarded, and the
/// three-counter predicate is evaluated INSIDE that critical section (see `racked`).
///
/// Normally LIFO (`pop`) — see `traceLifecycle` on why the order is not guessable from the
/// source. Under `--chaos` it takes a random runnable task instead: same work, different
/// interleaving, which is what makes a determinism bug reproducible.
fn pull(self: *Engine) Next {
    self.mutex.lock();
    defer self.mutex.unlock();
    if (self.run_queue.items.len == 0) {
        // An empty queue is NOT termination on its own: a worker may hold a task that will
        // rack children. Only "nothing runnable AND nothing running" ends the run.
        return if (self.in_flight == 0) .done else .wait;
    }
    self.in_flight += 1;
    if (self.chaos) |*prng| {
        const i = prng.random().uintLessThan(usize, self.run_queue.items.len);
        return .{ .run = self.run_queue.swapRemove(i) };
    }
    return .{ .run = self.run_queue.pop().? }; // non-empty: checked above
}

/// The task with the given index (from the append-only table). Not mutex-guarded — the
/// table never moves an existing entry (append-only), so a held index is always valid.
fn taskOf(self: *const Engine, index: TaskIndex) Task {
    return self.tasks.items[@intFromEnum(index)];
}

/// Number of tasks ever racked (the append-only table's length).
pub fn taskCount(self: *const Engine) usize {
    return self.tasks.items.len;
}

/// Run the worker loop to QUIESCENCE. Returns when nothing is runnable and nothing is in
/// flight. A task error stops the engine and propagates; the stop flag also ends the loop.
///
/// Tasks left PARKED at that point are a wedge — see `wedged` and `Context.reportWedge`.
/// Run to quiescence on `workers` threads (1 = the calling thread only, today's behavior).
///
/// Every worker runs the SAME loop; parallelism is at task granularity and the tasks
/// coordinate through the Context's own locks. The caller's thread is one of the workers, so
/// `workers` threads means `workers - 1` spawned.
pub fn runWorkers(self: *Engine, workers: usize) std.mem.Allocator.Error!void {
    if (workers <= 1) return self.run();

    const spawned = try self.arena.alloc(std.Thread, workers - 1);
    var started: usize = 0;
    for (spawned) |*t| {
        t.* = std.Thread.spawn(.{}, workerMain, .{self}) catch break; // fewer threads is fine
        started += 1;
    }
    self.run() catch |err| {
        // stop the others before joining, or they run on against a dying Context
        self.should_stop.store(true, .release);
        for (spawned[0..started]) |t| t.join();
        return err;
    };
    for (spawned[0..started]) |t| t.join();
    if (self.failure) |err| return err;
}

/// A spawned worker: the same loop, its error recorded on the engine (a thread cannot
/// propagate one) for `runWorkers` to re-raise.
fn workerMain(self: *Engine) void {
    self.run() catch {}; // `run` already recorded it in `self.failure`
}

pub fn run(self: *Engine) std.mem.Allocator.Error!void {
    while (!self.should_stop.load(.acquire)) {
        const index = switch (self.pull()) {
            .run => |i| i,
            .done => break,
            // Another worker holds a task that may yet rack more. Yield rather than spin
            // hot; whoever resolves that task pushes to the queue or ends the run.
            .wait => {
                std.Thread.yield() catch {};
                continue;
            },
        };
        const task = self.taskOf(index);
        var handle: Handle = .{ .engine = self, .self_index = index };
        self.traceLifecycle("run", index, null);
        task.run(self.ctx, task.payload, &handle) catch |err| {
            // Stop every worker, not just this one, and re-raise after the loop.
            self.mutex.lock();
            if (self.failure == null) self.failure = err;
            self.in_flight -= 1; // this task is resolved (by failing)
            self.mutex.unlock();
            self.should_stop.store(true, .release);
            break;
        };
        if (handle.blocked_on) |blocker| {
            // SUSPENDED: park it (do NOT count as completed — it hasn't finished).
            self.traceLifecycle("park", index, blocker);
            self.mutex.lock();
            self.in_flight -= 1; // resolved: parked, not running
            try self.parked.append(self.arena, .{ .task = index, .blocked_on = blocker });
            self.mutex.unlock();
        } else {
            // COMPLETED: count it, then wake everyone parked blocked-on it.
            self.traceLifecycle("done", index, null);
            self.mutex.lock();
            self.in_flight -= 1; // resolved: completed
            self.completed += 1;
            self.mutex.unlock();
            try self.wake(index);
        }
    }
    if (self.failure) |err| return err;
}

/// `--trace-facts` lifecycle line: what the scheduler did with a task. The run queue is a
/// STACK (`pull` pops the most recently racked or woken task), so an interleaving is not
/// guessable from the source order of declarations — this is how you see it.
fn traceLifecycle(self: *Engine, what: []const u8, index: TaskIndex, other: ?TaskIndex) void {
    if (!self.trace) return; // never touch `ctx` unless tracing was switched on by a real run
    const line = if (other) |o|
        std.fmt.allocPrint(self.arena, "[engine] {s} task#{d} (on task#{d})\n", .{ what, @intFromEnum(index), @intFromEnum(o) }) catch return
    else
        std.fmt.allocPrint(self.arena, "[engine] {s} task#{d}\n", .{ what, @intFromEnum(index) }) catch return;
    self.ctx.traceLine(line);
}

/// A task `finished` completed — move every parked task blocked-on it back to the run
/// queue (it will re-enter its `run` and resume from its saved state). Mutex-guarded;
/// the "stupid simple" parked-queue scan (no separate waiter lists).
fn wake(self: *Engine, finished: TaskIndex) std.mem.Allocator.Error!void {
    self.mutex.lock();
    defer self.mutex.unlock();
    var i: usize = 0;
    while (i < self.parked.items.len) {
        if (self.parked.items[i].blocked_on == finished) {
            const woken = self.parked.swapRemove(i);
            self.traceLifecycle("wake", woken.task, finished);
            try self.run_queue.append(self.arena, woken.task);
        } else {
            i += 1;
        }
    }
}

/// A task that is parked forever: the run queue drained while it was still waiting.
pub const Wedged = struct {
    /// The stuck task, and what it was waiting for.
    task: TaskIndex,
    blocked_on: TaskIndex,
    /// True when following `blocked_on` from this task leads BACK to it: a genuine cycle
    /// that no scheduling order could have resolved. False when the chain instead runs into
    /// a task that completed (a failed proof whose claim stands forever) — a consequence
    /// whose root cause is already in the sink, so re-reporting it would add an error to
    /// every failing file.
    in_cycle: bool,
};

/// The tasks still parked at quiescence — empty on a healthy run.
///
/// A parked task is not counted `completed`, so `completed != racked` here means work was
/// abandoned. Two shapes, which must be reported differently:
///
///   - a CYCLE: following `blocked_on` from the task leads back to the task. Nobody could
///     have proceeded in any order — this is the real diagnostic.
///   - a CHAIN ending in a FAILURE: the walk reaches a task that COMPLETED (a proof that
///     diagnosed and published nothing leaves its FactKV claim standing forever, so its
///     citers never wake) or reaches a self-park. The root cause is already in the sink;
///     re-reporting the consequence would add an error to every failing file.
///
/// Each parked task has exactly ONE out-edge, so the wait-for graph is FUNCTIONAL and the
/// walk is a plain cycle-find (bounded by the parked count, so a chain cannot loop forever).
/// No strongly-connected-components machinery is needed.
pub fn wedged(self: *const Engine, arena: std.mem.Allocator) std.mem.Allocator.Error![]const Wedged {
    if (self.parked.items.len == 0) return &.{};
    // blocker edges of the tasks that never completed: `blocked_on` for a parked task,
    // absent for one that finished (which is what ends a failure chain).
    var edge: std.AutoHashMapUnmanaged(TaskIndex, TaskIndex) = .empty;
    defer edge.deinit(arena);
    for (self.parked.items) |p| try edge.put(arena, p.task, p.blocked_on);

    var out: std.ArrayList(Wedged) = .empty;
    for (self.parked.items) |p| {
        // walk the wait-for chain from this task; it is a cycle only if we come back here.
        var cursor = p.blocked_on;
        var hops: usize = 0;
        const cyclic = while (hops <= self.parked.items.len) : (hops += 1) {
            if (cursor == p.task) break true; // closed the loop
            cursor = edge.get(cursor) orelse break false; // blocker completed: a failure chain
        } else false;
        try out.append(arena, .{ .task = p.task, .blocked_on = p.blocked_on, .in_cycle = cyclic });
    }
    return out.items;
}

pub fn deinit(self: *Engine) void {
    self.run_queue.deinit(self.arena);
    self.tasks.deinit(self.arena);
    self.parked.deinit(self.arena);
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
    const seed_index = try e.rack(.{ .payload = seed, .run = &S.run });
    try std.testing.expectEqual(@as(TaskIndex, @enumFromInt(0)), seed_index); // first task
    try e.run();
    // 8 + 4 + 2 + 1 = 15; and racked == completed at quiescence.
    try std.testing.expectEqual(@as(usize, 15), S.total);
    try std.testing.expectEqual(e.racked, e.completed);
    // the task TABLE is append-only: it holds every task ever racked (8,4,2,1 = 4).
    try std.testing.expectEqual(@as(usize, 4), e.taskCount());
}

test "engine suspends a task blocked on another, resumes it when the blocker completes" {
    // Synthetic demand: task A, on first run, DEMANDS a dependency B — racks B and suspends
    // blocked-on it. B completes; the engine wakes A; A re-enters, sees its dependency done
    // (via shared state, since a task's output lives in shared memory, not a return value),
    // and completes. `run` stays void; suspension is a CONTROL signal via `h.suspendOn(T)`.
    const Shared = struct { a_runs: usize = 0, b_runs: usize = 0, b_index: ?TaskIndex = null };
    const B = struct {
        fn run(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = h;
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            s.b_runs += 1;
        }
    };
    const A = struct {
        fn run(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            s.a_runs += 1;
            if (s.b_index == null) {
                // first entry: demand B, then suspend blocked-on it
                s.b_index = try h.rackIndexed(.{ .payload = payload, .run = &B.run });
                h.suspendOn(s.b_index.?);
                return;
            }
            // resumed: B is done (b_runs == 1) — nothing more to do, complete.
        }
    };

    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var shared: Shared = .{};
    var e = Engine.init(arena_state.allocator(), undefined);
    _ = try e.rack(.{ .payload = &shared, .run = &A.run });
    try e.run();

    try std.testing.expectEqual(@as(usize, 2), shared.a_runs); // ran, suspended, resumed
    try std.testing.expectEqual(@as(usize, 1), shared.b_runs); // ran once
    try std.testing.expectEqual(e.racked, e.completed); // quiescent: both A and B completed
    // A did NOT complete on its suspending run — completed counts each task ONCE.
    try std.testing.expectEqual(@as(usize, 2), e.completed); // A + B
}

test "wedged: a healthy run leaves nothing parked" {
    const S = struct {
        fn run(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            _ = payload;
            _ = h;
        }
    };
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var e = Engine.init(arena, undefined);
    var dummy: u32 = 0;
    _ = try e.rack(.{ .payload = &dummy, .run = &S.run });
    try e.run();
    try std.testing.expectEqual(@as(usize, 0), (try e.wedged(arena)).len);
    try std.testing.expectEqual(e.racked, e.completed);
}

test "wedged: two tasks parked on each other are reported as a CYCLE" {
    // The real shape of a citation cycle: task A demands B (racks it) and suspends on it;
    // B, running, demands A — which already exists and is parked — and suspends on THAT.
    // Neither can ever complete, the run queue drains, and `run` returns as if quiescent.
    // This is what made two mutually-citing theorems print "OK: 0 theorems proven", exit 0.
    const Shared = struct { a: ?TaskIndex = null, b: ?TaskIndex = null };
    const Tasks = struct {
        fn a(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            s.a = h.self_index;
            if (s.b == null) s.b = try h.rackIndexed(.{ .payload = payload, .run = &@This().b });
            h.suspendOn(s.b.?); // wait for B, which will wait for us
        }
        fn b(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            h.suspendOn(s.a.?); // A is parked on us; now we park on A — the cycle closes
        }
    };
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var e = Engine.init(arena, undefined);
    var shared: Shared = .{};
    _ = try e.rack(.{ .payload = &shared, .run = &Tasks.a });
    try e.run();

    const w = try e.wedged(arena);
    try std.testing.expectEqual(@as(usize, 2), w.len); // both stuck
    for (w) |entry| try std.testing.expect(entry.in_cycle); // each blocker is itself stuck
    try std.testing.expect(e.completed < e.racked); // work was abandoned
}

test "wedged: a CHAIN into a failed task is not a cycle, however long" {
    // A waits on B, B waits on C, C completes without publishing (a failed proof leaves its
    // claim standing, so B never wakes). Nothing here is cyclic — the chain has an end — and
    // reporting it would add a second error to every file that already failed. Regression:
    // a one-hop "is my blocker parked?" test called A a cycle, because B *is* parked.
    const Shared = struct { b: ?TaskIndex = null, c: ?TaskIndex = null };
    const Tasks = struct {
        fn c(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            _ = payload;
            _ = h; // completes, publishing nothing
        }
        fn b(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            if (s.c == null) s.c = try h.rackIndexed(.{ .payload = payload, .run = &@This().c });
            h.suspendOn(s.c.?); // waits forever: C finished and will never wake anyone again
        }
        fn a(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            if (s.b == null) s.b = try h.rackIndexed(.{ .payload = payload, .run = &@This().b });
            h.suspendOn(s.b.?);
        }
    };
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var e = Engine.init(arena, undefined);
    var shared: Shared = .{};
    _ = try e.rack(.{ .payload = &shared, .run = &Tasks.a });
    try e.run();

    const w = try e.wedged(arena);
    try std.testing.expectEqual(@as(usize, 2), w.len); // A and B are both stuck
    for (w) |entry| try std.testing.expect(!entry.in_cycle); // but neither is in a cycle
}

test "wedged: a task parked on a COMPLETED task is not a cycle (the blocker failed)" {
    // B runs to completion but publishes nothing useful; A waits on it forever. A is stuck,
    // but the cause is B's own (already-diagnosed) failure — so this must NOT be reported as
    // a cycle, or every failing file would grow a spurious second error.
    const Shared = struct { b_index: ?TaskIndex = null };
    const Tasks = struct {
        fn b(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            _ = payload;
            _ = h; // completes, having "failed" (published nothing)
        }
        fn a(ctx: *Context, payload: *anyopaque, h: *Handle) std.mem.Allocator.Error!void {
            _ = ctx;
            const s: *Shared = @ptrCast(@alignCast(payload));
            if (s.b_index) |blocker| {
                h.suspendOn(blocker); // wait on a task that already finished — never woken
                return;
            }
            s.b_index = try h.rackIndexed(.{ .payload = payload, .run = &@This().b });
            h.suspendOn(s.b_index.?);
        }
    };
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var e = Engine.init(arena, undefined);
    var shared: Shared = .{};
    _ = try e.rack(.{ .payload = &shared, .run = &Tasks.a });
    try e.run();

    const w = try e.wedged(arena);
    try std.testing.expectEqual(@as(usize, 1), w.len);
    try std.testing.expect(!w[0].in_cycle); // blocked on a COMPLETED task: not a cycle
}
