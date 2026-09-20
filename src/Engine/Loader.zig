//! The off-worker FILE LOADER. A ParseTask hands "load this file" here and suspends on
//! itself; a thread of a DEDICATED, bounded `std.Io.Threaded` pool does the blocking
//! open+read (and, for a literate `.md`, the block extraction), publishes the result on the
//! task, and wakes it through `Engine.externalEnd`. A prover worker never blocks in a read.
//!
//! Why a separate pool: the prover workers are compute-bound and sized to the physical cores
//! (`Verify.workers`); a thread that sleeps in a syscall costs a core nothing, so the loader
//! is sized on its own (`Verify.io_threads`, a ceiling, capped at 64) and may exceed them.
//! `std.Io.Threaded` spawns lazily — a thread per submission that finds no idle one — and
//! its threads persist, so `prewarm` can raise the floor before the run starts.
//!
//! Engine contract (see `Engine.externalBegin`/`externalEnd`): the count is bumped BEFORE the
//! hand-off and retired by the thread that did the work, so the engine cannot reach its
//! termination check with a read outstanding, and the engine mutex is the publication
//! barrier for what the read produced. A submission the pool refuses (its ceiling reached,
//! or a thread failed to spawn) is unwound with `externalCancel` and the caller reads
//! inline — the loader is an accelerator, never a requirement.
//!
//! Allocation: the source bytes are DURABLE (read to render time) and land on `ctx.arena`,
//! whose bump is thread-safe; a `.md`'s raw bytes are transient and go through a scratch
//! arena reclaimed on the loading thread. The pool's own per-task closures come from the
//! gpa handed to `Threaded.init` — `root.gpa()`, never an arena: `Group.Task.destroy` frees.

const std = @import("std");
const Context = @import("../Context.zig");
const Engine = @import("../Engine.zig");
const ParseTask = @import("ParseTask.zig");

const Loader = @This();

/// The dedicated pool's `Io` (never the prover's).
io: std.Io,
/// Every submitted load. Awaited ONCE, by `drain`, as the barrier that no read outlives the
/// engine it will report to.
group: std.Io.Group = .init,

/// Hand `task`'s file to the pool. On success the caller suspends on `waiter` (its own
/// index); the load's completion wakes it. On `error.Unavailable` nothing was submitted and
/// nothing is owed — read inline.
pub fn submit(self: *Loader, ctx: *Context, engine: *Engine, task: *ParseTask, waiter: Engine.TaskIndex) error{Unavailable}!void {
    engine.externalBegin(); // BEFORE the hand-off: never a window where the work exists and the count does not
    self.group.concurrent(self.io, load, .{ ctx, engine, task, waiter }) catch {
        engine.externalCancel(); // nothing ran, nothing to wake
        return error.Unavailable;
    };
}

/// The pool-thread side: read, publish on the task, retire the external count (which wakes
/// the task). The read's own failures are DATA here (`ParseTask.land` records them); the
/// resumed task diagnoses on its worker, where `sink`/`origins` belong.
fn load(ctx: *Context, engine: *Engine, task: *ParseTask, waiter: Engine.TaskIndex) void {
    task.land(ParseTask.readSource(ctx, ctx.files.get(@intFromEnum(task.file_id)).path));
    engine.externalEnd(waiter);
}

/// Barrier: block until every submitted load has landed. Called with no worker running (so
/// nothing submits concurrently — `Group.await` requires that) and BEFORE the engine the
/// loads report to goes out of scope.
pub fn drain(self: *Loader) void {
    self.group.await(self.io) catch {}; // Canceled: nobody cancels this group
}

/// Raise the pool to `n` live threads before the run: submit `n` holds that stay busy until
/// the LAST one is in (the pool spawns only when no thread is idle, so instantly-finishing
/// no-ops would all land on one thread), then release them.
///
/// The release is NOT a count barrier. Fewer than `n` may ever start — the ceiling, or a
/// spawn failure mid-loop — and "wait until n have arrived" would then hold the pool's
/// threads forever, wedging every later load into the inline fallback and hanging `drain` at
/// exit. So the submitter posts one permit per SUBMISSION, unconditionally, whatever
/// happened: a hold that never submitted never waits, and a hold that did gets its permit
/// whenever it runs. Then the holds are awaited (microseconds) so they are not occupying
/// ceiling slots when the first real load is submitted. A spawn failure degrades to fewer
/// warm threads, nothing else.
pub fn prewarm(self: *Loader, n: usize) void {
    var gate: std.Io.Semaphore = .{};
    var holds: std.Io.Group = .init;
    var submitted: usize = 0;
    while (submitted < n) : (submitted += 1) {
        holds.concurrent(self.io, hold, .{ &gate, self.io }) catch break;
    }
    var released: usize = 0;
    while (released < submitted) : (released += 1) gate.post(self.io);
    holds.await(self.io) catch {};
}

fn hold(gate: *std.Io.Semaphore, io: std.Io) void {
    gate.waitUncancelable(io);
}
