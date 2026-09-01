//! The prove task — the SECOND task type, racked by the parse SCAN for each theorem in
//! the requested (root) file. It is the root of demand: in the target design a prove task
//! resolves its theorem (pulling parses/proofs of what it cites), then checks the proof.
//!
//! ITS FIRST REAL JOB is to create the INTERNED REPRESENTATION of the theorem: intern
//! `(namespace, name)` into the pool, so the theorem exists as an entity whose `Index` IS
//! its identity. It does NOT check the proof yet — the existing eager `Context` back-end
//! still verifies — so this stays behavior-neutral. The proof-checking body grows later.
//!
//! Payload = which theorem: its file's pool `.file` Index + its interned name. The
//! theorem's namespace is the file's universe-namespace `(universe, file)`.

const std = @import("std");
const InternPool = @import("../InternPool.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const FactKV = @import("../FactKV.zig");

const ProveTask = @This();

/// the `.file` entity Index of the theorem's home file (not the dense FileId — the pool
/// identity, which the namespace is built from).
file: InternPool.Index,
name: InternPool.StrId,

/// Package a payload into a rack-ready `Engine.Task` (arena-allocated payload + typed
/// erased run), mirroring `ParseTask.new`.
pub fn new(arena: std.mem.Allocator, payload: ProveTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(ProveTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *ProveTask = @ptrCast(@alignCast(payload));
    return run(self, task.*, h);
}

/// The demand ENTRY PROTOCOL (see FactKV): look up `(namespace, name)`, claiming it if
/// absent. Branches:
///   - proven    -> nothing to do.
///   - in_flight -> SUSPEND blocked-on the task already proving it (a redundant duplicate
///                  prove-task dedups to a no-op waiter; on resume it re-runs, finds
///                  `proven`, and completes).
///   - claimed   -> we own it: BEGIN PROVING. For now the eager back-end still does the
///                  actual checking, so we immediately `publish` (mint the fact token,
///                  in_flight -> proven). When the reentrant prover lands, "begin proving"
///                  becomes the real suspendable lowering, and publish moves to its
///                  success path.
pub fn run(self: *Context, task: ProveTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const ns = try self.interner.namespace(.universe, task.file);
    const key = FactKV.Key{ .namespace = ns, .name = task.name };
    switch (try self.facts.claimOrLookup(self.io, key, h.self_index)) {
        .proven => return,
        .in_flight => |blocker| {
            h.suspendOn(blocker);
            return;
        },
        .claimed => {
            // BEGIN PROVING — eager back-end still verifies (scaffolding); publish flips
            // in_flight -> proven. (No demand/suspend on citations yet — the risky slice.)
            // The fact now carries a formula; the REAL asserted proposition comes with the
            // one-walk lowering — for now a placeholder term stands in (this path is not
            // yet wired to actual proving).
            const formula = try self.interner.get(.{ .term_bvar = 0 });
            _ = try self.facts.publish(self.io, key, .theorem, formula);
        },
    }
}
