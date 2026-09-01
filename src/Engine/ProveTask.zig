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

/// Intern the theorem's representation: `(universe-namespace(file), name)` -> a `.theorem`
/// entity whose `Index` is the theorem's identity. (Later: also demand its citations and
/// check the proof; for now interning is the whole job and verification stays with the
/// eager back-end.)
pub fn run(self: *Context, task: ProveTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    _ = h;
    // create-if-absent through FactKV (the locked demand layer), not the pool directly —
    // this is the coordination point a concurrent prover would serialize on.
    const ns = try self.interner.namespace(.universe, task.file);
    _ = try self.facts.write(self.io, .{ .namespace = ns, .name = task.name }, .theorem);
}
