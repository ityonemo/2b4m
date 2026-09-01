//! The fetch task — the task type that produces an IDENTIFIER (sort/const/func/pred/
//! define), the non-fact sibling of ProveTask. It resolves an identifier's shape into the
//! pool via IdentKV, following the SAME demand entry protocol as ProveTask does via FactKV
//! (claim / suspend-on-in-flight / use-done).
//!
//! NOT WIRED into the prover or real resolution yet (this slice builds it in isolation).
//! For now `run` runs the entry protocol and, on `claimed`, immediately publishes the
//! identifier token (the real shape-interning — resolving the identifier's referenced
//! names, which is where a FetchTask will later SUSPEND — comes when the prover drives it).
//!
//! Payload = which identifier: its file's pool `.file` Index + its interned name + which
//! IdentKind it is. Namespace is the file's universe-namespace `(universe, file)`.

const std = @import("std");
const InternPool = @import("../InternPool.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const IdentKV = @import("../IdentKV.zig");

const FetchTask = @This();

file: InternPool.Index,
name: InternPool.StrId,
kind: InternPool.Key.IdentKind,

/// Package a payload into a rack-ready `Engine.Task` (arena-allocated payload + typed
/// erased run), mirroring `ParseTask.new` / `ProveTask.new`.
pub fn new(arena: std.mem.Allocator, payload: FetchTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(FetchTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *FetchTask = @ptrCast(@alignCast(payload));
    return run(self, task.*, h);
}

/// The demand ENTRY PROTOCOL (see IdentKV): look up `(namespace, name)`, claiming it if
/// absent.
///   - done      -> already fetched; nothing to do.
///   - in_flight -> SUSPEND blocked-on the task already fetching it (a redundant duplicate
///                  fetch dedups to a no-op waiter).
///   - claimed   -> we own it: intern the identifier token. (Later this is where the shape
///                  RESOLVES its referenced names and may suspend; for now it just mints.)
pub fn run(self: *Context, task: FetchTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const ns = try self.interner.namespace(.universe, task.file);
    const key = IdentKV.Key{ .namespace = ns, .name = task.name };
    switch (try self.idents.claimOrLookup(self.io, key, h.self_index)) {
        .done => return,
        .in_flight => |blocker| {
            h.suspendOn(blocker);
            return;
        },
        .claimed => {
            _ = try self.idents.publish(self.io, key, task.kind);
        },
    }
}

test "FetchTask through the engine: two fetches of one identifier dedup (claim, then suspend+resume)" {
    const std_ = std;
    var arena_state: std_.heap.ArenaAllocator = .init(std_.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var threaded: std_.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    var pool: InternPool = try .init(arena);
    // A partial Context: FetchTask.run only touches io/interner/idents; the rest is
    // never dereferenced on this path (mirrors the engine test's `undefined` ctx trick).
    var ctx: Context = undefined;
    ctx.io = io;
    ctx.interner = &pool;
    ctx.idents = .init(&pool);

    const f = try pool.get(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });
    const nat = try pool.internString("Nat");

    var eng = Engine.init(arena, &ctx);
    defer eng.deinit();
    // rack TWO fetches of the same identifier — the second must dedup to a no-op waiter.
    _ = try eng.rack(try new(arena, .{ .file = f, .name = nat, .kind = .sort }));
    _ = try eng.rack(try new(arena, .{ .file = f, .name = nat, .kind = .sort }));
    try eng.run();

    // Exactly ONE identifier token was minted (dedup): the pool has universe + Nat's file
    // + its path string + the namespace + ONE ident. Assert the ident is present & a sort.
    const ns = try pool.namespace(.universe, f);
    switch (try ctx.idents.claimOrLookup(io, .{ .namespace = ns, .name = nat }, @enumFromInt(99))) {
        .done => |ident| try std_.testing.expectEqual(InternPool.Key.IdentKind.sort, pool.keyOf(ident).ident),
        else => try std_.testing.expect(false), // must be done after both fetches ran
    }
    try std_.testing.expectEqual(eng.racked, eng.completed); // quiescent
}
