//! IdentKV — the demand table for IDENTIFIERS (sort/const/func/pred/import), filled
//! by FetchTask. `(namespace, name) -> State`, where State is `done` (the interned
//! identifier `Index`) or `in_flight` (the TaskIndex currently fetching it); "absent" = no
//! entry. The pool holds the identifier's CONTENT (its refinement/sort/signature/body);
//! IdentKV owns its `(namespace,name)` IDENTITY AND the done/in-flight/absent lifecycle.
//! The non-fact sibling of FactKV — same shape, same lock discipline; differs only in what
//! it produces (an identifier, not a fact).
//! (Deliberately a peer clone of FactKV, NOT a shared generic — two concrete tables read
//! clearer than a generalization extracted from one instance.)
//!
//! CONCURRENCY (see the internpool-concurrency-model memory; single-threaded today, so
//! locks are uncontended). `claimOrLookup` and `publish` take the RwLock EXCLUSIVE and hold
//! it across the whole check(->claim | ->mint->publish), so two fetchers can't both see
//! "absent" and both claim/build (the dedup race). The mint nests the InternPool
//! WRITE-MUTEX (lock order IdentKV -> InternPool, never reversed).

const std = @import("std");
const InternPool = @import("InternPool.zig");
const Engine = @import("Engine.zig");

const IdentKV = @This();

/// Key: an identifier's identity — its namespace + name.
pub const Key = struct { namespace: InternPool.Index, name: InternPool.StrId };

/// The stored value: `done` (the interned identifier token — durable) or `in_flight` (the
/// `TaskIndex` currently fetching it; others block on it). "Absent" = no map entry.
pub const State = union(enum) {
    done: InternPool.Index,
    in_flight: Engine.TaskIndex,
};

/// What `claimOrLookup` tells a FetchTask to do (the entry protocol's 3 branches):
/// - `done`: already fetched (its token) — nothing to do.
/// - `in_flight`: another task (this TaskIndex) is fetching it — SUSPEND blocked-on it.
/// - `claimed`: it was absent; you just claimed it — BEGIN FETCHING.
pub const Outcome = union(enum) {
    done: InternPool.Index,
    in_flight: Engine.TaskIndex,
    claimed,
};

pool: *InternPool,
map: std.AutoHashMapUnmanaged(Key, State) = .empty,
lock: std.Io.RwLock = .init,

pub fn init(pool: *InternPool) IdentKV {
    return .{ .pool = pool };
}

/// A plain READ of the current state — no claim, no side effects. Used by ELABORATION,
/// which runs after a read pass has ensured its names are `done` and only needs to map
/// name -> Index (an absent/in_flight result there is a driver bug or a benign race).
/// Takes the exclusive lock for simplicity (uncontended single-threaded; a shared-read
/// optimization can come with real multi-threading).
pub fn lookup(self: *IdentKV, io: std.Io, key: Key) ?State {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    return self.map.get(key);
}

/// The FetchTask ENTRY PROTOCOL, atomic under the EXCLUSIVE lock (the claim in the absent
/// case must share the critical section with the lookup, or two fetchers both see "absent"
/// and both claim). `self_task` is the calling fetch-task's own `TaskIndex`.
pub fn claimOrLookup(self: *IdentKV, io: std.Io, key: Key, self_task: Engine.TaskIndex) std.mem.Allocator.Error!Outcome {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    if (self.map.get(key)) |state| return switch (state) {
        .done => |index| .{ .done = index },
        .in_flight => |task| .{ .in_flight = task },
    };
    try self.map.put(self.pool.arena, key, .{ .in_flight = self_task });
    return .claimed;
}

/// A descriptor for the identifier a fetcher wants minted — one variant per concrete pool
/// identifier kind, carrying that kind's content (the fetcher assembled it; `publish`
/// mints it under the correct nested lock). Mirrors the pool's identifier `Key`s.
pub const Mint = union(enum) {
    sort: InternPool.Key.Sort,
    constant: InternPool.Key.Constant,
    func: InternPool.Key.Callable,
    pred: InternPool.Key.Callable,
    import: InternPool.Key.Import,
    /// a MODEL (interpretation). Unlike the others, a model is DEDUPED by content
    /// (parent+overlay), so it goes through `get`, not a `mint*`; a model name in IdentKV
    /// maps to that (possibly shared) `.model` Index.
    model: InternPool.Key.Model,
    /// ALIAS-COLLAPSE (Foundation C): bind this name to an ALREADY-EXISTING pool `Index` —
    /// mint NOTHING. `sort A = B` / `const X = Y` / `func f = g` / `pred p = q` bind the
    /// local name to the target's origin Index, so kernel terms + lookups coincide
    /// (identity by origin, transitive to the defining entity). The fetcher resolves the
    /// target (demanding it + walking a chain of aliases) and publishes its Index here.
    existing: InternPool.Index,
};

/// SUCCESS transition: the claiming task fetched `key`, so mint its concrete identifier
/// (per `mint`) and flip the entry in_flight -> done. Returns the identifier `Index`. The
/// mint nests the InternPool write-mutex inside the exclusive lock (order IdentKV ->
/// InternPool). Callers then wake anyone parked on the claiming task's index (engine-side).
pub fn publish(self: *IdentKV, io: std.Io, key: Key, mint: Mint) std.mem.Allocator.Error!InternPool.Index {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    const index = try self.mintUnderLock(mint);
    try self.map.put(self.pool.arena, key, .{ .done = index });
    return index;
}

/// Dispatch the concrete pool mint for a `Mint` descriptor. Called with the InternPool
/// write-mutex already held (via `publish`).
fn mintUnderLock(self: *IdentKV, mint: Mint) std.mem.Allocator.Error!InternPool.Index {
    return switch (mint) {
        .sort => |s| self.pool.mintSort(s),
        .constant => |c| self.pool.mintConstant(c),
        .func => |c| self.pool.mintFunc(c),
        .pred => |c| self.pool.mintPred(c),
        .import => |m| self.pool.mintImport(m),
        .model => |m| self.pool.intern(.{ .model = m }), // deduped by content (parent+overlay)
        .existing => |ix| ix, // alias-collapse: bind to the target's origin Index, mint nothing
    };
}

test "IdentKV demand table: claim -> in_flight -> publish -> done, deduped per key" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());
    var kv: IdentKV = .init(&pool);

    var threaded: std.Io.Threaded = .init(arena_state.allocator(), .{});
    const io = threaded.io();

    const f = try pool.intern(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });
    const ns = try pool.namespace(.universe, f);
    const nat = try pool.internString("Nat");
    const k = IdentKV.Key{ .namespace = ns, .name = nat };

    const my_task: Engine.TaskIndex = @enumFromInt(7);
    const other_task: Engine.TaskIndex = @enumFromInt(3);

    // ABSENT -> claim with my task; begin fetching.
    try std.testing.expectEqual(IdentKV.Outcome.claimed, try kv.claimOrLookup(io, k, my_task));
    // now IN-FLIGHT -> a second fetcher is told to suspend on the claiming task.
    try std.testing.expectEqual(IdentKV.Outcome{ .in_flight = my_task }, try kv.claimOrLookup(io, k, other_task));
    // PUBLISH -> mints the concrete identifier (a root sort here), flips in_flight -> done.
    const ident = try kv.publish(io, k, .{ .sort = .{ .name = k.name, .loc = 0, .refinement = null } });
    try std.testing.expect(pool.keyOf(ident).sort.refinement == null);
    // now DONE -> lookups return the token, fetch-nothing.
    try std.testing.expectEqual(IdentKV.Outcome{ .done = ident }, try kv.claimOrLookup(io, k, other_task));
}
