//! FactKV — the `(namespace, name) -> fact Index` resolution/coordination table over the
//! InternPool. It is the demand layer above the pool: a citation resolves a fact by its
//! `(namespace, name)`, and a scan/prove creates one if absent. Holds BOTH axioms and
//! theorems (one mechanism; the axiom/theorem distinction is the fact's `kind`, branched
//! only at the prove-or-not boundary — an axiom is a resolve-and-store leaf).
//!
//! It is the DEMAND TABLE: `(namespace, name) -> State`, where State is `proven` (an
//! interned fact token) or `in_flight` (the TaskIndex currently proving it); "absent" =
//! no entry. The pool holds only bare fact tokens (no identity); FactKV owns the identity
//! index AND this proven/in-flight/absent lifecycle.
//!
//! CONCURRENCY (see the internpool-concurrency-model memory; single-threaded today, so
//! locks are uncontended). `claimOrLookup` and `publish` take the RwLock EXCLUSIVE and
//! hold it across the whole check(->claim | ->mint->publish), so two provers can't both
//! see "absent" and both claim/build (the dedup race). The mint nests the InternPool
//! WRITE-MUTEX (lock order FactKV -> InternPool, never reversed). (A lock-free SHARED
//! `read` fast path can be added if a read-only hot path emerges.)

const std = @import("std");
const InternPool = @import("InternPool.zig");
const Engine = @import("Engine.zig");

const FactKV = @This();

/// Key: a fact's identity — its namespace + name (NOT its kind; kind isn't identity).
pub const Key = struct { namespace: InternPool.Index, name: InternPool.StrId };

/// The state of a `(namespace, name)` in the demand graph — the entry's stored value.
/// PROVEN: an interned fact token (durable, done). IN-FLIGHT: the `TaskIndex` currently
/// proving it (transient; others block on it). "Absent" is the map having no entry.
pub const State = union(enum) {
    proven: InternPool.Index,
    in_flight: Engine.TaskIndex,
};

/// What `claimOrLookup` tells a prover to do (the entry protocol's 3 branches):
/// - `proven`: already proven (its fact token) — nothing to do.
/// - `in_flight`: another task (this TaskIndex) is proving it — SUSPEND blocked-on it.
/// - `claimed`: it was absent; you just claimed it — BEGIN PROVING.
pub const Outcome = union(enum) {
    proven: InternPool.Index,
    in_flight: Engine.TaskIndex,
    claimed,
};

pool: *InternPool,
map: std.AutoHashMapUnmanaged(Key, State) = .empty,
lock: std.Io.RwLock = .init,

pub fn init(pool: *InternPool) FactKV {
    return .{ .pool = pool };
}

/// A plain READ of the current state — no claim, no side effects. Used by citation
/// resolution (a step's read pass ensures its cited facts are `proven` before the
/// justification lowering maps name -> fact Index). Exclusive lock for simplicity
/// (uncontended single-threaded; a shared-read optimization can come with real threads).
pub fn lookup(self: *FactKV, io: std.Io, key: Key) ?State {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    return self.map.get(key);
}

/// The ProveTask ENTRY PROTOCOL, atomic under the EXCLUSIVE lock (the claim in the absent
/// case must be part of the same critical section as the lookup, or two provers both see
/// "absent" and both claim). `self_task` is the calling prove-task's own `TaskIndex`.
///   - PROVEN   -> `.proven(index)`         (nothing to do)
///   - IN-FLIGHT-> `.in_flight(TaskIndex)`  (SUSPEND blocked-on it)
///   - ABSENT   -> store `self_task` in-flight, return `.claimed` (BEGIN PROVING)
/// (Uses the exclusive lock even for the proven/in-flight read: the claim branch mutates,
/// so the whole op must be exclusive. A pure lock-free `read` can be added later if a
/// read-only hot path emerges.)
pub fn claimOrLookup(self: *FactKV, io: std.Io, key: Key, self_task: Engine.TaskIndex) std.mem.Allocator.Error!Outcome {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    if (self.map.get(key)) |state| return switch (state) {
        .proven => |index| .{ .proven = index },
        .in_flight => |task| .{ .in_flight = task },
    };
    try self.map.put(self.pool.arena, key, .{ .in_flight = self_task });
    return .claimed;
}

/// SUCCESS transition: the claiming task proved `key`, so mint its fact token (carrying
/// its `kind` + the `formula` it asserts) and flip the entry in_flight -> proven. Returns
/// the fact `Index`. The mint nests the InternPool write-mutex inside the FactKV exclusive
/// lock (order FactKV -> InternPool). Callers then wake anyone parked on the claiming
/// task's index (engine-side).
pub fn publish(self: *FactKV, io: std.Io, key: Key, kind: InternPool.Key.Kind, formula: InternPool.TermOff, loc: u32) std.mem.Allocator.Error!InternPool.Index {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    self.pool.lockWrite(io);
    // the fact's name IS its identity key's name; loc comes from the caller (declaration site).
    const index = self.pool.mintFact(kind, formula, key.name, loc) catch |e| {
        self.pool.unlockWrite(io);
        return e;
    };
    self.pool.unlockWrite(io);
    try self.map.put(self.pool.arena, key, .{ .proven = index });
    return index;
}

/// A SCHEMA (a fact WITH params) resolves through the fact table like any axiom/theorem, but
/// carries no ground formula — its content is a LOCATOR back to its AST decl. Mint the
/// `.schema` locator (under the nested InternPool write-mutex, order FactKV -> InternPool)
/// and flip in_flight -> proven. The instantiation path reads it back, expects `.schema`, and
/// re-reads params/body/steps from the by-name AST registry. (Its producer is a ProveTask —
/// FetchTask never touches facts.)
pub fn publishSchema(self: *FactKV, io: std.Io, key: Key, s: InternPool.Key.Schema) std.mem.Allocator.Error!InternPool.Index {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    self.pool.lockWrite(io);
    const index = self.pool.mintSchema(s) catch |e| {
        self.pool.unlockWrite(io);
        return e;
    };
    self.pool.unlockWrite(io);
    try self.map.put(self.pool.arena, key, .{ .proven = index });
    return index;
}

/// ALIAS-COLLAPSE (Foundation C): bind `key` to an ALREADY-PROVEN fact `Index` — mint
/// nothing. `theorem foo = bar.baz` / `axiom foo = bar.baz` maps `foo` to the origin fact's
/// Index, so a citation of `foo` resolves to the same proven fact (identity by origin). The
/// origin was kernel-checked by its own ProveTask; the alias re-uses that verified fact
/// (sound in strict mode — the formula IS the origin's). Transitive: aliasing an alias binds
/// to the origin the first alias already collapsed to.
pub fn publishExisting(self: *FactKV, io: std.Io, key: Key, index: InternPool.Index) std.mem.Allocator.Error!void {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    try self.map.put(self.pool.arena, key, .{ .proven = index });
}

test "FactKV demand table: claim -> in_flight -> publish -> proven; the entry protocol" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());
    var kv: FactKV = .init(&pool);

    var threaded: std.Io.Threaded = .init(arena_state.allocator(), .{});
    const io = threaded.io();

    const f = try pool.get(.{ .file = .{ .path = try pool.internString("std/integer.bpa") } });
    const ns = try pool.namespace(.universe, f);
    const comm = try pool.internString("addIsCommutative");
    const k = FactKV.Key{ .namespace = ns, .name = comm };

    const my_task: Engine.TaskIndex = @enumFromInt(7);
    const other_task: Engine.TaskIndex = @enumFromInt(3);

    // ABSENT -> claim it with my task index; I'm told to begin proving.
    try std.testing.expectEqual(FactKV.Outcome.claimed, try kv.claimOrLookup(io, k, my_task));

    // now IN-FLIGHT -> a second (redundant) prover looking it up is told to suspend on the
    // task that claimed it (my_task), NOT to prove.
    try std.testing.expectEqual(
        FactKV.Outcome{ .in_flight = my_task },
        try kv.claimOrLookup(io, k, other_task),
    );

    // PUBLISH on success: in-flight -> proven, minting the fact token (kind + formula).
    // formula = a reified-term `extra` offset (Step 3); any u32 works for this round-trip.
    const formula: InternPool.TermOff = 5;
    const fact = try kv.publish(io, k, .theorem, formula, 0);
    try std.testing.expectEqual(InternPool.Key.Kind.theorem, pool.keyOf(fact).fact.kind);
    try std.testing.expectEqual(formula, pool.keyOf(fact).fact.formula);
    try std.testing.expectEqual(k.name, pool.keyOf(fact).fact.name);

    // now PROVEN -> any lookup returns the fact index, prove-nothing.
    try std.testing.expectEqual(
        FactKV.Outcome{ .proven = fact },
        try kv.claimOrLookup(io, k, other_task),
    );
}
