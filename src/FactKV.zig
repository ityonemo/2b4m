//! FactKV — the `(namespace, name) -> fact Index` resolution/coordination table over the
//! InternPool. It is the demand layer above the pool: a citation resolves a fact by its
//! `(namespace, name)`, and a scan/prove creates one if absent. Holds BOTH axioms and
//! theorems (one mechanism; the axiom/theorem distinction is the fact's `kind`, branched
//! only at the prove-or-not boundary — an axiom is a resolve-and-store leaf).
//!
//! CONCURRENCY (see the internpool-concurrency-model memory; single-threaded today, so
//! locks are uncontended):
//!   * `read`  takes the RwLock SHARED — many readers concurrent (lookups dominate).
//!   * `write` takes the RwLock EXCLUSIVE and HOLDS it across check -> mint -> publish, so
//!     two threads can't both miss-then-build the same key (the dedup race). Inside that
//!     hold it takes the InternPool WRITE-MUTEX to mint (nested; lock order FactKV ->
//!     InternPool, never reversed).
//!
//! The pool ALREADY dedups facts by `(namespace, name)`, so FactKV's own map is partly
//! redundant with the pool's — but FactKV is where the LOCK discipline lives (the pool's
//! `get` is lock-free and mustn't coordinate builds), and later it carries the demand
//! state (proven? in-flight?) the pool doesn't. For now it's the locked create-if-absent.

const std = @import("std");
const InternPool = @import("InternPool.zig");

const FactKV = @This();

/// Key: a fact's identity — its namespace + name (NOT its kind; kind isn't identity).
pub const Key = struct { namespace: InternPool.Index, name: InternPool.StrId };

pool: *InternPool,
map: std.AutoHashMapUnmanaged(Key, InternPool.Index) = .empty,
lock: std.Io.RwLock = .init,

pub fn init(pool: *InternPool) FactKV {
    return .{ .pool = pool };
}

/// Resolve a fact by `(namespace, name)` — SHARED (read) lock. Returns its `Index`, or
/// null if not yet created. Many readers run concurrently.
pub fn read(self: *FactKV, io: std.Io, key: Key) ?InternPool.Index {
    self.lock.lockSharedUncancelable(io);
    defer self.lock.unlockShared(io);
    return self.map.get(key);
}

/// Create-if-absent: return the fact's `Index`, minting it (with `kind`) if this is the
/// first request. EXCLUSIVE (write) lock, HELD across check -> mint -> publish so a
/// concurrent writer can't double-create. The mint nests the InternPool write-mutex.
pub fn write(self: *FactKV, io: std.Io, key: Key, kind: InternPool.Key.Kind) std.mem.Allocator.Error!InternPool.Index {
    self.lock.lockUncancelable(io);
    defer self.lock.unlock(io);
    // re-check under the exclusive lock (a racer may have published between our read and
    // acquiring the lock)
    if (self.map.get(key)) |existing| return existing;
    // still absent — mint a fresh truth-token under the pool write-mutex (nested), then
    // publish the (ns,name)->Index mapping. FactKV's map is the identity index; the pool
    // just hands out a bare token, so the map's dedup is what guarantees single-mint.
    self.pool.lockWrite(io);
    const index = self.pool.mintFact(kind) catch |e| {
        self.pool.unlockWrite(io);
        return e;
    };
    self.pool.unlockWrite(io);
    try self.map.put(self.pool.arena, key, index);
    return index;
}

test "FactKV create-if-absent dedups; read finds it; distinct keys distinct" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());
    var kv: FactKV = .init(&pool);

    var threaded: std.Io.Threaded = .init(arena_state.allocator(), .{});
    const io = threaded.io();

    const f = try pool.get(.{ .file = .{ .path = try pool.internString("std/integer.bpa") } });
    const ns = try pool.namespace(.universe, f);
    const comm = try pool.internString("addIsCommutative");
    const assoc = try pool.internString("addIsAssociative");

    const k = FactKV.Key{ .namespace = ns, .name = comm };
    try std.testing.expectEqual(@as(?InternPool.Index, null), kv.read(io, k)); // absent first
    const a = try kv.write(io, k, .theorem);
    try std.testing.expectEqual(a, kv.read(io, k).?); // now readable
    try std.testing.expectEqual(a, try kv.write(io, k, .theorem)); // create-if-absent dedups
    // distinct name -> distinct fact
    const b = try kv.write(io, .{ .namespace = ns, .name = assoc }, .theorem);
    try std.testing.expect(a != b);
}
