//! The interned entity pool — a uniform, deduplicated store for the denotations bpa's
//! checker works with (types/sorts/symbols/statements/models/files), modeled on the Zig
//! compiler's `InternPool` (src/InternPool.zig in the zig tree).
//!
//! First slices of the data-model rebuild. Kinds so far: `string` (identifiers/paths,
//! content-deduped), `file` (deduped by resolved path — Context's file identity rests on
//! this), `model` (an interpretation: a parent link + sparse overlay; the UNIVERSE model
//! is seeded at `Index.universe` = 0, its own parent), and `namespace` (a `(model, file)`
//! scope — the spec's
//! `(model?, file, id)` factored as `(namespace, id)`), and `fact` (an axiom or theorem
//! keyed `(namespace, name)`; `kind` is attached, not identity). Later kinds (sort,
//! symbol) are added as `Key`/`Tag` variants on this same machinery.
//!
//! THE THREE-TIER SHAPE (Zig's design, adopted):
//!   * `Index` — a dense `enum(u32)` handle. Low values are RESERVED for well-known
//!     entries (like a builtin `Prop` sort would be); dynamic entries follow.
//!   * `Key` — the ERGONOMIC tagged union you construct with and match on. This is the
//!     public face: `get(key) -> Index`, `keyOf(index) -> Key`.
//!   * `Item {tag, data}` + `extra` — the PACKED storage. `data` is either an inline
//!     payload, another `Index`, or an offset into `extra` (the variable-length spill).
//!     You never touch this directly; `get`/`keyOf` are the only bridge.
//!
//! DEDUP: always-intern. `get` hashes the key, structurally compares against existing
//! entries, and returns the existing `Index` on a match (else appends). Two keys that
//! are structurally equal collapse to one `Index` — which for `file` means one id per
//! physical file, shared across every importer.
//!
//! `extra` ENCODING is reflection-based (`addExtra(anytype)` / `extraData(T)`): a payload
//! struct's fields are serialized field-by-field as `u32` (enum-cast for ids, bit-cast
//! for scalars) and read back the same way — so a new variable-length kind is a payload
//! struct + one `keyOf` case, no hand-written pack/unpack.

const std = @import("std");

const InternPool = @This();

/// A string id IS a pool `Index` (the `.string` kind) — so a string, a file, and every
/// future entity share ONE id space, distinguished only by their item `tag`. Kept as a
/// public alias because the name `StrId` reads clearly across the codebase (a `StrId`
/// value is understood to name a string, even though the type is the general `Index`).
pub const StrId = Index;

/// The packed store: one `Item` per interned entity, indexed by `@intFromEnum(Index)`.
items: std.MultiArrayList(Item) = .empty,
/// Variable-length payload spill. An `Item.data` may be an offset into here; the run of
/// `u32`s starting there decodes (via reflection) into a payload struct.
extra: std.ArrayList(u32) = .empty,
/// Raw byte store for `.string` items. An interned string's bytes live here as a
/// contiguous run (its `String` payload in `extra` records the offset + length).
string_bytes: std.ArrayList(u8) = .empty,
/// Dedup map: structural key hash -> Index. `void` value; the Index is recovered by
/// re-deriving the key from the stored item (adapter context compares against `items`).
map: std.HashMapUnmanaged(Index, void, MapContext, std.hash_map.default_max_load_percentage) = .empty,

/// The WRITE mutex (see [[internpool-concurrency-model]]). `get` READS lock-free and never
/// touches this — reads take NO lock, so the read path needs no `Io`. WRITERS (anything
/// that mints a new `Index`) must hold it around the mint: a higher build layer (e.g. a
/// theorem KV) takes `lockWrite(io)`, then calls `get` (which appends), then
/// `unlockWrite(io)`. Reads stay lock-free; only writers serialize. `std.Io.Mutex` (not
/// an RwLock — readers never take a shared lock) needs an `Io`, which writers get from the
/// `Context` they hold.
///
/// CONCURRENCY PREREQUISITE (NOT yet satisfied): lock-free reads are only ACTUALLY safe
/// once the store is NON-MOVING. `items`/`extra`/`string_bytes` are plain `ArrayList`s
/// that reallocate on grow — a single-threaded placeholder. Until they become segmented
/// (list-of-fixed-blocks) or pre-reserved, a lock-free reader can race a writer's
/// reallocation. This mutex makes the WRITE DISCIPLINE correct; the non-moving store is the
/// separate, still-pending half. Single-threaded today, so neither hazard is live.
write_mutex: std.Io.Mutex = .init,

arena: std.mem.Allocator,

/// A dense handle into the pool. Non-exhaustive: low values are RESERVED for well-known
/// entries, `_` covers dynamically-interned ones.
///
/// `universe` (Index 0) is the UNIVERSE MODEL — the `(∅, …)` abstract/ground reading in
/// the namespace spec. Seeded at `init`, always present. Because it exists, the model
/// slot of a `(model, file, id)` namespace is never truly optional: "no model" IS the
/// universe model. Every model's parent chain bottoms out here.
pub const Index = enum(u32) {
    universe = 0,
    _,
};

/// The packed storage form. `tag` discriminates; `data` is interpreted per the tag's doc
/// (inline value, an `Index`, or an offset into `extra`).
pub const Item = struct {
    tag: Tag,
    data: u32,
};

/// One kind per interned entity family. Each variant documents how to read `Item.data`.
pub const Tag = enum(u8) {
    /// An interned string (identifier/path). `data` is an offset into `extra` decoding to
    /// `String` (byte offset + length into `string_bytes`).
    string,
    /// A source file, identified by its resolved-path string. `data` is an offset into
    /// `extra` decoding to `File` (the path's string `Index`).
    file,
    /// A MODEL — an interpretation. `data` is an offset into `extra` holding
    /// `[parent, overlay_count, src0, tgt0, src1, tgt1, …]`: a single parent model
    /// `Index`, then a count of `(src -> tgt)` overlay mappings, then that many Index
    /// PAIRS. The ancestor chain is the parent WALK: follow `parent` until it points at
    /// itself. Universe (Index 0) is its own parent with an EMPTY overlay (`[0, 0]`) — the
    /// fixpoint that terminates the walk, so no sentinel is needed.
    ///
    /// The overlay slot is present now but always empty (count 0) — the sparse mappings
    /// are DEFERRED; when they land they join identity (models with the same parent but
    /// different overlays won't dedup) without reshaping this layout.
    model,
    /// A NAMESPACE — a file seen through a model, i.e. the `(model, file)` SCOPE that
    /// identifiers resolve within (the spec's `(model?, file, id)` is `(namespace, id)`).
    /// `data` is an offset into `extra` decoding to `Namespace` (a model Index + a file
    /// Index). Every file has its universe-namespace: `(universe, file)`.
    namespace,
    /// A FACT — a declared axiom or theorem. `data` is an offset into `extra` decoding to
    /// `Fact` (its namespace Index, its name string Index, and its `kind`). Keyed by
    /// `(namespace, name)` ONLY: unique per declaration-site (two facts named `foo` in
    /// different namespaces are distinct; a namespace can't have two `foo`s, so `kind` is
    /// NOT an identity axis — it's attached data). This Index IS the fact's identity.
    /// axiom vs theorem is one `kind` field, branched at the prove-or-not boundary (an
    /// axiom is a resolve-and-store leaf; a theorem's proof gets checked). One `fact` kind
    /// for now; split into distinct kinds only if a roadbump demands it.
    fact,
};

/// The ERGONOMIC view — what callers build and match on. One variant per `Tag`.
pub const Key = union(enum) {
    /// A string's bytes. Interned by CONTENT: equal bytes collapse to one `Index`.
    string: []const u8,
    file: File,
    /// A model: a parent link + a sparse overlay of `src -> tgt` mappings. Universe is its
    /// own parent with an empty overlay. Identity is the pair (parent + overlay); the
    /// overlay is empty for now (mappings deferred) but already part of the key.
    model: Model,
    /// A namespace: a file scoped by a model. Two references to the same `(model, file)`
    /// pair collapse to one `Index`.
    namespace: Namespace,
    /// A fact (axiom or theorem), identified by its namespace + name. Two references to
    /// the same `(namespace, name)` collapse to one `Index` (the fact's identity); `kind`
    /// is attached data, not part of the key.
    fact: Fact,

    /// A source file's interned payload: its resolved-path string id. Identity IS the
    /// path — two importers of the same file get the same `Index`.
    pub const File = struct { path: StrId };

    /// A fact's payload: its namespace + name (the identity) plus its `kind` (axiom or
    /// theorem — attached, not identity). namespace/name are pool `Index`es.
    pub const Fact = struct { namespace: Index, name: StrId, kind: Kind };

    /// What a fact IS. Branched only at the prove-or-not boundary: an axiom is a
    /// resolve-and-store leaf; a theorem's proof gets checked.
    pub const Kind = enum(u8) { axiom, theorem };

    /// A model's payload: its parent model `Index` (universe = itself) + its sparse
    /// overlay (`src -> tgt` mappings; empty for now). The ancestor chain is the parent
    /// walk to the universe fixpoint.
    pub const Model = struct { parent: Index, overlay: []const Mapping = &.{} };

    /// One `src -> tgt` overlay entry (both pool `Index`es).
    pub const Mapping = struct { src: Index, tgt: Index };

    /// A namespace's payload: the model it is viewed through + the file it scopes. Both
    /// are pool `Index`es (a `.model` and a `.file` respectively).
    pub const Namespace = struct { model: Index, file: Index };

    /// `.string` storage payload: where the bytes live in `string_bytes`.
    const String = struct { off: u32, len: u32 };
};

// -- the dedup map's hashing/equality, computed over the ergonomic Key ----------------

const MapContext = struct {
    pool: *const InternPool,

    pub fn hash(ctx: MapContext, index: Index) u64 {
        return hashKey(ctx.pool.keyOf(index));
    }
    pub fn eql(ctx: MapContext, a: Index, b: Index) bool {
        return keyEql(ctx.pool.keyOf(a), ctx.pool.keyOf(b));
    }
};

/// Adapter so we can look up / insert by a Key we haven't stored yet (getOrPutAdapted).
const KeyAdapter = struct {
    pool: *const InternPool,

    pub fn hash(_: KeyAdapter, key: Key) u64 {
        return hashKey(key);
    }
    pub fn eql(ctx: KeyAdapter, key: Key, index: Index) bool {
        return keyEql(key, ctx.pool.keyOf(index));
    }
};

fn hashKey(key: Key) u64 {
    var h = std.hash.Wyhash.init(0);
    std.hash.autoHash(&h, std.meta.activeTag(key));
    switch (key) {
        .string => |bytes| h.update(bytes), // identity IS the bytes
        .file => |f| std.hash.autoHash(&h, f.path),
        .model => |m| {
            std.hash.autoHash(&h, m.parent);
            for (m.overlay) |mapping| std.hash.autoHash(&h, mapping);
        },
        .namespace => |ns| std.hash.autoHash(&h, ns),
        // identity is (namespace, name) ONLY — `kind` is attached, not hashed
        .fact => |f| {
            std.hash.autoHash(&h, f.namespace);
            std.hash.autoHash(&h, f.name);
        },
    }
    return h.final();
}

fn modelEql(a: Key.Model, b: Key.Model) bool {
    if (a.parent != b.parent or a.overlay.len != b.overlay.len) return false;
    for (a.overlay, b.overlay) |x, y| if (x.src != y.src or x.tgt != y.tgt) return false;
    return true;
}

fn keyEql(a: Key, b: Key) bool {
    if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
    return switch (a) {
        .string => std.mem.eql(u8, a.string, b.string),
        .file => a.file.path == b.file.path,
        .model => modelEql(a.model, b.model),
        .namespace => std.meta.eql(a.namespace, b.namespace),
        // identity is (namespace, name) ONLY — `kind` ignored
        .fact => a.fact.namespace == b.fact.namespace and a.fact.name == b.fact.name,
    };
}

/// Seed the pool with the reserved entries. Currently: the UNIVERSE MODEL at
/// `Index.universe` (0) — an empty parent stack. Every other model's chain bottoms out
/// here, and "no model" resolves to it.
pub fn init(arena: std.mem.Allocator) std.mem.Allocator.Error!InternPool {
    var self: InternPool = .{ .arena = arena };
    // Universe is its own parent — a self-reference at Index 0. The `.universe` constant
    // IS 0, so we can name it as the parent before the entry physically exists.
    const universe = try self.get(.{ .model = .{ .parent = .universe } });
    std.debug.assert(universe == .universe); // the universe model MUST be Index 0
    return self;
}

/// Intern a key: return the existing `Index` if a structurally-equal entry exists, else
/// append a new packed `Item` (+ `extra`) and record it. The always-intern entry point.
pub fn get(self: *InternPool, key: Key) std.mem.Allocator.Error!Index {
    const gop = try self.map.getOrPutContextAdapted(self.arena, key, KeyAdapter{ .pool = self }, MapContext{ .pool = self });
    if (gop.found_existing) return gop.key_ptr.*;

    const index: Index = @enumFromInt(self.items.len);
    switch (key) {
        .string => |bytes| {
            const bytes_off: u32 = @intCast(self.string_bytes.items.len);
            try self.string_bytes.appendSlice(self.arena, bytes);
            const off = try self.addExtra(Key.String{ .off = bytes_off, .len = @intCast(bytes.len) });
            try self.items.append(self.arena, .{ .tag = .string, .data = off });
        },
        .file => |f| {
            const off = try self.addExtra(Key.File{ .path = f.path });
            try self.items.append(self.arena, .{ .tag = .file, .data = off });
        },
        .model => |m| {
            const off = try self.addModel(m); // [parent, overlay_count, ...src/tgt pairs]
            try self.items.append(self.arena, .{ .tag = .model, .data = off });
        },
        .namespace => |ns| {
            const off = try self.addExtra(ns);
            try self.items.append(self.arena, .{ .tag = .namespace, .data = off });
        },
        .fact => |f| {
            // dedup is on (namespace, name); the FIRST-interned `kind` is what sticks
            // (re-interning the same name with a different kind returns the existing entry
            // unchanged — a name is declared once, so this is fine).
            const off = try self.addExtra(f);
            try self.items.append(self.arena, .{ .tag = .fact, .data = off });
        },
    }
    gop.key_ptr.* = index;
    return index;
}

/// Reconstruct the ergonomic `Key` from an `Index` — the inverse of `get`'s packing.
pub fn keyOf(self: *const InternPool, index: Index) Key {
    const item = self.items.get(@intFromEnum(index));
    return switch (item.tag) {
        .string => {
            const s = self.extraData(Key.String, item.data);
            return .{ .string = self.string_bytes.items[s.off .. s.off + s.len] };
        },
        .file => .{ .file = self.extraData(Key.File, item.data) },
        .model => .{ .model = self.modelData(item.data) },
        .namespace => .{ .namespace = self.extraData(Key.Namespace, item.data) },
        .fact => .{ .fact = self.extraData(Key.Fact, item.data) },
    };
}

/// Number of interned entries.
pub fn count(self: *const InternPool) usize {
    return self.items.len;
}

// -- string convenience (the StrId façade rests on these) -----------------------------

/// Intern bytes as a string, returning its `StrId` (== a pool `Index`). Content-deduped.
pub fn internString(self: *InternPool, bytes: []const u8) std.mem.Allocator.Error!StrId {
    return self.get(.{ .string = bytes });
}

/// The bytes of an interned string. Asserts `id` names a `.string` item.
pub fn stringBytes(self: *const InternPool, id: StrId) []const u8 {
    std.debug.assert(self.items.get(@intFromEnum(id)).tag == .string);
    return self.keyOf(id).string;
}

// -- namespace convenience ------------------------------------------------------------

/// Intern the namespace `(model, file)` — a file viewed through a model. Deduped: the
/// same pair always yields the same `Index`. The universe-namespace of `file` is
/// `namespace(.universe, file)`.
pub fn namespace(self: *InternPool, model: Index, file: Index) std.mem.Allocator.Error!Index {
    return self.get(.{ .namespace = .{ .model = model, .file = file } });
}

/// Intern the fact `name` declared in `ns` with `kind` (axiom/theorem) — its identity.
/// Deduped per (namespace, name); the returned `Index` IS the fact identifier. If the
/// name is already interned, the existing entry (and its first-interned kind) is returned.
pub fn fact(self: *InternPool, ns: Index, name: StrId, kind: Key.Kind) std.mem.Allocator.Error!Index {
    return self.get(.{ .fact = .{ .namespace = ns, .name = name, .kind = kind } });
}

// -- model encoding (`[parent, overlay_count, src0, tgt0, …]`) -------------------------
// A model's parent + sparse overlay; variable-length, so the fixed-struct reflection
// encoder can't express it. The overlay is empty for now (mappings deferred).

/// Append `[parent, overlay_count, src0, tgt0, …]` to `extra`; return the start offset.
fn addModel(self: *InternPool, m: Key.Model) std.mem.Allocator.Error!u32 {
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, 2 + m.overlay.len * 2);
    self.extra.appendAssumeCapacity(@intFromEnum(m.parent));
    self.extra.appendAssumeCapacity(@intCast(m.overlay.len));
    for (m.overlay) |mapping| {
        self.extra.appendAssumeCapacity(@intFromEnum(mapping.src));
        self.extra.appendAssumeCapacity(@intFromEnum(mapping.tgt));
    }
    return off;
}

/// Read the model payload at `off` back — the inverse of `addModel`. The overlay slice
/// reinterprets the `u32` pair-run in `extra` as `Mapping` (same layout: two `Index`es).
fn modelData(self: *const InternPool, off: u32) Key.Model {
    const parent: Index = @enumFromInt(self.extra.items[off]);
    const n = self.extra.items[off + 1];
    const raw = self.extra.items[off + 2 .. off + 2 + n * 2];
    return .{ .parent = parent, .overlay = @ptrCast(raw) };
}

// -- reflection-based `extra` encoding ------------------------------------------------
// A payload struct is serialized field-by-field as `u32`: enum fields by their integer
// tag, integer fields by bit-cast. Reading reverses it. Field ORDER is the contract.

/// Append `payload`'s fields to `extra` as a run of `u32`; return the start offset.
fn addExtra(self: *InternPool, payload: anytype) std.mem.Allocator.Error!u32 {
    const T = @TypeOf(payload);
    const fields = @typeInfo(T).@"struct".fields;
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, fields.len);
    inline for (fields) |field| {
        const v = @field(payload, field.name);
        self.extra.appendAssumeCapacity(encodeField(v));
    }
    return off;
}

/// Decode a `T` payload from `extra` starting at `off` — the inverse of `addExtra`.
fn extraData(self: *const InternPool, comptime T: type, off: u32) T {
    const fields = @typeInfo(T).@"struct".fields;
    var result: T = undefined;
    inline for (fields, 0..) |field, i| {
        @field(result, field.name) = decodeField(field.type, self.extra.items[off + i]);
    }
    return result;
}

fn encodeField(v: anytype) u32 {
    return switch (@typeInfo(@TypeOf(v))) {
        .@"enum" => @intFromEnum(v),
        .int => @bitCast(v),
        else => @compileError("InternPool extra: unsupported field type " ++ @typeName(@TypeOf(v))),
    };
}

fn decodeField(comptime T: type, raw: u32) T {
    return switch (@typeInfo(T)) {
        .@"enum" => @enumFromInt(raw),
        .int => @bitCast(raw),
        else => @compileError("InternPool extra: unsupported field type " ++ @typeName(T)),
    };
}

test "strings intern by content and round-trip their bytes" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const add = try pool.internString("add");
    const zero = try pool.internString("zero");
    const add2 = try pool.internString("add");

    try std.testing.expectEqual(add, add2); // DEDUP: equal bytes collapse to one Index
    try std.testing.expect(add != zero);
    try std.testing.expectEqualStrings("add", pool.stringBytes(add));
    try std.testing.expectEqualStrings("zero", pool.stringBytes(zero));
    // universe model (Index 0) + two strings
    try std.testing.expectEqual(@as(usize, 3), pool.count());
}

test "universe model is seeded at Index 0 as its own parent" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    // seeded, at Index 0; universe is its own parent (the walk fixpoint), empty overlay
    try std.testing.expectEqual(@as(usize, 1), pool.count());
    try std.testing.expectEqual(InternPool.Index.universe, pool.keyOf(.universe).model.parent);
    try std.testing.expectEqual(@as(usize, 0), pool.keyOf(.universe).model.overlay.len);
    // re-asking for the universe payload dedups back to Index 0
    try std.testing.expectEqual(InternPool.Index.universe, try pool.get(.{ .model = .{ .parent = .universe } }));

    // a model whose parent is universe: distinct from universe, round-trips its parent
    const child = try pool.get(.{ .model = .{ .parent = .universe } });
    // NOTE: with an empty overlay, this child has the SAME payload as universe {parent:0}
    // and therefore DEDUPS to universe. Distinct child models require a distinct parent or
    // a non-empty overlay (deferred). Assert the dedup is exactly that:
    try std.testing.expectEqual(InternPool.Index.universe, child);
}

test "namespace = (model, file), deduped per pair" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const f_int = try pool.get(.{ .file = .{ .path = try pool.internString("std/integer.bpa") } });
    const f_nat = try pool.get(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });

    // universe-namespace of each file (distinct non-universe models need overlays, deferred)
    const u_int = try pool.namespace(.universe, f_int);
    const u_nat = try pool.namespace(.universe, f_nat);

    try std.testing.expect(u_int != u_nat); // different file -> different namespace
    // same (model, file) pair -> same Index (dedup)
    try std.testing.expectEqual(u_int, try pool.namespace(.universe, f_int));

    // round-trip the pair
    const ns = pool.keyOf(u_int).namespace;
    try std.testing.expectEqual(InternPool.Index.universe, ns.model);
    try std.testing.expectEqual(f_int, ns.file);
}

test "fact = (namespace, name), deduped per pair; kind is attached not identity" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const f_int = try pool.get(.{ .file = .{ .path = try pool.internString("std/integer.bpa") } });
    const f_nat = try pool.get(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });
    const ns_int = try pool.namespace(.universe, f_int);
    const ns_nat = try pool.namespace(.universe, f_nat);
    const comm = try pool.internString("addIsCommutative");
    const assoc = try pool.internString("addIsAssociative");

    const t = try pool.fact(ns_int, comm, .theorem);
    // same (namespace, name) -> same Index (the fact's identity)
    try std.testing.expectEqual(t, try pool.fact(ns_int, comm, .theorem));
    // same name in a DIFFERENT namespace -> distinct fact
    try std.testing.expect(t != try pool.fact(ns_nat, comm, .theorem));
    // different name in the same namespace -> distinct fact
    try std.testing.expect(t != try pool.fact(ns_int, assoc, .theorem));

    // KIND is NOT identity: re-interning the same (ns, name) with a different kind
    // returns the SAME Index, and the FIRST-interned kind sticks.
    try std.testing.expectEqual(t, try pool.fact(ns_int, comm, .axiom));
    try std.testing.expectEqual(InternPool.Key.Kind.theorem, pool.keyOf(t).fact.kind);

    // round-trip identity
    const key = pool.keyOf(t).fact;
    try std.testing.expectEqual(ns_int, key.namespace);
    try std.testing.expectEqual(comm, key.name);
}

test "file interns by path: same path -> same Index, distinct paths -> distinct" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const p_int = try pool.internString("std/integer.bpa");
    const p_nat = try pool.internString("std/peano.bpa");

    const a = try pool.get(.{ .file = .{ .path = p_int } });
    const b = try pool.get(.{ .file = .{ .path = p_nat } });
    const a2 = try pool.get(.{ .file = .{ .path = p_int } }); // second importer, same file

    try std.testing.expectEqual(a, a2); // DEDUP: same path collapses to one Index
    try std.testing.expect(a != b); // distinct paths are distinct entities

    // round-trip: the Index reconstructs the original key (path StrId)
    try std.testing.expectEqual(p_int, pool.keyOf(a).file.path);
    try std.testing.expectEqual(p_nat, pool.keyOf(b).file.path);
    // a file entity's Index is distinct from its path's string Index (one id space)
    try std.testing.expect(@intFromEnum(a) != @intFromEnum(p_int));
}
