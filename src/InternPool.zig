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

/// A DURABLE TERM's location: an offset into `extra` where a term is serialized as a
/// self-contained u32 run (see `appendExtraRun` + term.zig `reify`/`copyIn`). NOT an
/// `Index` — a term is not an interned entity (bpa is explicit; no term dedup). Named
/// distinctly so a term-offset is never confused with an entity `Index` at a field.
pub const TermOff = u32;

/// The ABSENT marker for an optional `TermOff` (e.g. a func's missing guard). Offset 0 is a
/// valid term location, so the top of the range is the sentinel — mirrors `Index.none`.
pub const no_term: TermOff = 0xFFFF_FFFF;

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

    /// The ABSENT marker for optional `Index` slots packed into `extra` (e.g. a func's
    /// missing guard). Index 0 is a real entry (the universe model), so the top of the
    /// range is the sentinel. A `?Index` is encoded as this on `null`, decoded back to
    /// `null` on read. NOT a valid pool entry — never appears as a `get`/`keyOf` result.
    pub const none: Index = @enumFromInt(0xFFFF_FFFF);
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
    /// A FACT — a proven axiom or theorem. A TRUTH TOKEN: `data` is an offset into `extra`
    /// holding `[kind, formula]` (the axiom/theorem `Kind` + the formula term `Index` it
    /// asserts), NO identity. INTERNED ⇒ TRUE: a fact exists in the pool only when proven
    /// (interning is the commit point of proving); there is no proven-bit, presence IS
    /// truth. Its `(namespace,name)` identity lives in FactKV (the sole forward index) —
    /// nothing does a reverse fact→(ns,name) lookup, so the pool stores none of it. Facts
    /// BYPASS dedup: `mintFact` always appends a fresh token; FactKV's map + write-lock
    /// guarantee single-mint per `(ns,name)`.
    fact,

    // NOTE: terms are NOT interned Items (bpa is an explicit prover — no term dedup, so
    // α-equality-as-Index-equality buys nothing). A DURABLE term lives as a self-contained
    // u32 run in `extra` (see `appendExtraRun`/`extraRun` + term.zig `reify`/`copyIn`); a
    // WORKING term is a scratchpad `term.Pool` node. See memory `terms-not-interned`.

    // -- SUPPORTING (structural, deduped like terms) --------------------------------------

    /// A SIGNATURE — a func/pred's arrow type. `data` is an offset into `extra` holding
    /// `[result, result_refined, argc, a0, …]`: the result sort `Index`, the result's
    /// refinement sort `Index` (or `none`), an arg count, then that many argument sort
    /// `Index`es. Variable-length (hand-encoded). Deduped: two symbols with the same
    /// arrow share one sig Index (harmless — a sig has no identity of its own).
    sig,

    // -- IDENTIFIERS (MINTED, never deduped — identity is IdentKV's (ns,name); the pool
    //    stores only the identifier's CONTENT). ------------------------------------------

    /// A SORT. Its NAME lives in IdentKV; the pool stores its refinement. `data` is
    /// `none` for a ROOT sort (no refinement), else an offset into `extra` holding
    /// `[parent, qualc, q0, …]`: the parent sort `Index` + a count + that many qualifier
    /// (predicate) `Index`es. Minted (two root sorts have identical content but distinct
    /// Indexes).
    sort,
    /// A CONSTANT. `data` IS its sort `Index` (single-ref, no `extra`). Minted; its name
    /// lives in IdentKV.
    constant,
    /// A FUNCTION. `data` is an offset into `extra` holding `[sig, guard, paramc, pn0, …]`:
    /// its signature `Index`, an optional guard term `Index` (`none` if unguarded), a
    /// param-name count, then that many param-name string `Index`es. Minted; name is
    /// IdentKV's.
    func,
    /// A PREDICATE. Identical `[sig, guard, paramc, pn0, …]` layout to `func`, a distinct
    /// tag. Minted; name is IdentKV's.
    pred,
    /// A DEFINE (transparent macro). `data` is an offset into `extra` holding
    /// `[body, paramc, pn0, …]`: the template body term `Index` (an unelaborated template,
    /// expanded during proving — the reason a define's FetchTask doesn't suspend on its
    /// body's contents) + a param-name count + that many param-name string `Index`es.
    /// Minted; name is IdentKV's.
    define,
    /// An IMPORT. `data` IS the `.namespace` `Index` it binds to (single-ref, no `extra`).
    /// Minted (a file can bind one namespace under several local names — distinct imports).
    /// Its local name lives in IdentKV.
    import,
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
    /// A fact (proven axiom or theorem) — a truth token carrying its `Kind` AND the
    /// formula it asserts. No identity here (that's FactKV's); minted by `mintFact`,
    /// never deduped.
    fact: Fact,
    /// A signature (func/pred arrow type). Deduped on `(result, result_refined, args…)`.
    sig: Sig,
    /// A sort identifier's content: its refinement (null = a root sort). Minted; identity
    /// (its name/namespace) is IdentKV's, not here.
    sort: Sort,
    /// A constant identifier's content: its sort `Index`. Minted; name is IdentKV's.
    constant: Index,
    /// A function identifier's content: signature + optional guard + param names. Minted.
    func: Callable,
    /// A predicate identifier's content — same `Callable` payload, a distinct kind. Minted.
    pred: Callable,
    /// A define identifier's content: its template body term + param names. Minted.
    define: Define,
    /// An import identifier's content: the `.namespace` `Index` it binds to. Minted.
    import: Index,

    /// A source file's interned payload: its resolved-path string id. Identity IS the
    /// path — two importers of the same file get the same `Index`.
    pub const File = struct { path: StrId };

    /// What a fact IS. Branched only at the prove-or-not boundary: an axiom is a
    /// resolve-and-store leaf; a theorem's proof gets checked.
    pub const Kind = enum(u8) { axiom, theorem };

    /// A fact's payload: its kind + the `extra`-offset of the formula term it asserts.
    /// Spilled into `extra` as `[kind, formula_off]`.
    pub const Fact = struct { kind: Kind, formula: TermOff };

    /// A model's payload: its parent model `Index` (universe = itself) + its sparse
    /// overlay (`src -> tgt` mappings; empty for now). The ancestor chain is the parent
    /// walk to the universe fixpoint.
    pub const Model = struct { parent: Index, overlay: []const Mapping = &.{} };

    /// One `src -> tgt` overlay entry (both pool `Index`es).
    pub const Mapping = struct { src: Index, tgt: Index };

    /// A namespace's payload: the model it is viewed through + the file it scopes. Both
    /// are pool `Index`es (a `.model` and a `.file` respectively).
    pub const Namespace = struct { model: Index, file: Index };

    /// A signature payload: the result sort `Index`, its refinement sort `Index` (or
    /// `Index.none`), and the argument sort `Index`es. Variable-length.
    pub const Sig = struct { result: Index, result_refined: Index, args: []const Index };

    /// A sort's content. `refinement == null` is a ROOT sort; otherwise it is a subsort
    /// of `parent` cut by a list of qualifier (predicate) `Index`es.
    pub const Sort = struct {
        refinement: ?Refinement = null,
        pub const Refinement = struct { parent: Index, qualifiers: []const Index };
    };

    /// A func/pred's content: its signature `Index`, the `extra`-offset of an optional
    /// guard term (`no_term` = unguarded), and its param-name string `Index`es. Shared by
    /// `func` and `pred` (identical layout; the tag says which). Variable-length.
    pub const Callable = struct { sig: Index, guard: TermOff, param_names: []const Index };

    /// A define's content: the `extra`-offset of its template body term + its param-name
    /// string `Index`es. Variable-length.
    pub const Define = struct { body: TermOff, param_names: []const Index };

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
        .sig => |s| {
            std.hash.autoHash(&h, s.result);
            std.hash.autoHash(&h, s.result_refined);
            for (s.args) |arg| std.hash.autoHash(&h, arg);
        },
        // facts and identifiers are never deduped — minted via mintFact/mint*, not get
        .fact, .sort, .constant, .func, .pred, .define, .import => unreachable,
    }
    return h.final();
}

fn sigEql(a: Key.Sig, b: Key.Sig) bool {
    if (a.result != b.result or a.result_refined != b.result_refined or a.args.len != b.args.len) return false;
    for (a.args, b.args) |x, y| if (x != y) return false;
    return true;
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
        .sig => sigEql(a.sig, b.sig),
        .fact, .sort, .constant, .func, .pred, .define, .import => unreachable, // minted
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
        .sig => |s| {
            const off = try self.addSig(s); // [result, result_refined, argc, a0, …]
            try self.items.append(self.arena, .{ .tag = .sig, .data = off });
        },
        // facts/identifiers are minted via mintFact/mint*, never `get` (no dedup)
        .fact, .sort, .constant, .func, .pred, .define, .import => unreachable,
    }
    gop.key_ptr.* = index;
    return index;
}

/// Mint a fresh fact truth-token carrying `(kind, formula)` in `extra` — ALWAYS appends
/// (no dedup). Bypasses `get`/`map` because a fact has no structural identity in the pool
/// (FactKV owns `(ns,name)→Index` and guarantees single-mint). Interning a fact IS
/// committing "this fact is proven true". Takes the write-mutex like any pool write.
pub fn mintFact(self: *InternPool, kind: Key.Kind, formula: TermOff) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addExtra(Key.Fact{ .kind = kind, .formula = formula });
    try self.items.append(self.arena, .{ .tag = .fact, .data = off });
    return index;
}


/// Mint a fresh SORT identifier, ALWAYS appending (no dedup; IdentKV owns identity). A
/// root sort stores `data = none`; a refined sort spills `[parent, qualc, q0, …]` into
/// `extra`. Two root sorts have identical content but distinct Indexes (name-identity is
/// IdentKV's). Callers hold the write-mutex, as with any pool write.
pub fn mintSort(self: *InternPool, s: Key.Sort) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    const data: u32 = if (s.refinement) |r| try self.addRefinement(r) else @intFromEnum(Index.none);
    try self.items.append(self.arena, .{ .tag = .sort, .data = data });
    return index;
}

/// Append `[parent, qualc, q0, …]` to `extra`; return the start offset.
fn addRefinement(self: *InternPool, r: Key.Sort.Refinement) std.mem.Allocator.Error!u32 {
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, 2 + r.qualifiers.len);
    self.extra.appendAssumeCapacity(@intFromEnum(r.parent));
    self.extra.appendAssumeCapacity(@intCast(r.qualifiers.len));
    for (r.qualifiers) |q| self.extra.appendAssumeCapacity(@intFromEnum(q));
    return off;
}

/// Read a refinement payload at `off` back — the inverse of `addRefinement`.
fn refinementData(self: *const InternPool, off: u32) Key.Sort.Refinement {
    const parent: Index = @enumFromInt(self.extra.items[off]);
    const n = self.extra.items[off + 1];
    const raw = self.extra.items[off + 2 .. off + 2 + n];
    return .{ .parent = parent, .qualifiers = @ptrCast(raw) };
}

/// Mint a fresh CONSTANT identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// `data` IS its sort `Index`. Two constants of the same sort get distinct Indexes.
pub fn mintConstant(self: *InternPool, sort: Index) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    try self.items.append(self.arena, .{ .tag = .constant, .data = @intFromEnum(sort) });
    return index;
}

/// Append `[sig, guard, paramc, pn0, …]` to `extra`; return the start offset.
fn addCallable(self: *InternPool, c: Key.Callable) std.mem.Allocator.Error!u32 {
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, 3 + c.param_names.len);
    self.extra.appendAssumeCapacity(@intFromEnum(c.sig));
    self.extra.appendAssumeCapacity(c.guard); // TermOff (u32), not an Index
    self.extra.appendAssumeCapacity(@intCast(c.param_names.len));
    for (c.param_names) |n| self.extra.appendAssumeCapacity(@intFromEnum(n));
    return off;
}

/// Read a callable payload at `off` back — the inverse of `addCallable`.
fn callableData(self: *const InternPool, off: u32) Key.Callable {
    const sig: Index = @enumFromInt(self.extra.items[off]);
    const guard: TermOff = self.extra.items[off + 1]; // TermOff (u32), not an Index
    const n = self.extra.items[off + 2];
    const raw = self.extra.items[off + 3 .. off + 3 + n];
    return .{ .sig = sig, .guard = guard, .param_names = @ptrCast(raw) };
}

/// Mint a fresh FUNCTION identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// Spills `[sig, guard, paramc, pn0, …]` into `extra`.
pub fn mintFunc(self: *InternPool, c: Key.Callable) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addCallable(c);
    try self.items.append(self.arena, .{ .tag = .func, .data = off });
    return index;
}

/// Mint a fresh PREDICATE identifier — same `Callable` payload as `mintFunc`, a distinct
/// tag. ALWAYS appends (no dedup; IdentKV owns identity).
pub fn mintPred(self: *InternPool, c: Key.Callable) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addCallable(c);
    try self.items.append(self.arena, .{ .tag = .pred, .data = off });
    return index;
}

/// Append `[body, paramc, pn0, …]` to `extra`; return the start offset.
fn addDefine(self: *InternPool, d: Key.Define) std.mem.Allocator.Error!u32 {
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, 2 + d.param_names.len);
    self.extra.appendAssumeCapacity(d.body); // TermOff (u32), not an Index
    self.extra.appendAssumeCapacity(@intCast(d.param_names.len));
    for (d.param_names) |n| self.extra.appendAssumeCapacity(@intFromEnum(n));
    return off;
}

/// Read a define payload at `off` back — the inverse of `addDefine`.
fn defineData(self: *const InternPool, off: u32) Key.Define {
    const body: TermOff = self.extra.items[off]; // TermOff (u32), not an Index
    const n = self.extra.items[off + 1];
    const raw = self.extra.items[off + 2 .. off + 2 + n];
    return .{ .body = body, .param_names = @ptrCast(raw) };
}

/// Mint a fresh DEFINE identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// Spills `[body, paramc, pn0, …]` into `extra`.
pub fn mintDefine(self: *InternPool, d: Key.Define) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addDefine(d);
    try self.items.append(self.arena, .{ .tag = .define, .data = off });
    return index;
}

/// Mint a fresh IMPORT identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// `data` IS the `.namespace` `Index` it binds to.
pub fn mintImport(self: *InternPool, ns: Index) std.mem.Allocator.Error!Index {
    const index: Index = @enumFromInt(self.items.len);
    try self.items.append(self.arena, .{ .tag = .import, .data = @intFromEnum(ns) });
    return index;
}

/// Take the WRITE mutex around a mint (see [[internpool-concurrency-model]]). A writer
/// wraps its `get`-that-appends in `lockWrite`/`unlockWrite`; `get` itself never touches
/// the mutex, so READS stay lock-free. Uncontended today (single-threaded). Uncancelable
/// so the lock discipline can't be interrupted mid-mint.
pub fn lockWrite(self: *InternPool, io: std.Io) void {
    self.write_mutex.lockUncancelable(io);
}
pub fn unlockWrite(self: *InternPool, io: std.Io) void {
    self.write_mutex.unlock(io);
}

// -- raw `extra` u32-run API (term serialization rests on this) ------------------------
// Terms are NOT interned Items (bpa is an explicit prover — no term dedup); a DURABLE term
// is a self-contained u32 run in `extra`, written/read by term.zig's `reify`/`copyIn`. The
// pool stays term-AGNOSTIC: it just stores and hands back the run. (term.zig imports
// InternPool, not the reverse, so the term-shaped encode/decode lives there.)

/// Append a run of `u32`s to `extra`; return its start offset. A WRITE — the caller must
/// hold the write-mutex (`lockWrite`), same discipline as any mint. `reify` calls this once
/// per term (the whole serialized run in one append).
pub fn appendExtraRun(self: *InternPool, run: []const u32) std.mem.Allocator.Error!u32 {
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.appendSlice(self.arena, run);
    return off;
}

/// Read `len` `u32`s from `extra` starting at `off` — a lock-free read (the run is
/// immutable once appended). `copyIn` walks the returned slice to rebuild a scratchpad term.
pub fn extraRun(self: *const InternPool, off: u32, len: u32) []const u32 {
    return self.extra.items[off .. off + len];
}

/// The first `u32` of a serialized term run is its payload WORD-COUNT (number of u32s after
/// the header). A reader that only has the offset uses this to slice the run:
/// `extraRun(off + 1, extraRunLen(off))`. `copyIn` then walks the payload node-by-node (each
/// node self-describes its width via its tag), post-order, until consumed — the last node is
/// the root.
pub fn extraRunLen(self: *const InternPool, off: u32) u32 {
    return self.extra.items[off];
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
        .fact => .{ .fact = self.extraData(Key.Fact, item.data) }, // [kind, formula]
        .sig => .{ .sig = self.sigData(item.data) },
        .sort => {
            if (item.data == @intFromEnum(Index.none)) return .{ .sort = .{ .refinement = null } };
            return .{ .sort = .{ .refinement = self.refinementData(item.data) } };
        },
        .constant => .{ .constant = @enumFromInt(item.data) }, // sort Index inline
        .func => .{ .func = self.callableData(item.data) },
        .pred => .{ .pred = self.callableData(item.data) },
        .define => .{ .define = self.defineData(item.data) },
        .import => .{ .import = @enumFromInt(item.data) }, // namespace Index inline
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

// -- signature encoding (`[result, result_refined, argc, a0, …]`) ----------------------

/// Append `[result, result_refined, argc, a0, …]` to `extra`; return the start offset.
fn addSig(self: *InternPool, s: Key.Sig) std.mem.Allocator.Error!u32 {
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, 3 + s.args.len);
    self.extra.appendAssumeCapacity(@intFromEnum(s.result));
    self.extra.appendAssumeCapacity(@intFromEnum(s.result_refined));
    self.extra.appendAssumeCapacity(@intCast(s.args.len));
    for (s.args) |arg| self.extra.appendAssumeCapacity(@intFromEnum(arg));
    return off;
}

/// Read a signature payload at `off` back — the inverse of `addSig`.
fn sigData(self: *const InternPool, off: u32) Key.Sig {
    const result: Index = @enumFromInt(self.extra.items[off]);
    const result_refined: Index = @enumFromInt(self.extra.items[off + 1]);
    const n = self.extra.items[off + 2];
    const raw = self.extra.items[off + 3 .. off + 3 + n];
    return .{ .result = result, .result_refined = result_refined, .args = @ptrCast(raw) };
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

test "sig: [result, result_refined, argc, args…] interns/round-trips; dedups structurally" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nat = try pool.internString("Nat"); // stand-in sort Indexes
    const int = try pool.internString("Int");
    const bool_ = try pool.internString("Bool");

    // (Nat, Int) -> Bool, with no result refinement (none)
    const s1 = try pool.get(.{ .sig = .{ .result = bool_, .result_refined = .none, .args = &.{ nat, int } } });
    const s1_again = try pool.get(.{ .sig = .{ .result = bool_, .result_refined = .none, .args = &.{ nat, int } } });
    const s2 = try pool.get(.{ .sig = .{ .result = bool_, .result_refined = .none, .args = &.{ int, nat } } }); // arg order
    const s3 = try pool.get(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{ nat, int } } }); // result
    const s4 = try pool.get(.{ .sig = .{ .result = bool_, .result_refined = nat, .args = &.{ nat, int } } }); // refined
    const s_nullary = try pool.get(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{} } });

    try std.testing.expectEqual(s1, s1_again); // structural dedup
    try std.testing.expect(s1 != s2);
    try std.testing.expect(s1 != s3);
    try std.testing.expect(s1 != s4);

    const k = pool.keyOf(s1).sig;
    try std.testing.expectEqual(bool_, k.result);
    try std.testing.expectEqual(InternPool.Index.none, k.result_refined);
    try std.testing.expectEqual(@as(usize, 2), k.args.len);
    try std.testing.expectEqual(nat, k.args[0]);
    try std.testing.expectEqual(int, k.args[1]);
    try std.testing.expectEqual(@as(usize, 0), pool.keyOf(s_nullary).sig.args.len);
}

test "sort: root (no refinement) + refined [parent, quals…] mint fresh, round-trip, never dedup" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    // two ROOT sorts: identical content (no refinement) but MINTED, so DISTINCT Indexes
    // (identity is IdentKV's (ns,name), not pool structure).
    const nat = try pool.mintSort(.{ .refinement = null });
    const int = try pool.mintSort(.{ .refinement = null });
    try std.testing.expect(nat != int);
    try std.testing.expect(pool.keyOf(nat).sort.refinement == null);

    // a REFINED sort: parent + a qualifier list (stand-in pred Indexes)
    const even = try pool.internString("isEven"); // stand-in qualifier
    const pos = try pool.internString("isPos");
    const refined = try pool.mintSort(.{ .refinement = .{ .parent = nat, .qualifiers = &.{ even, pos } } });
    const r = pool.keyOf(refined).sort.refinement.?;
    try std.testing.expectEqual(nat, r.parent);
    try std.testing.expectEqual(@as(usize, 2), r.qualifiers.len);
    try std.testing.expectEqual(even, r.qualifiers[0]);
    try std.testing.expectEqual(pos, r.qualifiers[1]);
}

test "constant: data = sort Index, minted fresh (same sort → distinct constants), round-trips" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nat = try pool.mintSort(.{ .refinement = null });

    const zero = try pool.mintConstant(nat);
    const one = try pool.mintConstant(nat); // same sort, different constant
    try std.testing.expect(zero != one); // minted, so distinct despite same sort
    try std.testing.expectEqual(nat, pool.keyOf(zero).constant);
    try std.testing.expectEqual(nat, pool.keyOf(one).constant);
}

test "func: [sig, guard|none, paramc, names…] minted fresh, round-trips; guard optional" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nat = try pool.mintSort(.{ .refinement = null });
    const sig = try pool.get(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{ nat, nat } } });
    const n_name = try pool.internString("n");
    const m_name = try pool.internString("m");
    // stand-in guard term-offset (a real guard is a reified `extra` offset; any u32 works).
    const guard: TermOff = 42;

    // a func WITHOUT a guard
    const add = try pool.mintFunc(.{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{ n_name, m_name } });
    const add2 = try pool.mintFunc(.{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{ n_name, m_name } });
    try std.testing.expect(add != add2); // minted → distinct despite identical content
    const ka = pool.keyOf(add).func;
    try std.testing.expectEqual(sig, ka.sig);
    try std.testing.expectEqual(InternPool.no_term, ka.guard);
    try std.testing.expectEqual(@as(usize, 2), ka.param_names.len);
    try std.testing.expectEqual(n_name, ka.param_names[0]);
    try std.testing.expectEqual(m_name, ka.param_names[1]);

    // a func WITH a guard
    const g = try pool.mintFunc(.{ .sig = sig, .guard = guard, .param_names = &.{n_name} });
    const kg = pool.keyOf(g).func;
    try std.testing.expectEqual(guard, kg.guard);
    try std.testing.expectEqual(@as(usize, 1), kg.param_names.len);
}

test "pred: same Callable payload as func, minted under a DISTINCT kind" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nat = try pool.mintSort(.{ .refinement = null });
    // a predicate's sig has no meaningful result sort in the pool layout; use none-ish.
    const sig = try pool.get(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{nat} } });
    const x = try pool.internString("x");

    const is_even = try pool.mintPred(.{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{x} });
    const k = pool.keyOf(is_even).pred;
    try std.testing.expectEqual(sig, k.sig);
    try std.testing.expectEqual(InternPool.no_term, k.guard);
    try std.testing.expectEqual(@as(usize, 1), k.param_names.len);
    try std.testing.expectEqual(x, k.param_names[0]);
}

test "define: [body, paramc, names…] minted fresh, round-trips its template body + params" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const body: TermOff = 7; // stand-in template body term-offset (a reified extra offset)
    const n = try pool.internString("n");

    const def = try pool.mintDefine(.{ .body = body, .param_names = &.{n} });
    const def2 = try pool.mintDefine(.{ .body = body, .param_names = &.{n} });
    try std.testing.expect(def != def2); // minted → distinct

    const k = pool.keyOf(def).define;
    try std.testing.expectEqual(body, k.body);
    try std.testing.expectEqual(@as(usize, 1), k.param_names.len);
    try std.testing.expectEqual(n, k.param_names[0]);
}

test "import: data = the .namespace it binds; minted (two imports of one ns are distinct)" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const f = try pool.get(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });
    const ns = try pool.namespace(.universe, f);

    const imp = try pool.mintImport(ns);
    const imp2 = try pool.mintImport(ns); // same target ns, different local binding
    try std.testing.expect(imp != imp2); // minted → distinct
    try std.testing.expectEqual(ns, pool.keyOf(imp).import);
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

test "fact is a truth token carrying (kind, formula): mintFact always appends, round-trips" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    // stand-in formula term-offsets (a fact records the proposition it asserts, as a
    // reified `extra` offset; any distinct u32s work for this round-trip test).
    const f1: TermOff = 11;
    const f2: TermOff = 22;

    // mintFact ALWAYS appends a fresh token — no dedup (identity/(ns,name) is FactKV's
    // job, not the pool's). Two mints, even same (kind, formula), are DISTINCT Indexes.
    const a = try pool.mintFact(.theorem, f1);
    const b = try pool.mintFact(.theorem, f1);
    try std.testing.expect(a != b);

    // a fact carries its kind AND its formula (in extra).
    try std.testing.expectEqual(InternPool.Key.Kind.theorem, pool.keyOf(a).fact.kind);
    try std.testing.expectEqual(f1, pool.keyOf(a).fact.formula);
    const x = try pool.mintFact(.axiom, f2);
    try std.testing.expectEqual(InternPool.Key.Kind.axiom, pool.keyOf(x).fact.kind);
    try std.testing.expectEqual(f2, pool.keyOf(x).fact.formula);
    try std.testing.expect(x != a);
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
