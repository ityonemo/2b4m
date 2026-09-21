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
const Segmented = @import("segmented.zig").Segmented;

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
/// NON-MOVING (`Segmented`): an appended element's address is stable for the pool's life,
/// which is what makes the lock-free read path below sound. See `segmented.zig`.
items: Segmented(Item) = .empty,
/// Variable-length payload spill. An `Item.data` may be an offset into here; the run of
/// `u32`s starting there decodes (via reflection) into a payload struct. Non-moving, and
/// runs that are handed out as SLICES are appended contiguously (see `sortData`/`sigData`).
extra: Segmented(u32) = .empty,
/// Raw byte store for `.string` items. An interned string's bytes live here as a
/// contiguous run (its `String` payload in `extra` records the offset + length).
string_bytes: Segmented(u8) = .empty,
/// Dedup table: structural key -> Index, probed LOCK-FREE by `get` and written only under
/// `write_lock` by `intern`. NOT a `std.HashMapUnmanaged`: that type rehashes by swapping
/// its header non-atomically and writes slots non-atomically, so a lock-free probe racing an
/// insert reads a torn `Index`, hands it to `keyOf`, and faults (or worse, silently matches
/// the wrong item). See `Dedup` for the structure that makes the probe sound.
dedup: Dedup = .{},

/// Guards the pool's WRITE paths — `intern`'s create arm, and (still to be routed through
/// it) the `mint*` family. A self-contained spinlock, like `Engine.mutex`: `std.Io.Mutex`
/// needs an `Io` handle, and the pool is constructed in a dozen places (mostly test rigs)
/// that have none.
///
/// READS never take it: `get` is pure and lock-free.
write_lock: Lock = .{},

arena: std.mem.Allocator,
/// TRANSIENT staging for payloads that must land in `extra` as ONE contiguous run (a
/// segmented store cannot hand out a slice spanning two blocks, so a payload whose tail is
/// read back as a slice is built here first, then appended in one go). Defaults to `arena`.
scratch: std.mem.Allocator,

/// A dense handle into the pool. Non-exhaustive: low values are RESERVED for well-known
/// entries, `_` covers dynamically-interned ones.
///
/// `universe` (Index 0) is the UNIVERSE MODEL — the `(∅, …)` abstract/ground reading in
/// the namespace spec. Seeded at `init`, always present. Because it exists, the model
/// slot of a `(model, file, id)` namespace is never truly optional: "no model" IS the
/// universe model. Every model's parent chain bottoms out here.
pub const Index = enum(u32) {
    universe = 0,
    /// The "Prop" NAME STRING, reserved at Index 1 (the sort item's name field references
    /// it, and a stamped `Token.name` for the surface word `Prop` compares against it —
    /// the "no strcmp past parsing" invariant).
    prop_name = 1,
    /// The builtin `Prop` sort, reserved at Index 2 (seeded by `init`: universe at 0, the
    /// "Prop" name string at 1, the Prop SORT at 2). `term.SortId.prop` is the same value:
    /// once `SortId` becomes a pool `Index` (demand-prover Step 5+6), `Prop` already sits at
    /// its reserved slot and can't collide with the universe model at 0.
    prop = 2,
    _,

    /// The ABSENT marker for optional `Index` slots packed into `extra` (e.g. a func's
    /// missing guard). Index 0 is a real entry (the universe model), so the top of the
    /// range is the sentinel. A `?Index` is encoded as this on `null`, decoded back to
    /// `null` on read. NOT a valid pool entry — never appears as a `get`/`keyOf` result.
    pub const none: Index = @enumFromInt(0xFFFF_FFFF);
};

/// The proof-rule vocabulary, RESERVED as StrIds at `init` (contiguously from Index 3, in
/// declaration order — each field's NAME is the interned string, its VALUE its StrId). A
/// stamped `Token.name` in rule position is dispatched by integer comparison via `of` —
/// the "no strcmp past parsing" invariant. Accelerant/unknown rule words are simply not in
/// this range (`of` returns null → diagnosed as unsupported at the use site).
pub const RuleStr = enum(u32) {
    axiom = 3,
    theorem,
    hypothesis,
    predicate,
    modus_ponens,
    implies_intro,
    forall_intro,
    forall_elim,
    exists_intro,
    exists_elim,
    and_intro,
    and_elim_left,
    and_elim_right,
    iff_intro,
    iff_elim_forward,
    iff_elim_backward,
    or_intro_left,
    or_intro_right,
    or_elim,
    not_intro,
    absurd,
    double_negation,
    symmetry,
    reflexivity,
    rewrite,
    iff_rewrite,
    instantiation,
    model,
    /// KIND-AGNOSTIC fact citation (`[by cite foo]`): cites an axiom OR a theorem without
    /// naming which — the kernel picks its arm by the RESOLVED fact's kind (it already did
    /// for `axiom`/`theorem`; the word was never trusted). THE citation word for GENERATED
    /// proofs (accelerant certs can't know a lemma's kind) and handy for authors.
    /// `axiom`/`theorem` are being DEPRECATED in favor of `cite` (corpus migration TBD);
    /// they remain as equals meanwhile.
    cite,
    /// IMPORTED-THEOREM citation accelerant (`[using import(I) thm]`): cite a theorem from
    /// import `I`'s file as a cross-file transfer — the explicit accelerant seam at the file
    /// boundary (a `--fast`/strict trust boundary later), mirroring `model(M)`. `using`-side.
    import,

    pub fn id(self: RuleStr) StrId {
        return @enumFromInt(@intFromEnum(self));
    }

    /// The rule a stamped name-id denotes, or null if it is not a rule word.
    pub fn of(sid: StrId) ?RuleStr {
        const v = @intFromEnum(sid);
        if (v < @intFromEnum(RuleStr.axiom) or v > @intFromEnum(RuleStr.import)) return null;
        return @enumFromInt(v);
    }

    /// Which justification keyword this reserved rule word REQUIRES. `instantiation`/`model`
    /// are engine proof-generation → `using`; every other reserved word is a kernel
    /// primitive (incl. the `axiom`/`theorem` fact citations) → `by`. A NON-reserved word
    /// (an accelerant name, or a typo) is `using`-side by definition — the parser handles
    /// that case separately (it can't call this). Single source of truth for the parse-time
    /// by/using vocabulary partition. (A bare two-variant enum, not the AST's Kind, to keep
    /// InternPool free of an AST import — the parser maps it to `ast.Step.Claim.Kind`.)
    pub fn keyword(self: RuleStr) enum { by, using } {
        return switch (self) {
            .instantiation, .model, .import => .using,
            else => .by,
        };
    }
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
    /// An anonymous GUARD TERM: a refined sort's qualifier given by a define'd predicate
    /// (`sort Big = Nat where isBig` with `define isBig(n) = …`), EXPANDED and reified at
    /// fetch as a prop over the hygienic fvar `#g0` (the guarded element) at `carrier`. Sits
    /// in a sort's qualifier list beside opaque `.pred` qualifiers; applied by substituting
    /// `#g0`. `data` is an offset into `extra` holding `[term, carrier]`. Minted; nameless.
    guard,
    /// An IMPORT. `data` IS the `.namespace` `Index` it binds to (single-ref, no `extra`).
    /// Minted (a file can bind one namespace under several local names — distinct imports).
    /// Its local name lives in IdentKV.
    import,
    /// A SCHEMA — a parametric proof TEMPLATE. Stored as its EXISTENCE + a LOCATOR only:
    /// `data` is an offset into `extra` holding `[name, file, loc]` — enough to re-read the
    /// authoritative `ast.Decl.schema` (params/body/steps) from the by-NAME AST registry
    /// (`Context.declOf(file, name)`) at instantiation time. NO term/step reification — a
    /// schema's content is never durably encoded; each instantiation monomorphizes from the
    /// AST into its own `.fact`. Minted; name in IdentKV. (Resolving by name, not a
    /// positional decl_index, lets accelerant-generated synthetic schemas — which have no
    /// slot in `parsed[file].decls` — resolve identically.)
    schema,
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
    /// A sort identifier's content: its refinement (null = a root sort) + name/loc. Minted.
    sort: Sort,
    /// A constant identifier's content: its sort `Index` + name/loc. Minted.
    constant: Constant,
    /// A function identifier's content: signature + optional guard + param names + name/loc.
    func: Callable,
    /// A predicate identifier's content — same `Callable` payload, a distinct kind. Minted.
    pred: Callable,
    /// An anonymous guard TERM (see the `guard` tag): `[term, carrier]`.
    guard: Guard,
    /// An import identifier's content: the `.namespace` `Index` it binds to + name/loc.
    import: Import,
    /// A schema identifier's content: a LOCATOR back to its AST decl (name/file/loc). The
    /// template itself (params/body/steps) is re-read from the by-name AST registry, not stored.
    schema: Schema,

    /// A source file's interned payload: its resolved-path string id. Identity IS the
    /// path — two importers of the same file get the same `Index`.
    pub const File = struct { path: StrId };

    /// What a fact IS. Branched only at the prove-or-not boundary: an axiom is a
    /// resolve-and-store leaf; a theorem's proof gets checked.
    pub const Kind = enum(u8) { axiom, theorem };

    /// A fact's payload: its kind, the `extra`-offset of the formula term it asserts, and
    /// its name + source `loc`. Spilled into `extra` (reflection) as
    /// `[kind, formula_off, name, loc]`.
    pub const Fact = struct { kind: Kind, formula: TermOff, name: StrId, loc: u32 };

    /// A model's payload: its parent model `Index` (universe = itself) + its sparse
    /// overlay (`src -> tgt` mappings). The ancestor chain is the parent walk to the universe
    /// fixpoint. `dischargers` is a SEPARATE parallel table for guard-discharge (13e): each
    /// entry `(src=target-symbol, tgt=establishing-fact)` names a fact that proves the TARGET
    /// symbol's refined-sort guard — a base fact for a mapped const, a closure fact for a mapped
    /// func. Keyed by the TARGET symbol (`src` slot holds it), so the transfer's discharge walk,
    /// working in target space, finds a symbol's dischargers by scanning for matching `src`.
    /// Multiple entries with the same `src` = multiple facts (multi-guard const / >1 closure).
    /// `home` is the `.file` Index of the file the model is DECLARED in — where its guard
    /// predicates / closure facts live. A transferred proof's re-elaboration falls back to
    /// `(universe, home)` for names absent from the SOURCE file (relativization introduces
    /// target-file symbols like `inH` into the transferred formulas; the model's home file is
    /// exactly where they resolve). `.none` for universe (no fallback).
    pub const Model = struct { parent: Index, overlay: []const Mapping = &.{}, dischargers: []const Mapping = &.{}, home: Index = .none };

    /// One `src -> tgt` overlay entry (both pool `Index`es). Also reused for a discharger entry
    /// (`src` = the target symbol, `tgt` = the establishing fact).
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
        name: StrId,
        loc: u32,
        refinement: ?Refinement = null,
        pub const Refinement = struct { parent: Index, qualifiers: []const Index };
    };

    /// A constant's content: its sort `Index` + name/loc.
    pub const Constant = struct { sort: Index, name: StrId, loc: u32 };

    /// A func/pred's content: its signature `Index`, the `extra`-offset of an optional
    /// guard term (`no_term` = unguarded), its param-name string `Index`es, and name/loc.
    /// Shared by `func` and `pred` (identical layout; the tag says which). Variable-length.
    pub const Callable = struct { sig: Index, guard: TermOff, param_names: []const Index, name: StrId, loc: u32 };

    /// A define'd refinement guard reified as a prop TERM over the fvar `#g0` at `carrier`.
    pub const Guard = struct { term: TermOff, carrier: Index };

    /// An import's content: the `.namespace` `Index` it binds to + name/loc.
    pub const Import = struct { namespace: Index, name: StrId, loc: u32 };

    /// A schema's content: a LOCATOR — its name, the `.file` Index it is declared in, and its
    /// source `loc`. The authoritative params/body/steps come from the by-name AST registry,
    /// `Context.declOf(file, name).schema` (so a synthetic schema with no positional slot
    /// resolves the same way as a parsed one).
    pub const Schema = struct { name: StrId, file: Index, loc: u32 };

    /// `.string` storage payload: where the bytes live in `string_bytes`.
    const String = struct { off: u32, len: u32 };
};

// -- the dedup map's hashing/equality, computed over the ergonomic Key ----------------

fn hashKey(key: Key) u64 {
    var h = std.hash.Wyhash.init(0);
    std.hash.autoHash(&h, std.meta.activeTag(key));
    switch (key) {
        .string => |bytes| h.update(bytes), // identity IS the bytes
        .file => |f| std.hash.autoHash(&h, f.path),
        .model => |m| {
            std.hash.autoHash(&h, m.parent);
            std.hash.autoHash(&h, m.home);
            for (m.overlay) |mapping| std.hash.autoHash(&h, mapping);
            for (m.dischargers) |d| std.hash.autoHash(&h, d);
        },
        .namespace => |ns| std.hash.autoHash(&h, ns),
        .sig => |s| {
            std.hash.autoHash(&h, s.result);
            std.hash.autoHash(&h, s.result_refined);
            for (s.args) |arg| std.hash.autoHash(&h, arg);
        },
        // facts and identifiers are never deduped — minted via mintFact/mint*, not get
        .fact, .sort, .constant, .func, .pred, .guard, .import, .schema => unreachable,
    }
    return h.final();
}

fn sigEql(a: Key.Sig, b: Key.Sig) bool {
    if (a.result != b.result or a.result_refined != b.result_refined or a.args.len != b.args.len) return false;
    for (a.args, b.args) |x, y| if (x != y) return false;
    return true;
}

fn modelEql(a: Key.Model, b: Key.Model) bool {
    if (a.parent != b.parent or a.home != b.home or a.overlay.len != b.overlay.len or a.dischargers.len != b.dischargers.len) return false;
    for (a.overlay, b.overlay) |x, y| if (x.src != y.src or x.tgt != y.tgt) return false;
    for (a.dischargers, b.dischargers) |x, y| if (x.src != y.src or x.tgt != y.tgt) return false;
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
        .fact, .sort, .constant, .func, .pred, .guard, .import, .schema => unreachable, // minted
    };
}

/// The dedup table: open addressing, linear probing, one atomic `u32` (a raw `Index`) per
/// slot, `Index.none` meaning empty.
///
/// SOUND FOR LOCK-FREE READERS because nothing a reader touches ever moves or tears:
///   - The live table is reached through `cur`, loaded ONCE per probe with acquire. Growth
///     builds a NEW table under `write_lock`, fully populated, then publishes it with
///     release. The old table is never written again and never freed (arena), so a reader
///     that loaded the old pointer probes a valid, immutable, at-most-half-full table. It
///     may MISS a key inserted after its load — harmless: a miss goes to the locked path,
///     which re-probes the current table.
///   - A slot is stored with release only AFTER the item it names is fully appended
///     (`intern` appends first, inserts last), so a reader that acquire-loads a non-empty
///     slot sees a complete item and `keyOf` is safe. No slot is ever overwritten.
///   - The writer keeps every table under 50% full, so every probe hits an empty slot and
///     terminates — on the current table and on any stale one.
/// Only `intern` writes, under `write_lock`, and it re-probes before inserting, so a key is
/// never in the table twice.
const Dedup = struct {
    const EMPTY: u32 = @intFromEnum(Index.none);
    const min_slots: u32 = 1024;

    const Slots = struct {
        mask: u32,
        slots: []std.atomic.Value(u32),
    };

    /// The live table; null until the first insert. Readers acquire-load, growth release-stores.
    cur: std.atomic.Value(?*Slots) = .init(null),
    /// Live entries. Written only under `write_lock`.
    count: u32 = 0,

    /// Lock-free probe. Returns the Index whose key is structurally equal to `key`, or null.
    fn find(self: *const Dedup, pool: *const InternPool, key: Key) ?Index {
        const t = self.cur.load(.acquire) orelse return null;
        var i: u32 = @as(u32, @truncate(hashKey(key))) & t.mask;
        while (true) : (i = (i + 1) & t.mask) {
            const raw = t.slots[i].load(.acquire);
            if (raw == EMPTY) return null;
            const index: Index = @enumFromInt(raw);
            if (keyEql(key, pool.keyOf(index))) return index;
        }
    }

    /// Record `index` for `key`. CALLER HOLDS `write_lock` and has already re-probed (so the
    /// key is absent) and already appended the item (so a reader that sees the slot sees a
    /// complete item).
    fn insertLocked(self: *Dedup, arena: std.mem.Allocator, pool: *const InternPool, key: Key, index: Index) std.mem.Allocator.Error!void {
        var t = self.cur.load(.monotonic); // we are the only writer; no acquire needed
        if (t == null or (self.count + 1) * 2 > t.?.mask + 1) t = try self.grow(arena, pool, t);
        var i: u32 = @as(u32, @truncate(hashKey(key))) & t.?.mask;
        while (t.?.slots[i].load(.monotonic) != EMPTY) i = (i + 1) & t.?.mask;
        t.?.slots[i].store(@intFromEnum(index), .release); // item first, slot second — see above
        self.count += 1;
    }

    /// Build a table twice the size, re-insert every live entry, publish it. The old table
    /// is abandoned in place (never freed) so stale readers stay valid.
    fn grow(self: *Dedup, arena: std.mem.Allocator, pool: *const InternPool, old: ?*Slots) std.mem.Allocator.Error!*Slots {
        const n: u32 = if (old) |o| (o.mask + 1) * 2 else min_slots;
        const fresh = try arena.create(Slots);
        fresh.* = .{ .mask = n - 1, .slots = try arena.alloc(std.atomic.Value(u32), n) };
        for (fresh.slots) |*slot| slot.* = .init(EMPTY);
        if (old) |o| for (o.slots) |*slot| {
            const raw = slot.load(.monotonic);
            if (raw == EMPTY) continue;
            const k = pool.keyOf(@enumFromInt(raw));
            var i: u32 = @as(u32, @truncate(hashKey(k))) & fresh.mask;
            while (fresh.slots[i].load(.monotonic) != EMPTY) i = (i + 1) & fresh.mask;
            fresh.slots[i].store(raw, .monotonic); // not yet visible to anyone
        };
        self.cur.store(fresh, .release); // publish the fully-built table
        return fresh;
    }
};

/// Seed the pool with the RESERVED entries: the UNIVERSE MODEL at `Index.universe` (0) —
/// an empty parent stack every model's chain bottoms out at — and the builtin `Prop` SORT
/// at `Index.prop` (1). Prop is a root sort (no refinement); reserving it here means the
/// well-known slot exists before anything else is interned, so `term.SortId.prop` can point
/// at it once sorts become pool Indexes.
/// A test-and-set spinlock. Uncontended while the engine is single-threaded; the value is
/// that the critical section is MARKED and correct when workers land.
pub const Lock = struct {
    locked: std.atomic.Value(bool) = .init(false),
    pub fn lock(self: *Lock) void {
        while (self.locked.swap(true, .acquire)) std.atomic.spinLoopHint();
    }
    pub fn unlock(self: *Lock) void {
        self.locked.store(false, .release);
    }
};

pub fn init(arena: std.mem.Allocator) std.mem.Allocator.Error!InternPool {
    // `scratch` defaults to the arena: payload staging buffers are short-lived, and an
    // arena leak of a few words per mint is cheaper than threading a GPA in. (A caller that
    // cares can set `scratch` to a reclaiming allocator afterwards.)
    var self: InternPool = .{ .arena = arena, .scratch = arena };
    // Universe is its own parent — a self-reference at Index 0. The `.universe` constant
    // IS 0, so we can name it as the parent before the entry physically exists.
    const universe = try self.intern(.{ .model = .{ .parent = .universe } });
    std.debug.assert(universe == .universe); // the universe model MUST be Index 0
    // The "Prop" name string lands at Index 1, then the builtin Prop SORT at Index 2 (its
    // name field references the string). `Index.prop` names the sort. Ordering matters:
    // interning the name first fixes the sort at the next slot without a forward reference.
    const prop_name = try self.internString("Prop");
    std.debug.assert(prop_name == .prop_name); // "Prop" string MUST land at Index.prop_name
    const prop = try self.mintSort(.{ .name = prop_name, .loc = 0, .refinement = null });
    std.debug.assert(prop == .prop); // Prop sort MUST land at Index.prop
    // Reserve the rule-word strings contiguously from Index 3, each at its RuleStr value —
    // the enum's field NAMES are the strings, so the vocabulary has one source of truth.
    inline for (@typeInfo(RuleStr).@"enum".fields) |f| {
        const sid = try self.internString(f.name);
        std.debug.assert(@intFromEnum(sid) == f.value); // rule word MUST land at its RuleStr slot
    }
    return self;
}

/// LOOK UP a key — a PURE READ. Returns null when the key has never been interned.
///
/// Takes NO lock and mutates nothing, so it is free to call from any thread: the stores it
/// reads through are `Segmented` (non-moving), so an entry's address is stable once written.
/// This is the hot path — the overwhelming majority of interning calls are hits — and it is
/// deliberately the cheapest thing in the pool.
///
/// Use `intern` when a miss should CREATE the entry. Splitting the two is what keeps the
/// read path free: `get` used to create on a miss, which forced every caller — hit or miss —
/// through the write lock.
pub fn get(self: *const InternPool, key: Key) ?Index {
    return self.dedup.find(self, key);
}

/// INTERN a key: its existing `Index` if one exists, else create the entry and return the
/// fresh `Index`. The canonical-identity entry point — two structurally equal keys always
/// yield the same `Index`.
///
/// Protocol (the miss path is the only part that locks):
///   1. probe lock-free via `get`; a hit returns immediately;
///   2. on a miss take `write_lock`;
///   3. RE-PROBE under the lock — another thread may have interned this key while we were
///      blocked, in which case we must return ITS index and build nothing;
///   4. only if still absent, build the entry and publish it.
///
/// Step 3 is load-bearing: without it two threads that both miss would both build, putting
/// two items in the store for one key and breaking the identity the whole pool rests on.
pub fn intern(self: *InternPool, key: Key) std.mem.Allocator.Error!Index {
    if (self.get(key)) |existing| return existing; // lock-free fast path

    self.write_lock.lock();
    defer self.write_lock.unlock();

    // RE-PROBE: someone may have interned it between our miss and taking the lock.
    if (self.dedup.find(self, key)) |existing| return existing;

    const index: Index = @enumFromInt(self.items.len);
    switch (key) {
        .string => |bytes| {
            // the START comes from the append itself: a contiguous append may PAD past a
            // block boundary first, so the pre-append length is not where the bytes land.
            const bytes_off = try self.string_bytes.appendSliceContiguous(self.arena, bytes);
            const off = try self.addExtra(Key.String{ .off = bytes_off, .len = @intCast(bytes.len) });
            _ = try self.items.append(self.arena, .{ .tag = .string, .data = off });
        },
        .file => |f| {
            const off = try self.addExtra(Key.File{ .path = f.path });
            _ = try self.items.append(self.arena, .{ .tag = .file, .data = off });
        },
        .model => |m| {
            const off = try self.addModel(m); // [parent, overlay_count, ...src/tgt pairs]
            _ = try self.items.append(self.arena, .{ .tag = .model, .data = off });
        },
        .namespace => |ns| {
            const off = try self.addExtra(ns);
            _ = try self.items.append(self.arena, .{ .tag = .namespace, .data = off });
        },
        .sig => |s| {
            const off = try self.addSig(s); // [result, result_refined, argc, a0, …]
            _ = try self.items.append(self.arena, .{ .tag = .sig, .data = off });
        },
        // facts/identifiers are minted via mintFact/mint*, never `get` (no dedup)
        .fact, .sort, .constant, .func, .pred, .guard, .import, .schema => unreachable,
    }
    try self.dedup.insertLocked(self.arena, self, key, index); // item is complete; publish it
    return index;
}

/// Mint a fresh fact truth-token carrying `(kind, formula, name, loc)` in `extra` — ALWAYS
/// appends (no dedup). Bypasses `get`/`map` because a fact has no structural identity in the
/// pool (FactKV owns `(ns,name)→Index` and guarantees single-mint). Interning a fact IS
/// committing "this fact is proven true". Takes the write-mutex like any pool write.
pub fn mintFact(self: *InternPool, kind: Key.Kind, formula: TermOff, name: StrId, loc: u32) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addExtra(Key.Fact{ .kind = kind, .formula = formula, .name = name, .loc = loc });
    _ = try self.items.append(self.arena, .{ .tag = .fact, .data = off });
    return index;
}

/// Mint a fresh SORT identifier, ALWAYS appending (no dedup; IdentKV owns identity). Spills
/// `[name, loc, parent, qualc, q0, …]` into `extra` (`parent == Index.none` ⇒ a ROOT sort,
/// no qualifiers). Two root sorts have identical content but distinct Indexes (name-identity
/// is IdentKV's). Callers hold the write-mutex, as with any pool write.
pub fn mintSort(self: *InternPool, s: Key.Sort) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addSortPayload(s);
    _ = try self.items.append(self.arena, .{ .tag = .sort, .data = off });
    return index;
}

/// Append `[name, loc, parent, qualc, q0, …]` to `extra`; return the start offset.
fn addSortPayload(self: *InternPool, s: Key.Sort) std.mem.Allocator.Error!u32 {
    const qn: u32 = if (s.refinement) |r| @intCast(r.qualifiers.len) else 0;
    // ONE contiguous run: `sortData` hands the qualifier tail back as a live SLICE, which a
    // segmented store can only do within a single block. Build the whole payload in scratch,
    // then append it contiguously (the store pads past a boundary rather than straddling).
    var buf: std.ArrayList(u32) = .empty;
    defer buf.deinit(self.scratch);
    try buf.ensureTotalCapacity(self.scratch, 4 + qn);
    buf.appendAssumeCapacity(@intFromEnum(s.name));
    buf.appendAssumeCapacity(s.loc);
    buf.appendAssumeCapacity(if (s.refinement) |r| @intFromEnum(r.parent) else @intFromEnum(Index.none));
    buf.appendAssumeCapacity(qn);
    if (s.refinement) |r| for (r.qualifiers) |q| buf.appendAssumeCapacity(@intFromEnum(q));
    return self.extra.appendSliceContiguous(self.arena, buf.items);
}

/// Read a sort payload at `off` back — the inverse of `addSortPayload`.
fn sortData(self: *const InternPool, off: u32) Key.Sort {
    const name: StrId = @enumFromInt(self.extra.get(off));
    const loc = self.extra.get(off + 1);
    const parent_raw = self.extra.get(off + 2);
    const qn = self.extra.get(off + 3);
    if (parent_raw == @intFromEnum(Index.none)) return .{ .name = name, .loc = loc, .refinement = null };
    const raw = self.extra.sliceContiguous(off + 4, qn);
    return .{ .name = name, .loc = loc, .refinement = .{ .parent = @enumFromInt(parent_raw), .qualifiers = @ptrCast(raw) } };
}

// -- pool-backed refinement / signature queries -------------------------------------
// These mirror `env.Env`'s `carrierOf`/`qualifiersOf`/`isRefined`/`symResult` over the
// pool's `sort`/`func`/`pred` Items, reading refinement chains stored in `extra`. As the
// demand model takes over (env dissolves), name resolution + kernel reads route here.
// (`sortName` waits until a `sort` Item carries its name — Step 6.)

/// Whether a `sort` Item is refined (a predicated sort with a guard) — has a refinement.
pub fn isRefined(self: *const InternPool, sort: Index) bool {
    std.debug.assert(self.items.get(@intFromEnum(sort)).tag == .sort);
    return self.keyOf(sort).sort.refinement != null;
}

/// A sort's name bytes (for diagnostics/render). Asserts `id` names a `.sort` Item.
pub fn sortName(self: *const InternPool, id: Index) []const u8 {
    return self.stringBytes(self.keyOf(id).sort.name);
}

/// A named Item's `name` StrId (sort/constant/func/pred/define/import/fact). For readers
/// that need the entity's source name (render, diagnostics) without caring about its kind.
pub fn nameOf(self: *const InternPool, id: Index) StrId {
    return switch (self.keyOf(id)) {
        .sort => |s| s.name,
        .constant => |c| c.name,
        .func, .pred => |c| c.name,
        .import => |m| m.name,
        .fact => |f| f.name,
        .schema => |s| s.name,
        else => unreachable,
    };
}

/// The KERNEL sort a (possibly refined) sort `Index` lowers to: walk `parent` to the root
/// (a `sort` with no refinement). A root sort is its own carrier. Mirrors env.carrierOf.
pub fn carrierOf(self: *const InternPool, sort: Index) Index {
    var cur = sort;
    while (self.keyOf(cur).sort.refinement) |r| cur = r.parent;
    return cur;
}

/// The guard qualifiers accumulated along a sort's refinement chain (empty for a root
/// sort), innermost-refinement first. Mirrors env.qualifiersOf. Arena-allocated result.
pub fn qualifiersOf(self: *const InternPool, arena: std.mem.Allocator, sort: Index) std.mem.Allocator.Error![]const Index {
    var acc: std.ArrayList(Index) = .empty;
    var cur = sort;
    while (self.keyOf(cur).sort.refinement) |r| {
        try acc.appendSlice(arena, r.qualifiers);
        cur = r.parent;
    }
    return acc.toOwnedSlice(arena);
}

/// A symbol's RESULT sort `Index`: a func/pred's signature result, or a constant's sort
/// (a constant is a nullary application to every term reader). Asserts `sym` names a
/// `.func`/`.pred`/`.constant` Item.
pub fn symResult(self: *const InternPool, sym: Index) Index {
    const callable = switch (self.keyOf(sym)) {
        .func => |c| c,
        .pred => |c| c,
        .constant => |c| return c.sort,
        else => unreachable,
    };
    return self.keyOf(callable.sig).sig.result;
}

/// Mint a fresh CONSTANT identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// Spills `[sort, name, loc]` into `extra`. Two constants of the same sort get distinct
/// Indexes.
/// Mint an anonymous GUARD term Item (a define'd `where` qualifier), always appending.
pub fn mintGuard(self: *InternPool, g: Key.Guard) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addExtra(g); // reflection: [term, carrier]
    _ = try self.items.append(self.arena, .{ .tag = .guard, .data = off });
    return index;
}

pub fn mintConstant(self: *InternPool, c: Key.Constant) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addExtra(c); // reflection: [sort, name, loc]
    _ = try self.items.append(self.arena, .{ .tag = .constant, .data = off });
    return index;
}

/// Append `[sig, guard, name, loc, paramc, pn0, …]` to `extra`; return the start offset.
fn addCallable(self: *InternPool, c: Key.Callable) std.mem.Allocator.Error!u32 {
    // ONE contiguous run — `callableData` slices the param-name tail (see `addSortPayload`).
    var buf: std.ArrayList(u32) = .empty;
    defer buf.deinit(self.scratch);
    try buf.ensureTotalCapacity(self.scratch, 5 + c.param_names.len);
    buf.appendAssumeCapacity(@intFromEnum(c.sig));
    buf.appendAssumeCapacity(c.guard); // TermOff (u32), not an Index
    buf.appendAssumeCapacity(@intFromEnum(c.name));
    buf.appendAssumeCapacity(c.loc);
    buf.appendAssumeCapacity(@intCast(c.param_names.len));
    for (c.param_names) |n| buf.appendAssumeCapacity(@intFromEnum(n));
    return self.extra.appendSliceContiguous(self.arena, buf.items);
}

/// Read a callable payload at `off` back — the inverse of `addCallable`.
fn callableData(self: *const InternPool, off: u32) Key.Callable {
    const sig: Index = @enumFromInt(self.extra.get(off));
    const guard: TermOff = self.extra.get(off + 1); // TermOff (u32), not an Index
    const name: StrId = @enumFromInt(self.extra.get(off + 2));
    const loc = self.extra.get(off + 3);
    const n = self.extra.get(off + 4);
    const raw = self.extra.sliceContiguous(off + 5, n);
    return .{ .sig = sig, .guard = guard, .name = name, .loc = loc, .param_names = @ptrCast(raw) };
}

/// Mint a fresh FUNCTION identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// Spills `[sig, guard, paramc, pn0, …]` into `extra`.
pub fn mintFunc(self: *InternPool, c: Key.Callable) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addCallable(c);
    _ = try self.items.append(self.arena, .{ .tag = .func, .data = off });
    return index;
}

/// Mint a fresh PREDICATE identifier — same `Callable` payload as `mintFunc`, a distinct
/// tag. ALWAYS appends (no dedup; IdentKV owns identity).
pub fn mintPred(self: *InternPool, c: Key.Callable) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addCallable(c);
    _ = try self.items.append(self.arena, .{ .tag = .pred, .data = off });
    return index;
}

/// Mint a fresh IMPORT identifier, ALWAYS appending (no dedup; IdentKV owns identity).
/// Spills `[namespace, name, loc]` into `extra`.
pub fn mintImport(self: *InternPool, m: Key.Import) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addExtra(m); // reflection: [namespace, name, loc]
    _ = try self.items.append(self.arena, .{ .tag = .import, .data = off });
    return index;
}

/// Mint a fresh SCHEMA locator, ALWAYS appending (no dedup; IdentKV owns identity).
/// Spills `[name, file, loc]` into `extra` (reflection). The template content is NOT stored
/// — it is re-read from the by-name AST registry via `file`+`name`.
pub fn mintSchema(self: *InternPool, s: Key.Schema) std.mem.Allocator.Error!Index {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    const index: Index = @enumFromInt(self.items.len);
    const off = try self.addExtra(s); // reflection: [name, file, loc]
    _ = try self.items.append(self.arena, .{ .tag = .schema, .data = off });
    return index;
}

// -- raw `extra` u32-run API (term serialization rests on this) ------------------------
// Terms are NOT interned Items (bpa is an explicit prover — no term dedup); a DURABLE term
// is a self-contained u32 run in `extra`, written/read by term.zig's `reify`/`copyIn`. The
// pool stays term-AGNOSTIC: it just stores and hands back the run. (term.zig imports
// InternPool, not the reverse, so the term-shaped encode/decode lives there.)

/// Append a run of `u32`s to `extra`; return its start offset. A WRITE, synchronized
/// internally like every mint (see `write_lock`). `reify` calls this once per term (the
/// whole serialized run in one append).
pub fn appendExtraRun(self: *InternPool, run: []const u32) std.mem.Allocator.Error!u32 {
    self.write_lock.lock();
    defer self.write_lock.unlock();
    // CONTIGUOUS: `extraRun` hands this back as a slice, so it must live in one block.
    return self.extra.appendSliceContiguous(self.arena, run);
}

/// Read `len` `u32`s from `extra` starting at `off` — a lock-free read (the run is
/// immutable once appended). `copyIn` walks the returned slice to rebuild a scratchpad term.
pub fn extraRun(self: *const InternPool, off: u32, len: u32) []const u32 {
    return self.extra.sliceContiguous(off, len);
}

/// The first `u32` of a serialized term run is its payload WORD-COUNT (number of u32s after
/// the header). A reader that only has the offset uses this to slice the run:
/// `extraRun(off + 1, extraRunLen(off))`. `copyIn` then walks the payload node-by-node (each
/// node self-describes its width via its tag), post-order, until consumed — the last node is
/// the root.
pub fn extraRunLen(self: *const InternPool, off: u32) u32 {
    return self.extra.get(off);
}

/// Reconstruct the ergonomic `Key` from an `Index` — the inverse of `get`'s packing.
pub fn keyOf(self: *const InternPool, index: Index) Key {
    const item = self.items.get(@intFromEnum(index));
    return switch (item.tag) {
        .string => {
            const s = self.extraData(Key.String, item.data);
            return .{ .string = self.string_bytes.sliceContiguous(s.off, s.len) };
        },
        .file => .{ .file = self.extraData(Key.File, item.data) },
        .model => .{ .model = self.modelData(item.data) },
        .namespace => .{ .namespace = self.extraData(Key.Namespace, item.data) },
        .fact => .{ .fact = self.extraData(Key.Fact, item.data) }, // [kind, formula, name, loc]
        .sig => .{ .sig = self.sigData(item.data) },
        .sort => .{ .sort = self.sortData(item.data) },
        .constant => .{ .constant = self.extraData(Key.Constant, item.data) },
        .func => .{ .func = self.callableData(item.data) },
        .pred => .{ .pred = self.callableData(item.data) },
        .guard => .{ .guard = self.extraData(Key.Guard, item.data) },
        .import => .{ .import = self.extraData(Key.Import, item.data) },
        .schema => .{ .schema = self.extraData(Key.Schema, item.data) },
    };
}

/// Number of interned entries.
pub fn count(self: *const InternPool) usize {
    return self.items.len;
}

// -- string convenience (the StrId façade rests on these) -----------------------------

/// Intern bytes as a string, returning its `StrId` (== a pool `Index`). Content-deduped.
pub fn internString(self: *InternPool, bytes: []const u8) std.mem.Allocator.Error!StrId {
    return self.intern(.{ .string = bytes });
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
    return self.intern(.{ .namespace = .{ .model = model, .file = file } });
}

/// Interpret a SOURCE entity `Index` THROUGH a model: walk `model`'s overlay chain (its
/// own overlay, then its parent's, … up to the universe fixpoint) and return the TARGET
/// the source is mapped to. An UNMAPPED source returns unchanged (universe = empty overlay
/// = identity). This is how resolving a name in a model namespace remaps it: resolve the
/// name to its source `Index` (in the source file's universe namespace), then `applyModel`.
/// Lock-free (models are immutable once interned).
pub fn applyModel(self: *const InternPool, model: Index, source: Index) Index {
    var cur = model;
    while (true) {
        const m = self.keyOf(cur).model;
        for (m.overlay) |e| if (e.src == source) return e.tgt;
        if (cur == m.parent) return source; // universe fixpoint: unmapped ⇒ identity
        cur = m.parent;
    }
}

/// Collect the model-nominated GUARD-DISCHARGER facts for a TARGET `symbol` (a const or func
/// in target space) into `out` — the facts the model named to establish that symbol's
/// refined-sort guard (13e: a const's base facts, a func's closure facts). Walks the model's
/// discharger table (and its parents'). `out` accumulates; may append 0+ facts (multi-guard /
/// >1 closure). Lock-free (models are immutable once interned).
pub fn modelDischargers(self: *const InternPool, model: Index, symbol: Index, out: *std.ArrayList(Index), gpa: std.mem.Allocator) std.mem.Allocator.Error!void {
    var cur = model;
    while (true) {
        const m = self.keyOf(cur).model;
        for (m.dischargers) |d| if (d.src == symbol) try out.append(gpa, d.tgt);
        if (cur == m.parent) return;
        cur = m.parent;
    }
}

/// COMPOSE two models: the model that is `outer ∘ inner` AS A FUNCTION on symbols — for every
/// `x`, `applyModel(composed, x) == applyModel(outer, applyModel(inner, x))`. Returns a new
/// (interned, deduped) `.model` whose overlay maps each source in `inner`'s WHOLE domain to
/// `applyModel(outer, applyModel(inner, src))` — inner's answer run one more step through the
/// ambient model — with `parent = outer`, so a source `inner` does not touch falls through to
/// `outer` (correct, since `inner` is the identity there). Dischargers compose the same way
/// (the establishing facts are target-space Indices, so they too route through `outer`).
///
/// WHY precompose instead of parent-chaining `inner` onto `outer`: a model is an OVERRIDE
/// table, not a function — `applyModel` returns the overlay target on FIRST hit and never
/// re-applies the parent to that result, so an inner mapping `{src → tgt}` would stop at
/// `tgt` (source space) instead of reaching `applyModel(outer, tgt)`. Baking the second hop
/// into the overlay makes the result exact function composition.
///
/// WHY flatten `inner`'s ENTIRE parent chain (not just its top overlay): `inner`'s domain is
/// everything any level of its chain maps (nearest level wins — exactly `applyModel(inner, ·)`).
/// A top-overlay-only composition would send a source mapped only by inner's PARENT to
/// `outer(src)` instead of `outer(parent(src))` — silently mis-relativized. Every declared
/// model is universe-parented today, but a composed model is not (its parent is the ambient
/// model), and a nested transfer at depth ≥ 2 composes with one of those as the inner. So
/// composition is associative and holds at ANY nesting depth by induction: the outer side is
/// always `applyModel` (correct for any chain), and the inner side is fully flattened here.
///
/// Used by a NESTED model transfer: proving `[using model(inner) src.thm]` while an ambient
/// `outer` model is active (a transferred proof re-proving a transfer) must relativize down
/// BOTH models. The chain is copied out BEFORE the mint (`Key.Model` slices alias `extra`,
/// which the `get` may grow). Takes the write lock around the `get`-that-appends, like any
/// model mint.
pub fn composeModel(self: *InternPool, io: std.Io, outer: Index, inner: Index) std.mem.Allocator.Error!Index {
    var overlay: std.ArrayList(Key.Mapping) = .empty;
    var dischargers: std.ArrayList(Key.Mapping) = .empty;
    const home = self.keyOf(inner).model.home;
    var cur = inner;
    while (true) {
        const m = self.keyOf(cur).model;
        // overlay: nearest level wins per source (applyModel's first-hit rule), then compose.
        for (m.overlay) |e| {
            const seen = for (overlay.items) |have| {
                if (have.src == e.src) break true;
            } else false;
            if (!seen) try overlay.append(self.arena, .{ .src = e.src, .tgt = self.applyModel(outer, e.tgt) });
        }
        // dischargers ACCUMULATE across the chain (modelDischargers collects every level).
        for (m.dischargers) |d| try dischargers.append(self.arena, .{ .src = d.src, .tgt = self.applyModel(outer, d.tgt) });
        if (cur == m.parent) break; // universe fixpoint
        cur = m.parent;
    }
    // `intern` synchronizes itself; no caller-held lock (see `write_lock`).
    _ = io;
    return self.intern(.{ .model = .{ .parent = outer, .overlay = overlay.items, .dischargers = dischargers.items, .home = home } });
}

// -- model encoding (`[parent, overlay_count, src0, tgt0, …]`) -------------------------
// A model's parent + sparse overlay; variable-length, so the fixed-struct reflection
// encoder can't express it. The overlay is empty for now (mappings deferred).

/// Append `[parent, overlay_count, src0, tgt0, …]` to `extra`; return the start offset.
fn addModel(self: *InternPool, m: Key.Model) std.mem.Allocator.Error!u32 {
    // ONE contiguous run — `modelData` reinterprets both pair-runs as slices (see
    // `addSortPayload` for why a segmented store needs the whole payload in one block).
    var buf: std.ArrayList(u32) = .empty;
    defer buf.deinit(self.scratch);
    try buf.ensureTotalCapacity(self.scratch, 4 + (m.overlay.len + m.dischargers.len) * 2);
    buf.appendAssumeCapacity(@intFromEnum(m.parent));
    buf.appendAssumeCapacity(@intFromEnum(m.home));
    buf.appendAssumeCapacity(@intCast(m.overlay.len));
    for (m.overlay) |mapping| {
        buf.appendAssumeCapacity(@intFromEnum(mapping.src));
        buf.appendAssumeCapacity(@intFromEnum(mapping.tgt));
    }
    buf.appendAssumeCapacity(@intCast(m.dischargers.len));
    for (m.dischargers) |d| {
        buf.appendAssumeCapacity(@intFromEnum(d.src));
        buf.appendAssumeCapacity(@intFromEnum(d.tgt));
    }
    return self.extra.appendSliceContiguous(self.arena, buf.items);
}

/// Read the model payload at `off` back — the inverse of `addModel`. Each pair-run
/// reinterprets the `u32` run in `extra` as `Mapping` (two `Index`es), zero-copy. Layout:
/// `[parent, home, overlay_count, ...overlay pairs, discharger_count, ...discharger pairs]`.
fn modelData(self: *const InternPool, off: u32) Key.Model {
    const parent: Index = @enumFromInt(self.extra.get(off));
    const home: Index = @enumFromInt(self.extra.get(off + 1));
    const on = self.extra.get(off + 2);
    const overlay_raw = self.extra.sliceContiguous(off + 3, on * 2);
    const dcount_at = off + 3 + on * 2;
    const dn = self.extra.get(dcount_at);
    const disch_raw = self.extra.sliceContiguous(dcount_at + 1, dn * 2);
    return .{ .parent = parent, .home = home, .overlay = @ptrCast(overlay_raw), .dischargers = @ptrCast(disch_raw) };
}

// -- signature encoding (`[result, result_refined, argc, a0, …]`) ----------------------

/// Append `[result, result_refined, argc, a0, …]` to `extra`; return the start offset.
fn addSig(self: *InternPool, s: Key.Sig) std.mem.Allocator.Error!u32 {
    // ONE contiguous run — `sigData` slices the arg tail.
    var buf: std.ArrayList(u32) = .empty;
    defer buf.deinit(self.scratch);
    try buf.ensureTotalCapacity(self.scratch, 3 + s.args.len);
    buf.appendAssumeCapacity(@intFromEnum(s.result));
    buf.appendAssumeCapacity(@intFromEnum(s.result_refined));
    buf.appendAssumeCapacity(@intCast(s.args.len));
    for (s.args) |arg| buf.appendAssumeCapacity(@intFromEnum(arg));
    return self.extra.appendSliceContiguous(self.arena, buf.items);
}

/// Read a signature payload at `off` back — the inverse of `addSig`.
fn sigData(self: *const InternPool, off: u32) Key.Sig {
    const result: Index = @enumFromInt(self.extra.get(off));
    const result_refined: Index = @enumFromInt(self.extra.get(off + 1));
    const n = self.extra.get(off + 2);
    const raw = self.extra.sliceContiguous(off + 3, n);
    return .{ .result = result, .result_refined = result_refined, .args = @ptrCast(raw) };
}

// -- reflection-based `extra` encoding ------------------------------------------------
// A payload struct is serialized field-by-field as `u32`: enum fields by their integer
// tag, integer fields by bit-cast. Reading reverses it. Field ORDER is the contract.

/// Append `payload`'s fields to `extra` as a run of `u32`; return the start offset.
fn addExtra(self: *InternPool, payload: anytype) std.mem.Allocator.Error!u32 {
    const T = @TypeOf(payload);
    const fields = @typeInfo(T).@"struct".fields;
    // Staged then appended as ONE run so the payload's fields are contiguous and the
    // returned offset is where they actually landed (a contiguous append may pad first).
    var buf: [fields.len]u32 = undefined;
    inline for (fields, 0..) |field, i| buf[i] = encodeField(@field(payload, field.name));
    return self.extra.appendSliceContiguous(self.arena, &buf);
}

/// Decode a `T` payload from `extra` starting at `off` — the inverse of `addExtra`.
fn extraData(self: *const InternPool, comptime T: type, off: u32) T {
    const fields = @typeInfo(T).@"struct".fields;
    var result: T = undefined;
    inline for (fields, 0..) |field, i| {
        @field(result, field.name) = decodeField(field.type, self.extra.get(off + @as(u32, i)));
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
    const s1 = try pool.intern(.{ .sig = .{ .result = bool_, .result_refined = .none, .args = &.{ nat, int } } });
    const s1_again = try pool.intern(.{ .sig = .{ .result = bool_, .result_refined = .none, .args = &.{ nat, int } } });
    const s2 = try pool.intern(.{ .sig = .{ .result = bool_, .result_refined = .none, .args = &.{ int, nat } } }); // arg order
    const s3 = try pool.intern(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{ nat, int } } }); // result
    const s4 = try pool.intern(.{ .sig = .{ .result = bool_, .result_refined = nat, .args = &.{ nat, int } } }); // refined
    const s_nullary = try pool.intern(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{} } });

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
    const nm = try pool.internString("s"); // stand-in name
    const nat = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = null });
    const int = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = null });
    try std.testing.expect(nat != int);
    try std.testing.expect(pool.keyOf(nat).sort.refinement == null);
    try std.testing.expectEqual(nm, pool.keyOf(nat).sort.name);

    // a REFINED sort: parent + a qualifier list (stand-in pred Indexes)
    const even = try pool.internString("isEven"); // stand-in qualifier
    const pos = try pool.internString("isPos");
    const refined = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = .{ .parent = nat, .qualifiers = &.{ even, pos } } });
    const r = pool.keyOf(refined).sort.refinement.?;
    try std.testing.expectEqual(nat, r.parent);
    try std.testing.expectEqual(@as(usize, 2), r.qualifiers.len);
    try std.testing.expectEqual(even, r.qualifiers[0]);
    try std.testing.expectEqual(pos, r.qualifiers[1]);
}

test "refinement queries: carrierOf/qualifiersOf/isRefined walk the chain" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var pool: InternPool = try .init(arena);

    const in_b = try pool.internString("inB"); // stand-in qualifier preds
    const in_c = try pool.internString("inC");
    const nm = try pool.internString("s");
    // chain: C = B where inC, B = A where inB, A root.
    const a = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = null });
    const b = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = .{ .parent = a, .qualifiers = &.{in_b} } });
    const c = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = .{ .parent = b, .qualifiers = &.{in_c} } });

    try std.testing.expect(!pool.isRefined(a));
    try std.testing.expect(pool.isRefined(b));
    try std.testing.expect(pool.isRefined(c));

    // carrier collapses to the root A for every level.
    try std.testing.expectEqual(a, pool.carrierOf(a));
    try std.testing.expectEqual(a, pool.carrierOf(b));
    try std.testing.expectEqual(a, pool.carrierOf(c));

    // qualifiers accumulate innermost-first along the chain.
    try std.testing.expectEqualSlices(Index, &.{}, try pool.qualifiersOf(arena, a));
    try std.testing.expectEqualSlices(Index, &.{ in_c, in_b }, try pool.qualifiersOf(arena, c));

    // symResult reads a func's signature result sort.
    const sig = try pool.intern(.{ .sig = .{ .result = a, .result_refined = .none, .args = &.{a} } });
    const f = try pool.mintFunc(.{ .sig = sig, .guard = no_term, .param_names = &.{try pool.internString("x")}, .name = nm, .loc = 0 });
    try std.testing.expectEqual(a, pool.symResult(f));
}

test "constant: data = sort Index, minted fresh (same sort → distinct constants), round-trips" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nm = try pool.internString("s");
    const nat = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = null });

    const zero = try pool.mintConstant(.{ .sort = nat, .name = nm, .loc = 0 });
    const one = try pool.mintConstant(.{ .sort = nat, .name = nm, .loc = 0 }); // same sort, distinct
    try std.testing.expect(zero != one); // minted, so distinct despite same sort
    try std.testing.expectEqual(nat, pool.keyOf(zero).constant.sort);
    try std.testing.expectEqual(nat, pool.keyOf(one).constant.sort);
}

test "func: [sig, guard|none, paramc, names…] minted fresh, round-trips; guard optional" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nm = try pool.internString("s");
    const nat = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = null });
    const sig = try pool.intern(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{ nat, nat } } });
    const n_name = try pool.internString("n");
    const m_name = try pool.internString("m");
    // stand-in guard term-offset (a real guard is a reified `extra` offset; any u32 works).
    const guard: TermOff = 42;

    // a func WITHOUT a guard
    const add = try pool.mintFunc(.{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{ n_name, m_name }, .name = nm, .loc = 0 });
    const add2 = try pool.mintFunc(.{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{ n_name, m_name }, .name = nm, .loc = 0 });
    try std.testing.expect(add != add2); // minted → distinct despite identical content
    const ka = pool.keyOf(add).func;
    try std.testing.expectEqual(sig, ka.sig);
    try std.testing.expectEqual(InternPool.no_term, ka.guard);
    try std.testing.expectEqual(@as(usize, 2), ka.param_names.len);
    try std.testing.expectEqual(n_name, ka.param_names[0]);
    try std.testing.expectEqual(m_name, ka.param_names[1]);

    // a func WITH a guard
    const g = try pool.mintFunc(.{ .sig = sig, .guard = guard, .param_names = &.{n_name}, .name = nm, .loc = 0 });
    const kg = pool.keyOf(g).func;
    try std.testing.expectEqual(guard, kg.guard);
    try std.testing.expectEqual(@as(usize, 1), kg.param_names.len);
}

test "pred: same Callable payload as func, minted under a DISTINCT kind" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const nm = try pool.internString("s");
    const nat = try pool.mintSort(.{ .name = nm, .loc = 0, .refinement = null });
    // a predicate's sig has no meaningful result sort in the pool layout; use none-ish.
    const sig = try pool.intern(.{ .sig = .{ .result = nat, .result_refined = .none, .args = &.{nat} } });
    const x = try pool.internString("x");

    const is_even = try pool.mintPred(.{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{x}, .name = nm, .loc = 0 });
    const k = pool.keyOf(is_even).pred;
    try std.testing.expectEqual(sig, k.sig);
    try std.testing.expectEqual(InternPool.no_term, k.guard);
    try std.testing.expectEqual(@as(usize, 1), k.param_names.len);
    try std.testing.expectEqual(x, k.param_names[0]);
}

test "import: data = the .namespace it binds; minted (two imports of one ns are distinct)" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const f = try pool.intern(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });
    const ns = try pool.namespace(.universe, f);

    const nm = try pool.internString("P");
    const imp = try pool.mintImport(.{ .namespace = ns, .name = nm, .loc = 0 });
    const imp2 = try pool.mintImport(.{ .namespace = ns, .name = nm, .loc = 0 }); // same ns, distinct
    try std.testing.expect(imp != imp2); // minted → distinct
    try std.testing.expectEqual(ns, pool.keyOf(imp).import.namespace);
}

test "schema: locator [name, file, loc] minted fresh, round-trips" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const f = try pool.intern(.{ .file = .{ .path = try pool.internString("std/ind.bpa") } });
    const nm = try pool.internString("induction");
    const s = try pool.mintSchema(.{ .name = nm, .file = f, .loc = 42 });
    const s2 = try pool.mintSchema(.{ .name = nm, .file = f, .loc = 42 }); // distinct
    try std.testing.expect(s != s2); // minted → distinct
    const key = pool.keyOf(s).schema;
    try std.testing.expectEqual(nm, key.name);
    try std.testing.expectEqual(f, key.file);
    try std.testing.expectEqual(@as(u32, 42), key.loc);
    try std.testing.expectEqual(nm, pool.nameOf(s)); // nameOf serves .schema
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
    // reserved seeds: universe model (0) + "Prop" string (1) + Prop sort (2) + the 30
    // rule-word strings (3..32); then two more strings ("add", "zero").
    try std.testing.expectEqual(@as(usize, 35), pool.count());
}

test "universe model is seeded at Index 0 as its own parent" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    // reserved seeds: universe model (0) + "Prop" string (1) + Prop sort (2) + the 30
    // rule-word strings (3..32)
    try std.testing.expectEqual(@as(usize, 33), pool.count());
    try std.testing.expect(pool.keyOf(.prop).sort.refinement == null); // Prop is a root sort
    try std.testing.expectEqual(InternPool.Index.universe, pool.keyOf(.universe).model.parent);
    try std.testing.expectEqual(@as(usize, 0), pool.keyOf(.universe).model.overlay.len);
    // re-asking for the universe payload dedups back to Index 0
    try std.testing.expectEqual(InternPool.Index.universe, try pool.intern(.{ .model = .{ .parent = .universe } }));

    // a model whose parent is universe: distinct from universe, round-trips its parent
    const child = try pool.intern(.{ .model = .{ .parent = .universe } });
    // NOTE: with an empty overlay, this child has the SAME payload as universe {parent:0}
    // and therefore DEDUPS to universe. Distinct child models require a distinct parent or
    // a non-empty overlay (deferred). Assert the dedup is exactly that:
    try std.testing.expectEqual(InternPool.Index.universe, child);
}

test "composeModel is exact function composition, at any depth, through a parented inner" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var pool: InternPool = try .init(arena);
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    // symbols: any distinct Indexes serve (applyModel only compares sources).
    const a = try pool.internString("a");
    const b = try pool.internString("b");
    const c = try pool.internString("c");
    const d = try pool.internString("d");
    const e = try pool.internString("e");
    const f = try pool.internString("f");
    const g = try pool.internString("g");
    const p = try pool.internString("p");
    const q = try pool.internString("q");
    const all = [_]Index{ a, b, c, d, e, f, g, p, q };

    // inner = {a→b} PARENTED on {c→d}: its domain is {a, c}, and `c` lives ONLY in the parent
    // level — the case a top-overlay-only composition gets wrong.
    const inner_parent = try pool.intern(.{ .model = .{ .parent = .universe, .overlay = &.{.{ .src = c, .tgt = d }} } });
    const inner = try pool.intern(.{ .model = .{ .parent = inner_parent, .overlay = &.{.{ .src = a, .tgt = b }} } });
    try std.testing.expectEqual(d, pool.applyModel(inner, c)); // the parent level is live
    // outer maps inner's targets on (b→e, d→f) plus a source inner never touches (g→p).
    const outer = try pool.intern(.{ .model = .{ .parent = .universe, .overlay = &.{ .{ .src = b, .tgt = e }, .{ .src = d, .tgt = f }, .{ .src = g, .tgt = p } } } });

    // THE PROPERTY: composed(x) == outer(inner(x)) for every x — inner's top overlay (a→b→e),
    // inner's PARENT level (c→d→f), outer-only fallthrough (g→p), and unmapped (q→q).
    const composed = try pool.composeModel(io, outer, inner);
    for (all) |x| {
        try std.testing.expectEqual(pool.applyModel(outer, pool.applyModel(inner, x)), pool.applyModel(composed, x));
    }
    try std.testing.expectEqual(e, pool.applyModel(composed, a));
    try std.testing.expectEqual(f, pool.applyModel(composed, c)); // parent-level source composed, not dropped
    try std.testing.expectEqual(p, pool.applyModel(composed, g));
    try std.testing.expectEqual(q, pool.applyModel(composed, q));

    // A THIRD LAYER: composing with the (parented, composed) model as the AMBIENT still holds —
    // the associativity that makes nesting sound at any depth.
    const third = try pool.intern(.{ .model = .{ .parent = .universe, .overlay = &.{.{ .src = q, .tgt = a }} } });
    const composed2 = try pool.composeModel(io, composed, third);
    for (all) |x| {
        try std.testing.expectEqual(pool.applyModel(composed, pool.applyModel(third, x)), pool.applyModel(composed2, x));
    }
    try std.testing.expectEqual(e, pool.applyModel(composed2, q)); // q→a→b→e, three hops

    // structural interning: the same composition is the same model (stable namespace identity).
    try std.testing.expectEqual(composed, try pool.composeModel(io, outer, inner));
    // composing with the universe on either side is the identity on the other.
    try std.testing.expectEqual(pool.applyModel(inner, c), pool.applyModel(try pool.composeModel(io, .universe, inner), c));
}

test "namespace = (model, file), deduped per pair" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = try .init(arena_state.allocator());

    const f_int = try pool.intern(.{ .file = .{ .path = try pool.internString("std/integer.bpa") } });
    const f_nat = try pool.intern(.{ .file = .{ .path = try pool.internString("std/peano.bpa") } });

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
    const nm = try pool.internString("thm");

    // mintFact ALWAYS appends a fresh token — no dedup (identity/(ns,name) is FactKV's
    // job, not the pool's). Two mints, even same (kind, formula), are DISTINCT Indexes.
    const a = try pool.mintFact(.theorem, f1, nm, 0);
    const b = try pool.mintFact(.theorem, f1, nm, 0);
    try std.testing.expect(a != b);

    // a fact carries its kind AND its formula (in extra).
    try std.testing.expectEqual(InternPool.Key.Kind.theorem, pool.keyOf(a).fact.kind);
    try std.testing.expectEqual(f1, pool.keyOf(a).fact.formula);
    const x = try pool.mintFact(.axiom, f2, nm, 0);
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

    const a = try pool.intern(.{ .file = .{ .path = p_int } });
    const b = try pool.intern(.{ .file = .{ .path = p_nat } });
    const a2 = try pool.intern(.{ .file = .{ .path = p_int } }); // second importer, same file

    try std.testing.expectEqual(a, a2); // DEDUP: same path collapses to one Index
    try std.testing.expect(a != b); // distinct paths are distinct entities

    // round-trip: the Index reconstructs the original key (path StrId)
    try std.testing.expectEqual(p_int, pool.keyOf(a).file.path);
    try std.testing.expectEqual(p_nat, pool.keyOf(b).file.path);
    // a file entity's Index is distinct from its path's string Index (one id space)
    try std.testing.expect(@intFromEnum(a) != @intFromEnum(p_int));
}

test "dedup: lock-free readers never see a torn slot while a writer interns" {
    // THE regression gate for the lock-free `get`. Before the `Dedup` table, `get` probed a
    // `std.HashMapUnmanaged` while `intern` inserted into it on another thread; a rehash
    // swaps the map's header non-atomically and slots are written non-atomically, so a
    // reader could pull a torn `Index` out of a slot and fault inside `keyOf` — 2 runs in 6
    // on `check tests/cases/iff.bpa -j8`, debug build. Release hid it (no safety checks).
    //
    // Readers spin on keys interned BEFORE they started and must always get the same Index
    // back; meanwhile the writer interns thousands of fresh keys, forcing several growths.
    // Under the old map this crashes or returns a wrong Index within milliseconds.
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var pool: InternPool = try .init(arena);

    const n_known = 64;
    var known: [n_known]Index = undefined;
    var names: [n_known][8]u8 = undefined;
    for (&known, &names, 0..) |*ix, *nm, i| {
        _ = try std.fmt.bufPrint(nm, "k{d:0>6}", .{i});
        ix.* = try pool.internString(nm);
    }

    const Reader = struct {
        fn run(p: *InternPool, keys: *const [n_known]Index, nms: *const [n_known][8]u8, stop: *std.atomic.Value(bool), bad: *std.atomic.Value(u32)) void {
            var i: usize = 0;
            while (!stop.load(.acquire)) : (i +%= 1) {
                const k = i % n_known;
                // `get` is the lock-free probe under test
                const got = p.get(.{ .string = &nms[k] }) orelse {
                    _ = bad.fetchAdd(1, .monotonic);
                    continue;
                };
                if (got != keys[k]) _ = bad.fetchAdd(1, .monotonic);
            }
        }
    };
    var stop: std.atomic.Value(bool) = .init(false);
    var bad: std.atomic.Value(u32) = .init(0);
    var readers: [6]std.Thread = undefined;
    for (&readers) |*t| t.* = try std.Thread.spawn(.{}, Reader.run, .{ &pool, &known, &names, &stop, &bad });

    // the writer: thousands of fresh keys, growing the table several times over
    var buf: [16]u8 = undefined;
    var i: usize = 0;
    while (i < 20_000) : (i += 1) {
        const nm = try std.fmt.bufPrint(&buf, "fresh{d}", .{i});
        _ = try pool.internString(nm);
    }
    stop.store(true, .release);
    for (readers) |t| t.join();

    try std.testing.expectEqual(@as(u32, 0), bad.load(.acquire)); // every read exact
    // and the writer's keys all dedup to themselves afterwards
    i = 0;
    while (i < 20_000) : (i += 1000) {
        const nm = try std.fmt.bufPrint(&buf, "fresh{d}", .{i});
        try std.testing.expectEqual(try pool.internString(nm), pool.get(.{ .string = nm }).?);
    }
}
