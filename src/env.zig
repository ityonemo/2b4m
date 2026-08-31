//! The environment: entities (sorts, symbols, statements) are GLOBAL across
//! all loaded files — ids are meaningful everywhere, which is what makes
//! aliases views rather than copies. NAME RESOLUTION is per-file: each file
//! has its own scope mapping names to entity ids, plus its imported
//! namespaces. An alias just registers an existing entity id under a local
//! name.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("term.zig");
const kernel = @import("kernel.zig");
const SortId = term.SortId;
const SymId = term.SymId;
const TermId = term.TermId;
const ast = @import("ast.zig");

pub const FileId = enum(u32) { _ };

pub const Symbol = struct {
    name: StrId,
    kind: term.AppKind, // .app: func/const; .pred: predicate
    arg_sorts: []const SortId,
    /// result sort (the KERNEL/carrier sort); for predicates always .prop
    result: SortId,
    /// the result sort AS WRITTEN — a predicated result (`func op(...): H`) keeps
    /// its refined SortId here (while `result` is the carrier), so an application
    /// can surface the result postcondition `inH(op(...))`. Equals `result` for an
    /// unrefined result.
    result_refined: SortId = @enumFromInt(0),
    /// `requires` clause, elaborated with params as fvars (by param name)
    guard: ?TermId,
    /// `define`d symbols: the term every use transparently expands to
    /// (the kernel never sees the symbol itself)
    definition: ?TermId = null,
    /// param names, needed to substitute actuals into the guard
    param_names: []const StrId,
    loc: u32,
};

pub const StatementId = enum(u32) { _ };

pub const Statement = union(enum) {
    axiom: Fact,
    theorem: Fact,
    /// stored form: NOT elaborated until instantiated (comptime semantics)
    schema: Schema,

    pub const Fact = struct {
        name: StrId,
        formula: TermId,
        loc: u32,
        /// the file this fact was declared in (set by addStatement); used to
        /// render a hole's location in the rejection report.
        file: FileId = @enumFromInt(0),
        proven: bool = true,
        /// proven-by-trust: an imported theorem whose proof was NOT checked
        /// (no --recursive). Reported separately in the summary.
        trusted: bool = false,
        /// accelerated-tactic names this proof leaned on, transitively through
        /// citations (empty = every step kernel-checked). Disclosed in the summary; rejected
        /// by --pure.
        accelerated: []const StrId = &.{},
        /// a `hole` — an axiom-shaped placeholder for ASPIRATIONAL work: a claim
        /// stated up front so a proof can build on it before it is filled in
        /// (scaffolding), or a claim deliberately assumed to explore what follows
        /// ("suppose an odd perfect number exists; here are facts about it" —
        /// conditional reasoning). Accepted mechanically like an axiom, but
        /// default mode REJECTS any proof that (transitively) rests on one so the
        /// result is never mistaken for unconditional; `--draft` allows it.
        /// `is_hole` marks the declaration; `holes` lists the hole names a
        /// theorem depends on (transitively), for the rejection enumeration.
        is_hole: bool = false,
        holes: []const StrId = &.{},
        /// a `model`-materialized theorem (`Model$thm`): kernel-checked machinery,
        /// not authored — SUPPRESSED from the user-facing declaration/theorem count.
        synthetic: bool = false,
        /// the LOWERED kernel proof (steps + blocks), RETAINED for proven
        /// theorems so a `model` transfer can materialize a remapped copy in
        /// strict mode (remap each step's formula via remapFormula + translate
        /// its justification's ids through the model). Kernel steps are id-based,
        /// so the remap is clean (unlike the text-token AST). null for
        /// axioms/holes and for trusted (unchecked) imports. Arena-allocated.
        proof: ?LoweredProof = null,
    };

    /// A checked theorem's lowered kernel proof, retained for `model` transfer
    /// materialization. Mirrors the `kernel.Proof` shape (steps + blocks) but
    /// stored here to avoid an env->kernel import cycle; the fields are
    /// structurally the kernel's `Step`/`Block` slices.
    pub const LoweredProof = struct {
        steps: []const kernel.Step,
        blocks: []const kernel.Block,
    };
    pub const Schema = struct {
        name: StrId,
        params: []const ast.SchemaParam,
        body: *const ast.Expr,
        /// proof steps for a theorem-schema; re-elaborated per instantiation
        proof: ?[]const ast.Step,
        /// the defining file: its scope resolves the body/proof, and its
        /// source carries the diagnostics
        file: FileId,
        /// the defining file's source — the stored AST's tokens index into it
        source: []const u8,
        loc: u32,
    };
};

pub const FileScope = struct {
    sort_names: std.AutoHashMapUnmanaged(StrId, SortId) = .empty,
    sym_names: std.AutoHashMapUnmanaged(StrId, SymId) = .empty,
    statement_names: std.AutoHashMapUnmanaged(StrId, StatementId) = .empty,
    namespaces: std.AutoHashMapUnmanaged(StrId, FileId) = .empty,
};

/// A sort entity. METADATA (name, loc) is always present — root or refined.
/// `refinement` is an OPTIONAL component (ECS-style): null for a base/root sort
/// (`sort G`), present for a PREDICATED sort (`sort H = G where inH`), naming the
/// parent it refines and the guard qualifier(s). A refined SortId is an
/// elaborator-level bookkeeping id; it LOWERS to its carrier (root) sort before any
/// kernel term (see `carrierOf`/`qualifiersOf`).
pub const Sort = struct {
    name: StrId,
    loc: u32,
    refinement: ?Refinement = null,

    pub const Refinement = struct { parent: SortId, qualifiers: []const SymId };
};

pub const Env = struct {
    arena: Allocator,
    sorts: std.ArrayList(Sort) = .empty,
    syms: std.ArrayList(Symbol) = .empty,
    statements: std.ArrayList(Statement) = .empty,
    scopes: std.ArrayList(FileScope) = .empty,
    prop_name: StrId,

    /// Creates the builtin `Prop` sort entity (SortId 0). Files are added
    /// with `newFile`, each seeing `Prop` under its own scope.
    pub fn init(arena: Allocator, interner: *InternPool) !Env {
        var env: Env = .{ .arena = arena, .prop_name = try interner.internString("Prop") };
        try env.sorts.append(arena, .{ .name = env.prop_name, .loc = 0 });
        return env;
    }

    pub fn newFile(self: *Env) !FileId {
        const id: FileId = @enumFromInt(self.scopes.items.len);
        try self.scopes.append(self.arena, .{});
        try self.scopes.items[@intFromEnum(id)].sort_names.put(self.arena, self.prop_name, .prop);
        return id;
    }

    fn scope(self: *Env, file: FileId) *FileScope {
        return &self.scopes.items[@intFromEnum(file)];
    }

    // --- entity accessors (file-independent) ---

    pub fn sym(self: *const Env, id: SymId) Symbol {
        return self.syms.items[@intFromEnum(id)];
    }

    pub fn sortName(self: *const Env, interner: *const InternPool, id: SortId) []const u8 {
        return interner.stringBytes(self.sorts.items[@intFromEnum(id)].name);
    }

    // --- declaration (create entity + bind name in the declaring file) ---

    pub fn addSort(self: *Env, file: FileId, name: StrId, loc: u32) !SortId {
        const id: SortId = @enumFromInt(self.sorts.items.len);
        try self.sorts.append(self.arena, .{ .name = name, .loc = loc });
        try self.scope(file).sort_names.put(self.arena, name, id);
        return id;
    }

    /// A PREDICATED sort `sort H = G where inH`: a NEW SortId with a refinement
    /// component (parent + guard qualifiers), BOUND under `name`. Its own id is
    /// elaborator-level; it lowers to `carrierOf(id)` before any kernel term.
    pub fn addRefinedSort(self: *Env, file: FileId, name: StrId, loc: u32, parent: SortId, qualifiers: []const SymId) !SortId {
        const id = try self.addAnonymousRefinedSort(name, loc, parent, qualifiers);
        try self.scope(file).sort_names.put(self.arena, name, id);
        return id;
    }

    /// An ANONYMOUS refined sort (inline `x: G where inH`): a NEW refined SortId
    /// NOT bound to any name (so it never clobbers the base sort's name binding).
    /// `name` is display-only (typically the base sort's name).
    pub fn addAnonymousRefinedSort(self: *Env, name: StrId, loc: u32, parent: SortId, qualifiers: []const SymId) !SortId {
        const id: SortId = @enumFromInt(self.sorts.items.len);
        try self.sorts.append(self.arena, .{ .name = name, .loc = loc, .refinement = .{ .parent = parent, .qualifiers = qualifiers } });
        return id;
    }

    /// The KERNEL sort a (possibly refined) SortId lowers to: walk `parent` to the
    /// root (a sort with no refinement). A base sort is its own carrier.
    pub fn carrierOf(self: *const Env, id: SortId) SortId {
        var cur = id;
        while (self.sorts.items[@intFromEnum(cur)].refinement) |r| cur = r.parent;
        return cur;
    }

    /// The guard qualifiers accumulated along the refinement chain of a SortId
    /// (empty for a base sort). INNERMOST-refinement qualifiers first (walk order
    /// C→B→A yields [inC, inB] for `C = B where inC`, `B = A where inB`). Binder
    /// injection wraps each in turn, so the desugared formula reads outermost-first
    /// (`inB(c) -> inC(c) -> …`), matching the declaration order A→B→C.
    pub fn qualifiersOf(self: *const Env, arena: Allocator, id: SortId) ![]const SymId {
        var acc: std.ArrayList(SymId) = .empty;
        var cur = id;
        while (self.sorts.items[@intFromEnum(cur)].refinement) |r| {
            try acc.appendSlice(arena, r.qualifiers);
            cur = r.parent;
        }
        return acc.toOwnedSlice(arena);
    }

    /// Whether a SortId is refined (a predicated sort) — has a guard.
    pub fn isRefined(self: *const Env, id: SortId) bool {
        return self.sorts.items[@intFromEnum(id)].refinement != null;
    }

    pub fn addSym(self: *Env, file: FileId, symbol: Symbol) !SymId {
        const id: SymId = @enumFromInt(self.syms.items.len);
        try self.syms.append(self.arena, symbol);
        try self.scope(file).sym_names.put(self.arena, symbol.name, id);
        return id;
    }

    pub fn addStatement(self: *Env, file: FileId, name: StrId, stmt: Statement) !StatementId {
        const id: StatementId = @enumFromInt(self.statements.items.len);
        try self.statements.append(self.arena, stmt);
        // record the defining file on Facts (holes need it to render location)
        switch (self.statements.items[@intFromEnum(id)]) {
            .axiom, .theorem => |*fact| fact.file = file,
            .schema => {},
        }
        try self.scope(file).statement_names.put(self.arena, name, id);
        return id;
    }

    pub fn addNamespace(self: *Env, file: FileId, name: StrId, target: FileId) !void {
        try self.scope(file).namespaces.put(self.arena, name, target);
    }

    // --- aliasing (bind an EXISTING entity under a local name) ---

    pub fn registerSort(self: *Env, file: FileId, name: StrId, id: SortId) !void {
        try self.scope(file).sort_names.put(self.arena, name, id);
    }

    pub fn registerSym(self: *Env, file: FileId, name: StrId, id: SymId) !void {
        try self.scope(file).sym_names.put(self.arena, name, id);
    }

    pub fn registerStatement(self: *Env, file: FileId, name: StrId, id: StatementId) !void {
        try self.scope(file).statement_names.put(self.arena, name, id);
    }

    // --- per-file resolution ---

    pub fn findSort(self: *Env, file: FileId, name: StrId) ?SortId {
        return self.scope(file).sort_names.get(name);
    }

    pub fn findSym(self: *Env, file: FileId, name: StrId) ?SymId {
        return self.scope(file).sym_names.get(name);
    }

    pub fn findStatementId(self: *Env, file: FileId, name: StrId) ?StatementId {
        return self.scope(file).statement_names.get(name);
    }

    pub fn findStatement(self: *Env, file: FileId, name: StrId) ?*Statement {
        const id = self.findStatementId(file, name) orelse return null;
        return &self.statements.items[@intFromEnum(id)];
    }

    /// Every statement id visible in `file`'s scope (its own + aliased/imported
    /// names). Used by tactics that must scan a theory's lemmas rather than
    /// resolve one by a guessed name (e.g. `ext`'s apply-lemma collection).
    pub fn scopeStatements(self: *Env, file: FileId) []const StatementId {
        var out: std.ArrayList(StatementId) = .empty;
        var it = self.scope(file).statement_names.valueIterator();
        while (it.next()) |sid| out.append(self.arena, sid.*) catch return &.{};
        return out.items;
    }

    pub fn findNamespace(self: *Env, file: FileId, name: StrId) ?FileId {
        return self.scope(file).namespaces.get(name);
    }

    pub fn nameTaken(self: *Env, file: FileId, name: StrId) bool {
        const s = self.scope(file);
        return s.sort_names.contains(name) or s.sym_names.contains(name) or
            s.statement_names.contains(name) or s.namespaces.contains(name);
    }
};

// --- tests ---

const testing = std.testing;

test "refinement chain: C = B where inC, B = A where inB → carrier A, quals [inB, inC]" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var interner = try InternPool.init(arena);
    var env = try Env.init(arena, &interner);
    const file = try env.newFile();

    const a_name = try interner.internString("A");
    const b_name = try interner.internString("B");
    const c_name = try interner.internString("C");
    const inb_name = try interner.internString("inB");
    const inc_name = try interner.internString("inC");

    // sort A (root); pred inB(a: A); sort B = A where inB
    const a = try env.addSort(file, a_name, 0);
    const in_b = try env.addSym(file, .{
        .name = inb_name,
        .kind = .pred,
        .arg_sorts = try arena.dupe(SortId, &.{a}),
        .result = .prop,
        .guard = null,
        .param_names = &.{},
        .loc = 0,
    });
    const b = try env.addRefinedSort(file, b_name, 0, a, try arena.dupe(SymId, &.{in_b}));

    // pred inC(b: B) — arg over the REFINED B (its arg sort is the refined id here,
    // but carrierOf collapses it to A); sort C = B where inC
    const in_c = try env.addSym(file, .{
        .name = inc_name,
        .kind = .pred,
        .arg_sorts = try arena.dupe(SortId, &.{b}),
        .result = .prop,
        .guard = null,
        .param_names = &.{},
        .loc = 0,
    });
    const c = try env.addRefinedSort(file, c_name, 0, b, try arena.dupe(SymId, &.{in_c}));

    // C is A: walking parents from C lands on the root A.
    try testing.expectEqual(a, env.carrierOf(c));
    try testing.expectEqual(a, env.carrierOf(b));
    try testing.expectEqual(a, env.carrierOf(a)); // a base sort is its own carrier

    // C's guards accumulate the whole chain, INNERMOST first: [inC, inB]. (Binder
    // injection wraps each in turn, so the desugared formula reads inB -> inC -> …,
    // matching the A→B→C declaration order — verified at the language level.)
    const quals = try env.qualifiersOf(arena, c);
    try testing.expectEqual(@as(usize, 2), quals.len);
    try testing.expectEqual(in_c, quals[0]);
    try testing.expectEqual(in_b, quals[1]);

    // B has just [inB]; A (root) has none.
    const b_quals = try env.qualifiersOf(arena, b);
    try testing.expectEqual(@as(usize, 1), b_quals.len);
    try testing.expectEqual(in_b, b_quals[0]);
    try testing.expectEqual(@as(usize, 0), (try env.qualifiersOf(arena, a)).len);

    try testing.expect(env.isRefined(c));
    try testing.expect(env.isRefined(b));
    try testing.expect(!env.isRefined(a));
}
