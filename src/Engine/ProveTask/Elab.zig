//! Elab — walk-side EXPRESSION ELABORATION (Step 8, W4): an `ast.Expr` becomes a
//! scratchpad `term.Pool` term, with names resolved the DEMAND way and sorts/symbols
//! carried as POOL `Index`es. See memory `provetask-step-walk-design`.
//!
//! RESOLUTION ORDER for a name in an expression:
//!   1. expression-local binders (quantifier binders bound during THIS elaboration —
//!      innermost wins; they close into de Bruijn indices),
//!   2. proof-local binders (the Walk's LocalIdentKV: fix eigenvariables, unpack
//!      witnesses — elaborate as the binder's hygienic fvar at its sort),
//!   3. global identifiers via IdentKV `lookup` — the READ PASS already ran, so every
//!      global this expression references is `done`; an absent/in-flight entry here is
//!      diagnosed (defensively) as unresolved, not fetched.
//! Qualified `ns.name` resolves the import first (IdentKV, must be `done`), then the
//! base in the imported namespace.
//!
//! POOL-NATIVE SORTS: terms built here carry pool `Index`es in their `fvar.sort` /
//! `app.sym` fields (cast into the distinct `SortId`/`SymId` enums). `prop_sort` is the
//! pool's reserved Prop (`Index.prop`); at the demand flip `term.SortId.prop` renumbers
//! to the same value and the two spellings collapse.
//!
//! GUARDED FUNCTIONS (`requires`): a call to a guarded func emits its precondition — the stored
//! guard term with the param fvars (`#gN`) substituted by the actual args — as a proof obligation
//! into `tccs`, exactly as a refined param sort does (Step 3c). The guard was reified over `#gN`
//! fvars by FetchTask `reifyGuard`; here `emitGuardObligation` copies + substitutes it.
//!
//! NOT YET SUPPORTED (diagnosed, proof goes red; later layers/phases): lambdas (schema arguments
//! — schemas are unsupported wholesale).

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const SortId = term.SortId;
const TermId = term.TermId;
const Diagnostics = @import("../../diagnostics.zig");
const IdentKV = @import("../../IdentKV.zig");
const FactKV = @import("../../FactKV.zig");
const Walk = @import("Walk.zig");
const Schema = @import("Schema.zig");
const Context = @import("../../Context.zig");
const kernel = @import("../../kernel.zig");
const print = @import("../../print.zig");

const Elab = @This();

pub const Error = error{ Recover, OutOfMemory };
pub const Typed = struct { id: TermId, sort: SortId };
/// KNOWN PROPOSITIONS — the obligation-discharge table (memory `obligation-discharge-by-
/// identity`). A proposition enters when it is TAUGHT: a binder's refinement guard at a
/// `fix`/`unpack`, an `assume`'s hypothesis, every proved step's formula, a refined-RESULT
/// function's closure fact. A guarded application's REQUIRED proposition (`inH(arg)` for a refined
/// param sort, the substituted precondition of a `requires` func) is then LOOKED UP by canonical
/// identity (the proof pool is hash-consed: alpha-equal ⇔ same id) — never searched for by
/// content. Visibility is block-structured: an entry taught in block `b` is visible to a use in `b`
/// or any block nested in it; steps precede uses by construction (a step teaches after it is
/// appended). The teaching step is recorded so use-all-facts sees it consumed (`reachable`).
pub const Known = struct {
    /// the driving proof's kernel blocks (parent links), for the ancestor-or-self visibility test
    blocks: *const std.ArrayList(kernel.Block),
    entries: std.ArrayList(Teach) = .empty,
    /// proposition id -> its most recent entry (entries chain backwards via `next`)
    index: std.AutoHashMapUnmanaged(TermId, u32) = .empty,
    /// step indices a lookup consumed (use-all-facts reachability roots)
    reachable: std.ArrayList(u32) = .empty,
    /// set by a failed lookup; the driver rejects the step after its formula is elaborated
    missed: bool = false,
    /// the failed lookups of the current step, for the driver to SETTLE: under a model
    /// transfer the model's nominated dischargers may derive one (a closure fact instantiated
    /// for the term, deterministically from the nomination — `Prove.settleMisses`); what remains
    /// is diagnosed there as `unproved obligation`.
    misses: std.ArrayList(Miss) = .empty,

    pub const Teach = struct { prop: TermId, block: kernel.BlockId, step: ?u32, next: ?u32 };
    pub const Miss = struct { prop: TermId, loc: u32 };

    pub fn teach(self: *Known, arena: Allocator, prop: TermId, block: kernel.BlockId, step: ?u32) Allocator.Error!void {
        const idx: u32 = @intCast(self.entries.items.len);
        const gop = try self.index.getOrPut(arena, prop);
        try self.entries.append(arena, .{ .prop = prop, .block = block, .step = step, .next = if (gop.found_existing) gop.value_ptr.* else null });
        gop.value_ptr.* = idx;
    }

    /// The visible entry teaching `prop` for a use in block `kb`, if any.
    pub fn lookup(self: *const Known, prop: TermId, kb: kernel.BlockId) ?Teach {
        var cur = self.index.get(prop);
        while (cur) |i| {
            const t = self.entries.items[i];
            if (self.ancestorOrSelf(t.block, kb)) return t;
            cur = t.next;
        }
        return null;
    }

    fn ancestorOrSelf(self: *const Known, a: kernel.BlockId, b: kernel.BlockId) bool {
        var cur: ?kernel.BlockId = b;
        while (cur) |c| {
            if (c == a) return true;
            cur = self.blocks.items[@intFromEnum(c)].parent;
        }
        return false;
    }
};

/// The pool's reserved Prop sort, as a scratchpad SortId. Numerically `Index.prop`; the
/// flip renumbers `term.SortId.prop` onto it.
pub const prop_sort: SortId = @enumFromInt(@intFromEnum(InternPool.Index.prop));

arena: Allocator,
io: std.Io,
/// the owning Context — read-only here (the define-expansion pass that once ran through Elab
/// now runs BEFORE elaboration, over the AST; see Engine/Expand).
ctx: *Context,
interner: *InternPool,
idents: *IdentKV,
/// the task's term SCRATCHPAD — every term this elaboration builds lives here
scratch: *term.Pool,
sink: *Diagnostics.Sink,
source: []const u8,
/// proof-local binders (fix/unpack) resolve through the walk
walk: *const Walk,
/// the proving file's universe namespace — bare globals resolve here
ns: InternPool.Index,
/// hygienic fresh-name counter, owned by the driving task (proof-unique names)
fresh_counter: *u32,
/// SCHEMA PARAMS in scope while elaborating a schema body/steps (param name -> bound arg);
/// null in ordinary proofs. Consulted BEFORE the global lookup in name/call position: a
/// value param resolves to its term, a generator param BETA-REDUCES at a call. Set by the
/// instance ProveTask (post-init) on the Elab it uses for the schema body/steps.
schema_args: ?*const Schema.SchemaArgs = null,
/// MODEL this elaboration resolves THROUGH (Step 13): when set, every global identifier
/// resolved here is filtered `interner.applyModel(model, source)` — so proving a source
/// theorem in model M's namespace remaps `op`→`add` etc. Null (`.universe` at the call
/// site) in an ordinary proof = identity. Set by the model ProveTask on its Elab.
model: InternPool.Index = .universe,
/// SOURCE SPACE: this Elab builds the un-remapped term of a formula whose proof runs under a
/// model transfer (`model` is the universe here; the driving Prove's is not). Proof-local
/// binders were bound in TARGET space (their fvar sort is the model's image), so in this mode
/// a local resolves at its recorded SOURCE sort (`BinderInfo.source_sort`) — otherwise a
/// source symbol's parameter (`Src`) would be checked against a target-sorted fvar (`Tgt`).
/// Set by `Prove.sourceElab`; the accelerant producers' inputs are built this way.
source_space: bool = false,
/// NO_RELATIVIZE (13e): set when elaborating a SYNTHETIC (accelerant-generated) schema's
/// formulas — they were DELABORATED from already-elaborated terms, so refined-sort guard
/// injection at binders must be SKIPPED (it would double the guards). Parsed schemas keep
/// injection (their AST is source text, not a round-trip).
no_relativize: bool = false,
/// The driving Prove's known-proposition table (see `Known`) and the block a use in this
/// elaboration sits in. Null `known` = obligations not checked (a source-space pass, a throwaway
/// sort-resolution Elab, the read pass — the process pass re-elaborates and checks).
known: ?*Known = null,
known_block: kernel.BlockId = @enumFromInt(0),
/// FORMULA-LOCAL knowledge: an antecedent `P -> …` teaches its consequent, `P and …` its right
/// conjunct. Pushed when the scope opens, popped when it closes — no relativization of anything.
/// (A binder teaches nothing: a proposition about a bound element is never owed, see
/// `requireKnown`.)
local_known: std.ArrayList(TermId) = .empty,
/// STATEMENT (goal) phase: elaborating a fact's STATED formula rather than a proof step. A
/// statement is a CLAIM and carries no obligation of either kind (a `requires` precondition or a
/// refined-sort argument guard): the proof step that writes the guarded term owes its guard
/// there, where something can teach it — a stated law over a bound element (`∀k: NonNeg;
/// … sumUpTo(s, succ(k)) …`) has nothing that could teach `nonneg(succ(k))` at statement level.
/// (User ruling 2026-09-13: "only the proof steps carry the guards".)
in_statement: bool = false,

/// expression-local binders (quantifiers), innermost last; transient per elaboration
scope: std.ArrayList(ScopeEntry) = .empty,

const ScopeEntry = struct { name: StrId, sort: SortId, fvar: StrId };

pub fn init(
    arena: Allocator,
    io: std.Io,
    ctx: *Context,
    interner: *InternPool,
    idents: *IdentKV,
    scratch: *term.Pool,
    sink: *Diagnostics.Sink,
    source: []const u8,
    walk: *const Walk,
    ns: InternPool.Index,
    fresh_counter: *u32,
) Elab {
    return .{
        .arena = arena,
        .io = io,
        .ctx = ctx,
        .interner = interner,
        .idents = idents,
        .scratch = scratch,
        .sink = sink,
        .source = source,
        .walk = walk,
        .ns = ns,
        .fresh_counter = fresh_counter,
    };
}

/// Elaborate to any sort. Callers wanting a proposition wrap with `requireProp`.
///
/// DE-RECURSIFIED (task #92): the surface-expression spine (`.binary`, `.not`, `.quant`) is
/// walked by an EXPLICIT heap work-stack so a pathologically deep nesting (e.g. `not not …`,
/// long `and`-chains, deep quantifier prefixes) cannot overflow the C stack. Each `Frame` is a
/// "what to do next" continuation; a parallel `results` stack holds finished `Typed` values in
/// post-order. Leaf forms (`.name`/`.call`/`.lambda`) dispatch directly.
///
/// NOTE ON `.call` ARGS: `elaborateCall` still elaborates each argument by a RECURSIVE call
/// into this function (each spins up its own bounded work-stack). Argument nesting therefore
/// still consumes one Zig frame per call-nesting level (`f(f(f(…)))`); the connective/quantifier
/// spine — the dominant deep-nesting driver in practice — is fully iterative. Converting call
/// args too would drag the whole intricate name/define/schema resolution into the stack; the
/// task explicitly permits leaving `elaborateCall` recursive on args.
pub fn elaborateExpr(self: *Elab, root: *const ast.Expr) Error!Typed {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();

    var frames: std.ArrayList(Frame) = .empty;
    var results: std.ArrayList(Typed) = .empty;
    try frames.append(wa, .{ .elaborate = root });

    while (frames.pop()) |frame| switch (frame) {
        .elaborate => |e| switch (e.*) {
            // leaf forms — resolve directly onto the results stack.
            .name => |tok| try results.append(wa, try self.elaborateName(tok)),
            .call => |c| try results.append(wa, try self.elaborateCall(c)),
            .lambda => |l| return self.fail(l.tok.start, "lambdas (schema arguments) are not supported by the demand prover", .{}),

            .not => |n| {
                // finish AFTER the operand, then push the operand.
                try frames.append(wa, .{ .finish_not = n });
                try frames.append(wa, .{ .elaborate = n.operand });
            },

            .binary => |b| switch (b.op) {
                .equal, .not_equal => {
                    // `=`/`!=`: elaborate lhs THEN rhs (no obligation window), then compare.
                    try frames.append(wa, .{ .finish_eq = b });
                    try frames.append(wa, .{ .elaborate = b.rhs });
                    try frames.append(wa, .{ .elaborate = b.lhs });
                },
                .iff => {
                    // SURFACE SUGAR `P iff Q` → `(P -> Q) and (Q -> P)`. No TCC window (matches
                    // the original: iff snapshots nothing).
                    try frames.append(wa, .{ .finish_iff = b });
                    try frames.append(wa, .{ .elaborate = b.rhs });
                    try frames.append(wa, .{ .elaborate = b.lhs });
                },
                .implies, .and_op, .or_op => {
                    // LHS must FULLY elaborate before the TCC window opens for the RHS. So:
                    // push a mid-frame that (after LHS is on the results stack) opens the
                    // window and pushes the RHS + the finisher. Order on the stack (LIFO):
                    // elaborate(lhs) runs first, then open_binary_rhs.
                    try frames.append(wa, .{ .open_binary_rhs = b });
                    try frames.append(wa, .{ .elaborate = b.lhs });
                },
            },

            .quant => |q| {
                // ENTER: resolve the shared binder sort, compute quals, push scope entries,
                // snapshot the TCC/result-fact windows — then elaborate the body, then LEAVE.
                const refined = try self.resolveBinderSort(q.binders[0]);
                const sort: SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(refined)))));
                // NO_RELATIVIZE (13e): a SYNTHETIC schema's formulas are DELABORATED from
                // already-elaborated (already-relativized) terms — re-injecting guards here would
                // DOUBLE them (`inH(x) -> inH(x) -> …`). The faithful round-trip skips injection.
                const quals: []const InternPool.Index = if (self.no_relativize) &.{} else self.interner.qualifiersOf(self.arena, @enumFromInt(@intFromEnum(refined))) catch return error.OutOfMemory;
                const fresh = try self.arena.alloc(StrId, q.binders.len);
                const mark = self.scope.items.len;
                for (q.binders, fresh) |b, *fr| {
                    const bname = try self.localName(b.name);
                    try self.checkNoShadow(bname, b.name);
                    fr.* = try self.freshNamed(bname);
                    try self.scope.append(self.arena, .{ .name = bname, .sort = sort, .fvar = fr.* });
                }
                try frames.append(wa, .{ .finish_quant = .{
                    .q = q,
                    .sort = sort,
                    .quals = quals,
                    .fresh = fresh,
                    .mark = mark,
                } });
                try frames.append(wa, .{ .require_prop_body = q.body });
                try frames.append(wa, .{ .elaborate = q.body });
            },
        },

        .open_binary_rhs => |b| {
            // LHS is now the TOP of the results stack (fully elaborated). Require prop, open the
            // TCC window, then elaborate the RHS and finish.
            const lhs = try self.requireProp(results.items[results.items.len - 1], b.lhs);
            results.items[results.items.len - 1] = lhs;
            // an antecedent / left conjunct is KNOWN while the rest of the formula elaborates.
            const taught = b.op == .implies or b.op == .and_op;
            if (taught) try self.local_known.append(self.arena, lhs.id);
            try frames.append(wa, .{ .finish_binary = .{ .b = b, .taught = taught } });
            try frames.append(wa, .{ .require_prop_rhs = b.rhs });
            try frames.append(wa, .{ .elaborate = b.rhs });
        },

        .require_prop_rhs => |e| {
            const rhs = try self.requireProp(results.items[results.items.len - 1], e);
            results.items[results.items.len - 1] = rhs;
        },

        .require_prop_body => |e| {
            const body = try self.requireProp(results.items[results.items.len - 1], e);
            results.items[results.items.len - 1] = body;
        },

        .finish_binary => |f| {
            const b = f.b;
            const rhs = results.pop().?;
            const lhs = results.pop().?;
            if (f.taught) _ = self.local_known.pop();
            const op: term.BinOp = switch (b.op) {
                .implies => .implies,
                .and_op => .and_op,
                .or_op => .or_op,
                else => unreachable,
            };
            const id = try self.scratch.add(.{ .bin = .{ .op = op, .lhs = lhs.id, .rhs = rhs.id } });
            try results.append(wa, .{ .id = id, .sort = prop_sort });
        },

        .finish_iff => |b| {
            const rhs = try self.requireProp(results.pop().?, b.rhs);
            const lhs = try self.requireProp(results.pop().?, b.lhs);
            const fwd = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = lhs.id, .rhs = rhs.id } });
            const bwd = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = rhs.id, .rhs = lhs.id } });
            const id = try self.scratch.add(.{ .bin = .{ .op = .and_op, .lhs = fwd, .rhs = bwd } });
            try results.append(wa, .{ .id = id, .sort = prop_sort });
        },

        .finish_eq => |b| {
            const rhs = results.pop().?;
            const lhs = results.pop().?;
            if (lhs.sort == prop_sort) {
                return self.fail(exprLoc(b.lhs), "'=' compares terms, not propositions", .{});
            }
            if (rhs.sort != lhs.sort) {
                return self.fail(exprLoc(b.rhs), "expected sort '{s}', got '{s}'", .{
                    self.sortName(lhs.sort), self.sortName(rhs.sort),
                });
            }
            const eq = try self.scratch.add(.{ .eq = .{ .lhs = lhs.id, .rhs = rhs.id } });
            const id = if (b.op == .not_equal) try self.scratch.add(.{ .not = eq }) else eq;
            try results.append(wa, .{ .id = id, .sort = prop_sort });
        },

        .finish_not => |n| {
            const inner = try self.requireProp(results.pop().?, n.operand);
            const id = try self.scratch.add(.{ .not = inner.id });
            try results.append(wa, .{ .id = id, .sort = prop_sort });
        },

        .finish_quant => |f| {
            // LEAVE: the body is on the results stack (already require-prop'd). Pop scope, then
            // build the quantifier prefix + relativize the windows exactly as the recursion did.
            const q = f.q;
            const body = results.pop().?;
            self.scope.shrinkRetainingCapacity(f.mark);
            var id = body.id;
            var i = q.binders.len;
            while (i > 0) {
                i -= 1;
                // inject the binder's guard: the CONJUNCTION of its qualifiers (canonical —
                // matches the kernel's guarded-fix forall_intro derivation and bindProofVar),
                // as a single `guard -> body` (∀) / `guard and body` (∃).
                if (try self.conjoinQuals(f.quals, f.fresh[i], f.sort)) |guard| {
                    const connective: term.BinOp = if (q.q == .forall) .implies else .and_op;
                    id = try self.scratch.add(.{ .bin = .{ .op = connective, .lhs = guard, .rhs = id } });
                }
                id = try self.scratch.close(id, f.fresh[i]);
                id = try self.scratch.add(.{ .quant = .{
                    .q = if (q.q == .forall) .forall else .exists,
                    .sort = f.sort,
                    .hint = tokName(q.binders[i].name),
                    .body = id,
                } });
            }
            try results.append(wa, .{ .id = id, .sort = prop_sort });
        },
    };

    std.debug.assert(results.items.len == 1);
    return results.items[0];
}

/// A work-stack continuation for `elaborateExpr` (de-recursified spine, task #92). Popped LIFO:
/// an `.elaborate` frame decomposes an expr, pushing its finisher THEN its children so children
/// are processed first and their `Typed` results sit on the results stack when the finisher runs.
const Frame = union(enum) {
    /// decompose an expression (leaf → result; compound → push finisher + children).
    elaborate: *const ast.Expr,
    /// LHS of a prop binary is done (top of results); require-prop it, open the RHS TCC window.
    open_binary_rhs: ast.Expr.Binary,
    /// require the top-of-results value to be a proposition (RHS of a binary).
    require_prop_rhs: *const ast.Expr,
    /// require the top-of-results value to be a proposition (quantifier body).
    require_prop_body: *const ast.Expr,
    /// build the prop binary node; pop the LHS from the formula-local knowledge if it taught.
    finish_binary: struct { b: ast.Expr.Binary, taught: bool },
    /// desugar `iff` into `(P->Q) and (Q->P)`.
    finish_iff: ast.Expr.Binary,
    /// build the `eq`/`not eq` node with sort-checks.
    finish_eq: ast.Expr.Binary,
    /// build the `not` node.
    finish_not: @FieldType(ast.Expr, "not"),
    /// LEAVE a quantifier: pop scope, build the binder prefix.
    finish_quant: struct {
        q: @FieldType(ast.Expr, "quant"),
        sort: SortId,
        quals: []const InternPool.Index,
        fresh: []StrId,
        mark: usize,
    },
};

pub fn requireProp(self: *Elab, typed: Typed, e: *const ast.Expr) Error!Typed {
    if (typed.sort != prop_sort) {
        return self.fail(exprLoc(e), "expected a proposition, got a term of sort '{s}'", .{self.sortName(typed.sort)});
    }
    return typed;
}

// -- name resolution -------------------------------------------------------------------

fn elaborateName(self: *Elab, tok: lexer.Token) Error!Typed {
    // a resolved-symbol token is a global by construction — never a local of any kind.
    if (tok.tag == .symbol) return self.elaborateSymRef(tok, self.ns, tok.name);
    if (tok.qualifier != InternPool.Index.none) {
        const target = try self.resolveQualified(tok);
        return self.elaborateSymRef(tok, target.ns, target.base);
    }
    const name = tokName(tok);
    // 1. expression-local quantifier binders (innermost wins)
    var i = self.scope.items.len;
    while (i > 0) {
        i -= 1;
        const entry = self.scope.items[i];
        if (entry.name == name) {
            const id = try self.scratch.add(.{ .fvar = .{ .name = entry.fvar, .sort = entry.sort } });
            return .{ .id = id, .sort = entry.sort };
        }
    }
    // 2. proof-local binders (fix eigenvariables / unpack witnesses)
    if (self.walk.findIdent(name)) |local| {
        // a source-space pass sees the binder at its SOURCE sort (see `source_space`).
        const sort = if (self.source_space) local.info.source_sort else local.info.sort;
        const id = try self.scratch.add(.{ .fvar = .{ .name = local.info.fvar, .sort = sort } });
        return .{ .id = id, .sort = sort };
    }
    // 3. schema parameter (only while elaborating a schema body/steps)
    if (self.schema_args) |sa| if (sa.get(name)) |arg| switch (arg) {
        .value => |v| return .{ .id = v.id, .sort = v.sort },
        .lambda => return self.fail(tok.start, "schema parameter '{s}' needs arguments", .{self.text(tok)}),
    };
    // 4. global
    return self.elaborateSymRef(tok, self.ns, name);
}

/// A resolved global in NAME position (no written arguments): a constant or a nullary
/// func/pred applies bare; anything wanting arguments (or that isn't a value) errors.
fn elaborateSymRef(self: *Elab, tok: lexer.Token, ns: InternPool.Index, name: StrId) Error!Typed {
    const sym = self.resolveSymbolTok(tok) orelse self.lookupIdent(ns, name) orelse {
        return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
    };
    switch (self.interner.keyOf(sym)) {
        .func, .pred => |c| {
            const sig = self.interner.keyOf(c.sig).sig;
            if (sig.args.len != 0) {
                return self.fail(tok.start, "'{s}' expects {d} argument(s), got 0", .{ self.text(tok), sig.args.len });
            }
            // a nullary guarded func (guard over globals only, no params) still owes its
            // precondition here; a guarded func WITH params can't reach name position (the
            // arg-count check above already rejected it).
            try self.emitGuardObligation(c.guard, &.{}, tok.start);
            return self.applyResolved(sym, &.{});
        },
        // a constant is a nullary application — route through applyResolved so a REFINED
        // result sort (`const E: H`) surfaces its closure fact `inH(E)` (Step 3c).
        .constant => return self.applyResolved(sym, &.{}),
        .sort => return self.fail(tok.start, "'{s}' is a sort, not a value", .{self.text(tok)}),
        .import => return self.fail(tok.start, "'{s}' is a namespace, not a value", .{self.text(tok)}),
        else => return self.fail(tok.start, "'{s}' cannot appear in an expression", .{self.text(tok)}),
    }
}

fn elaborateCall(self: *Elab, c: ast.Expr.Call) Error!Typed {
    const dotted = c.callee.tag != .symbol and c.callee.qualifier != InternPool.Index.none;
    const target = if (dotted)
        try self.resolveQualified(c.callee)
    else
        Qualified{ .ns = self.ns, .base = tokName(c.callee) };
    // schema GENERATOR param in call position: beta-reduce (only a bare name is a param).
    if (!dotted) if (self.schema_args) |sa| if (sa.get(target.base)) |arg| switch (arg) {
        .lambda => |lam| return self.applyGeneratorParam(c, lam),
        .value => return self.fail(c.callee.start, "schema parameter '{s}' takes no arguments", .{self.text(c.callee)}),
    };
    const sym = self.resolveSymbolTok(c.callee) orelse self.lookupIdent(target.ns, target.base) orelse {
        return self.fail(c.callee.start, "unknown identifier '{s}'", .{self.text(c.callee)});
    };
    const callable = switch (self.interner.keyOf(sym)) {
        .func, .pred => |cb| cb,
        else => return self.fail(c.callee.start, "'{s}' is not callable", .{self.text(c.callee)}),
    };
    const sig = self.interner.keyOf(callable.sig).sig;
    if (sig.args.len != c.args.len) {
        return self.fail(c.callee.start, "'{s}' expects {d} argument(s), got {d}", .{
            self.text(c.callee), sig.args.len, c.args.len,
        });
    }
    const arg_ids = try self.arena.alloc(TermId, c.args.len);
    for (c.args, sig.args, arg_ids) |arg, expected_ix, *out| {
        const typed = try self.elaborateExpr(arg);
        // compare at the CARRIER (refined sorts lower before kernel terms)
        const expected: SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(expected_ix)));
        const actual: SortId = if (typed.sort == prop_sort)
            typed.sort // prop args are rejected by the mismatch below
        else
            @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort)))));
        if (actual != expected) {
            return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                self.sortName(expected), self.sortName(typed.sort),
            });
        }
        // a REFINED param sort demands `inH(arg)` — a proof obligation (Step 3c).
        try self.emitArgObligations(expected_ix, typed.id, exprLoc(arg));
        out.* = typed.id;
    }
    // a GUARDED func demands its (substituted) precondition — the TCC that forbids `div(x, 0)`
    // (mirrors the refined-sort obligation above). Emitted AFTER the args, so a nested guarded
    // arg's obligation is reported before the outer one.
    try self.emitGuardObligation(callable.guard, arg_ids, c.callee.start);
    return self.applyResolved(sym, arg_ids);
}

/// A GUARDED function's precondition, instantiated at a call's actual arguments, is REQUIRED
/// (the obligation that forbids `div(x, 0)`). The stored guard is a term over the hygienic `#gN`
/// param fvars (see FetchTask `reifyGuard`): copy it into the scratchpad, `substFvar` each `#gi`
/// with the corresponding actual arg term (capture-safe — `#` cannot lex, so no userland arg fvar
/// collides), and look the closed result up. No-op for an unguarded func (`no_term`).
fn emitGuardObligation(self: *Elab, guard: InternPool.TermOff, args: []const TermId, loc: u32) Error!void {
    if (guard == InternPool.no_term) return;
    if (self.known == null) return;
    // a STATEMENT carries no obligation of either kind (user ruling 2026-09-13: a statement is a
    // claim; the proof step that writes the term owes its guard) — same as `emitArgObligations`.
    if (self.in_statement) return;
    try self.requireKnown(try self.guardProposition(guard, args), loc);
}

/// A `requires` guard (a stored term over the hygienic `#gN` param fvars) at actual `args`.
pub fn guardProposition(self: *Elab, guard: InternPool.TermOff, args: []const TermId) Error!TermId {
    var g = self.scratch.copyIn(self.interner, guard) catch return error.OutOfMemory;
    for (args, 0..) |arg, i| {
        const bytes = std.fmt.allocPrint(self.arena, "#g{d}", .{i}) catch return error.OutOfMemory;
        const fv = self.interner.internString(bytes) catch return error.OutOfMemory;
        g = self.scratch.substFvar(g, fv, arg) catch return error.OutOfMemory;
    }
    return g;
}

/// The obligations a TERM owes, appended to `out` (deduplicated by identity, first-seen
/// order): at every application, a refined param's qualifier applied to the arg, and a
/// `requires` guard at the args — for LOCALLY CLOSED subterms only (a proposition over a bound
/// variable belongs to the statement that binds it). Iterative walk; no lookup, no diagnosis —
/// the reading half of `requireKnown`, for a producer that must STATE its synthetic's
/// preconditions (`Prove.wrapObligations`).
pub fn collectObligations(self: *Elab, root: TermId, out: *std.ArrayList(TermId), respect_local: bool) Error!void {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    // each frame carries the FORMULA-LOCAL knowledge on its path (the same rule `requireKnown`
    // applies while elaborating: an antecedent `P -> …` teaches its consequent, `P and …` its
    // right conjunct) — an obligation that formula already discharges is not the caller's.
    const Visit = struct { id: TermId, local: []const TermId };
    var stack: std.ArrayList(Visit) = .empty;
    try stack.append(wa, .{ .id = root, .local = &.{} });
    while (stack.pop()) |f| {
        const node = self.scratch.get(f.id);
        switch (node) {
            .app, .pred => |ap| {
                const callable = switch (self.interner.keyOf(@enumFromInt(@intFromEnum(ap.sym)))) {
                    .func, .pred => |cb| cb,
                    else => null,
                };
                if (callable) |cb| {
                    const sig = self.interner.keyOf(cb.sig).sig;
                    var all_closed = true;
                    for (ap.args, sig.args) |arg, expected| {
                        const closed = self.scratch.isLocallyClosed(arg);
                        if (!closed) all_closed = false;
                        if (closed and self.interner.isRefined(expected)) {
                            const quals = self.interner.qualifiersOf(self.arena, expected) catch return error.OutOfMemory;
                            for (quals) |q| try self.appendUnlessLocal(out, f.local, try self.qualifierApp(q, arg));
                        }
                    }
                    if (cb.guard != InternPool.no_term and all_closed) {
                        try self.appendUnlessLocal(out, f.local, try self.guardProposition(cb.guard, ap.args));
                    }
                }
                for (ap.args) |x| try stack.append(wa, .{ .id = x, .local = f.local });
            },
            .bin => |b| {
                try stack.append(wa, .{ .id = b.lhs, .local = f.local });
                const rhs_local = if (respect_local and (b.op == .implies or b.op == .and_op))
                    try std.mem.concat(wa, TermId, &.{ f.local, &.{b.lhs} })
                else
                    f.local;
                try stack.append(wa, .{ .id = b.rhs, .local = rhs_local });
            },
            .eq => |p| {
                try stack.append(wa, .{ .id = p.lhs, .local = f.local });
                try stack.append(wa, .{ .id = p.rhs, .local = f.local });
            },
            .not => |t| try stack.append(wa, .{ .id = t, .local = f.local }),
            .quant => |q| try stack.append(wa, .{ .id = q.body, .local = f.local }),
            .bvar, .fvar => {},
        }
    }
}

fn appendUnlessLocal(self: *const Elab, out: *std.ArrayList(TermId), local: []const TermId, p: TermId) Allocator.Error!void {
    for (local) |k| if (self.conjunctOf(k, p)) return;
    try appendUnique(self.arena, out, p);
}

fn appendUnique(arena: Allocator, out: *std.ArrayList(TermId), p: TermId) Allocator.Error!void {
    for (out.items) |x| if (x == p) return;
    try out.append(arena, p);
}

/// For a refined param sort, REQUIRE `qpred(arg)` (one per qualifier). No-op for a root param
/// sort or when obligations aren't checked.
fn emitArgObligations(self: *Elab, param_sort: InternPool.Index, arg: TermId, loc: u32) Error!void {
    if (self.known == null) return;
    // a refined-sort argument obligation is NOT enforced in the statement phase (see `in_statement`).
    if (self.in_statement) return;
    if (!self.interner.isRefined(param_sort)) return;
    const quals = self.interner.qualifiersOf(self.arena, param_sort) catch return error.OutOfMemory;
    for (quals) |qpred| try self.requireKnown(try self.qualifierApp(qpred, arg), loc);
}

/// The one discharge: is `prop` KNOWN here? Formula-local knowledge first (identity), then the
/// proof's table from this use's block. A hit through a proved step marks that step reachable;
/// a miss is reported once at the use and flags the driver to reject the step.
/// The members of `root`'s `and`-tree, root included (iterative). A hypothesis makes every
/// conjunct known — and-elimination is structural, not a search.
pub fn conjuncts(self: *Elab, root: TermId, out: *std.ArrayList(TermId)) Allocator.Error!void {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, root);
    while (stack.pop()) |cur| {
        try out.append(self.arena, cur);
        const node = self.scratch.get(cur);
        if (node == .bin and node.bin.op == .and_op) {
            try stack.append(wa, node.bin.rhs);
            try stack.append(wa, node.bin.lhs);
        }
    }
}

/// Is `prop` a member of `k`'s `and`-tree (k itself included)?
fn conjunctOf(self: *const Elab, k: TermId, prop: TermId) bool {
    var fb = std.heap.stackFallback(64 * @sizeOf(TermId), self.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, k) catch return false;
    while (stack.pop()) |cur| {
        if (cur == prop) return true;
        const node = self.scratch.get(cur);
        if (node == .bin and node.bin.op == .and_op) {
            stack.append(a, node.bin.rhs) catch return false;
            stack.append(a, node.bin.lhs) catch return false;
        }
    }
    return false;
}

fn requireKnown(self: *Elab, prop: TermId, loc: u32) Error!void {
    const known = self.known orelse return;
    // a proposition about a BOUND element (its subject mentions one of this formula's
    // quantifier binders, still open as a scope fvar while the body elaborates) is not owed:
    // a quantified formula is a CLAIM about all its elements, like a statement (user ruling
    // 2026-09-13); the step that uses a specific element — a `fix`-var, a constant — owes it.
    for (self.scope.items) |entry| if (self.scratch.occursFree(prop, entry.fvar)) return;
    for (self.local_known.items) |k| if (self.conjunctOf(k, prop)) return;
    if (known.lookup(prop, self.known_block)) |t| {
        if (t.step) |s| known.reachable.append(self.arena, s) catch return error.OutOfMemory;
        return;
    }
    known.misses.append(self.arena, .{ .prop = prop, .loc = loc }) catch return error.OutOfMemory;
    known.missed = true;
}

/// Render a proposition for a diagnostic.
pub fn renderProp(self: *Elab, prop: TermId) Error![]const u8 {
    return print.render(self.arena, self.scratch, self.interner, prop) catch return error.OutOfMemory;
}

/// Apply a schema GENERATOR param at a call site: elaborate each actual, sort-check against
/// the param's `arg_sorts`, then BETA-REDUCE the kept-free param body — `substFvar` each
/// `params[i]` fvar with the actual. Simultaneous-safe: the param fvars are fresh/distinct
/// hygienic names and the actuals are locally closed, so sequential subst can't capture.
fn applyGeneratorParam(self: *Elab, c: ast.Expr.Call, lam: @FieldType(Schema.SchemaArg, "lambda")) Error!Typed {
    if (c.args.len != lam.arg_sorts.len) {
        return self.fail(c.callee.start, "schema parameter '{s}' expects {d} argument(s), got {d}", .{
            self.text(c.callee), lam.arg_sorts.len, c.args.len,
        });
    }
    var reduced = lam.body;
    for (c.args, lam.arg_sorts, lam.params) |arg, expected_sort, param_fvar| {
        const typed = try self.elaborateExpr(arg);
        const expected: SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(expected_sort)))));
        const actual: SortId = if (typed.sort == prop_sort)
            typed.sort
        else
            @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort)))));
        if (actual != expected) {
            return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                self.sortName(expected_sort), self.sortName(typed.sort),
            });
        }
        reduced = try self.scratch.substFvar(reduced, param_fvar, typed.id);
    }
    return .{ .id = reduced, .sort = lam.result_sort };
}

/// Build the app/pred node for a resolved callable symbol; result sort from its sig.
/// A refined RESULT sort SURFACES its closure facts `inH(result)` (an available discharger
/// for later obligations — e.g. `op(h,h): H` lets `f(op(h,h))` type-check).
fn applyResolved(self: *Elab, sym: InternPool.Index, args: []const TermId) Error!Typed {
    const kind: term.AppKind = switch (self.interner.keyOf(sym)) {
        .pred => .pred,
        else => .app,
    };
    const id = try self.scratch.addApp(kind, @enumFromInt(@intFromEnum(sym)), args);
    const result: SortId = @enumFromInt(@intFromEnum(self.interner.symResult(sym)));
    // a REFINED result sort TEACHES the application its closure fact `inH(f(…))` — a universal
    // truth about that term, so it is known proof-wide (the root block).
    if (self.known) |known| {
        const result_ix: InternPool.Index = @enumFromInt(@intFromEnum(result));
        if (self.interner.isRefined(result_ix)) {
            const quals = self.interner.qualifiersOf(self.arena, result_ix) catch return error.OutOfMemory;
            for (quals) |qpred| try known.teach(self.arena, try self.qualifierApp(qpred, id), @enumFromInt(0), null);
        }
    }
    return .{ .id = id, .sort = result };
}

/// Resolve a binder's sort to its pool sort Index. A plain binder → the (possibly refined)
/// sort. An INLINE-refined binder `x: S where inH` → an ANONYMOUS refined sort narrowing S
/// by the guard pred (minted fresh, no IdentKV name).
pub fn resolveBinderSort(self: *Elab, b: ast.Binder) Error!SortId {
    const base = try self.resolveSortTok(b.sort);
    const g = b.guard orelse return base;
    const gname = try self.localName(g);
    const gpred = self.resolveSymbolTok(g) orelse self.lookupIdent(self.ns, gname) orelse {
        return self.fail(g.start, "sort refinement '{s}' is not a predicate in scope", .{self.text(g)});
    };
    const carrier = self.interner.carrierOf(@enumFromInt(@intFromEnum(base)));
    const cb = switch (self.interner.keyOf(gpred)) {
        .pred => |c| c,
        else => return self.fail(g.start, "sort refinement '{s}' must be a unary predicate", .{self.text(g)}),
    };
    const sig = self.interner.keyOf(cb.sig).sig;
    if (sig.args.len != 1 or self.interner.carrierOf(sig.args[0]) != carrier) {
        return self.fail(g.start, "sort refinement '{s}' must be a unary predicate over '{s}'", .{ self.text(g), self.text(b.sort) });
    }
    // mint an anonymous refined sort (no IdentKV identity — scratchpad-only interpretation).
    const quals = try self.arena.alloc(InternPool.Index, 1);
    quals[0] = gpred;
    const label = std.fmt.allocPrint(self.arena, "{s} where {s}", .{ self.text(b.sort), self.text(g) }) catch return error.OutOfMemory;
    const nm = self.interner.internString(label) catch return error.OutOfMemory;
    self.interner.lockWrite(self.io);
    defer self.interner.unlockWrite(self.io);
    const ix = self.interner.mintSort(.{ .name = nm, .loc = b.sort.start, .refinement = .{ .parent = @enumFromInt(@intFromEnum(base)), .qualifiers = quals } }) catch return error.OutOfMemory;
    return @enumFromInt(@intFromEnum(ix));
}

/// Build the guard proposition for a refinement qualifier at `arg`: an opaque predicate
/// applies (`qpred(arg)`); a define'd guard (an anonymous `.guard` TERM over `#g0`, see
/// InternPool.Key.Guard) substitutes `arg` for `#g0`.
pub fn qualifierApp(self: *Elab, qual: InternPool.Index, arg: TermId) Error!TermId {
    switch (self.interner.keyOf(qual)) {
        .guard => |g| {
            const t = self.scratch.copyIn(self.interner, g.term) catch return error.OutOfMemory;
            const g0 = self.interner.internString("#g0") catch return error.OutOfMemory;
            return self.scratch.substFvar(t, g0, arg) catch return error.OutOfMemory;
        },
        else => return self.scratch.addApp(.pred, @enumFromInt(@intFromEnum(qual)), &.{arg}),
    }
}

/// The CONJUNCTION of a refined sort's qualifier guards over `fvar` — the CANONICAL
/// relativization guard shape (`inH(v) and inK(v)`, left-fold in declaration order; a single
/// qualifier is just its atom). Matches bindProofVar and the kernel's guarded forall_intro.
/// Null for an unrefined sort.
fn conjoinQuals(self: *Elab, quals: []const InternPool.Index, fvar: StrId, sort: SortId) Error!?TermId {
    var guard: ?TermId = null;
    for (quals) |qpred| {
        const bound = try self.scratch.add(.{ .fvar = .{ .name = fvar, .sort = sort } });
        const app = try self.qualifierApp(qpred, bound);
        guard = if (guard) |prev| try self.scratch.add(.{ .bin = .{ .op = .and_op, .lhs = prev, .rhs = app } }) else app;
    }
    return guard;
}

pub fn resolveSortTok(self: *Elab, tok: lexer.Token) Error!SortId {
    // `Prop` is the reserved builtin sort (schema generator-param results `P: T -> Prop`,
    // etc.) — never a userland-declared/fetched sort. Its name string is reserved, so the
    // check is an integer comparison.
    if (tok.qualifier == InternPool.Index.none and tok.name == InternPool.Index.prop_name) return prop_sort;
    if (self.resolveSymbolTok(tok)) |sym| switch (self.interner.keyOf(sym)) {
        .sort => return @enumFromInt(@intFromEnum(sym)),
        else => return self.fail(tok.start, "'{s}' is not a sort", .{self.text(tok)}),
    };
    const target = if (tok.qualifier != InternPool.Index.none)
        try self.resolveQualified(tok)
    else
        Qualified{ .ns = self.ns, .base = tokName(tok) };
    const sym = self.lookupIdent(target.ns, target.base) orelse {
        return self.fail(tok.start, "unknown sort '{s}'", .{self.text(tok)});
    };
    switch (self.interner.keyOf(sym)) {
        .sort => return @enumFromInt(@intFromEnum(sym)),
        else => return self.fail(tok.start, "'{s}' is not a sort", .{self.text(tok)}),
    }
}

const Qualified = struct { ns: InternPool.Index, base: StrId };

/// A stamped `ns.base` token: the ns must be a `done` import; the base resolves in its
/// namespace. (Multi-level qualification was diagnosed at parse.)
fn resolveQualified(self: *Elab, tok: lexer.Token) Error!Qualified {
    const qtext = self.interner.stringBytes(tok.qualifier);
    const imp = self.lookupIdent(self.ns, tok.qualifier) orelse {
        return self.fail(tok.start, "unknown namespace '{s}'", .{qtext});
    };
    switch (self.interner.keyOf(imp)) {
        .import => |m| return .{ .ns = m.namespace, .base = tokName(tok) },
        else => return self.fail(tok.start, "'{s}' is not a namespace", .{qtext}),
    }
}

/// A `done` IdentKV entry's Index, or null. The read pass ran first, so a live name is
/// expected to be done; absent/in-flight reads as unresolved (diagnosed by callers).
/// The resolved source Index is filtered through `self.model` (identity for `.universe`),
/// so a model proof remaps source symbols to their targets (Step 13).
fn lookupIdent(self: *Elab, ns: InternPool.Index, name: StrId) ?InternPool.Index {
    if (self.idents.lookup(self.io, .{ .namespace = ns, .name = name })) |state| switch (state) {
        .done => |ix| return self.interner.applyModel(self.model, ix),
        .in_flight => return null,
    };
    // MODEL-HOME fallback (13e): a transferred proof's re-elaborated synthetics mention
    // TARGET-file symbols (guard preds like `inH`) absent from the source file; they resolve
    // in the model's HOME file (where the model was declared). Mirrors resolveRefs' fallback.
    if (self.model != InternPool.Index.none and self.model != .universe) {
        const home = self.interner.keyOf(self.model).model.home;
        if (home != InternPool.Index.none) {
            const hns = self.interner.namespace(.universe, home) catch return null;
            if (hns != ns) if (self.idents.lookup(self.io, .{ .namespace = hns, .name = name })) |state| switch (state) {
                // a home-file symbol is already in TARGET terms — no applyModel remap.
                .done => |ix| return ix,
                .in_flight => return null,
            };
        }
    }
    return null;
}

/// A quantifier binder may not shadow an expression-local, a proof-local, or an
/// ALREADY-FETCHED global. (An unfetched global can slip — nonexistence is unknowable
/// without fetching; a known gap vs the eager checker, acceptable in the red phase.)
///
/// A define body's binders arrive already renamed to hygienic `name#N` by the expansion
/// pass (Engine/Expand), so they never collide here.
fn checkNoShadow(self: *Elab, name: StrId, tok: lexer.Token) Error!void {
    for (self.scope.items) |entry| {
        if (entry.name == name) {
            return self.fail(tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(tok)});
        }
    }
    if (self.walk.findIdent(name) != null) {
        return self.fail(tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(tok)});
    }
    if (self.lookupIdent(self.ns, name) != null) {
        return self.fail(tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(tok)});
    }
}

// -- small utilities -------------------------------------------------------------------

/// Mint a hygienic fresh fvar identity: '#' cannot lex, so `#N` never collides with a
/// userland name. Proof-unique via the task-owned counter.
/// A hygienic fresh name with the binder's own stem (`k#7`): unique like `freshName`, but a
/// diagnostic that renders it (an obligation reported inside the binder's scope) shows `k`.
pub fn freshNamed(self: *Elab, stem: StrId) Error!StrId {
    const n = self.fresh_counter.*;
    self.fresh_counter.* += 1;
    const bytes = std.fmt.allocPrint(self.arena, "{s}#{d}", .{ self.interner.stringBytes(stem), n }) catch return error.OutOfMemory;
    return self.interner.internString(bytes) catch return error.OutOfMemory;
}

pub fn freshName(self: *Elab) Error!StrId {
    const n = self.fresh_counter.*;
    self.fresh_counter.* += 1;
    const bytes = std.fmt.allocPrint(self.arena, "#{d}", .{n}) catch return error.OutOfMemory;
    return self.interner.internString(bytes) catch return error.OutOfMemory;
}

fn sortName(self: *const Elab, sort: SortId) []const u8 {
    if (sort == prop_sort) return "Prop";
    return self.interner.sortName(@enumFromInt(@intFromEnum(sort)));
}

/// A stamped token's interned name — the parser stamped every engine-parsed token, so past
/// parsing names are integers, never re-derived from source text.
fn tokName(t: lexer.Token) StrId {
    std.debug.assert(t.name != InternPool.Index.none);
    return t.name;
}

/// A stamped name in a LOCAL-only position (a binder name): a `ns.`-qualified token is
/// rejected — binding only its base name would silently drop the qualifier.
fn localName(self: *Elab, t: lexer.Token) Error!StrId {
    if (t.qualifier != InternPool.Index.none) {
        return self.fail(t.start, "'{s}' cannot be namespace-qualified here", .{self.text(t)});
    }
    return tokName(t);
}

// -- accessors for the schema-instantiation driver (Prove.zig) -------------------------
// These expose the expression-local binder scope + name lookup so the instantiate handler
// can elaborate a lambda ARG's body with its binders in scope (kept-free), reusing this
// Elab's scratchpad + resolution.

pub fn lookupIdentPub(self: *Elab, ns: InternPool.Index, name: StrId) ?InternPool.Index {
    return self.lookupIdent(ns, name);
}

/// A `.symbol` token's identity (see lexer.Token.Tag.symbol): the Index it carries, under the
/// ambient model like any resolved name — or EXACT (qualifier `.universe`: the parent-space
/// symbol, no model). Null for an ordinary name token.
pub fn resolveSymbolTok(self: *const Elab, tok: lexer.Token) ?InternPool.Index {
    if (tok.tag != .symbol) return null;
    if (tok.qualifier == .universe) return tok.name;
    return self.interner.applyModel(self.model, tok.name);
}

/// Current expr-local scope depth — pair with `scopeTruncate` to bracket lambda binders.
pub fn scopeMark(self: *const Elab) usize {
    return self.scope.items.len;
}

pub fn scopeTruncate(self: *Elab, mark: usize) void {
    self.scope.shrinkRetainingCapacity(mark);
}

/// Push an expression-local binder (`name` → the hygienic `fvar` of `sort`), so the lambda
/// body elaborates with it in scope. The instantiate handler keeps these fvars FREE (it
/// does not close them); beta-reduction substitutes them at application.
pub fn pushBinder(self: *Elab, name: StrId, sort: SortId, fvar: StrId) Error!void {
    self.scope.append(self.arena, .{ .name = name, .sort = sort, .fvar = fvar }) catch return error.OutOfMemory;
}

fn text(self: *const Elab, t: lexer.Token) []const u8 {
    // A SYNTHETIC token (accelerant-generated AST) has an empty source span (start == end) but
    // carries the real interned name — render that so a diagnostic on generated code names the
    // identifier instead of an empty slice. Real tokens span their source text.
    if (t.tag == .symbol) return self.interner.stringBytes(self.interner.nameOf(t.name));
    if (t.start == t.end and t.name != InternPool.Index.none) {
        // a hygienic `name#N` (an expanded define's binder) renders as the name the author wrote.
        const bytes = self.interner.stringBytes(t.name);
        return bytes[0 .. std.mem.indexOfScalar(u8, bytes, '#') orelse bytes.len];
    }
    return self.source[t.start..t.end];
}

pub fn exprLoc(e: *const ast.Expr) u32 {
    return switch (e.*) {
        .name => |t| t.start,
        .call => |c| c.callee.start,
        .binary => |b| b.tok.start,
        .not => |n| n.tok.start,
        .quant => |q| q.tok.start,
        .lambda => |l| l.tok.start,
    };
}

fn fail(self: *Elab, offset: u32, comptime fmt: []const u8, args: anytype) Error {
    self.sink.add(self.diagFile(), offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
}

/// The file this elaboration's offsets index: the one its namespace is built over. Derived
/// rather than passed so a diagnostic's file is never ambient state (see diagnostics.zig).
fn diagFile(self: *const Elab) u32 {
    const home = self.interner.keyOf(self.ns).namespace.file;
    const fid = self.ctx.fileOf(home) orelse return 0;
    return @intFromEnum(fid);
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../../parser.zig");

/// A hand-populated demand world: sort Nat, func add(Nat,Nat):Nat, pred le(Nat,Nat) —
/// published as `done` IdentKV entries under the fixture file's namespace.
const World = struct {
    arena: Allocator,
    io: std.Io,
    ctx: *Context,
    interner: *InternPool,
    idents: *IdentKV,
    scratch: *term.Pool,
    sink: *Diagnostics.Sink,
    walk: *Walk,
    ns: InternPool.Index,
    fresh: u32 = 0,
    nat: InternPool.Index = undefined,
    add_f: InternPool.Index = undefined,
    le_p: InternPool.Index = undefined,
    /// `pred inH(Nat)`, `sort H = Nat where inH`, `func shift(h: H): Nat` (a GUARDED param),
    /// `func mk(n: Nat): H` (a refined RESULT) — the obligation-discharge fixtures.
    inh_p: InternPool.Index = undefined,
    h_sort: InternPool.Index = undefined,
    shift_f: InternPool.Index = undefined,
    mk_f: InternPool.Index = undefined,

    fn init(arena: Allocator) !*World {
        const w = try arena.create(World);
        const threaded = try arena.create(std.Io.Threaded);
        threaded.* = .init(arena, .{});
        const interner = try arena.create(InternPool);
        interner.* = try .init(arena);
        const idents = try arena.create(IdentKV);
        idents.* = IdentKV.init(interner);
        const scratch = try arena.create(term.Pool);
        scratch.* = term.Pool.init(arena, arena);
        const sink = try arena.create(Diagnostics.Sink);
        sink.* = .init(arena);
        const walk = try arena.create(Walk);
        // a minimal Context for Elab's define-locator resolution (`declOf`). These tests
        // declare no defines, so its ast_index/pool_file stay empty; only the shared arena/
        // io/interner/sink matter. `facts`/`idents` are embedded-by-value and unused here.
        const ctx = try arena.create(Context);
        ctx.* = .{
            .arena = arena,
            .gpa = arena, // test fixture: arena doubles as the scratch GPA
            .io = threaded.io(),
            .sink = sink,
            .interner = interner,
            .facts = FactKV.init(interner),
            .idents = IdentKV.init(interner),
            .read_ctx = null,
            .read_fn = undefined,
            .verify = .{},
            .std_root = "",
        };
        w.* = .{
            .arena = arena,
            .io = threaded.io(),
            .ctx = ctx,
            .interner = interner,
            .idents = idents,
            .scratch = scratch,
            .sink = sink,
            .walk = walk,
            .ns = undefined,
        };
        walk.* = Walk.init(arena, interner, "", sink);

        const file = try interner.intern(.{ .file = .{ .path = try interner.internString("/t/w.bpa") } });
        w.ns = try interner.namespace(.universe, file);

        const nat_name = try interner.internString("Nat");
        w.nat = try idents.publish(w.io, .{ .namespace = w.ns, .name = nat_name }, .{ .sort = .{
            .name = nat_name,
            .loc = 0,
            .refinement = null,
        } });

        const nat2 = [_]InternPool.Index{ w.nat, w.nat };
        const add_sig = try interner.intern(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &nat2 } });
        const add_name = try interner.internString("add");
        w.add_f = try idents.publish(w.io, .{ .namespace = w.ns, .name = add_name }, .{ .func = .{
            .sig = add_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = add_name,
            .loc = 0,
        } });

        const le_sig = try interner.intern(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &nat2 } });
        const le_name = try interner.internString("le");
        w.le_p = try idents.publish(w.io, .{ .namespace = w.ns, .name = le_name }, .{ .pred = .{
            .sig = le_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = le_name,
            .loc = 0,
        } });

        // a global constant `a: Nat`, for tests that need a free term symbol.
        const a_name = try interner.internString("a");
        _ = try idents.publish(w.io, .{ .namespace = w.ns, .name = a_name }, .{ .constant = .{
            .sort = w.nat,
            .name = a_name,
            .loc = 0,
        } });

        // the refinement fixtures: pred inH(Nat); sort H = Nat where inH; shift(h: H): Nat; mk(n: Nat): H.
        const nat1 = [_]InternPool.Index{w.nat};
        const inh_sig = try interner.intern(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &nat1 } });
        const inh_name = try interner.internString("inH");
        w.inh_p = try idents.publish(w.io, .{ .namespace = w.ns, .name = inh_name }, .{ .pred = .{
            .sig = inh_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = inh_name,
            .loc = 0,
        } });
        const h_name = try interner.internString("H");
        const h_quals = try arena.dupe(InternPool.Index, &.{w.inh_p});
        w.h_sort = try idents.publish(w.io, .{ .namespace = w.ns, .name = h_name }, .{ .sort = .{
            .name = h_name,
            .loc = 0,
            .refinement = .{ .parent = w.nat, .qualifiers = h_quals },
        } });
        const h1 = [_]InternPool.Index{w.h_sort};
        const shift_sig = try interner.intern(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &h1 } });
        const shift_name = try interner.internString("shift");
        w.shift_f = try idents.publish(w.io, .{ .namespace = w.ns, .name = shift_name }, .{ .func = .{
            .sig = shift_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = shift_name,
            .loc = 0,
        } });
        const mk_sig = try interner.intern(.{ .sig = .{ .result = w.h_sort, .result_refined = .none, .args = &nat1 } });
        const mk_name = try interner.internString("mk");
        w.mk_f = try idents.publish(w.io, .{ .namespace = w.ns, .name = mk_name }, .{ .func = .{
            .sig = mk_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = mk_name,
            .loc = 0,
        } });
        return w;
    }

    /// Publish a guarded `div(Nat, Nat): Nat requires le(#g0, #g1)` (the reified guard over
    /// the two param fvars, as FetchTask would).
    fn publishGuardedDiv(w: *World) !void {
        const nat_sort: SortId = @enumFromInt(@intFromEnum(w.nat));
        const g0 = try w.scratch.add(.{ .fvar = .{ .name = try w.interner.internString("#g0"), .sort = nat_sort } });
        const g1 = try w.scratch.add(.{ .fvar = .{ .name = try w.interner.internString("#g1"), .sort = nat_sort } });
        const guard_term = try w.scratch.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ g0, g1 });
        w.interner.lockWrite(w.io);
        const guard_off = try w.scratch.reify(guard_term, w.interner);
        w.interner.unlockWrite(w.io);
        const nat2 = [_]InternPool.Index{ w.nat, w.nat };
        const div_sig = try w.interner.intern(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &nat2 } });
        const div_name = try w.interner.internString("div");
        _ = try w.idents.publish(w.io, .{ .namespace = w.ns, .name = div_name }, .{ .func = .{
            .sig = div_sig,
            .guard = guard_off,
            .param_names = &.{},
            .name = div_name,
            .loc = 0,
        } });
    }

    /// A fresh known-proposition table over a one-block (root) proof, for tests.
    fn known(w: *World) !*Known {
        const blocks = try w.arena.create(std.ArrayList(kernel.Block));
        blocks.* = .empty;
        try blocks.append(w.arena, .{ .parent = null, .label = try w.interner.internString("proof"), .kind = .root, .first_step = 0, .last_step = 0 });
        const k = try w.arena.create(Known);
        k.* = .{ .blocks = blocks };
        return k;
    }

    /// Elaborate `formula` with obligations CHECKED against `k` (root block); the diagnostics it
    /// raised are left in `w.sink` for the caller to inspect.
    fn checkWith(w: *World, k: *Known, comptime formula: []const u8) !Typed {
        const rig = try w.elabOf(formula);
        rig.elab.known = k;
        const typed = try rig.elab.elaborateExpr(rig.expr);
        try w.settle(rig.elab, k);
        return typed;
    }

    /// What the driver does with the misses Elab recorded and nothing else could settle:
    /// diagnose each as `unproved obligation` (Prove.settleMisses' residue path) and drain them.
    fn settle(w: *World, elab: *Elab, k: *Known) !void {
        for (k.misses.items) |m| {
            try w.sink.add(0, m.loc, "unproved obligation: '{s}'", .{try elab.renderProp(m.prop)});
        }
        k.misses.clearRetainingCapacity();
    }

    fn diagnosticCount(w: *World) usize {
        return w.sink.list.items.len;
    }
    fn lastDiagnostic(w: *World) []const u8 {
        return w.sink.list.items[w.sink.list.items.len - 1].message;
    }

    /// Parse `theorem t: <expr> ...` and hand back the formula expr + an Elab over it.
    fn elabOf(w: *World, comptime formula: []const u8) !struct { elab: *Elab, expr: *const ast.Expr } {
        const source = "theorem t: " ++ formula ++ "\nproof\n  @c |\n    " ++ formula ++ "\n    [by cite ax]\nqed";
        const before = w.sink.list.items.len; // earlier tests' diagnostics may be pending inspection
        var p: parser.Parser = .initInterning(w.arena, source, w.sink, w.interner);
        const parsed = try p.parseFile();
        try testing.expectEqual(before, w.sink.list.items.len);
        const elab = try w.arena.create(Elab);
        elab.* = Elab.init(w.arena, w.io, w.ctx, w.interner, w.idents, w.scratch, w.sink, source, w.walk, w.ns, &w.fresh);
        return .{ .elab = elab, .expr = parsed.decls[0].theorem.local.fact.formula };
    }
};

test "elab: quantified formula — pool-native sorts, de Bruijn closing, prop result" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    const rig = try w.elabOf("forall k: Nat; le(add(k, k), k)");
    const typed = try rig.elab.elaborateExpr(rig.expr);
    try testing.expectEqual(Elab.prop_sort, typed.sort);

    // expected shape, built by hand in the same scratchpad: ∀(bvar0): le(add(b0,b0),b0)
    const p = w.scratch;
    const nat_sort: SortId = @enumFromInt(@intFromEnum(w.nat));
    const b0 = try p.add(.{ .bvar = 0 });
    const add_app = try p.addApp(.app, @enumFromInt(@intFromEnum(w.add_f)), &.{ b0, b0 });
    const le_app = try p.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ add_app, b0 });
    const want = try p.add(.{ .quant = .{
        .q = .forall,
        .sort = nat_sort,
        .hint = try w.interner.internString("k"),
        .body = le_app,
    } });
    try testing.expect(p.alphaEq(typed.id, want));
    try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);
}

test "elab: proof-local binder resolves through the Walk's LocalIdentKV" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    // seed a proof-local binder `n : Nat` with hygienic fvar "#42" (as a fix-step's
    // process would via pending_binder)
    const nat_sort: SortId = @enumFromInt(@intFromEnum(w.nat));
    const hyg = try w.interner.internString("#42");
    try w.walk.local_idents.append(arena, .{
        .name = try w.interner.internString("n"),
        .block = .root,
        .info = .{ .sort = nat_sort, .fvar = hyg },
    });

    const rig = try w.elabOf("le(n, n)");
    const typed = try rig.elab.elaborateExpr(rig.expr);
    try testing.expectEqual(Elab.prop_sort, typed.sort);

    const p = w.scratch;
    const fv = try p.add(.{ .fvar = .{ .name = hyg, .sort = nat_sort } });
    const want = try p.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ fv, fv });
    try testing.expect(p.alphaEq(typed.id, want));
}

test "elab: sort mismatch and prop-in-'=' diagnose and Recover" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    { // an unknown identifier diagnoses (zzz is not published in the World)
        const rig = try w.elabOf("le(zzz, zzz)");
        try testing.expectError(error.Recover, rig.elab.elaborateExpr(rig.expr));
        try testing.expect(w.sink.list.items.len > 0);
        try testing.expect(std.mem.indexOf(u8, w.sink.list.items[0].message, "unknown identifier") != null);
    }
    w.sink.list.clearRetainingCapacity();
    { // '=' on propositions is rejected
        const rig = try w.elabOf("forall k: Nat; le(k, k) = le(k, k)");
        try testing.expectError(error.Recover, rig.elab.elaborateExpr(rig.expr));
        try testing.expect(std.mem.indexOf(u8, w.sink.list.items[0].message, "compares terms") != null);
    }
}

test "elab: a `requires` guard is REQUIRED at the call — unknown is one diagnosis, taught is accepted and consumes the teacher" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);
    try w.publishGuardedDiv();

    // `div(a, a)` requires `le(a, a)`: nothing taught → exactly ONE diagnosis naming it, and the
    // driver flag set; the elaboration itself still completes (the step is rejected by the driver).
    const k = try w.known();
    const typed = try w.checkWith(k, "le(div(a, a), a)");
    try testing.expectEqual(prop_sort, typed.sort);
    try testing.expectEqual(@as(usize, 1), w.diagnosticCount());
    try testing.expectEqualStrings("unproved obligation: 'le(a, a)'", w.lastDiagnostic());
    try testing.expect(k.missed);

    // TEACH `le(a, a)` (as a proved step 7 of the root block) → accepted, no new diagnosis, and
    // the teaching step is recorded reachable.
    k.missed = false;
    const a_ix = w.idents.lookup(w.io, .{ .namespace = w.ns, .name = try w.interner.internString("a") }).?.done;
    const a_term = try w.scratch.addApp(.app, @enumFromInt(@intFromEnum(a_ix)), &.{});
    const le_a_a = try w.scratch.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ a_term, a_term });
    try k.teach(arena, le_a_a, @enumFromInt(0), 7);
    _ = try w.checkWith(k, "le(div(a, a), a)");
    try testing.expectEqual(@as(usize, 1), w.diagnosticCount());
    try testing.expect(!k.missed);
    try testing.expectEqualSlices(u32, &.{7}, k.reachable.items);
}

test "elab: a refined param sort requires its qualifier atom for a CLOSED subject; a bound subject is a claim, not owed" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);
    const k = try w.known();
    // a closed subject with nothing taught: owed, and missed.
    _ = try w.checkWith(k, "le(shift(a), a)");
    try testing.expectEqual(@as(usize, 1), w.diagnosticCount());
    try testing.expectEqualStrings("unproved obligation: 'inH(a)'", w.lastDiagnostic());
    // a BOUND subject — at H or at Nat — is a quantified claim about every element: never owed.
    _ = try w.checkWith(k, "forall k: H; le(shift(k), k)");
    _ = try w.checkWith(k, "forall k: Nat; le(shift(k), k)");
    try testing.expectEqual(@as(usize, 1), w.diagnosticCount());
    // …but a closed subject INSIDE a quantifier still is.
    _ = try w.checkWith(k, "forall k: Nat; le(shift(a), k)");
    try testing.expectEqual(@as(usize, 2), w.diagnosticCount());
}

test "elab: an antecedent teaches its consequent only; a left conjunct its right conjunct only" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);
    const k = try w.known();
    _ = try w.checkWith(k, "inH(a) -> le(shift(a), a)");
    try testing.expectEqual(@as(usize, 0), w.diagnosticCount());
    _ = try w.checkWith(k, "inH(a) and le(shift(a), a)");
    try testing.expectEqual(@as(usize, 0), w.diagnosticCount());
    // the other way round nothing is known yet where the use sits.
    _ = try w.checkWith(k, "le(shift(a), a) -> inH(a)");
    try testing.expectEqual(@as(usize, 1), w.diagnosticCount());
    _ = try w.checkWith(k, "le(shift(a), a) and inH(a)");
    try testing.expectEqual(@as(usize, 2), w.diagnosticCount());
    // an antecedent's knowledge does not leak PAST its implication: `(inH(a) -> P) and Q`.
    _ = try w.checkWith(k, "(inH(a) -> le(a, a)) and le(shift(a), a)");
    try testing.expectEqual(@as(usize, 3), w.diagnosticCount());
    // `or` teaches nothing.
    _ = try w.checkWith(k, "inH(a) or le(shift(a), a)");
    try testing.expectEqual(@as(usize, 4), w.diagnosticCount());
}

test "elab: a refined RESULT sort teaches the application its closure fact, proof-wide" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);
    const k = try w.known();
    // `mk(a): H` → `inH(mk(a))` is known → `shift(mk(a))` is fine.
    _ = try w.checkWith(k, "le(shift(mk(a)), a)");
    try testing.expectEqual(@as(usize, 0), w.diagnosticCount());
    // and it stays known for a LATER elaboration in the same proof (taught at the root block).
    _ = try w.checkWith(k, "le(shift(mk(a)), shift(mk(a)))");
    try testing.expectEqual(@as(usize, 0), w.diagnosticCount());
}

test "elab: the proof table — a taught COMPOUND is found at another occurrence by identity; visibility is block-structured" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);
    // root 0, a nested block 1 under it, and a sibling block 2 under it.
    const blocks = try arena.create(std.ArrayList(kernel.Block));
    blocks.* = .empty;
    for ([_]?kernel.BlockId{ null, @enumFromInt(0), @enumFromInt(0) }) |parent| {
        try blocks.append(arena, .{ .parent = parent, .label = try w.interner.internString("b"), .kind = .root, .first_step = 0, .last_step = 0 });
    }
    const k = try arena.create(Known);
    k.* = .{ .blocks = blocks };

    // teach `inH(add(a, a))` INSIDE block 1 (say by a step there).
    const a_ix = w.idents.lookup(w.io, .{ .namespace = w.ns, .name = try w.interner.internString("a") }).?.done;
    const a_term = try w.scratch.addApp(.app, @enumFromInt(@intFromEnum(a_ix)), &.{});
    const aa = try w.scratch.addApp(.app, @enumFromInt(@intFromEnum(w.add_f)), &.{ a_term, a_term });
    const inh_aa = try w.scratch.addApp(.pred, @enumFromInt(@intFromEnum(w.inh_p)), &.{aa});
    try k.teach(arena, inh_aa, @enumFromInt(1), 3);

    // a use in block 1 writes `add(a, a)` AFRESH — the hash-consed pool makes it the same term.
    {
        const rig = try w.elabOf("le(shift(add(a, a)), a)");
        rig.elab.known = k;
        rig.elab.known_block = @enumFromInt(1);
        _ = try rig.elab.elaborateExpr(rig.expr);
        try w.settle(rig.elab, k);
        try testing.expectEqual(@as(usize, 0), w.diagnosticCount());
        try testing.expectEqualSlices(u32, &.{3}, k.reachable.items);
    }
    // a use in the SIBLING block 2 does not see block 1's knowledge; nor does the root.
    {
        const rig = try w.elabOf("le(shift(add(a, a)), a)");
        rig.elab.known = k;
        rig.elab.known_block = @enumFromInt(2);
        _ = try rig.elab.elaborateExpr(rig.expr);
        try w.settle(rig.elab, k);
        try testing.expectEqual(@as(usize, 1), w.diagnosticCount());
        try testing.expectEqualStrings("unproved obligation: 'inH(add(a, a))'", w.lastDiagnostic());
    }
    _ = try w.checkWith(k, "le(shift(add(a, a)), a)");
    try testing.expectEqual(@as(usize, 2), w.diagnosticCount());
}

test "elab: collectObligations reads a term's guarded applications — refined params and requires — once each, closed subterms only" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);
    try w.publishGuardedDiv();
    const p = w.scratch;
    const a_ix = w.idents.lookup(w.io, .{ .namespace = w.ns, .name = try w.interner.internString("a") }).?.done;
    const a_term = try p.addApp(.app, @enumFromInt(@intFromEnum(a_ix)), &.{});
    const aa = try p.addApp(.app, @enumFromInt(@intFromEnum(w.add_f)), &.{ a_term, a_term });
    const inh_aa = try p.addApp(.pred, @enumFromInt(@intFromEnum(w.inh_p)), &.{aa});
    const le_a_a = try p.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ a_term, a_term });

    // `shift(add(a, a))` twice and `div(a, a)` once: two obligations, in first-seen order.
    const rig = try w.elabOf("le(shift(add(a, a)), div(a, a)) and le(shift(add(a, a)), a)");
    const t = try rig.elab.elaborateExpr(rig.expr); // known == null: nothing checked, nothing taught
    var out: std.ArrayList(TermId) = .empty;
    try rig.elab.collectObligations(t.id, &out, true);
    try testing.expectEqual(@as(usize, 2), out.items.len);
    try testing.expectEqual(inh_aa, out.items[0]);
    try testing.expectEqual(le_a_a, out.items[1]);
    // a left conjunct / antecedent discharges its right side INSIDE the term: not the caller's.
    const rig3 = try w.elabOf("inH(add(a, a)) and le(shift(add(a, a)), a)");
    const t3 = try rig3.elab.elaborateExpr(rig3.expr);
    var out3: std.ArrayList(TermId) = .empty;
    try rig3.elab.collectObligations(t3.id, &out3, true);
    try testing.expectEqual(@as(usize, 0), out3.items.len);
    const rig5 = try w.elabOf("(le(a, a) and inH(add(a, a))) -> le(shift(add(a, a)), a)");
    const t5 = try rig5.elab.elaborateExpr(rig5.expr);
    var out5: std.ArrayList(TermId) = .empty;
    try rig5.elab.collectObligations(t5.id, &out5, true);
    try testing.expectEqual(@as(usize, 0), out5.items.len);
    const rig4 = try w.elabOf("le(shift(add(a, a)), a) and inH(add(a, a))");
    const t4 = try rig4.elab.elaborateExpr(rig4.expr);
    var out4: std.ArrayList(TermId) = .empty;
    try rig4.elab.collectObligations(t4.id, &out4, true);
    try testing.expectEqual(@as(usize, 1), out4.items.len);
    // under a binder the subject is bound: not a term-level obligation.
    const rig2 = try w.elabOf("forall k: Nat; le(shift(k), div(k, k))");
    const t2 = try rig2.elab.elaborateExpr(rig2.expr);
    var out2: std.ArrayList(TermId) = .empty;
    try rig2.elab.collectObligations(t2.id, &out2, true);
    try testing.expectEqual(@as(usize, 0), out2.items.len);
    try testing.expectEqual(@as(usize, 0), w.diagnosticCount());
}

test "elab: pathologically deep spine does not overflow the C stack (task #92)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    // Build a ~50k-deep `not not not … le(a,a)` chain of ast.Expr nodes DIRECTLY (bypassing the
    // parser, whose own recursion would overflow first) and elaborate it. Native recursion over
    // this spine would blow the C stack; the work-stack drives it iteratively.
    const depth = 50_000;

    // innermost: `le(a, a)` — a prop leaf.
    const a_tok = lexer.Token{ .tag = .identifier, .start = 0, .end = 0, .name = try w.interner.internString("a") };
    const le_tok = lexer.Token{ .tag = .identifier, .start = 0, .end = 0, .name = try w.interner.internString("le") };
    const a_expr = try arena.create(ast.Expr);
    a_expr.* = .{ .name = a_tok };
    const args = try arena.alloc(*const ast.Expr, 2);
    args[0] = a_expr;
    args[1] = a_expr;
    const leaf = try arena.create(ast.Expr);
    leaf.* = .{ .call = .{ .callee = le_tok, .args = args } };

    const not_tok = lexer.Token{ .tag = .keyword_not, .start = 0, .end = 0 };
    var cur: *const ast.Expr = leaf;
    var d: usize = 0;
    while (d < depth) : (d += 1) {
        const nxt = try arena.create(ast.Expr);
        nxt.* = .{ .not = .{ .tok = not_tok, .operand = cur } };
        cur = nxt;
    }

    var fresh_counter: u32 = 0;
    var e = Elab.init(w.arena, w.io, w.ctx, w.interner, w.idents, w.scratch, w.sink, "", w.walk, w.ns, &fresh_counter);
    const typed = try e.elaborateExpr(cur);
    try testing.expectEqual(Elab.prop_sort, typed.sort);
    try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);
}

// -- delaborate (term -> ast.Expr) round-trips through elaboration -----------------------
// The correctness oracle for `Delaborate`: elaborate a formula to a term, delaborate that
// term back to AST, re-elaborate, and assert the result is alpha-equal to the original.
// Elaboration is the real consumer, so this tests exactly the property that matters — the
// delaborated AST re-elaborates to the same term.

const Delaborate = @import("Delaborate.zig");

/// elaborate `formula` -> T; delaborate T -> AST; re-elaborate -> T'; assert alphaEq(T, T').
fn expectDelaborateRoundTrip(w: *World, comptime formula: []const u8) !void {
    const rig = try w.elabOf(formula);
    const t = try rig.elab.elaborateExpr(rig.expr);
    try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);

    const back = try Delaborate.run(w.arena, w.scratch, w.interner, t.id, 0);
    // a fresh Elab over the same world (new scope), re-elaborating the delaborated AST.
    var fresh_counter: u32 = 0;
    var e2 = Elab.init(w.arena, w.io, w.ctx, w.interner, w.idents, w.scratch, w.sink, "", w.walk, w.ns, &fresh_counter);
    const t2 = try e2.elaborateExpr(back);
    try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);
    try testing.expect(w.scratch.alphaEq(t.id, t2.id));
}

test "delaborate: round-trips atoms, applications, connectives, comparisons, quantifiers" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    // a nested application under a predicate
    try expectDelaborateRoundTrip(w, "le(add(a, a), a)");
    // boolean connectives (and / or / implies), mixed + nested
    try expectDelaborateRoundTrip(w, "(le(a, a) and le(a, a)) -> le(a, a)");
    try expectDelaborateRoundTrip(w, "le(a, a) or (le(a, a) -> le(a, a))");
    // equality and its `!=` (not(eq)) sugar
    try expectDelaborateRoundTrip(w, "a = a");
    try expectDelaborateRoundTrip(w, "a != a");
    // a plain `not`
    try expectDelaborateRoundTrip(w, "not le(a, a)");
    // quantifiers: single, and NESTED (the b1/b2 fresh-binder + de Bruijn structure)
    try expectDelaborateRoundTrip(w, "forall k: Nat; le(k, k)");
    try expectDelaborateRoundTrip(w, "forall m: Nat; forall n: Nat; le(add(m, n), m) -> le(n, m)");
    // a quantifier whose body mixes a bound var with a free global constant symbol
    try expectDelaborateRoundTrip(w, "forall k: Nat; le(add(k, a), a)");
}
