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
//! NOT YET SUPPORTED (diagnosed, proof goes red; later layers/phases): guarded functions
//! (`requires` — the TCC machinery), transparent defines, predicated sorts/binders
//! (`where`), lambdas (schema arguments — schemas are unsupported wholesale).

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

const Elab = @This();

pub const Error = error{ Recover, OutOfMemory };
pub const Typed = struct { id: TermId, sort: SortId };
/// A refined-sort proof obligation `inH(arg)` from a guarded application (Step 3c).
pub const Tcc = struct { formula: TermId, loc: u32 };

/// The pool's reserved Prop sort, as a scratchpad SortId. Numerically `Index.prop`; the
/// flip renumbers `term.SortId.prop` onto it.
pub const prop_sort: SortId = @enumFromInt(@intFromEnum(InternPool.Index.prop));

arena: Allocator,
io: std.Io,
/// the owning Context — read-only here, consulted ONLY to resolve a `.define` locator to
/// its AST decl (`declOf`) for in-place macro expansion. Every other resolution goes
/// through `idents`/`interner`.
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
/// DEFINE-EXPANSION param bindings (param name -> the caller's already-elaborated arg term),
/// installed while elaborating a define's BODY (under the define's home namespace). Consulted
/// in name/call position BEFORE the global lookup — a param resolves to its bound arg term.
/// Save/restored around each `expandDefine`, so nested/remote defines each see their own map.
/// Distinct from `schema_args` (schemas may have generator params; a define's are value-only).
define_args: ?*const std.AutoHashMapUnmanaged(StrId, Typed) = null,
/// currently-expanding defines (by their locator Index), the cycle guard for a define whose
/// body reaches itself. Owned by the driving Prove so it persists across the Elabs a proof
/// builds; null = not tracked (a throwaway sort-resolution Elab, which sees no defines).
define_stack: ?*std.ArrayList(InternPool.Index) = null,
/// MODEL this elaboration resolves THROUGH (Step 13): when set, every global identifier
/// resolved here is filtered `interner.applyModel(model, source)` — so proving a source
/// theorem in model M's namespace remaps `op`→`add` etc. Null (`.universe` at the call
/// site) in an ordinary proof = identity. Set by the model ProveTask on its Elab.
model: InternPool.Index = .universe,
/// NO_RELATIVIZE (13e): set when elaborating a SYNTHETIC (accelerant-generated) schema's
/// formulas — they were DELABORATED from already-elaborated terms, so refined-sort guard
/// injection at binders must be SKIPPED (it would double the guards). Parsed schemas keep
/// injection (their AST is source text, not a round-trip).
no_relativize: bool = false,
/// REFINED-SORT obligation sinks (Step 3c), owned by the driving Prove (so they persist
/// across the several Elabs a proof builds). A guarded-function application over a refined
/// param sort `H` appends the obligation `inH(arg)` to `tccs`; a refined-RESULT func/const
/// surfaces `inH(result)` into `result_facts` (an available discharger). Null = obligations
/// not tracked (e.g. a throwaway sort-resolution Elab). Prove discharges `tccs` after each
/// formula against the LOCAL proof context (result_facts + block guards + prior steps).
tccs: ?*std.ArrayList(Tcc) = null,
result_facts: ?*std.ArrayList(TermId) = null,

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
pub fn elaborateExpr(self: *Elab, e: *const ast.Expr) Error!Typed {
    switch (e.*) {
        .name => |tok| return self.elaborateName(tok),
        .call => |c| return self.elaborateCall(c),
        .binary => |b| switch (b.op) {
            .implies, .and_op, .or_op => {
                const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                // obligations arising in the RHS may depend on the LHS (an antecedent /
                // conjunct in scope for the rest), so relativize them: an obligation `O`
                // from the rhs becomes `lhs -> O` under `->`/`and`. (Step 3c.)
                const tcc_start = if (self.tccs) |t| t.items.len else 0;
                const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                if ((b.op == .implies or b.op == .and_op)) if (self.tccs) |t| {
                    for (t.items[tcc_start..]) |*obl| {
                        obl.formula = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = lhs.id, .rhs = obl.formula } });
                    }
                };
                const op: term.BinOp = switch (b.op) {
                    .implies => .implies,
                    .and_op => .and_op,
                    .or_op => .or_op,
                    else => unreachable,
                };
                const id = try self.scratch.add(.{ .bin = .{ .op = op, .lhs = lhs.id, .rhs = rhs.id } });
                return .{ .id = id, .sort = prop_sort };
            },
            .iff => {
                // SURFACE SUGAR: `P iff Q` desugars to `(P -> Q) and (Q -> P)`.
                const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                const fwd = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = lhs.id, .rhs = rhs.id } });
                const bwd = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = rhs.id, .rhs = lhs.id } });
                const id = try self.scratch.add(.{ .bin = .{ .op = .and_op, .lhs = fwd, .rhs = bwd } });
                return .{ .id = id, .sort = prop_sort };
            },
            .equal, .not_equal => {
                const lhs = try self.elaborateExpr(b.lhs);
                const rhs = try self.elaborateExpr(b.rhs);
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
                return .{ .id = id, .sort = prop_sort };
            },
        },
        .not => |n| {
            const inner = try self.requireProp(try self.elaborateExpr(n.operand), n.operand);
            const id = try self.scratch.add(.{ .not = inner.id });
            return .{ .id = id, .sort = prop_sort };
        },
        .quant => |q| {
            // one shared sort for all binders of this quantifier (surface rule). A REFINED
            // sort lowers to its CARRIER for the kernel term; its qualifiers are injected as
            // guards around the body (`inH(x) -> body` for forall, `inH(x) and body` for
            // exists) — the intrinsic relativization of a predicated sort.
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
                fr.* = try self.freshName();
                try self.scope.append(self.arena, .{ .name = bname, .sort = sort, .fvar = fr.* });
            }
            const tcc_start = if (self.tccs) |t| t.items.len else 0;
            const rf_start = if (self.result_facts) |r| r.items.len else 0;
            const body = try self.requireProp(try self.elaborateExpr(q.body), q.body);
            self.scope.shrinkRetainingCapacity(mark);
            var id = body.id;
            var i = q.binders.len;
            while (i > 0) {
                i -= 1;
                // inject the binder's guard: the CONJUNCTION of its qualifiers (canonical —
                // matches the kernel's guarded-fix forall_intro derivation and bindProofVar),
                // as a single `guard -> body` (∀) / `guard and body` (∃).
                if (try self.conjoinQuals(quals, fresh[i], sort)) |guard| {
                    const connective: term.BinOp = if (q.q == .forall) .implies else .and_op;
                    id = try self.scratch.add(.{ .bin = .{ .op = connective, .lhs = guard, .rhs = id } });
                }
                id = try self.scratch.close(id, fresh[i]);
                id = try self.scratch.add(.{ .quant = .{
                    .q = if (q.q == .forall) .forall else .exists,
                    .sort = sort,
                    .hint = tokName(q.binders[i].name),
                    .body = id,
                } });
                // an obligation from the body over binder `i` must be discharged for ALL
                // values of it: close it under a `forall` with the binder's guard as
                // antecedent — `∀x; inH(x) -> O` — so the discharge sees the same shape as
                // the relativized goal. (Step 3c; mirrors the body relativization above.)
                if (self.tccs) |t| for (t.items[tcc_start..]) |*obl| {
                    obl.formula = try self.relativizeUnderBinder(obl.formula, quals, fresh[i], sort, q.binders[i].name);
                };
                // SURFACED result-facts (closure facts like `inH(op2(h,h))`) over binder `i`
                // relativize the SAME way (`∀x; inH(x) -> inH(op2(x,x))`) — so a discharge of
                // the equally-relativized obligation matches them whole (Step 3c closure gap).
                if (self.result_facts) |r| for (r.items[rf_start..]) |*rf| {
                    rf.* = try self.relativizeUnderBinder(rf.*, quals, fresh[i], sort, q.binders[i].name);
                };
            }
            return .{ .id = id, .sort = prop_sort };
        },
        .lambda => |l| {
            return self.fail(l.tok.start, "lambdas (schema arguments) are not supported by the demand prover", .{});
        },
    }
}

pub fn requireProp(self: *Elab, typed: Typed, e: *const ast.Expr) Error!Typed {
    if (typed.sort != prop_sort) {
        return self.fail(exprLoc(e), "expected a proposition, got a term of sort '{s}'", .{self.sortName(typed.sort)});
    }
    return typed;
}

// -- name resolution -------------------------------------------------------------------

fn elaborateName(self: *Elab, tok: lexer.Token) Error!Typed {
    if (tok.qualifier != InternPool.Index.none) {
        const target = try self.resolveQualified(tok);
        return self.elaborateSymRef(tok, target.ns, target.base);
    }
    const name = tokName(tok);
    // 0. define parameter (while expanding a define body): a param SHADOWS everything in the
    // body — it must win over proof-local/expression-local binders that happen to share its
    // spelling (the capture the `define_no_capture` fixture guards). The bound value is the
    // caller's already-elaborated arg term, so it carries the caller's own binder identities.
    if (self.define_args) |da| if (da.get(name)) |bound| return bound;
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
        const id = try self.scratch.add(.{ .fvar = .{ .name = local.info.fvar, .sort = local.info.sort } });
        return .{ .id = id, .sort = local.info.sort };
    }
    // 3. schema parameter (only while elaborating a schema body/steps)
    if (self.schema_args) |sa| if (sa.get(name)) |arg| switch (arg) {
        .value => |v| return .{ .id = v.id, .sort = v.sort },
        .lambda => return self.fail(tok.start, "schema parameter '{s}' needs arguments", .{self.text(tok)}),
    };
    // 4. global (define params were consulted at step 0 — they shadow everything)
    return self.elaborateSymRef(tok, self.ns, name);
}

/// A resolved global in NAME position (no written arguments): a constant or a nullary
/// func/pred applies bare; anything wanting arguments (or that isn't a value) errors.
fn elaborateSymRef(self: *Elab, tok: lexer.Token, ns: InternPool.Index, name: StrId) Error!Typed {
    const sym = self.lookupIdent(ns, name) orelse {
        return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
    };
    switch (self.interner.keyOf(sym)) {
        .func, .pred => |c| {
            const sig = self.interner.keyOf(c.sig).sig;
            if (sig.args.len != 0) {
                return self.fail(tok.start, "'{s}' expects {d} argument(s), got 0", .{ self.text(tok), sig.args.len });
            }
            if (c.guard != InternPool.no_term) {
                return self.fail(tok.start, "guarded functions are not yet supported by the demand prover", .{});
            }
            return self.applyResolved(sym, &.{});
        },
        // a constant is a nullary application — route through applyResolved so a REFINED
        // result sort (`const E: H`) surfaces its closure fact `inH(E)` (Step 3c).
        .constant => return self.applyResolved(sym, &.{}),
        .sort => return self.fail(tok.start, "'{s}' is a sort, not a value", .{self.text(tok)}),
        .import => return self.fail(tok.start, "'{s}' is a namespace, not a value", .{self.text(tok)}),
        .define => return self.expandDefine(sym, tok, &.{}),
        else => return self.fail(tok.start, "'{s}' cannot appear in an expression", .{self.text(tok)}),
    }
}

fn elaborateCall(self: *Elab, c: ast.Expr.Call) Error!Typed {
    const dotted = c.callee.qualifier != InternPool.Index.none;
    const target = if (dotted)
        try self.resolveQualified(c.callee)
    else
        Qualified{ .ns = self.ns, .base = tokName(c.callee) };
    // a define VALUE param in call position is an error (params are value-only, not callable);
    // consulted before the global lookup so a param shadowing a global func still errors.
    if (!dotted) if (self.define_args) |da| if (da.get(target.base) != null) {
        return self.fail(c.callee.start, "define parameter '{s}' is not callable", .{self.text(c.callee)});
    };
    // schema GENERATOR param in call position: beta-reduce (only a bare name is a param).
    if (!dotted) if (self.schema_args) |sa| if (sa.get(target.base)) |arg| switch (arg) {
        .lambda => |lam| return self.applyGeneratorParam(c, lam),
        .value => return self.fail(c.callee.start, "schema parameter '{s}' takes no arguments", .{self.text(c.callee)}),
    };
    const sym = self.lookupIdent(target.ns, target.base) orelse {
        return self.fail(c.callee.start, "unknown identifier '{s}'", .{self.text(c.callee)});
    };
    const callable = switch (self.interner.keyOf(sym)) {
        .func, .pred => |cb| cb,
        .define => return self.expandDefine(sym, c.callee, c.args),
        else => return self.fail(c.callee.start, "'{s}' is not callable", .{self.text(c.callee)}),
    };
    const sig = self.interner.keyOf(callable.sig).sig;
    if (sig.args.len != c.args.len) {
        return self.fail(c.callee.start, "'{s}' expects {d} argument(s), got {d}", .{
            self.text(c.callee), sig.args.len, c.args.len,
        });
    }
    if (callable.guard != InternPool.no_term) {
        return self.fail(c.callee.start, "guarded functions are not yet supported by the demand prover", .{});
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
    return self.applyResolved(sym, arg_ids);
}

/// Expand a `define` IN PLACE (transparent macro). `sym` is its `.define` LOCATOR Index; the
/// authoritative params/body come from the AST registry (`ctx.declOf(home_file, name)`). Args
/// (empty for a bare-name use) are elaborated in the CALLER's context, bound to the params,
/// then the BODY is elaborated under the define's HOME namespace (so its own qualifiers
/// resolve against the define's imports) with the param bindings in scope. Cycle-guarded.
fn expandDefine(self: *Elab, sym: InternPool.Index, callee: lexer.Token, args: []const *const ast.Expr) Error!Typed {
    const loc = self.interner.keyOf(sym).define;
    // cycle guard: a define whose body reaches itself.
    if (self.define_stack) |stk| {
        for (stk.items) |seen| if (seen == sym) {
            return self.fail(callee.start, "cyclic define '{s}'", .{self.interner.stringBytes(loc.name)});
        };
    }
    const fid = self.ctx.pool_file.get(loc.file) orelse {
        return self.fail(callee.start, "internal: define '{s}' in an undiscovered file", .{self.interner.stringBytes(loc.name)});
    };
    const decl = self.ctx.declOf(fid, loc.name) orelse {
        return self.fail(callee.start, "internal: define '{s}' vanished from the AST registry", .{self.interner.stringBytes(loc.name)});
    };
    const d = decl.define;
    if (args.len != d.params.len) {
        return self.fail(callee.start, "'{s}' expects {d} argument(s), got {d}", .{ self.text(callee), d.params.len, args.len });
    }

    // elaborate each arg in the CALLER's context (current ns, scope, define_args); bind to
    // its param name. Sort-check against the param's declared sort (resolved in HOME ns).
    const home_ns = try self.interner.namespace(self.model, loc.file);
    var bindings: std.AutoHashMapUnmanaged(StrId, Typed) = .empty;
    for (d.params, args) |p, arg| {
        const typed = try self.elaborateExpr(arg);
        const pname = try self.localName(p.name);
        const expected = try self.resolveSortIn(home_ns, p.sort);
        const want: SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(expected)))));
        const got: SortId = if (typed.sort == prop_sort)
            typed.sort
        else
            @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort)))));
        if (got != want) {
            return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{ self.sortName(want), self.sortName(typed.sort) });
        }
        try bindings.put(self.arena, pname, typed);
    }

    // elaborate the BODY under the home namespace with the param bindings, restoring on exit.
    const saved_ns = self.ns;
    const saved_args = self.define_args;
    self.ns = home_ns;
    self.define_args = &bindings;
    if (self.define_stack) |stk| try stk.append(self.arena, sym);
    defer {
        self.ns = saved_ns;
        self.define_args = saved_args;
        if (self.define_stack) |stk| _ = stk.pop();
    }
    return self.elaborateExpr(d.value);
}

/// Resolve a sort token in a GIVEN namespace (not necessarily `self.ns`) to a scratchpad
/// SortId. Used to type-check define args against param sorts declared in the define's home
/// namespace. The read pass already fetched the sort (a define's body-closure demand covers
/// its param sorts), so a miss reads as an error rather than a suspend.
fn resolveSortIn(self: *Elab, ns: InternPool.Index, tok: lexer.Token) Error!SortId {
    const base = if (tok.qualifier != InternPool.Index.none) blk: {
        const imp = self.lookupIdent(ns, tok.qualifier) orelse
            return self.fail(tok.start, "unknown namespace '{s}'", .{self.interner.stringBytes(tok.qualifier)});
        switch (self.interner.keyOf(imp)) {
            .import => |m| break :blk Qualified{ .ns = m.namespace, .base = tokName(tok) },
            else => return self.fail(tok.start, "'{s}' is not a namespace", .{self.interner.stringBytes(tok.qualifier)}),
        }
    } else Qualified{ .ns = ns, .base = tokName(tok) };
    const sym = self.lookupIdent(base.ns, base.base) orelse
        return self.fail(tok.start, "unknown sort '{s}'", .{self.text(tok)});
    if (self.interner.keyOf(sym) != .sort) return self.fail(tok.start, "'{s}' is not a sort", .{self.text(tok)});
    return @enumFromInt(@intFromEnum(sym));
}

/// For a refined param sort, append `qpred(arg)` obligations to `tccs` (one per qualifier).
/// No-op for a root param sort or when obligations aren't tracked.
fn emitArgObligations(self: *Elab, param_sort: InternPool.Index, arg: TermId, loc: u32) Error!void {
    const sink = self.tccs orelse return;
    if (!self.interner.isRefined(param_sort)) return;
    const quals = self.interner.qualifiersOf(self.arena, param_sort) catch return error.OutOfMemory;
    for (quals) |qpred| {
        const app = try self.qualifierApp(qpred, arg);
        sink.append(self.arena, .{ .formula = app, .loc = loc }) catch return error.OutOfMemory;
    }
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
    if (self.result_facts) |sink| {
        const result_ix: InternPool.Index = @enumFromInt(@intFromEnum(result));
        if (self.interner.isRefined(result_ix)) {
            const quals = self.interner.qualifiersOf(self.arena, result_ix) catch return error.OutOfMemory;
            for (quals) |qpred| {
                const fact = try self.qualifierApp(qpred, id);
                sink.append(self.arena, fact) catch return error.OutOfMemory;
            }
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
    const gpred = self.lookupIdent(self.ns, gname) orelse {
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

/// Build the guard proposition `qpred(arg)` for a refinement qualifier.
fn qualifierApp(self: *Elab, qpred: InternPool.Index, arg: TermId) Error!TermId {
    return self.scratch.addApp(.pred, @enumFromInt(@intFromEnum(qpred)), &.{arg});
}

/// Close a proposition `f` (mentioning the free fvar `fvar` at carrier `sort`) under a
/// `forall` binder, injecting each qualifier guard as an antecedent: `∀x; q0(x) -> … -> f`.
/// Used to relativize obligations AND surfaced result-facts through a `forall x: H` binder
/// identically, so they match on discharge (Step 3c).
fn relativizeUnderBinder(self: *Elab, f0: TermId, quals: []const InternPool.Index, fvar: StrId, sort: SortId, hint: lexer.Token) Error!TermId {
    var f = f0;
    if (try self.conjoinQuals(quals, fvar, sort)) |guard| {
        f = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = guard, .rhs = f } });
    }
    const closed = try self.scratch.close(f, fvar);
    return self.scratch.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = tokName(hint), .body = closed } });
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
/// EXCEPTION — DEFINE EXPANSION (`define_args != null`): a define is an eager macro whose
/// body's own binders (`define divides(d,n) = exists k: Nat; …`) are freshened to hygienic
/// `#N` fvars on expansion, so they CANNOT capture; a collision with a caller's same-spelled
/// variable (`k`) is not a user error — the define author can't know the caller's scope. Skip
/// the stylistic shadow check for macro-internal binders (capture is already impossible).
fn checkNoShadow(self: *Elab, name: StrId, tok: lexer.Token) Error!void {
    if (self.define_args != null) return;
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
    self.sink.add(offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
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

    fn init(arena: Allocator) !*World {
        const w = try arena.create(World);
        const threaded = try arena.create(std.Io.Threaded);
        threaded.* = .init(arena, .{});
        const interner = try arena.create(InternPool);
        interner.* = try .init(arena);
        const idents = try arena.create(IdentKV);
        idents.* = IdentKV.init(interner);
        const scratch = try arena.create(term.Pool);
        scratch.* = term.Pool.init(arena);
        const sink = try arena.create(Diagnostics.Sink);
        sink.* = .init(arena);
        const walk = try arena.create(Walk);
        // a minimal Context for Elab's define-locator resolution (`declOf`). These tests
        // declare no defines, so its ast_index/pool_file stay empty; only the shared arena/
        // io/interner/sink matter. `facts`/`idents` are embedded-by-value and unused here.
        const ctx = try arena.create(Context);
        ctx.* = .{
            .arena = arena,
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

        const file = try interner.get(.{ .file = .{ .path = try interner.internString("/t/w.bpa") } });
        w.ns = try interner.namespace(.universe, file);

        const nat_name = try interner.internString("Nat");
        w.nat = try idents.publish(w.io, .{ .namespace = w.ns, .name = nat_name }, .{ .sort = .{
            .name = nat_name,
            .loc = 0,
            .refinement = null,
        } });

        const nat2 = [_]InternPool.Index{ w.nat, w.nat };
        const add_sig = try interner.get(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &nat2 } });
        const add_name = try interner.internString("add");
        w.add_f = try idents.publish(w.io, .{ .namespace = w.ns, .name = add_name }, .{ .func = .{
            .sig = add_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = add_name,
            .loc = 0,
        } });

        const le_sig = try interner.get(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &nat2 } });
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
        return w;
    }

    /// Parse `theorem t: <expr> ...` and hand back the formula expr + an Elab over it.
    fn elabOf(w: *World, comptime formula: []const u8) !struct { elab: *Elab, expr: *const ast.Expr } {
        const source = "theorem t: " ++ formula ++ "\nproof\n  @c |\n    " ++ formula ++ "\n    [by cite ax]\nqed";
        var p: parser.Parser = .initInterning(w.arena, source, w.sink, w.interner);
        const parsed = try p.parseFile();
        try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);
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

test "elab: guarded funcs, defines-absent, and lambdas are cleanly unsupported/unknown" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    // a guarded function: div(Nat,Nat):Nat requires ...
    const nat2 = [_]InternPool.Index{ w.nat, w.nat };
    const div_sig = try w.interner.get(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &nat2 } });
    const div_name = try w.interner.internString("div");
    _ = try w.idents.publish(w.io, .{ .namespace = w.ns, .name = div_name }, .{
        .func = .{
            .sig = div_sig,
            .guard = 123, // any reified guard offset — non-no_term means guarded
            .param_names = &.{},
            .name = div_name,
            .loc = 0,
        },
    });

    const rig = try w.elabOf("forall k: Nat; le(div(k, k), k)");
    try testing.expectError(error.Recover, rig.elab.elaborateExpr(rig.expr));
    try testing.expect(std.mem.indexOf(u8, w.sink.list.items[0].message, "guarded functions are not yet supported") != null);
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
