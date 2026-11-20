//! The `definition_consistency` accelerated tactic — one variant of `Accelerants.Tactic`. See
//! `Accelerants.zig` for the three-phase contract it implements.
//!
//! WHAT IT PROVES. A definition block whose clauses split on a sort's CONSTRUCTORS owes, per
//! clause pair, "where both conditions hold, the two arms agree":
//!
//!     forall <params>; forall k, n: Nat;
//!       (k = ZERO and k = succ(n)) -> <arm_i> = <arm_j>
//!
//! Those conditions never both hold, so the obligation is vacuous — but vacuously true is
//! still something to PROVE, and the proof is the same every time. `std/peano.b4m` packages
//! it as `zeroSuccSplitIsVacuous(prop(Nat, Nat))`, so this tactic's whole job is to emit one
//! `instantiation` of that schema at the obligation's own consequent.
//!
//! WHY A TACTIC AND NOT A BARE CITE. The obligation's non-matched params (`a` in `cpower`)
//! are bound by the goal's OWN `forall`, so they are not in scope at a step: writing
//! `[using instantiation zeroSuccSplitIsVacuous(...)]` by hand fails with
//! `reference not found: 'a'`. The certificate must `fix` those binders, instantiate inside,
//! and `generalize` back out — exactly what `simplify_quantified` does for its equation.
//!
//! The certificate is a kernel `instantiation` step, always producible (a schema lookup, not
//! a search), so this word never declines and trusting it under `--fast` buys nothing.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const Engine = @import("../Engine.zig");
const Walk = @import("../Engine/ProveTask/Walk.zig");
const Elab = @import("../Engine/ProveTask/Elab.zig");
const Accelerants = @import("../Accelerants.zig");
const Site = @import("Site.zig");
const Error = Site.Error;
const common = @import("common.zig");

pub const schema_slot: Accelerants.SchemaSlot = .theory_selector;
pub const premise_shape: Accelerants.PremiseShape = .local_refs_kept;
/// no fact arguments: the shared schema is found by name, not cited by the author
pub const lemma_args = false;

/// The shared schema this tactic instantiates. Supplied by the theory that declares the
/// constructors (the per-sort rule), so the citing file names that theory with the
/// word's selector: `[using definition_consistency(peano)]`.
const schema_name = "zeroSuccSplitIsVacuous";

pub fn read(self: @This(), site: *Site, w: *const Walk, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    _ = self;
    _ = site;
    _ = w;
    _ = c;
    return null;
}

pub fn decide(self: @This(), site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    return common.decideFused(self, site, w, e, goal, c);
}

pub fn certify(self: @This(), site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    _ = self;
    return produce(site, w, e, goal, c);
}

/// The obligation's shape, peeled from the goal: the binders to `fix`, the two
/// constructor-split variables, and the consequent the two arms claim.
/// WHICH triviality makes the obligation vacuous. The two are different mechanisms, not one:
/// a constructor split needs the sort's disequality (via its vacuity schema), while a
/// complementary pair is pure propositional contradiction and rests on NO axioms.
const Route = enum { constructor_split, complementary };

const Peeled = struct {
    route: Route = .constructor_split,
    /// `.complementary` only: the contradictory pair found in the conditions — a proposition
    /// and its own negation, as TERMS (not binders).
    pos: TermId = undefined,
    neg: TermId = undefined,
    /// the non-matched binders (fixed, then generalized back) — `a` in cpower's obligation
    outer: []const term.Node.Fvar,
    /// the matched-position variable `k` and the predecessor `n`, in schema order
    k: term.Node.Fvar,
    n: term.Node.Fvar,
    /// the conjoined conditions, taken straight off the goal (never reconstructed, so the
    /// claimed formula cannot differ from the author's by association or argument order)
    cond: TermId,
    /// the `<arm_i> = <arm_j>` equation, open over all of the above
    consequent: TermId,
};

pub fn produce(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    _ = w;
    _ = e;
    if (c.args.len != 0) return site.fail(c.rule.start, "definition_consistency takes no arguments (the theory supplying the vacuity schema is the parenthesized selector)", .{});

    const p = try peel(site, goal, c);

    var b: Accelerants.Builder = .{ .arena = site.ctx.arena, .interner = site.ctx.interner, .pool = site.pool, .loc = c.rule.start };

    if (p.route == .complementary) return produceComplementary(site, &b, p, goal, c);

    // `fun <k>, <n>: Nat => <consequent>` — the predicate the schema is instantiated at. BOTH
    // binders are needed: a recursive step arm always mentions the predecessor, so a
    // one-argument prop could not state the consequent.
    const lambda = try predicateLambda(site, &b, p);
    const args = try site.ctx.arena.alloc(*const ast.Expr, 1);
    args[0] = lambda;

    // the schema's conclusion at our consequent: `forall k, n; (k = Z and k = s(n)) -> P`
    const inst_formula = try closeTwo(site, p);
    const inst_label = try site.freshNamed("consistency-vacuous");
    var inner: std.ArrayList(ast.Step) = .empty;
    try inner.append(site.ctx.arena, .{ .label = b.tok(inst_label), .body = .{ .claim = .{
        .formula = try b.termExpr(inst_formula),
        .kind = .using,
        .rule = b.tok(try common.internStrRt(site, "instantiation")),
        .schema = try schemaCite(site, c),
        .args = args,
        .refs = &.{},
    } } });

    // `fix` each non-matched binder and `generalize` back out — the shared wrapper the
    // quantified tactics use, so the display names re-resolve the same way.
    const steps = try common.wrapSimplifyForall(site, &b, p.outer, inst_formula, inner.items);

    const name = try syntheticName(site, c);
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{
            .fact = .{ .name = b.tok(name), .formula = try b.termExpr(goal), .params = &.{} },
            .steps = steps,
        } } },
        .args = &.{},
        .premises = &.{},
        .seen = b.seen.items,
        .assumed = b.assumed.items,
        .fvar_binds = &.{},
    };
}

/// Recognize the obligation. The goal must be
///
///     forall <outer…>; forall <k>, <n>: S; (<k> = <c0> and <k> = <c1>(<n>)) -> <lhs> = <rhs>
///
/// peeled into its parts. Everything is read off the TERM, so a goal the author wrote in a
/// different but equivalent shape is rejected rather than guessed at — the statement must
/// match what the checker synthesizes (see DEFINITION-SOUNDNESS-PLAN.md).
fn peel(site: *Site, goal: TermId, c: ast.Step.Claim) Error!Peeled {
    var outer: std.ArrayList(term.Node.Fvar) = .empty;
    var cur = goal;
    // peel every leading ∀; the LAST TWO are the schema's own `k, n`.
    var peeled: std.ArrayList(term.Node.Fvar) = .empty;
    while (true) {
        const node = site.pool.get(cur);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = site.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{
            .name = try site.freshNamed(if (hint.len > 0) hint else "q"),
            .sort = node.quant.sort,
        };
        cur = try site.pool.open(node.quant.body, try site.pool.add(.{ .fvar = fv }));
        try peeled.append(site.ctx.arena, fv);
    }
    // the body must be `(… and …) -> …` either way
    const imp = site.pool.get(cur);
    if (imp != .bin or imp.bin.op != .implies) {
        return site.fail(c.rule.start, "definition_consistency: the obligation's body must be an implication `(conditions) -> <arm> = <arm>`", .{});
    }
    const conj = site.pool.get(imp.bin.lhs);
    if (conj != .bin or conj.bin.op != .and_op) {
        return site.fail(c.rule.start, "definition_consistency: the obligation's conditions must be conjoined with `and`", .{});
    }

    // ROUTE 2 first, because it needs no particular binders: somewhere in the conditions sits
    // a proposition and its own negation, so the antecedent is unsatisfiable by propositional
    // logic alone and the consequent follows by ex_falso. This is `swap`'s two trivial pairs.
    if (findComplementary(site, imp.bin.lhs)) |pairs| {
        try outer.appendSlice(site.ctx.arena, peeled.items);
        return .{
            .route = .complementary,
            .outer = outer.items,
            .k = undefined,
            .n = undefined,
            .pos = pairs.pos,
            .neg = pairs.neg,
            .cond = imp.bin.lhs,
            .consequent = imp.bin.rhs,
        };
    }

    // ROUTE 1: a constructor split, whose last two binders are the schema's `k` and `n`.
    if (peeled.items.len < 2) {
        return site.fail(c.rule.start, "definition_consistency expects either a constructor split (`forall …; (k = <base> and k = <step>(n)) -> …`) or conditions containing a proposition and its negation; this goal is neither", .{});
    }
    const n = peeled.items[peeled.items.len - 1];
    const k = peeled.items[peeled.items.len - 2];
    try outer.appendSlice(site.ctx.arena, peeled.items[0 .. peeled.items.len - 2]);
    return .{ .outer = outer.items, .k = k, .n = n, .cond = imp.bin.lhs, .consequent = imp.bin.rhs };
}

/// ROUTE 2's certificate: the conditions contain a proposition and its own negation, so
/// `assume` them, extract both conjuncts, and `ex_falso` to the consequent. Pure propositional
/// contradiction — NO schema and NO axioms, unlike the constructor route which needs the
/// sort's disequality. (`tautology` cannot do this: it sees `x = u` and `not (x = u)` as
/// unrelated atoms and declines with a countermodel.)
fn produceComplementary(site: *Site, b: *Accelerants.Builder, p: Peeled, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    const impl = try site.pool.add(.{ .bin = .{ .op = .implies, .lhs = p.cond, .rhs = p.consequent } });

    // inside the assume: restate the hypothesis, project out the two conjuncts, ex_falso.
    const hyp_label = try site.freshNamed("consistency-given");
    var body: std.ArrayList(ast.Step) = .empty;
    const both = try site.freshNamed("consistency-both");
    try body.append(site.ctx.arena, try b.claimStep(both, try b.termExpr(p.cond), .by, try common.internStrRt(site, "hypothesis"), &.{}, try b.oneRef(hyp_label)));
    const pos = try projectConjunct(site, b, &body, p.cond, both, p.pos);
    const neg = try projectConjunct(site, b, &body, p.cond, both, p.neg);
    const refs = try site.ctx.arena.alloc(lexer.Token, 2);
    refs[0] = b.tok(pos);
    refs[1] = b.tok(neg);
    try body.append(site.ctx.arena, try b.claimStep(try site.freshNamed("consistency-absurd"), try b.termExpr(p.consequent), .by, try common.internStrRt(site, "ex_falso"), &.{}, refs));

    var outer_steps: std.ArrayList(ast.Step) = .empty;
    try outer_steps.append(site.ctx.arena, try b.assumeTerm(hyp_label, p.cond, body.items));
    const disch = try site.freshNamed("consistency-discharge");
    try outer_steps.append(site.ctx.arena, try b.claimStep(disch, try b.termExpr(impl), .by, try common.internStrRt(site, "discharge"), &.{}, try b.oneRef(hyp_label)));

    const steps = try common.wrapSimplifyForall(site, b, p.outer, impl, outer_steps.items);
    const name = try syntheticName(site, c);
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{
            .fact = .{ .name = b.tok(name), .formula = try b.termExpr(goal), .params = &.{} },
            .steps = steps,
        } } },
        .args = &.{},
        .premises = &.{},
        .seen = b.seen.items,
        .assumed = b.assumed.items,
        .fvar_binds = &.{},
    };
}

/// Emit the `and_lhs`/`and_rhs` chain that projects `want` out of the conjunction `cond`
/// (proved by step `from`), returning the label of the step that holds it. The conjunction may
/// be nested either way round, so the path is walked rather than assumed.
fn projectConjunct(site: *Site, b: *Accelerants.Builder, out: *std.ArrayList(ast.Step), cond: TermId, from: StrId, want: TermId) Error!StrId {
    var cur = cond;
    var cur_label = from;
    while (!site.pool.alphaEq(cur, want)) {
        const node = site.pool.get(cur);
        if (node != .bin or node.bin.op != .and_op) return site.fail(b.loc, "internal: the contradictory conjunct is not reachable in the conditions", .{});
        const take_left = containsConjunct(site, node.bin.lhs, want);
        const next = if (take_left) node.bin.lhs else node.bin.rhs;
        const rule = if (take_left) "and_lhs" else "and_rhs";
        const label = try site.freshNamed("consistency-part");
        try out.append(site.ctx.arena, try b.claimStep(label, try b.termExpr(next), .by, try common.internStrRt(site, rule), &.{}, try b.oneRef(cur_label)));
        cur = next;
        cur_label = label;
    }
    return cur_label;
}

/// Is `want` one of the conjuncts of `t` (at any depth)?
fn containsConjunct(site: *Site, t: TermId, want: TermId) bool {
    if (site.pool.alphaEq(t, want)) return true;
    const node = site.pool.get(t);
    if (node != .bin or node.bin.op != .and_op) return false;
    return containsConjunct(site, node.bin.lhs, want) or containsConjunct(site, node.bin.rhs, want);
}

/// A proposition and its own negation among the conjoined conditions, or null.
///
/// Flattens the `and` tree (association is not canonical — `a and (b and c)` and
/// `(a and b) and c` are both written in the corpus) and looks for a conjunct whose negation
/// is also a conjunct. `x = u` beside `not (x = u)` is the `swap` case; this is strictly
/// propositional, so it needs no axiom and no schema.
fn findComplementary(site: *Site, cond: TermId) ?struct { pos: TermId, neg: TermId } {
    var flat: std.ArrayList(TermId) = .empty;
    flatten(site, cond, &flat) catch return null;
    for (flat.items) |a| {
        const na = site.pool.get(a);
        if (na != .not) continue;
        for (flat.items) |b| {
            if (site.pool.alphaEq(na.not, b)) return .{ .pos = b, .neg = a };
        }
    }
    return null;
}

/// The conjuncts of a (possibly nested) `and` tree, in left-to-right order.
fn flatten(site: *Site, t: TermId, out: *std.ArrayList(TermId)) Allocator.Error!void {
    const node = site.pool.get(t);
    if (node == .bin and node.bin.op == .and_op) {
        try flatten(site, node.bin.lhs, out);
        try flatten(site, node.bin.rhs, out);
        return;
    }
    try out.append(site.ctx.arena, t);
}

/// `fun <k>, <n>: S => <consequent>` — the two-argument predicate the schema takes.
fn predicateLambda(site: *Site, b: *Accelerants.Builder, p: Peeled) Error!*const ast.Expr {
    const binders = try site.ctx.arena.alloc(ast.Binder, 2);
    binders[0] = .{ .name = b.tok(try common.displayName(site, p.k.name)), .sort = b.sortTok(p.k.sort) };
    binders[1] = .{ .name = b.tok(try common.displayName(site, p.n.name)), .sort = b.sortTok(p.n.sort) };
    const e = try site.ctx.arena.create(ast.Expr);
    e.* = .{ .lambda = .{ .tok = b.tok(InternPool.Index.none), .binders = binders, .body = try b.termExpr(p.consequent) } };
    return e;
}

/// Re-close the obligation's inner two binders: the formula the `instantiation` step claims.
fn closeTwo(site: *Site, p: Peeled) Error!TermId {
    const imp = try site.pool.add(.{ .bin = .{ .op = .implies, .lhs = p.cond, .rhs = p.consequent } });
    const over_n = try closeForall(site, imp, p.n);
    return closeForall(site, over_n, p.k);
}

fn closeForall(site: *Site, body: TermId, fv: term.Node.Fvar) Error!TermId {
    const closed = try site.pool.close(body, fv.name);
    return site.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
}

/// A cite token for the shared schema, qualified by the word's selector
/// (`[using definition_consistency(peano)]`) — the generated ProveTask resolves and the
/// kernel re-checks it, so no facts.lookup here.
fn schemaCite(site: *Site, c: ast.Step.Claim) Error!lexer.Token {
    const nid = site.ctx.interner.internString(schema_name) catch return error.OutOfMemory;
    return .{
        .tag = .identifier,
        .start = c.rule.start,
        .end = c.rule.start,
        .name = nid,
        .qualifier = if (c.schema) |sel| sel.name else InternPool.Index.none,
    };
}

/// A re-entry-stable name for the synthetic: the rule's own source offset, which is what
/// `Context.registerSynthetic` already keys a step by.
fn syntheticName(site: *Site, c: ast.Step.Claim) Error!StrId {
    const bytes = std.fmt.allocPrint(site.ctx.arena, "definition_consistency{{{d}}}", .{c.rule.start}) catch return error.OutOfMemory;
    return site.ctx.interner.internString(bytes) catch return error.OutOfMemory;
}
