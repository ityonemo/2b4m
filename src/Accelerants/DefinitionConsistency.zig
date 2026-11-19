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
const Peeled = struct {
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
    if (peeled.items.len < 2) {
        return site.fail(c.rule.start, "definition_consistency expects a goal of the form `forall …; (k = <base> and k = <step>(n)) -> <arm> = <arm>`; this goal has fewer than two quantifiers", .{});
    }
    const n = peeled.items[peeled.items.len - 1];
    const k = peeled.items[peeled.items.len - 2];
    try outer.appendSlice(site.ctx.arena, peeled.items[0 .. peeled.items.len - 2]);

    // the body must be `(… and …) -> …`
    const imp = site.pool.get(cur);
    if (imp != .bin or imp.bin.op != .implies) {
        return site.fail(c.rule.start, "definition_consistency: the obligation's body must be an implication `(conditions) -> <arm> = <arm>`", .{});
    }
    const conj = site.pool.get(imp.bin.lhs);
    if (conj != .bin or conj.bin.op != .and_op) {
        return site.fail(c.rule.start, "definition_consistency: the obligation's conditions must be conjoined with `and`", .{});
    }
    return .{ .outer = outer.items, .k = k, .n = n, .cond = imp.bin.lhs, .consequent = imp.bin.rhs };
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
