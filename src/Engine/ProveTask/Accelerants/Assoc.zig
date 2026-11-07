//! The `assoc` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
//! `Accelerant.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../../ast.zig");
const lexer = @import("../../../lexer.zig");
const InternPool = @import("../../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const kernel = @import("../../../kernel.zig");
const Engine = @import("../../../Engine.zig");
const Context = @import("../../../Context.zig");
const Walk = @import("../Walk.zig");
const RefScan = @import("../RefScan.zig");
const Elab = @import("../Elab.zig");
const Schema = @import("../Schema.zig");
const Accelerant = @import("../Accelerant.zig");
const Verify = @import("../../../Verify.zig");
const EqCert = @import("../EqCert.zig");
const Polynomial = @import("../Polynomial.zig");
const simplify_mod = @import("../simplify.zig");
const presburger_mod = @import("../presburger.zig");
const smt = @import("../smt.zig");
const farkas = @import("../farkas.zig");
const FactKV = @import("../../../FactKV.zig");
const FetchTask = @import("../../../Engine/FetchTask.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const tokName = Prove.tokName;
const testing = std.testing;
const common = @import("common.zig");

/// `assoc_commut*`: commutativity too (sort to a summand multiset), not re-nesting only
commut: bool,
/// the `_quantified` variant: a `forall …; s = t` goal, peeled first
quantified: bool,

pub const schema_slot: Accelerant.SchemaSlot = .none;
pub const premise_shape: Accelerant.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = true;

/// Phase 1: nothing beyond the cited facts, which the scaffolding demands from the consts above.
pub fn read(self: @This(), prove: *Prove, w: *const Walk, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    _ = self;
    _ = prove;
    _ = w;
    _ = c;
    return null;
}

pub fn decide(self: @This(), prove: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    return common.decideFused(self, prove, w, e, goal, c);
}

pub fn certify(self: @This(), prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    return if (self.commut)
        (if (self.quantified) produceAssocCommutQuantified(prove, w, goal, c) else produceAssocCommut(prove, w, goal, c))
    else
        (if (self.quantified) produceAssocQuantified(prove, w, goal, c) else produceAssoc(prove, w, goal, c));
}

/// `using assoc(assocLemma)` — prove `s = t` when the sides differ by ASSOCIATIVITY ALONE of
/// a single operator. The lemma (the sole arg) must have shape `f(f(a,b),c) = f(a,f(b,c))`;
/// the operator `f` is recovered from its LHS head. Right-nests both sides with the lemma as
/// a terminating rewrite and joins.
pub fn produceAssoc(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const gn = prove.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return prove.fail(c.rule.start, "assoc proves equations; use assoc_quantified for a 'forall …; s = t' goal", .{});
        }
        return prove.fail(c.rule.start, "assoc proves equations; the goal is not an equation", .{});
    }
    return buildAssoc(prove, w, c, goal, &.{});
}

/// `using assoc_quantified(assocLemma)` — like assoc but over a `forall …; s = t` goal: peel
/// the ∀ prefix into eigenvariables, reorder the body, re-generalize.
pub fn produceAssocQuantified(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const peeled = try common.peelForallEq(prove, goal, c, "assoc_quantified") orelse return null;
    return buildAssoc(prove, w, c, peeled.body, peeled.eigen);
}

/// Shared assoc core over the (possibly ∀-peeled) equation body `eq_goal_raw`. Abstracts the
/// goal's free caller-locals into params, builds the one-rule assoc set from the arg lemma,
/// right-nests both sides, and hands the join to `finishReorder`.
fn buildAssoc(prove: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    if (c.args.len != 1) {
        return prove.fail(c.rule.start, "assoc requires an associativity lemma: assoc(<assocLemma>); got {d} argument(s)", .{c.args.len});
    }
    // ADMIT: goal-shape (equation) validated in the caller + arg-count here. The next step
    // (`argRule` → resolveFactRef) RESOLVES the associativity lemma — which is exactly what an
    // admitted step must NOT require proved (e.g. assoc_oracle's `opAssoc` is unresolvable). Skip.
    // `--fast` declines to EMIT the certificate; the ASSOCIATIVITY NORMALIZATION still runs.
    // Admit lands after the normal-form comparison below.
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    const prepared = try common.argRule(prove, w, c.args[0]);
    // validate the shape `f(f(a,b),c) = f(a,f(b,c))`: the LHS must be a binary app whose head
    // `f` is shared by the RHS. (The rule's binders/lhs/rhs carry pattern fvars already.)
    const l = prove.pool.get(prepared.rule.lhs);
    if (l != .app or l.app.args.len != 2) {
        return prove.fail(Elab.exprLoc(c.args[0]), "assoc: the associativity lemma must have shape 'f(f(a, b), c) = f(a, f(b, c))'", .{});
    }
    const op_sym = l.app.sym;
    const r = prove.pool.get(prepared.rule.rhs);
    if (r != .app or r.app.sym != op_sym) {
        return prove.fail(Elab.exprLoc(c.args[0]), "assoc: the associativity lemma's two sides must share the operator", .{});
    }

    // abstract free caller-local fvars into params UP FRONT (before normalizing) so the goal,
    // the trace, and the schema body all speak `p1, p2, …`. Eigenvariables stay free (re-bound
    // by the `fix` wrapper). A LOCAL lemma's formula may share such an fvar — include it.
    const local_pf: []const TermId = if (prepared.local) &.{prepared.formula} else &.{};
    const ag = try common.abstractGoal(prove, &b, eq_goal_raw, local_pf, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = prove.pool.get(eq_goal).eq;
    const s = gn.lhs;
    const t = gn.rhs;

    const rules = [_]simplify_mod.Rule{prepared.rule};
    const cites = [_]EqCert.RuleCite{prepared.cite};

    // right-nest each side by the single associativity rule (terminating). The resulting
    // canonical forms agree iff the sides differ by associativity alone.
    const rs = simplify_mod.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, &rules, s, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = simplify_mod.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, &rules, t, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!prove.pool.alphaEq(rs.nf, rt.nf)) {
        return prove.fail(c.rule.start, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
            try prove.renderTerm(try common.unabstract(prove, rs.nf, abs)),
            try prove.renderTerm(try common.unabstract(prove, rt.nf, abs)),
        });
    }
    // ADMIT: both sides reached the same associativity normal form, so a certificate
    // demonstrably exists — only emitting it is pruned.
    if (prove.admit_mode) {
        prove.producer_premise_refs = null;
        prove.admit_ok = true;
        return null;
    }
    return common.finishReorder(prove, w, &b, c, "assoc", s, t, &rules, &cites, rs, rt, abs, eigen, if (prepared.local) &.{prepared} else &.{});
}

/// `using assoc_commut` (bare = the well-known add/mul triple) or `assoc_commut(a, c, s)`
/// (an explicit assoc/comm/swap triple for a custom operator) — reorder an A/C sum: optional
/// distribute pre-pass (LOCAL cited refs → antecedents), then re-associate + flatten +
/// bubble-sort each side into canonical order, joining the concatenated traces.
pub fn produceAssocCommut(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const gn = prove.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return prove.fail(c.rule.start, "assoc_commut proves equations; use assoc_commut_quantified for a 'forall …; s = t' goal", .{});
        }
        return prove.fail(c.rule.start, "assoc_commut proves equations; the goal is not an equation", .{});
    }
    return buildAssocCommut(prove, w, c, goal, &.{});
}

pub fn produceAssocCommutQuantified(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const peeled = try common.peelForallEq(prove, goal, c, "assoc_commut_quantified") orelse return null;
    return buildAssocCommut(prove, w, c, peeled.body, peeled.eigen);
}

/// Shared assoc_commut core over the (possibly ∀-peeled) equation body. Prepares the AC rule
/// set (distribute pre-rules from `c.refs` at the FRONT, then the AC triple), abstracts the
/// goal, distributes + AC-sorts both sides, and hands the concatenated traces to
/// `finishReorder`.
fn buildAssocCommut(prove: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    // exactly two forms: bare (well-known add/mul) or three explicit lemmas. No partials.
    if (c.args.len != 0 and c.args.len != 3) {
        return prove.fail(c.rule.start, "assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got {d}", .{c.args.len});
    }
    // ADMIT: goal-shape (equation) validated in the caller + arg-count here. Everything below
    // RESOLVES the (distribute pre-rules and, for the explicit form, the AC triple) lemmas and
    // runs the AC re-association search. Skip the resolution + decision under `--fast`.
    // `--fast` declines to EMIT the certificate; the A/C REORDERING DECISION still runs.
    // Admit lands after the summand comparison below.
    const explicit = c.args.len == 3;
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // optional distribute PRE-RULES from the cited refs (L→R before flattening); their rule
    // indices sit at the FRONT so the AC bubble-sort's indices shift after them.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var pre_prepared: std.ArrayList(common.PreparedRule) = .empty;
    for (c.refs) |ref| {
        const p = try common.prepareRule(prove, w, ref);
        try rules.append(prove.ctx.arena, p.rule);
        try cites.append(prove.ctx.arena, p.cite);
        try pre_prepared.append(prove.ctx.arena, p);
    }
    const pre_count = rules.items.len;

    // resolve the AC triple + its operator BEFORE abstracting (an explicit lemma may carry
    // pattern fvars — never caller-locals — so it is unaffected by abstraction). Bare form:
    // pick the operator from the goal's LHS head and resolve the well-known triple.
    var op_sym: term.SymId = undefined;
    if (explicit) {
        const a_rule = try common.argRule(prove, w, c.args[0]);
        const c_rule = try common.argRule(prove, w, c.args[1]);
        const w_rule = try common.argRule(prove, w, c.args[2]);
        const c_lhs = prove.pool.get(c_rule.rule.lhs);
        if (c_lhs != .app or c_lhs.app.args.len != 2) {
            return prove.fail(Elab.exprLoc(c.args[1]), "assoc_commut: the commutativity lemma must have shape 'f(a, b) = f(b, a)'", .{});
        }
        op_sym = c_lhs.app.sym;
        try rules.append(prove.ctx.arena, a_rule.rule);
        try cites.append(prove.ctx.arena, a_rule.cite);
        try rules.append(prove.ctx.arena, c_rule.rule);
        try cites.append(prove.ctx.arena, c_rule.cite);
        try rules.append(prove.ctx.arena, w_rule.rule);
        try cites.append(prove.ctx.arena, w_rule.cite);
        // an explicit lemma cited by a LOCAL step is an antecedent too.
        if (a_rule.local) try pre_prepared.append(prove.ctx.arena, a_rule);
        if (c_rule.local) try pre_prepared.append(prove.ctx.arena, c_rule);
        if (w_rule.local) try pre_prepared.append(prove.ctx.arena, w_rule);
    } else {
        const gn = prove.pool.get(eq_goal_raw).eq;
        // the reordered operator is the head of the left side AFTER the cited pre-rules have
        // distributed it (`mul(add(a, b), c)` is an add-sum once mulAddDistribRight fires).
        const lhs_pre = simplify_mod.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules.items[0..pre_count], gn.lhs, 1000) catch |e| switch (e) {
            error.Limit => return prove.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const s_head: ?term.SymId = if (prove.pool.get(lhs_pre.nf) == .app) prove.pool.get(lhs_pre.nf).app.sym else null;
        const op = common.pickWellKnownOp(prove, s_head) orelse
            return prove.fail(c.rule.start, "assoc_commut reorders an add- or mul-sum; the goal's left side is '{s}'", .{try prove.renderTerm(gn.lhs)});
        op_sym = op.sym;
        // BUILD the AC triple as HARDCODED shapes (no facts.lookup, no existence check) — like
        // polynomial. Each rule's LHS/RHS is constructed from the goal's own operator sym; the
        // well-known lemma NAMES are emitted as bare cites, resolved + kernel-checked by the
        // generated schema's ProveTask (a missing lemma fails THERE). The operand sort is the
        // goal LHS's sort (the reordered operator's carrier).
        const sort: term.SortId = @enumFromInt(@intFromEnum(prove.termSort(gn.lhs)));
        try common.pushACTriple(prove, &rules, &cites, op_sym, sort, op.assoc, op.comm, op.swap, c.rule.start);
    }
    const assoc_idx = pre_count;
    const comm_idx = pre_count + 1;
    const swap_idx = pre_count + 2;

    // abstract free caller-locals into params (goal + any LOCAL premise formula), then rewrite
    // both sides IN PARAM SPACE so the trace + schema body speak `p1, p2, …`.
    var local_pf: std.ArrayList(TermId) = .empty;
    for (pre_prepared.items) |p| try local_pf.append(prove.ctx.arena, p.formula);
    const ag = try common.abstractGoal(prove, &b, eq_goal_raw, local_pf.items, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = prove.pool.get(eq_goal).eq;
    const s0 = gn.lhs;
    const t0 = gn.rhs;

    const symbols: presburger_mod.Symbols = .{ .add = op_sym };
    const pre_rules = rules.items[0..pre_count];

    // distribute both sides (L→R with the pre-rules); traces feed the join unchanged.
    const s_pre = simplify_mod.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, pre_rules, s0, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const t_pre = simplify_mod.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, pre_rules, t0, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };

    // per side: re-associate to a right-nested comb, flatten, bubble-sort.
    const plan_s = (try common.acPlan(prove, symbols, rules.items, assoc_idx, comm_idx, swap_idx, s_pre.nf)) orelse
        return prove.fail(c.rule.start, "assoc_commut: could not re-associate the left side", .{});
    const plan_t = (try common.acPlan(prove, symbols, rules.items, assoc_idx, comm_idx, swap_idx, t_pre.nf)) orelse
        return prove.fail(c.rule.start, "assoc_commut: could not re-associate the right side", .{});
    if (!prove.pool.alphaEq(plan_s.sorted, plan_t.sorted)) {
        return prove.fail(c.rule.start, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
            try prove.renderTerm(try common.unabstract(prove, plan_s.sorted, abs)),
            try prove.renderTerm(try common.unabstract(prove, plan_t.sorted, abs)),
        });
    }
    // prepend the distribution trace so the join replays s0 -> distributed -> sorted.
    const full_s = try common.concatTrace(prove, s_pre.trace, plan_s.trace);
    const full_t = try common.concatTrace(prove, t_pre.trace, plan_t.trace);
    const rs: simplify_mod.Result = .{ .nf = plan_s.sorted, .trace = full_s };
    const rt: simplify_mod.Result = .{ .nf = plan_t.sorted, .trace = full_t };
    // ADMIT: both sides sort to the same summand multiset, so a certificate demonstrably
    // exists — only emitting it is pruned.
    if (prove.admit_mode) {
        prove.producer_premise_refs = null;
        prove.admit_ok = true;
        return null;
    }
    return common.finishReorder(prove, w, &b, c, "assoc_commut", s0, t0, rules.items, cites.items, rs, rt, abs, eigen, pre_prepared.items);
}
