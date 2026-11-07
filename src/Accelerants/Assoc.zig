//! The `assoc` accelerated tactic — a struct that is one variant of `Accelerants.Tactic`. See
//! `Accelerants.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const term = @import("../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const kernel = @import("../kernel.zig");
const Engine = @import("../Engine.zig");
const Walk = @import("../Engine/ProveTask/Walk.zig");
const Elab = @import("../Engine/ProveTask/Elab.zig");
const Accelerants = @import("../Accelerants.zig");
const EqCert = @import("EqCert.zig");
const rewrite = @import("rewrite.zig");
const Site = @import("Site.zig");
const Error = Site.Error;
const common = @import("common.zig");
const ac = @import("ac.zig");
const Symbols = @import("symbols.zig").Symbols;

/// `assoc_commut*`: commutativity too (sort to a summand multiset), not re-nesting only
commut: bool,
/// the `_quantified` variant: a `forall …; s = t` goal, peeled first
quantified: bool,

pub const schema_slot: Accelerants.SchemaSlot = .none;
pub const premise_shape: Accelerants.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = true;

/// Phase 1: nothing beyond the cited facts, which the scaffolding demands from the consts above.
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
    return if (self.commut)
        (if (self.quantified) produceAssocCommutQuantified(site, w, e, goal, c) else produceAssocCommut(site, w, e, goal, c))
    else
        (if (self.quantified) produceAssocQuantified(site, w, e, goal, c) else produceAssoc(site, w, e, goal, c));
}

/// `using assoc(assocLemma)` — prove `s = t` when the sides differ by ASSOCIATIVITY ALONE of
/// a single operator. The lemma (the sole arg) must have shape `f(f(a,b),c) = f(a,f(b,c))`;
/// the operator `f` is recovered from its LHS head. Right-nests both sides with the lemma as
/// a terminating rewrite and joins.
pub fn produceAssoc(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    const gn = site.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return site.fail(c.rule.start, "assoc proves equations; use assoc_quantified for a 'forall …; s = t' goal", .{});
        }
        return site.fail(c.rule.start, "assoc proves equations; the goal is not an equation", .{});
    }
    return buildAssoc(site, w, e, c, goal, &.{});
}

/// `using assoc_quantified(assocLemma)` — like assoc but over a `forall …; s = t` goal: peel
/// the ∀ prefix into eigenvariables, reorder the body, re-generalize.
pub fn produceAssocQuantified(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    const peeled = try common.peelForallEq(site, goal, c, "assoc_quantified") orelse return null;
    return buildAssoc(site, w, e, c, peeled.body, peeled.eigen);
}

/// Shared assoc core over the (possibly ∀-peeled) equation body `eq_goal_raw`. Abstracts the
/// goal's free caller-locals into params, builds the one-rule assoc set from the arg lemma,
/// right-nests both sides, and hands the join to `finishReorder`.
fn buildAssoc(site: *Site, w: *const Walk, e: *Elab, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerants.Synthetic {
    if (c.args.len != 1) {
        return site.fail(c.rule.start, "assoc requires an associativity lemma: assoc(<assocLemma>); got {d} argument(s)", .{c.args.len});
    }
    // ADMIT: goal-shape (equation) validated in the caller + arg-count here. The next step
    // (`argRule` → resolveFactRef) RESOLVES the associativity lemma — which is exactly what an
    // admitted step must NOT require proved (e.g. assoc_oracle's `opAssoc` is unresolvable). Skip.
    // `--fast` declines to EMIT the certificate; the ASSOCIATIVITY NORMALIZATION still runs.
    // Admit lands after the normal-form comparison below.
    var b: Accelerants.Builder = .{ .arena = site.ctx.arena, .interner = site.ctx.interner, .pool = site.pool, .loc = c.rule.start };

    const prepared = try common.argRule(site, w, c.args[0]);
    // validate the shape `f(f(a,b),c) = f(a,f(b,c))`: the LHS must be a binary app whose head
    // `f` is shared by the RHS. (The rule's binders/lhs/rhs carry pattern fvars already.)
    const l = site.pool.get(prepared.rule.lhs);
    if (l != .app or l.app.args.len != 2) {
        return site.fail(Elab.exprLoc(c.args[0]), "assoc: the associativity lemma must have shape 'f(f(a, b), c) = f(a, f(b, c))'", .{});
    }
    const op_sym = l.app.sym;
    const r = site.pool.get(prepared.rule.rhs);
    if (r != .app or r.app.sym != op_sym) {
        return site.fail(Elab.exprLoc(c.args[0]), "assoc: the associativity lemma's two sides must share the operator", .{});
    }

    // abstract free caller-local fvars into params UP FRONT (before normalizing) so the goal,
    // the trace, and the schema body all speak `p1, p2, …`. Eigenvariables stay free (re-bound
    // by the `fix` wrapper). A LOCAL lemma's formula may share such an fvar — include it.
    const local_pf: []const TermId = if (prepared.local) &.{prepared.formula} else &.{};
    const ag = try common.abstractGoal(site, &b, eq_goal_raw, local_pf, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = site.pool.get(eq_goal).eq;
    const s = gn.lhs;
    const t = gn.rhs;

    const rules = [_]rewrite.Rule{prepared.rule};
    const cites = [_]EqCert.RuleCite{prepared.cite};

    // right-nest each side by the single associativity rule (terminating). The resulting
    // canonical forms agree iff the sides differ by associativity alone.
    const rs = rewrite.normalize(site.ctx.arena, site.pool, site.ctx.interner, &rules, s, 1000) catch |err| switch (err) {
        error.Limit => return site.fail(c.rule.start, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = rewrite.normalize(site.ctx.arena, site.pool, site.ctx.interner, &rules, t, 1000) catch |err| switch (err) {
        error.Limit => return site.fail(c.rule.start, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!site.pool.alphaEq(rs.nf, rt.nf)) {
        return site.fail(c.rule.start, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
            try site.renderTerm(try common.unabstract(site, rs.nf, abs)),
            try site.renderTerm(try common.unabstract(site, rt.nf, abs)),
        });
    }
    // ADMIT: both sides reached the same associativity normal form, so a certificate
    // demonstrably exists — only emitting it is pruned.
    if (site.admit_mode) {
        site.producer_premise_refs = null;
        site.admit_ok = true;
        return null;
    }
    return common.finishReorder(site, w, e, &b, c, "assoc", s, t, &rules, &cites, rs, rt, abs, eigen, if (prepared.local) &.{prepared} else &.{});
}

/// `using assoc_commut` (bare = the well-known add/mul triple) or `assoc_commut(a, c, s)`
/// (an explicit assoc/comm/swap triple for a custom operator) — reorder an A/C sum: optional
/// distribute pre-pass (LOCAL cited refs → antecedents), then re-associate + flatten +
/// bubble-sort each side into canonical order, joining the concatenated traces.
pub fn produceAssocCommut(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    const gn = site.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return site.fail(c.rule.start, "assoc_commut proves equations; use assoc_commut_quantified for a 'forall …; s = t' goal", .{});
        }
        return site.fail(c.rule.start, "assoc_commut proves equations; the goal is not an equation", .{});
    }
    return buildAssocCommut(site, w, e, c, goal, &.{});
}

pub fn produceAssocCommutQuantified(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    const peeled = try common.peelForallEq(site, goal, c, "assoc_commut_quantified") orelse return null;
    return buildAssocCommut(site, w, e, c, peeled.body, peeled.eigen);
}

/// Shared assoc_commut core over the (possibly ∀-peeled) equation body. Prepares the AC rule
/// set (distribute pre-rules from `c.refs` at the FRONT, then the AC triple), abstracts the
/// goal, distributes + AC-sorts both sides, and hands the concatenated traces to
/// `finishReorder`.
fn buildAssocCommut(site: *Site, w: *const Walk, e: *Elab, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerants.Synthetic {
    // exactly two forms: bare (well-known add/mul) or three explicit lemmas. No partials.
    if (c.args.len != 0 and c.args.len != 3) {
        return site.fail(c.rule.start, "assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got {d}", .{c.args.len});
    }
    // ADMIT: goal-shape (equation) validated in the caller + arg-count here. Everything below
    // RESOLVES the (distribute pre-rules and, for the explicit form, the AC triple) lemmas and
    // runs the AC re-association search. Skip the resolution + decision under `--fast`.
    // `--fast` declines to EMIT the certificate; the A/C REORDERING DECISION still runs.
    // Admit lands after the summand comparison below.
    const explicit = c.args.len == 3;
    var b: Accelerants.Builder = .{ .arena = site.ctx.arena, .interner = site.ctx.interner, .pool = site.pool, .loc = c.rule.start };

    // optional distribute PRE-RULES from the cited refs (L→R before flattening); their rule
    // indices sit at the FRONT so the AC bubble-sort's indices shift after them.
    var rules: std.ArrayList(rewrite.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var pre_prepared: std.ArrayList(common.PreparedRule) = .empty;
    for (c.refs) |ref| {
        const p = try common.prepareRule(site, w, ref);
        try rules.append(site.ctx.arena, p.rule);
        try cites.append(site.ctx.arena, p.cite);
        try pre_prepared.append(site.ctx.arena, p);
    }
    const pre_count = rules.items.len;

    // resolve the AC triple + its operator BEFORE abstracting (an explicit lemma may carry
    // pattern fvars — never caller-locals — so it is unaffected by abstraction). Bare form:
    // pick the operator from the goal's LHS head and resolve the well-known triple.
    var op_sym: term.SymId = undefined;
    if (explicit) {
        const a_rule = try common.argRule(site, w, c.args[0]);
        const c_rule = try common.argRule(site, w, c.args[1]);
        const w_rule = try common.argRule(site, w, c.args[2]);
        const c_lhs = site.pool.get(c_rule.rule.lhs);
        if (c_lhs != .app or c_lhs.app.args.len != 2) {
            return site.fail(Elab.exprLoc(c.args[1]), "assoc_commut: the commutativity lemma must have shape 'f(a, b) = f(b, a)'", .{});
        }
        op_sym = c_lhs.app.sym;
        try rules.append(site.ctx.arena, a_rule.rule);
        try cites.append(site.ctx.arena, a_rule.cite);
        try rules.append(site.ctx.arena, c_rule.rule);
        try cites.append(site.ctx.arena, c_rule.cite);
        try rules.append(site.ctx.arena, w_rule.rule);
        try cites.append(site.ctx.arena, w_rule.cite);
        // an explicit lemma cited by a LOCAL step is an antecedent too.
        if (a_rule.local) try pre_prepared.append(site.ctx.arena, a_rule);
        if (c_rule.local) try pre_prepared.append(site.ctx.arena, c_rule);
        if (w_rule.local) try pre_prepared.append(site.ctx.arena, w_rule);
    } else {
        const gn = site.pool.get(eq_goal_raw).eq;
        // the reordered operator is the head of the left side AFTER the cited pre-rules have
        // distributed it (`mul(add(a, b), c)` is an add-sum once mulAddDistribRight fires).
        const lhs_pre = rewrite.normalize(site.ctx.arena, site.pool, site.ctx.interner, rules.items[0..pre_count], gn.lhs, 1000) catch |err| switch (err) {
            error.Limit => return site.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
            error.OutOfMemory => return error.OutOfMemory,
        };
        const s_head: ?term.SymId = if (site.pool.get(lhs_pre.nf) == .app) site.pool.get(lhs_pre.nf).app.sym else null;
        const op = common.pickWellKnownOp(site, s_head) orelse
            return site.fail(c.rule.start, "assoc_commut reorders an add- or mul-sum; the goal's left side is '{s}'", .{try site.renderTerm(gn.lhs)});
        op_sym = op.sym;
        // BUILD the AC triple as HARDCODED shapes (no facts.lookup, no existence check) — like
        // polynomial. Each rule's LHS/RHS is constructed from the goal's own operator sym; the
        // well-known lemma NAMES are emitted as bare cites, resolved + kernel-checked by the
        // generated schema's ProveTask (a missing lemma fails THERE). The operand sort is the
        // goal LHS's sort (the reordered operator's carrier).
        const sort: term.SortId = @enumFromInt(@intFromEnum(site.termSort(gn.lhs)));
        try ac.pushACTriple(site, &rules, &cites, op_sym, sort, op.assoc, op.comm, op.swap, c.rule.start);
    }
    const assoc_idx = pre_count;
    const comm_idx = pre_count + 1;
    const swap_idx = pre_count + 2;

    // abstract free caller-locals into params (goal + any LOCAL premise formula), then rewrite
    // both sides IN PARAM SPACE so the trace + schema body speak `p1, p2, …`.
    var local_pf: std.ArrayList(TermId) = .empty;
    for (pre_prepared.items) |p| try local_pf.append(site.ctx.arena, p.formula);
    const ag = try common.abstractGoal(site, &b, eq_goal_raw, local_pf.items, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = site.pool.get(eq_goal).eq;
    const s0 = gn.lhs;
    const t0 = gn.rhs;

    const symbols: Symbols = .{ .add = op_sym };
    const pre_rules = rules.items[0..pre_count];

    // distribute both sides (L→R with the pre-rules); traces feed the join unchanged.
    const s_pre = rewrite.normalize(site.ctx.arena, site.pool, site.ctx.interner, pre_rules, s0, 1000) catch |err| switch (err) {
        error.Limit => return site.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const t_pre = rewrite.normalize(site.ctx.arena, site.pool, site.ctx.interner, pre_rules, t0, 1000) catch |err| switch (err) {
        error.Limit => return site.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };

    // per side: re-associate to a right-nested comb, flatten, bubble-sort.
    const plan_s = (try ac.acPlan(site, symbols, rules.items, assoc_idx, comm_idx, swap_idx, s_pre.nf)) orelse
        return site.fail(c.rule.start, "assoc_commut: could not re-associate the left side", .{});
    const plan_t = (try ac.acPlan(site, symbols, rules.items, assoc_idx, comm_idx, swap_idx, t_pre.nf)) orelse
        return site.fail(c.rule.start, "assoc_commut: could not re-associate the right side", .{});
    if (!site.pool.alphaEq(plan_s.sorted, plan_t.sorted)) {
        return site.fail(c.rule.start, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
            try site.renderTerm(try common.unabstract(site, plan_s.sorted, abs)),
            try site.renderTerm(try common.unabstract(site, plan_t.sorted, abs)),
        });
    }
    // prepend the distribution trace so the join replays s0 -> distributed -> sorted.
    const full_s = try common.concatTrace(site, s_pre.trace, plan_s.trace);
    const full_t = try common.concatTrace(site, t_pre.trace, plan_t.trace);
    const rs: rewrite.Result = .{ .nf = plan_s.sorted, .trace = full_s };
    const rt: rewrite.Result = .{ .nf = plan_t.sorted, .trace = full_t };
    // ADMIT: both sides sort to the same summand multiset, so a certificate demonstrably
    // exists — only emitting it is pruned.
    if (site.admit_mode) {
        site.producer_premise_refs = null;
        site.admit_ok = true;
        return null;
    }
    return common.finishReorder(site, w, e, &b, c, "assoc_commut", s0, t0, rules.items, cites.items, rs, rt, abs, eigen, pre_prepared.items);
}
