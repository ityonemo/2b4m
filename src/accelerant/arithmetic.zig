//! The `arithmetic` accelerant: closes a linear-integer-arithmetic goal from
//! its cited premises. Three certifiers are tried in order — an
//! equation/order/exists tower certificate, a Farkas combination for linear
//! inequalities, and a Cooper quantifier-elimination replay (with a
//! single-variable induction fallback) — each replaying the decision as
//! ordinary kernel steps; only in `--fast` (verify.certify_arithmetic = false)
//! does a `.valid` verdict that no certifier discharges fall back to an
//! `.accelerated` step. Split out of the elaborate monolith; the shared
//! block/step/tower/well-known-fact substrate stays as `pub` methods on
//! `Elaborator`.

const std = @import("std");
const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;

const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const Statement = @import("../env.zig").Statement;
const StatementId = @import("../env.zig").StatementId;

const lexer = @import("../lexer.zig");
const simplify_mod = @import("../simplify.zig");
const smt_mod = @import("arithmetic/smt.zig");
const presburger_mod = @import("arithmetic/presburger.zig");
const farkas_mod = @import("arithmetic/farkas.zig");
const common = @import("_common.zig");

// Plan/context types that live on the Elaborator (shared with the surface
// certificate machinery) but are named here.
const BodyPlan = Elaborator.BodyPlan;
const InnerPlan = Elaborator.InnerPlan;
const Ctx = Elaborator.Ctx;
const SchemaArgs = Elaborator.SchemaArgs;

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    return arithmeticJustification(self, low, block_id, goal, c);
}

/// The body-emit for arithmetic's strict-mode closure (`common.generate`): walk
/// the certifier chain against the fresh-eigenvar body, first-`certified`-wins.
/// The closure has surfaced each cited premise as a labeled hypothesis in the
/// fresh Lowering, so a certifier's `c.refs` lookups resolve them there. Returns
/// null when EVERY certifier declines (valid-but-uncertifiable) — the caller
/// then does fallback/terminal; each link's decline reason is left in `.reasons`.
const CertifierBody = struct {
    c: ast.Step.Claim,
    symbols: presburger_mod.Symbols,
    loc: u32,
    reasons: [certifiers.len]Reason,
    pub fn emit(b: *CertifierBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!?kernel.Justification {
        for (certifiers, 0..) |link, i| {
            switch (try link.run(self, low, block, body_goal, b.c, b.symbols, b.loc)) {
                .certified => |just| return just,
                .declined => |r| b.reasons[i] = r,
            }
        }
        return null;
    }
};

/// A cited hypothesis prepared for certificate use. A less_than premise
/// contributes its witness equation (via lessThanElim + unpack) as a
/// ground rewrite rule t0 -> add(s0, succ(w)); an equation premise is a
/// ground rule directly.
pub const CertStatement = struct { id: StatementId, is_axiom: bool };

pub const CertPremise = struct {
    formula: TermId,
    /// null = statement citation, emitted at certificate time
    step: ?kernel.SRef,
    statement: ?CertStatement,
    /// index of this premise's ground rule in the rule array (its
    /// source sref is patched in during emission)
    rule_idx: usize,
    /// less_than premises only: the elim/unpack plan
    elim: ?struct {
        rule: simplify_mod.Rule,
        args: []const TermId,
        /// the instantiated implication and its existential consequent
        implication: TermId,
        exists_formula: TermId,
        w: term.Node.Fvar,
        /// the existential body opened at w, and its flip
        opened_eq: TermId,
        sym_formula: TermId,
    },
};

fn containsSubterm(self: *const Elaborator, hay: TermId, needle: TermId) bool {
    if (self.pool.alphaEq(hay, needle)) return true;
    switch (self.pool.get(hay)) {
        .bvar, .fvar => return false,
        .app, .pred => |a| {
            for (self.pool.args(a)) |arg| {
                if (containsSubterm(self, arg, needle)) return true;
            }
            return false;
        },
        .eq => |p| return containsSubterm(self, p.lhs, needle) or containsSubterm(self, p.rhs, needle),
        .not => |inner| return containsSubterm(self, inner, needle),
        .bin => |b| return containsSubterm(self, b.lhs, needle) or containsSubterm(self, b.rhs, needle),
        .quant => |q| return containsSubterm(self, q.body, needle),
    }
}

fn arithmeticCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols) ElabError!?kernel.Justification {
    const loc = c.rule.start;

    // resolve the cited hypotheses (resolvePremises already validated
    // accessibility and existence on the accelerated path)
    var premises: std.ArrayList(CertPremise) = .empty;
    for (c.refs) |ref| {
        const name = try self.internTok(ref);
        var formula: TermId = undefined;
        var step: ?kernel.SRef = null;
        var statement: ?CertStatement = null;
        if (low.labels.get(name)) |target| {
            const sid = target.step;
            formula = low.steps.items[@intFromEnum(sid)].formula;
            step = .{ .id = sid, .loc = ref.start };
        } else {
            const stmt_id = try self.resolveStatementRef(ref);
            switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
                .axiom => |a| {
                    formula = a.formula;
                    statement = .{ .id = stmt_id, .is_axiom = true };
                },
                .theorem => |t| {
                    // an accelerated premise poisons the certificate
                    if (!t.proven or t.accelerated.len != 0) return null;
                    formula = t.formula;
                    statement = .{ .id = stmt_id, .is_axiom = false };
                },
                .schema => return null,
            }
        }
        const node = self.pool.get(formula);
        const kind_ok = node == .eq or
            (node == .pred and Elaborator.symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2);
        if (!kind_ok) return null; // quantified or foreign hypotheses: accelerated path
        try premises.append(self.arena, .{
            .formula = formula,
            .step = step,
            .statement = statement,
            .rule_idx = undefined, // assigned below
            .elim = null,
        });
    }
    if (try arithCertCore(self, low, block_id, goal, premises.items, symbols, loc)) |just| return just;
    // The rewrite-normalizer declined. Try the LINEAR-COMBINATION path: an
    // equation goal that follows by cancelling an equality PREMISE (e.g.
    // sub(a,r) = mul(b,q) from the premise add(mul(b,q), r) = a). The normalizer
    // can't fire a premise equation as a rewrite when its sides don't occur
    // literally in the goal — but the goal IS a linear combination of it.
    return premiseCombinationCert(self, low, block_id, goal, premises.items, symbols, loc);
}

/// Certify an equation goal `G_l = G_r` as a linear combination of a single
/// equality PREMISE `P_l = P_r`: it holds iff `add(P_l, G_l) = add(P_r, G_r)` is
/// a pure additive identity (the premise contributes ±1). Emit that identity via
/// the existing join, then rewrite the premise and cancel:
///   combined:  add(P_l, G_l) = add(P_r, G_r)          [pure identity, emitJoin]
///   rewrite P_l→P_r using the premise:  add(P_r, G_l) = add(P_r, G_r)
///   addCancelLeft(P_r, G_l, G_r):        G_l = G_r
/// Every emitted step is kernel-checked; a mis-combination fails the join.
fn premiseCombinationCert(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, premises: []CertPremise, symbols: presburger_mod.Symbols, loc: u32) ElabError!?kernel.Justification {
    const add_sym = symbols.add orelse return null;
    // need the well-known left-cancellation lemma to finish.
    const cancel = (try self.wellKnownFact("addCancelLeft", loc)) orelse return null;

    // the goal must be `forall …; G_l = G_r` (peel the prefix into fix blocks).
    const u = try self.peelUniversal(goal, "arith");
    const body_node = self.pool.get(u.body);
    if (body_node != .eq) return null;
    const gl = body_node.eq.lhs;
    const gr = body_node.eq.rhs;

    // build the normalizing rule set (the well-known term rules + AC), exactly as
    // arithCertCore does for a premise-free identity — NO premise rules here.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    for (Elaborator.wk_term_rule_names) |wk| {
        if (try self.wellKnownRule(wk, loc)) |r| try rules.append(self.arena, r);
    }
    if (rules.items.len == 0) return null;
    const term_rule_count = rules.items.len;
    var comm_idx: ?usize = null;
    var swap_idx: ?usize = null;
    if (try self.wellKnownRule("addIsCommutative", loc)) |r| {
        comm_idx = rules.items.len;
        try rules.append(self.arena, r);
    }
    if (try self.wellKnownRule("addLeftSwap", loc)) |r| {
        swap_idx = rules.items.len;
        try rules.append(self.arena, r);
    }

    // find an equality premise whose combined identity add(P_l,G_l)=add(P_r,G_r)
    // certifies, and whose sides are visible at this scope (a step ref).
    for (premises) |p| {
        const pn = self.pool.get(p.formula);
        if (pn != .eq) continue;
        if (p.step == null) continue; // need a step to cite for the rewrite + cancel
        const pl = pn.eq.lhs;
        const pr = pn.eq.rhs;
        const comb_lhs = try self.pool.addApp(.app, add_sym, &.{ pl, gl });
        const comb_rhs = try self.pool.addApp(.app, add_sym, &.{ pr, gr });
        const eq_plan = (try self.planEquation(symbols, rules.items, term_rule_count, comm_idx, swap_idx, comb_lhs, comb_rhs, loc)) orelse continue;

        // PLAN OK — emit inside the peeled fix blocks.
        var blocks: std.ArrayList(kernel.BlockId) = .empty;
        var parent = block_id;
        for (u.fix_vars) |fv| {
            const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = .{ .v = fv } });
            try blocks.append(self.arena, b);
            parent = b;
        }
        // combined identity: add(P_l, G_l) = add(P_r, G_r)
        const comb_formula = try self.pool.add(.{ .eq = .{ .lhs = comb_lhs, .rhs = comb_rhs } });
        const comb_just = try self.emitJoin(low, parent, loc, rules.items, comb_lhs, comb_rhs, eq_plan.rs, eq_plan.rt);
        const comb_ref = try self.emitStep(low, parent, loc, comb_formula, comb_just);
        // the premise, cited at this scope.
        const prem_ref = p.step.?;
        // rewrite P_l→P_r in the combined identity's LHS: add(P_r, G_l) = add(P_r, G_r)
        const rewritten_formula = try self.pool.add(.{ .eq = .{ .lhs = comb_rhs_with_pl_replaced: {
            break :comb_rhs_with_pl_replaced try self.pool.addApp(.app, add_sym, &.{ pr, gl });
        }, .rhs = comb_rhs } });
        const rewritten_ref = try self.emitStep(low, parent, loc, rewritten_formula, .{ .rewrite = .{ .equation = prem_ref, .target = comb_ref } });
        // addCancelLeft(P_r, G_l, G_r): add(P_r,G_l)=add(P_r,G_r) -> G_l=G_r.
        const cancel_inst = try self.emitInstance(low, parent, loc, try self.strippedRule(cancel.formula, cancel.source), &.{ pr, gl, gr });
        const goal_formula = try self.pool.add(.{ .eq = .{ .lhs = gl, .rhs = gr } });
        const carry: kernel.Justification = .{ .modus_ponens = .{ .implication = cancel_inst, .antecedent = rewritten_ref } };

        // forall_intro fold up.
        if (blocks.items.len == 0) return carry;
        _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, goal_formula, carry);
        var i = blocks.items.len;
        while (i > 1) {
            i -= 1;
            self.closeBlock(low, blocks.items[i]);
            _ = try self.emitStep(low, blocks.items[i - 1], loc, u.opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
        }
        self.closeBlock(low, blocks.items[0]);
        return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
    }
    return null;
}

/// The planning and emission core shared by the surface certificate and
/// the mixed-skeleton (D2) theory leaves.
pub fn arithCertCore(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, premises: []CertPremise, symbols: presburger_mod.Symbols, loc: u32) ElabError!?kernel.Justification {
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    for (Elaborator.wk_term_rule_names) |wk| {
        if (try self.wellKnownRule(wk, loc)) |r| try rules.append(self.arena, r);
    }
    if (rules.items.len == 0) return null;

    // hypothesis ground rules join the normalizing set
    for (premises) |*p| {
        const node = self.pool.get(p.formula);
        var rule: simplify_mod.Rule = undefined;
        if (node == .eq) {
            rule = .{
                .source = .{ .step = .{ .id = @enumFromInt(0), .loc = loc } }, // patched at emission
                .binders = &.{},
                .lhs = node.eq.lhs,
                .rhs = node.eq.rhs,
                .formula = p.formula,
            };
        } else {
            // less_than(s0, t0): instantiate lessThanElim structurally
            const elim_fact = (try self.wellKnownFact("lessThanElim", loc)) orelse return null;
            const elim_rule = try self.strippedRule(elim_fact.formula, elim_fact.source);
            const elim_body = self.pool.get(elim_rule.lhs);
            if (elim_body != .bin or elim_body.bin.op != .implies) return null;
            const args = (try simplify_mod.matchRule(self.arena, self.pool, self.env, elim_rule, elim_body.bin.lhs, p.formula)) orelse return null;
            var implication = elim_rule.formula;
            for (args) |arg| {
                const q = self.pool.get(implication);
                if (q != .quant) return null;
                implication = try self.pool.open(q.quant.body, arg);
            }
            const imp_node = self.pool.get(implication);
            if (imp_node != .bin or imp_node.bin.op != .implies) return null;
            const exists_formula = imp_node.bin.rhs;
            const ex_node = self.pool.get(exists_formula);
            if (ex_node != .quant or ex_node.quant.q != .exists) return null;
            const w: term.Node.Fvar = .{ .name = try self.freshNamed("w"), .sort = ex_node.quant.sort };
            const w_id = try self.pool.add(.{ .fvar = w });
            const opened_eq = try self.pool.open(ex_node.quant.body, w_id);
            const eq_node = self.pool.get(opened_eq);
            if (eq_node != .eq) return null;
            const sym_formula = try self.pool.add(.{ .eq = .{ .lhs = eq_node.eq.rhs, .rhs = eq_node.eq.lhs } });
            rule = .{
                .source = .{ .step = .{ .id = @enumFromInt(0), .loc = loc } }, // patched at emission
                .binders = &.{},
                .lhs = eq_node.eq.rhs,
                .rhs = eq_node.eq.lhs,
                .formula = sym_formula,
            };
            p.elim = .{
                .rule = elim_rule,
                .args = args,
                .implication = implication,
                .exists_formula = exists_formula,
                .w = w,
                .opened_eq = opened_eq,
                .sym_formula = sym_formula,
            };
        }
        // a self-embedding ground rule would loop the normalizer
        if (containsSubterm(self, rule.rhs, rule.lhs)) return null;
        p.rule_idx = rules.items.len;
        try rules.append(self.arena, rule);
    }
    const term_rule_count = rules.items.len;

    var comm_idx: ?usize = null;
    var swap_idx: ?usize = null;
    if (try self.wellKnownRule("addIsCommutative", loc)) |r| {
        comm_idx = rules.items.len;
        try rules.append(self.arena, r);
    }
    if (try self.wellKnownRule("addLeftSwap", loc)) |r| {
        swap_idx = rules.items.len;
        try rules.append(self.arena, r);
    }

    // peel the goal's universal prefix into synthesized fix blocks
    const u = try self.peelUniversal(goal, "arith");
    const opened = u.opened;
    const fix_vars = u.fix_vars;

    // plan completely before emitting anything (no rollback needed)
    const body = u.body;
    const body_node = self.pool.get(body);
    const plan: BodyPlan = plan: {
        if (try self.planInner(symbols, rules.items, term_rule_count, comm_idx, swap_idx, body, loc)) |inner| {
            break :plan .{ .inner = inner };
        }
        if (body_node == .quant and body_node.quant.q == .exists) {
            // C2c: search a constant witness tower, smallest first
            const zero_sym = symbols.zero orelse return null;
            const zero_term = try self.pool.addApp(.app, zero_sym, &.{});
            for (0..33) |k| {
                const witness = (try self.buildTower(symbols, k, zero_term)) orelse return null;
                const instance = try self.pool.open(body_node.quant.body, witness);
                if (try self.planInner(symbols, rules.items, term_rule_count, comm_idx, swap_idx, instance, loc)) |inner| {
                    break :plan .{ .exists = .{ .witness = witness, .instance = instance, .inner = inner } };
                }
            }
            return null;
        }
        return null;
    };

    var blocks: std.ArrayList(kernel.BlockId) = .empty;
    var parent = block_id;
    for (fix_vars) |fv| {
        const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = .{ .v = fv } });
        try blocks.append(self.arena, b);
        parent = b;
    }

    // hypothesis chains: citations, elim instances, witness unpacks;
    // each ground rule learns its source step here
    var unpacks: std.ArrayList(kernel.BlockId) = .empty;
    for (premises) |p| {
        const p_ref: kernel.SRef = p.step orelse blk: {
            const st = p.statement.?;
            break :blk try self.emitStep(low, parent, loc, p.formula, if (st.is_axiom)
                .{ .axiom_ref = .{ .stmt = st.id, .loc = loc } }
            else
                .{ .theorem_ref = .{ .stmt = st.id, .loc = loc } });
        };
        if (p.elim) |elim| {
            const imp_ref = try self.emitInstance(low, parent, loc, elim.rule, elim.args);
            const ex_ref = try self.emitStep(low, parent, loc, elim.exists_formula, .{ .modus_ponens = .{ .implication = imp_ref, .antecedent = p_ref } });
            const ub = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .unpack = .{ .v = elim.w, .source = ex_ref } });
            try unpacks.append(self.arena, ub);
            parent = ub;
            const eq_ref = try self.emitStep(low, ub, loc, elim.opened_eq, .{ .hypothesis = .{ .id = ub, .loc = loc } });
            const eq_node = self.pool.get(elim.opened_eq).eq;
            const refl_formula = try self.pool.add(.{ .eq = .{ .lhs = eq_node.lhs, .rhs = eq_node.lhs } });
            const refl_ref = try self.emitStep(low, ub, loc, refl_formula, .reflexivity);
            const sym_ref = try self.emitStep(low, ub, loc, elim.sym_formula, .{ .rewrite = .{ .equation = eq_ref, .target = refl_ref } });
            rules.items[p.rule_idx].source = .{ .step = sym_ref };
        } else {
            rules.items[p.rule_idx].source = .{ .step = p_ref };
        }
    }

    var carry: kernel.Justification = switch (plan) {
        .inner => |inner| try self.emitInner(low, parent, loc, inner),
        .exists => |ex| blk: {
            const inner_just = try self.emitInner(low, parent, loc, ex.inner);
            const inst_ref = try self.emitStep(low, parent, loc, ex.instance, inner_just);
            break :blk .{ .exists_intro = .{ .step = inst_ref, .witness = ex.witness, .witness_loc = loc } };
        },
    };
    // export the (witness-free) conclusion through each unpack
    var ui = unpacks.items.len;
    while (ui > 0) {
        ui -= 1;
        _ = try self.emitStep(low, unpacks.items[ui], loc, body, carry);
        self.closeBlock(low, unpacks.items[ui]);
        carry = .{ .exists_elim = .{ .id = unpacks.items[ui], .loc = loc } };
    }
    if (blocks.items.len == 0) return carry;
    _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, body, carry);
    var i = blocks.items.len;
    while (i > 1) {
        i -= 1;
        self.closeBlock(low, blocks.items[i]);
        _ = try self.emitStep(low, blocks.items[i - 1], loc, opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
    }
    self.closeBlock(low, blocks.items[0]);
    return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
}
fn arithmeticFallback(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, fb: lexer.Token, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const stmt_id = self.env.findStatementId(self.file, try self.internTok(fb)) orelse
        return self.fail(fb.start, "fallback names unknown theorem '{s}'", .{self.text(fb)});
    const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
    const formula: TermId, const cite_just: kernel.Justification, const is_hole: bool = switch (stmt) {
        .theorem => |t| blk: {
            if (!t.proven) return self.fail(fb.start, "fallback theorem '{s}' is not proven", .{self.text(fb)});
            try self.inheritAccelerated(t.accelerated);
            try self.inheritHoles(t.holes);
            break :blk .{ t.formula, .{ .theorem_ref = .{ .stmt = stmt_id, .loc = fb.start } }, false };
        },
        // an axiom (including a `hole`, which is an axiom-kind statement) is a
        // legitimate fallback: it discharges the goal by fiat. A hole propagates
        // its taint, so the whole proof is marked resting-on-a-hole and rejected
        // outside --draft — exactly the escape hatch for a goal the certifier
        // can't yet certify.
        .axiom => |a| .{ a.formula, .{ .axiom_ref = .{ .stmt = stmt_id, .loc = fb.start } }, a.is_hole },
        .schema => return self.fail(fb.start, "fallback cites a schema '{s}'; use a theorem", .{self.text(fb)}),
    };

    // FAST PATH: the fallback's statement IS the goal (alpha-equal). No
    // specialization — cite it directly (the original behaviour).
    if (self.pool.alphaEq(formula, goal)) {
        if (is_hole) try self.inheritHoles(self.env.statements.items[@intFromEnum(stmt_id)].axiom.holes);
        return cite_just;
    }

    // SPECIALIZE PATH: the goal is an INSTANCE of the fallback theorem —
    // `∀x₁…xₙ; A₁ -> … -> Aₘ -> C`, where C at some witnesses x⃗ is the goal and
    // each Aᵢ (at those witnesses) is supplied as a step ref. `arithmetic` already
    // DECIDED the goal, so this only needs to reconstruct the elim/mp chain; the
    // kernel re-checks every emitted step, so a mis-inferred witness cannot pass.
    //
    // Peel the ∀ prefix into fresh pattern fvars, then split the leading `->`
    // antecedents from the final consequent.
    var pattern_vars: std.ArrayList(StrId) = .empty;
    var f = formula;
    while (true) {
        const node = self.pool.get(f);
        if (node == .quant and node.quant.q == .forall) {
            const name = try self.freshNamed("fallback-var");
            const fv = try self.pool.add(.{ .fvar = .{ .name = name, .sort = node.quant.sort } });
            try pattern_vars.append(self.arena, name);
            f = try self.pool.open(node.quant.body, fv);
        } else break;
    }
    var antecedents: std.ArrayList(TermId) = .empty;
    while (true) {
        const node = self.pool.get(f);
        if (node == .bin and node.bin.op == .implies) {
            try antecedents.append(self.arena, node.bin.lhs);
            f = node.bin.rhs;
        } else break;
    }
    // Infer the witness for each pattern var by first-order matching the
    // consequent against the goal.
    var binds: std.AutoHashMapUnmanaged(StrId, TermId) = .empty;
    if (!try matchPattern(self, pattern_vars.items, f, goal, &binds)) {
        return self.fail(fb.start, "fallback theorem '{s}' does not prove this goal (its conclusion does not match, even after specialization)", .{self.text(fb)});
    }
    // Every pattern var must be pinned (no free-floating binder the consequent
    // didn't constrain — that would be an ambiguous specialization).
    var witnesses = try self.arena.alloc(TermId, pattern_vars.items.len);
    for (pattern_vars.items, 0..) |pv, i| {
        witnesses[i] = binds.get(pv) orelse
            return self.fail(fb.start, "fallback theorem '{s}' does not prove this goal (variable unconstrained by the conclusion)", .{self.text(fb)});
    }
    if (is_hole) try self.inheritHoles(self.env.statements.items[@intFromEnum(stmt_id)].axiom.holes);

    // For each fallback antecedent, substitute the inferred witnesses and find the
    // supplied ref whose formula matches it. The step's refs serve two roles here:
    // some are `arithmetic`-decision premises (they anchored the goal), others
    // discharge the fallback theorem's `->` antecedents. We pick, per antecedent,
    // the ref that proves it — order-independent — so the writer need not separate
    // the two groups.
    for (antecedents.items) |ant_raw| {
        var ant = ant_raw;
        for (pattern_vars.items, witnesses) |pv, w| ant = try self.pool.substFvar(ant, pv, w);
        var matched = false;
        for (c.refs) |ref| {
            const rid = try self.resolveStepRef(low, ref);
            if (self.pool.alphaEq(low.steps.items[@intFromEnum(rid.id)].formula, ant)) {
                matched = true;
                break;
            }
        }
        if (!matched) {
            return self.fail(fb.start, "fallback theorem '{s}' needs a hypothesis '{s}' — supply it as a ref to the arithmetic step", .{ self.text(fb), try self.renderTerm(ant) });
        }
    }

    // Emit: cite the theorem, forall_elim at each witness (peeling the ∀ prefix),
    // then modus_ponens each antecedent against its matching ref.
    var cur = try self.emitStep(low, block_id, fb.start, formula, cite_just);
    var cur_formula = formula;
    for (witnesses) |w| {
        const node = self.pool.get(cur_formula);
        const opened = try self.pool.open(node.quant.body, w);
        cur = try self.emitStep(low, block_id, fb.start, opened, .{ .forall_elim = .{ .step = cur, .with = w, .with_loc = fb.start } });
        cur_formula = opened;
    }
    for (antecedents.items) |ant_raw| {
        const node = self.pool.get(cur_formula);
        var ant = ant_raw;
        for (pattern_vars.items, witnesses) |pv, w| ant = try self.pool.substFvar(ant, pv, w);
        // find the matching ref (guaranteed to exist by the check above).
        var chosen: kernel.SRef = undefined;
        for (c.refs) |ref| {
            const rid = try self.resolveStepRef(low, ref);
            if (self.pool.alphaEq(low.steps.items[@intFromEnum(rid.id)].formula, ant)) {
                chosen = rid;
                break;
            }
        }
        cur = try self.emitStep(low, block_id, fb.start, node.bin.rhs, .{ .modus_ponens = .{ .implication = cur, .antecedent = chosen } });
        cur_formula = node.bin.rhs;
    }
    // The final step's formula must be the goal (kernel will confirm); return its
    // justification as this step's own.
    return low.steps.items[@intFromEnum(cur.id)].just;
}

/// First-order match: bind each `pattern` fvar (by name) to a witness term such
/// that substituting the bindings into `pat` yields `target`. Non-pattern fvars,
/// symbols, and structure must match exactly. A pattern var already bound must
/// bind consistently (alpha-equal witnesses). Returns false on any mismatch.
fn matchPattern(self: *Elaborator, pattern: []const StrId, pat: TermId, target: TermId, binds: *std.AutoHashMapUnmanaged(StrId, TermId)) ElabError!bool {
    const pn = self.pool.get(pat);
    // a bare pattern var: bind (or check consistency).
    if (pn == .fvar) {
        for (pattern) |pv| {
            if (pv == pn.fvar.name) {
                if (binds.get(pv)) |prev| return self.pool.alphaEq(prev, target);
                try binds.put(self.arena, pv, target);
                return true;
            }
        }
        // a non-pattern fvar: must match exactly.
        const tn = self.pool.get(target);
        return tn == .fvar and tn.fvar.name == pn.fvar.name and tn.fvar.sort == pn.fvar.sort;
    }
    const tn = self.pool.get(target);
    if (std.meta.activeTag(pn) != std.meta.activeTag(tn)) return false;
    switch (pn) {
        .bvar => return pn.bvar == tn.bvar,
        .fvar => unreachable, // handled above
        .app => |a| {
            if (a.sym != tn.app.sym or a.args_len != tn.app.args_len) return false;
            for (self.pool.args(a), self.pool.args(tn.app)) |pa, ta| {
                if (!try matchPattern(self, pattern, pa, ta, binds)) return false;
            }
            return true;
        },
        .pred => |a| {
            if (a.sym != tn.pred.sym or a.args_len != tn.pred.args_len) return false;
            for (self.pool.args(a), self.pool.args(tn.pred)) |pa, ta| {
                if (!try matchPattern(self, pattern, pa, ta, binds)) return false;
            }
            return true;
        },
        .eq => |p| return (try matchPattern(self, pattern, p.lhs, tn.eq.lhs, binds)) and
            (try matchPattern(self, pattern, p.rhs, tn.eq.rhs, binds)),
        .not => |t| return matchPattern(self, pattern, t, tn.not, binds),
        .bin => |b| return b.op == tn.bin.op and
            (try matchPattern(self, pattern, b.lhs, tn.bin.lhs, binds)) and
            (try matchPattern(self, pattern, b.rhs, tn.bin.rhs, binds)),
        .quant => |q| return q.q == tn.quant.q and q.sort == tn.quant.sort and
            (try matchPattern(self, pattern, q.body, tn.quant.body, binds)),
    }
}

fn arithmeticTerminal(self: *Elaborator, loc: u32, reasons: []const Reason) ElabError!kernel.Justification {
    const accelerated_name = self.interner.internString("arithmetic") catch return error.OutOfMemory;
    if (!self.verify.certify_arithmetic) {
        // --fast: take the accelerated verdict, record it
        for (self.accelerated_used.items) |o| {
            if (o == accelerated_name) return .{ .accelerated = accelerated_name };
        }
        try self.accelerated_used.append(self.arena, accelerated_name);
        return .{ .accelerated = accelerated_name };
    }
    // default: hard error listing why each link declined
    var msg: std.Io.Writer.Allocating = .init(self.arena);
    msg.writer.writeAll("'arithmetic' is valid but no certifier could prove it here:") catch return error.OutOfMemory;
    for (certifiers, reasons) |link, reason| {
        const detail = switch (reason) {
            .out_of_scope => "form not in certification scope",
            .missing_symbol => |s| blk: {
                var b: std.Io.Writer.Allocating = .init(self.arena);
                b.writer.print("theory lacks symbol '{s}'", .{s}) catch return error.OutOfMemory;
                break :blk b.written();
            },
            .missing_lemma => |s| blk: {
                var b: std.Io.Writer.Allocating = .init(self.arena);
                b.writer.print("theory lacks lemma '{s}'", .{s}) catch return error.OutOfMemory;
                break :blk b.written();
            },
        };
        msg.writer.print("\n  - {s}: {s}", .{ link.name, detail }) catch return error.OutOfMemory;
    }
    msg.writer.writeAll("\nuse --fast to accept the accelerated verdict") catch return error.OutOfMemory;
    return self.fail(loc, "{s}", .{msg.written()});
}
fn arithMixedCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols) ElabError!?kernel.Justification {
    const loc = c.rule.start;
    const steps_mark = low.steps.items.len;
    const blocks_mark = low.blocks.items.len;

    // premise steps (label refs are steps; statements get citations)
    const premise_steps = try self.arena.alloc(Elaborator.TautCert.Premise, c.refs.len);
    for (c.refs, premise_steps) |ref, *out| {
        const name = try self.internTok(ref);
        if (low.labels.get(name)) |target| {
            const sid = target.step; // resolvePremises rejected blocks
            out.* = .{
                .formula = low.steps.items[@intFromEnum(sid)].formula,
                .ref = .{ .id = sid, .loc = ref.start },
            };
        } else {
            const stmt_id = try self.resolveStatementRef(ref);
            switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
                .axiom => |a| out.* = .{
                    .formula = a.formula,
                    .ref = try self.emitStep(low, block_id, loc, a.formula, .{ .axiom_ref = .{ .stmt = stmt_id, .loc = loc } }),
                },
                .theorem => |t| {
                    if (!t.proven or t.accelerated.len != 0) {
                        low.steps.shrinkRetainingCapacity(steps_mark);
                        low.blocks.shrinkRetainingCapacity(blocks_mark);
                        return null; // an accelerated premise poisons the certificate
                    }
                    out.* = .{
                        .formula = t.formula,
                        .ref = try self.emitStep(low, block_id, loc, t.formula, .{ .theorem_ref = .{ .stmt = stmt_id, .loc = loc } }),
                    };
                },
                .schema => unreachable, // resolvePremises rejected these
            }
        }
    }

    // peel the universal prefix
    const u = try self.peelUniversal(goal, "arith");
    const opened = u.opened;
    const fix_vars = u.fix_vars;
    const body = u.body;

    var atoms: std.ArrayList(TermId) = .empty;
    for (premise_steps) |p| try smt_mod.collectAtoms(self.arena, self.pool, &atoms, p.formula);
    try smt_mod.collectAtoms(self.arena, self.pool, &atoms, body);
    if (atoms.items.len > smt_mod.atom_limit) {
        low.steps.shrinkRetainingCapacity(steps_mark);
        low.blocks.shrinkRetainingCapacity(blocks_mark);
        return null;
    }
    const assignment = try self.arena.alloc(?bool, atoms.items.len);
    @memset(assignment, null);
    const lits = try self.arena.alloc(?Elaborator.TautCert.Lit, atoms.items.len);
    @memset(lits, null);

    var blocks: std.ArrayList(kernel.BlockId) = .empty;
    var parent = block_id;
    for (fix_vars) |fv| {
        const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = .{ .v = fv } });
        try blocks.append(self.arena, b);
        parent = b;
    }

    var cert: Elaborator.TautCert = .{
        .elab = self,
        .low = low,
        .loc = loc,
        .goal = body,
        .premises = premise_steps,
        .atoms = atoms.items,
        .assignment = assignment,
        .lits = lits,
        .symbols = symbols,
    };
    const body_just = cert.goalJust(parent) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return error.Recover,
        error.Budget => {
            low.steps.shrinkRetainingCapacity(steps_mark);
            low.blocks.shrinkRetainingCapacity(blocks_mark);
            return null;
        },
    };
    if (blocks.items.len == 0) return body_just;
    _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, body, body_just);
    var i = blocks.items.len;
    while (i > 1) {
        i -= 1;
        self.closeBlock(low, blocks.items[i]);
        _ = try self.emitStep(low, blocks.items[i - 1], loc, opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
    }
    self.closeBlock(low, blocks.items[0]);
    return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
}

// --- the `arithmetic` accelerated tactic: Presburger arithmetic over Nat -
// The engine (src/presburger.zig) decides by quantifier elimination; a
// `.valid` verdict becomes an `.accelerated` kernel step. See ACCELERATION.md.

/// The arithmetic vocabulary, resolved by well-known name in this file's
/// scope. Absent names shrink the fragment.
/// Is `atom` a relation the arithmetic fragment is meant to decide — an
/// equation/disequation, or a `less_than` — as opposed to a genuinely
/// foreign predicate (which is legitimately opaque)?
fn looksArithmeticRelation(self: *const Elaborator, atom: TermId, symbols: presburger_mod.Symbols) bool {
    return switch (self.pool.get(atom)) {
        .eq => true,
        .not => |inner| self.pool.get(inner) == .eq,
        .pred => |p| Elaborator.symIs(p.sym, symbols.less_than),
        else => false,
    };
}

fn arithmeticSymbols(self: *Elaborator) ElabError!presburger_mod.Symbols {
    var symbols: presburger_mod.Symbols = .{};
    symbols.zero = try self.wellKnownSym("ZERO");
    symbols.one = try self.wellKnownSym("ONE");
    symbols.succ = try self.wellKnownSym("succ");
    symbols.prev = try self.wellKnownSym("prev");
    symbols.add = try self.wellKnownSym("add");
    symbols.mul = try self.wellKnownSym("mul");
    symbols.neg = try self.wellKnownSym("neg");
    symbols.sub = try self.wellKnownSym("sub");
    symbols.less_than = try self.wellKnownSym("less_than");
    // A well-known nonnegativity predicate: its PRESENCE in scope is the
    // theory's request to constrain its variables nonneg (ℕ binds it; ℤ does
    // not). Read as x >= 0 by the engine; injected per binder below.
    symbols.nonneg = try self.wellKnownSym("nonneg");
    const anchor = symbols.succ orelse symbols.add orelse symbols.zero orelse symbols.one;
    if (anchor) |sym| symbols.nat = self.env.sym(sym).result;
    return symbols;
}

const OrderHyp = struct { lo: TermId, hi: TermId, ref: kernel.SRef };

/// Why a certifier link declined a decided-valid goal. Surfaced (flat) at
/// the honest terminal when every link declines, so a goal that is valid
/// but sits on a thin theory yields an actionable fix rather than "write a
/// manual proof". `out_of_scope` is the expected "not my shape"; the
/// `missing_*` variants name a gap in the theory the user can close.
const Reason = union(enum) {
    out_of_scope,
    missing_symbol: []const u8,
    missing_lemma: []const u8,
};

/// A certifier link's result: it either emits kernel steps (certified) or
/// declines with a reason. Errors (OOM/Recover) stay in ElabError.
const Outcome = union(enum) {
    certified: kernel.Justification,
    declined: Reason,
};

/// One named entry in the certifier chain: the link's display name (for the
/// terminal reason list) and a function producing its Outcome.
const Certifier = struct {
    name: []const u8,
    run: *const fn (*Elaborator, *Lowering, kernel.BlockId, TermId, ast.Step.Claim, presburger_mod.Symbols, u32) ElabError!Outcome,
};

/// The certifier chain, walked first-`certified`-wins. Each link's decline
/// reason is collected for the honest terminal. A future Cooper-QE-replay
/// and a user-driven `manual` link slot in here as peer entries.
const certifiers = [_]Certifier{
    .{ .name = "equation/order/exists", .run = &equationCertifier },
    .{ .name = "mixed-skeleton", .run = &mixedCertifier },
    .{ .name = "farkas", .run = &farkasCertificate },
    .{ .name = "cooper", .run = &cooperCertificate },
};

/// Adapter: the equation/order/exists cert returns ?Justification; a null
/// is an "out of scope" decline (its internals resolve their own lemmas).
fn equationCertifier(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
    _ = loc;
    self.arith_missing_lemma = null;
    if (try arithmeticCertificate(self, low, block_id, goal, c, symbols)) |just| return .{ .certified = just };
    // if the decline was specifically a rewrite rule not imported into scope,
    // name it (a one-alias fix) rather than the generic "not my shape".
    if (self.arith_missing_lemma) |name| return .{ .declined = .{ .missing_lemma = name } };
    return .{ .declined = .out_of_scope };
}

/// Adapter: the mixed-skeleton (D2) cert returns ?Justification.
fn mixedCertifier(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
    _ = loc;
    if (try arithMixedCertificate(self, low, block_id, goal, c, symbols)) |just| return .{ .certified = just };
    return .{ .declined = .out_of_scope };
}

/// The Farkas certifier link over the difference-logic fragment. A goal
/// `forall v..; H1 -> ... -> Hn -> C` whose Hi are strict-order atoms is
/// certified by composing them with `lessThanTransitive`. Three conclusion
/// shapes (see emitFarkasConclusion): order composition `less_than(s, t)`
/// (fold a path s < ... < t), the self-loop `less_than(x, x)` (fold a
/// cycle), and INFEASIBILITY of an arbitrary conclusion (fold a cycle to
/// `less_than(x, x)`, contradict with `lessThanIrreflexive`, `absurd`).
/// Combines SEVERAL hypotheses, which the single-atom order cert cannot.
/// Declines when the goal is not this shape or a needed order lemma is
/// absent in the theory scope.
fn farkasCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
    _ = c;
    const less_than = symbols.less_than orelse return .{ .declined = .{ .missing_symbol = "less_than" } };
    const nat = symbols.nat orelse return .{ .declined = .out_of_scope };
    const transitive = (try self.wellKnownFact("lessThanTransitive", loc)) orelse
        return .{ .declined = .{ .missing_lemma = "lessThanTransitive" } };

    // 1. peel the forall prefix into fix blocks (eigenvariables), recording
    //    the residual formula at each depth for the forall_intro fold.
    var blocks: std.ArrayList(kernel.BlockId) = .empty;
    var opened: std.ArrayList(TermId) = .empty;
    var parent = block_id;
    var body = goal;
    while (true) {
        const node = self.pool.get(body);
        if (node != .quant or node.quant.q != .forall or node.quant.sort != nat) break;
        const name = try self.freshNamed(self.interner.stringBytes(node.quant.hint));
        const fv: term.Node.Fvar = .{ .name = name, .sort = nat };
        const fvt = try self.pool.add(.{ .fvar = fv });
        const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .fix = .{ .v = fv } });
        try blocks.append(self.arena, b);
        parent = b;
        body = try self.pool.open(node.quant.body, fvt);
        try opened.append(self.arena, body); // formula proved inside block[k]
    }

    // 2. peel the antecedent chain into assume blocks; restate each as a
    //    hypothesis and collect its strict-order edge.
    var assumes: std.ArrayList(kernel.BlockId) = .empty;
    var residual: std.ArrayList(TermId) = .empty; // formula proved inside assume[k]
    var edges: std.ArrayList(farkas_mod.Edge) = .empty;
    var hyps: std.ArrayList(OrderHyp) = .empty;
    var node_ids: std.ArrayList(TermId) = .empty;
    while (true) {
        const node = self.pool.get(body);
        if (node != .bin or node.bin.op != .implies) break;
        const ante = node.bin.lhs;
        const an = self.pool.get(ante);
        if (an != .pred or !Elaborator.symIs(an.pred.sym, less_than) or an.pred.args_len != 2) return .{ .declined = .out_of_scope };
        const b = try self.newBlock(low, try self.freshNamed("arithmetic"), parent, .{ .assume = ante });
        try assumes.append(self.arena, b);
        parent = b;
        const hyp_ref = try self.emitStep(low, b, loc, ante, .{ .hypothesis = .{ .id = b, .loc = loc } });
        const args = self.pool.args(an.pred);
        try edges.append(self.arena, .{
            .lo = try farkasNodeId(self, &node_ids, args[0]),
            .hi = try farkasNodeId(self, &node_ids, args[1]),
        });
        try hyps.append(self.arena, .{ .lo = args[0], .hi = args[1], .ref = hyp_ref });
        body = node.bin.rhs;
        try residual.append(self.arena, body);
    }
    if (edges.items.len == 0) return .{ .declined = .out_of_scope }; // nothing to combine: not Farkas

    // 2b. COEFFICIENT SCALING (stage 1): if the conclusion mentions a
    //     literal coefficient `mul(k, x)`, derive scaled edges
    //     less_than(mul(k,lo), mul(k,hi)) from each base hypothesis via
    //     multiplicationPreservesOrder, so the fold can line them up.
    const base_count = edges.items.len;
    var literals: std.ArrayList(usize) = .empty;
    try collectScaleLiterals(self, symbols, body, &literals);
    // literals also live in the hypotheses (a hyp `mul(THREE, b) <
    // mul(THREE, a)` while the conclusion is a bare `less_than(a, a)`).
    for (hyps.items) |h| {
        try collectScaleLiterals(self, symbols, h.lo, &literals);
        try collectScaleLiterals(self, symbols, h.hi, &literals);
    }
    if (!try emitScaledEdges(self, low, parent, loc, symbols, literals.items, base_count, &edges, &hyps, &node_ids)) {
        // scaling needed but a lemma/symbol absent: decline (a later stage
        // could report the specific missing_lemma).
        if (literals.items.len != 0) return .{ .declined = .{ .missing_lemma = "multiplicationPreservesOrder" } };
    }

    // 2c. SUM PATH (stage 2): if the conclusion is an add-sum order atom
    //     `less_than(add(_,_), add(_,_))` that no single hypothesis proves,
    //     derive a summed edge from a pair of base hypotheses via
    //     additionPreservesOrder + commutativity + transitivity.
    if (symbols.add) |_| {
        const cn0 = self.pool.get(body);
        const wants_sum = cn0 == .pred and Elaborator.symIs(cn0.pred.sym, less_than) and cn0.pred.args_len == 2 and
            isAddSum(self, symbols, self.pool.args(cn0.pred)[0]);
        if (wants_sum and base_count >= 2) {
            if (try trySumEdges(self, low, parent, loc, symbols, body, base_count, &edges, &hyps, &node_ids)) |missing| {
                if (missing.len != 0) return .{ .declined = .{ .missing_lemma = missing } };
            }
        }
    }

    // 3+4. prove the conclusion from the order chain, dispatching on its
    //      shape. Three cases:
    //   (a) less_than(s, t), s != t  — ORDER COMPOSITION: fold a path
    //       s < ... < t (no cycle, no irreflexivity).
    //   (b) less_than(x, x)          — the self-loop is the conclusion: a
    //       cycle folds directly to it.
    //   (c) anything else            — INFEASIBILITY CAP: fold a cycle to
    //       less_than(x, x), contradict with lessThanIrreflexive, and
    //       `absurd` proves the (arbitrary) conclusion.
    var carry = (try emitFarkasConclusion(self, low, parent, loc, transitive.formula, transitive.source, less_than, body, edges.items, hyps.items, &node_ids)) orelse
        return .{ .declined = .out_of_scope };

    // 5. export through the assume blocks (implies_intro), then the fix
    //    blocks (forall_intro).
    var ai = assumes.items.len;
    while (ai > 0) {
        ai -= 1;
        _ = try self.emitStep(low, assumes.items[ai], loc, residual.items[ai], carry);
        self.closeBlock(low, assumes.items[ai]);
        carry = .{ .implies_intro = .{ .id = assumes.items[ai], .loc = loc } };
    }
    if (blocks.items.len == 0) return .{ .certified = carry };
    _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, opened.items[opened.items.len - 1], carry);
    var i = blocks.items.len;
    while (i > 1) {
        i -= 1;
        self.closeBlock(low, blocks.items[i]);
        _ = try self.emitStep(low, blocks.items[i - 1], loc, opened.items[i - 1], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
    }
    self.closeBlock(low, blocks.items[0]);
    return .{ .certified = .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } } };
}
/// The simplify-rule set `planInner` needs: the well-known recursion
/// axioms plus the commutativity/left-swap rules (their indices for the
/// sorted-tower permutation). Shared by the Cooper certifier's arm planner.
const ArithRules = struct {
    rules: []const simplify_mod.Rule,
    term_rule_count: usize,
    comm_idx: ?usize,
    swap_idx: ?usize,
};

fn arithRules(self: *Elaborator, loc: u32) ElabError!?ArithRules {
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    for (Elaborator.wk_term_rule_names) |wk| {
        if (try self.wellKnownRule(wk, loc)) |r| try rules.append(self.arena, r);
    }
    if (rules.items.len == 0) return null;
    const term_rule_count = rules.items.len;
    var comm_idx: ?usize = null;
    var swap_idx: ?usize = null;
    if (try self.wellKnownRule("addIsCommutative", loc)) |r| {
        comm_idx = rules.items.len;
        try rules.append(self.arena, r);
    }
    if (try self.wellKnownRule("addLeftSwap", loc)) |r| {
        swap_idx = rules.items.len;
        try rules.append(self.arena, r);
    }
    return .{ .rules = rules.items, .term_rule_count = term_rule_count, .comm_idx = comm_idx, .swap_idx = swap_idx };
}

/// A proof of a (possibly disjunctive) body: the inner plan, plus the
/// or-intro path to lift it into the whole disjunction. `path` is the
/// sequence of left/right choices from the outside in (empty for a bare
/// atom), so the emitter wraps the inner proof in that many `or_intro`s.
const DisjPlan = struct { inner: InnerPlan, path: []const bool, atom: TermId };

/// Plan a body that may be a right/left nest of `or`: find the first arm an
/// InnerPlan certifies, recording the or-intro path to it. Returns null when
/// no arm is provable.
fn planDisjunction(self: *Elaborator, symbols: presburger_mod.Symbols, ar: ArithRules, body: TermId, loc: u32) ElabError!?DisjPlan {
    var path: std.ArrayList(bool) = .empty;
    var cur = body;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .bin and node.bin.op == .or_op) {
            // try the left arm (path so far + left), else descend right.
            try path.append(self.arena, false);
            if (try self.planInner(symbols, ar.rules, ar.term_rule_count, ar.comm_idx, ar.swap_idx, node.bin.lhs, loc)) |inner| {
                return .{ .inner = inner, .path = try self.arena.dupe(bool, path.items), .atom = node.bin.lhs };
            }
            _ = path.pop();
            try path.append(self.arena, true);
            cur = node.bin.rhs;
            continue;
        }
        if (try self.planInner(symbols, ar.rules, ar.term_rule_count, ar.comm_idx, ar.swap_idx, cur, loc)) |inner| {
            return .{ .inner = inner, .path = try self.arena.dupe(bool, path.items), .atom = cur };
        }
        return null;
    }
}

/// Reconstruct a boundary witness `boundaries[i] + j` (a linear form over
/// the fixed variables) as a term. Layer 2 handles the single-free-variable
/// case: coeff 0 (a constant `succ^(konst+j)(ZERO)` / `prev^…(ZERO)`) or coeff 1
/// on the one eigenvariable (`succ^(konst+j)(x)` / `prev^…(x)`). A NEGATIVE total
/// offset builds a `prev`-tower over ℤ (null for ℕ, which has no prev); a higher
/// coefficient is out of layer-2 scope → null.
fn buildWitness(self: *Elaborator, symbols: presburger_mod.Symbols, replay: presburger_mod.Replay, dump: presburger_mod.LinearDump, j: i128, fix_vars: []const term.Node.Fvar) ElabError!?TermId {
    // find the (at most one) free var with a nonzero coefficient. A boundary
    // coeff is indexed by presburger variable id; `free_ids[p]` is the id of
    // the p-th free var, which corresponds to fix_vars[p] (both in first-
    // appearance / forall-binder order).
    var fix_index: ?usize = null;
    for (dump.coeffs, 0..) |co, id| {
        if (co == 0) continue;
        if (co != 1) return null; // coeff>1: out of layer-2 scope
        // locate this id among the free vars
        const p = std.mem.indexOfScalar(u32, replay.free_ids, @intCast(id)) orelse return null;
        if (fix_index != null) return null; // 2+ free vars in the witness
        fix_index = p;
    }
    const offset = dump.konst + j;
    const zero_sym = symbols.zero orelse return null;
    const base = if (fix_index) |p| blk: {
        if (p >= fix_vars.len) return null;
        break :blk try self.pool.add(.{ .fvar = fix_vars[p] });
    } else try self.pool.addApp(.app, zero_sym, &.{});
    return try self.buildTowerSigned(symbols, offset, base);
}

/// Prove `exists_body` (an `exists y; disjunction`) in `block` by finding a
/// witness (from `candidates`) whose opened body — a right/left nest of
/// `or` — has a provable arm (equation/order, under `premises`). Emits the
/// arm proof, lifts it through the or-intro path, and returns the
/// `exists_intro` justification (NOT yet emitted as a step). Returns null
/// when no candidate witness proves the body. Shared by the period-1 layer,
/// the induction base case, and each induction step arm.
fn emitExistsWitness(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    exists_body: TermId, // exists y; disj
    candidates: []const TermId,
    ar: ArithRules,
    symbols: presburger_mod.Symbols,
    premises: []CertPremise,
    loc: u32,
) ElabError!?kernel.Justification {
    _ = ar;
    const en = self.pool.get(exists_body);
    if (en != .quant or en.quant.q != .exists) return null;
    for (candidates) |witness| {
        const instance = try self.pool.open(en.quant.body, witness);
        // find a provable arm of the (possibly disjunctive) instance; prove
        // it via arithCertCore (which handles the cited premises), then lift
        // through the or-intro path.
        const found = (try proveDisjArm(self, low, block, instance, symbols, premises, loc)) orelse continue;
        var arm_ref = found.ref;
        var pi = found.path.len;
        while (pi > 0) {
            pi -= 1;
            const disj = try disjunctionAt(self, instance, found.path[0..pi]);
            const just: kernel.Justification = if (found.path[pi])
                .{ .or_intro_right = arm_ref }
            else
                .{ .or_intro_left = arm_ref };
            arm_ref = try self.emitStep(low, block, loc, disj, just);
        }
        return .{ .exists_intro = .{ .step = arm_ref, .witness = witness, .witness_loc = loc } };
    }
    return null;
}

/// Prove one arm of a right/left `or`-nest `instance` via arithCertCore
/// (using `premises`), emitting the arm's proof step. Returns the arm's
/// step ref and the or-intro path to it, or null if no arm is provable.
fn proveDisjArm(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    instance: TermId,
    symbols: presburger_mod.Symbols,
    premises: []CertPremise,
    loc: u32,
) ElabError!?struct { ref: kernel.SRef, path: []const bool } {
    var path: std.ArrayList(bool) = .empty;
    var cur = instance;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .bin and node.bin.op == .or_op) {
            if (try arithCertCore(self, low, block, node.bin.lhs, premises, symbols, loc)) |just| {
                const ref = try self.emitStep(low, block, loc, node.bin.lhs, just);
                try path.append(self.arena, false);
                return .{ .ref = ref, .path = try self.arena.dupe(bool, path.items) };
            }
            try path.append(self.arena, true);
            cur = node.bin.rhs;
            continue;
        }
        if (try arithCertCore(self, low, block, cur, premises, symbols, loc)) |just| {
            const ref = try self.emitStep(low, block, loc, cur, just);
            return .{ .ref = ref, .path = try self.arena.dupe(bool, path.items) };
        }
        return null;
    }
}

/// The Cooper certifier link (layers 2-3). Layer 2 (period 1): pick a
/// boundary witness and prove the body directly. Layer 3 (period > 1):
/// synthesize an induction on the fixed variable (the periodicity/−∞
/// residue is provable over Nat only inductively). Nested/multi-var
/// alternation declines (out of scope).
fn cooperCertificate(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, symbols: presburger_mod.Symbols, loc: u32) ElabError!Outcome {
    _ = c;
    if (symbols.nat == null) return .{ .declined = .out_of_scope };

    // peel the forall prefix; the body must be `exists y; …`
    const u = try self.peelUniversal(goal, "cooper");
    const body_node = self.pool.get(u.body);
    if (body_node != .quant or body_node.quant.q != .exists) return .{ .declined = .out_of_scope };

    // record the Cooper elimination of the single existential
    const traced = try presburger_mod.trace(self.arena, self.pool, symbols, &.{}, u.body);
    if (traced != .replay) return .{ .declined = .out_of_scope };
    const replay = traced.replay;

    const ar = (try arithRules(self, loc)) orelse return .{ .declined = .{ .missing_lemma = "addZeroLeft" } };

    if (replay.period != 1) return cooperInduction(self, low, block_id, u, symbols, ar, loc);

    // period 1: the boundary witnesses (reconstructed as Nat terms) are the
    // candidate witnesses; prove the body at the first that works.
    var candidates: std.ArrayList(TermId) = .empty;
    for (replay.disjuncts) |d| {
        const bw = switch (d) {
            .minus_inf => continue,
            .boundary => |b| b,
        };
        if (try buildWitness(self, symbols, replay, replay.boundaries[bw.b_index], bw.j, u.fix_vars)) |w| {
            try candidates.append(self.arena, w);
        }
    }
    const carry = (try emitExistsWitnessInFix(self, low, block_id, u, u.body, candidates.items, ar, symbols, loc)) orelse
        return .{ .declined = .out_of_scope };
    return .{ .certified = carry };
}

/// Emit `u.body` (an existential) inside the peeled forall's fix blocks and
/// fold back out with forall_intro. `exists_body` is proved by
/// `emitExistsWitness` at one of `candidates`.
fn emitExistsWitnessInFix(
    self: *Elaborator,
    low: *Lowering,
    block_id: kernel.BlockId,
    u: Elaborator.Universal,
    exists_body: TermId,
    candidates: []const TermId,
    ar: ArithRules,
    symbols: presburger_mod.Symbols,
    loc: u32,
) ElabError!?kernel.Justification {
    var blocks: std.ArrayList(kernel.BlockId) = .empty;
    var parent = block_id;
    for (u.fix_vars) |fv| {
        const b = try self.newBlock(low, try self.freshNamed("cooper"), parent, .{ .fix = .{ .v = fv } });
        try blocks.append(self.arena, b);
        parent = b;
    }
    const carry = (try emitExistsWitness(self, low, parent, exists_body, candidates, ar, symbols, &.{}, loc)) orelse return null;
    if (blocks.items.len == 0) return carry;
    _ = try self.emitStep(low, blocks.items[blocks.items.len - 1], loc, exists_body, carry);
    var i = blocks.items.len;
    while (i > 1) {
        i -= 1;
        self.closeBlock(low, blocks.items[i]);
        _ = try self.emitStep(low, blocks.items[i - 1], loc, u.opened[i], .{ .forall_intro = .{ .id = blocks.items[i], .loc = loc } });
    }
    self.closeBlock(low, blocks.items[0]);
    return .{ .forall_intro = .{ .id = blocks.items[0], .loc = loc } };
}

/// Candidate existential witnesses for the induction base/step, built from
/// the fixed vars (`ZERO`, small towers) and, in the step, the unpacked IH
/// witness `y0` (`y0`, `succ(y0)`, `succ(succ(y0))`). The shift table for
/// arbitrary period is realized by this bounded search: one of these proves
/// the residue-class arm at succ(k).
fn witnessCandidates(self: *Elaborator, symbols: presburger_mod.Symbols, ih_witness: ?TermId) ElabError![]const TermId {
    var out: std.ArrayList(TermId) = .empty;
    const zero_sym = symbols.zero orelse return out.items;
    const zero = try self.pool.addApp(.app, zero_sym, &.{});
    // constant towers around ZERO: succ^0..3 and (over ℤ) prev^1..3 (base classes)
    for ([_]i128{ 0, 1, 2, 3, -1, -2, -3 }) |off| {
        if (try self.buildTowerSigned(symbols, off, zero)) |w| try out.append(self.arena, w);
    }
    // shifted IH witness, both directions (step case classes)
    if (ih_witness) |y0| {
        for ([_]i128{ 0, 1, 2, -1, -2 }) |off| {
            if (try self.buildTowerSigned(symbols, off, y0)) |w| try out.append(self.arena, w);
        }
    }
    return out.items;
}

/// Layer 3: synthesize an induction on the single fixed variable to certify
/// a period-D `forall x; exists y; body`. Predicate P(k) = body[x:=k];
/// base P(ZERO) and step `forall k; P(k) -> P(succ(k))` are proved by the
/// witness search (the step unpacks the IH witness and case-splits its
/// disjunction, shifting the witness per arm), then `induction` is
/// instantiated at P. Declines (out_of_scope) on multi-variable goals.
fn cooperInduction(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, u: Elaborator.Universal, symbols: presburger_mod.Symbols, ar: ArithRules, loc: u32) ElabError!Outcome {
    // layer 3 handles a single fixed variable (the induction variable).
    if (u.fix_vars.len != 1) return .{ .declined = .out_of_scope };
    const nat = symbols.nat.?;

    // the induction schema must be in scope (a parameterized axiom = a
    // proofless schema); resolve it for the instance construction.
    const induction_id = self.env.findStatementId(self.theoryScope(), self.interner.internString("induction") catch return error.OutOfMemory) orelse
        return .{ .declined = .{ .missing_lemma = "induction" } };
    const induction_stmt = &self.env.statements.items[@intFromEnum(induction_id)];
    if (induction_stmt.* != .schema or induction_stmt.schema.proof != null) return .{ .declined = .{ .missing_lemma = "induction" } };

    // P as a closed body over the induction variable: P[t] = open(P_closed, t)
    const x = u.fix_vars[0];
    const x_id = try self.pool.add(.{ .fvar = x });
    const p_closed = try self.pool.close(u.body, x.name);

    const zero_sym = symbols.zero orelse return .{ .declined = .{ .missing_symbol = "ZERO" } };
    const succ_sym = symbols.succ orelse return .{ .declined = .{ .missing_symbol = "succ" } };

    // --- base case: P(ZERO) ------------------------------------------
    const zero = try self.pool.addApp(.app, zero_sym, &.{});
    const p_zero = try self.pool.open(p_closed, zero);
    const base_candidates = try witnessCandidates(self, symbols, null);
    const base_just = (try emitExistsWitness(self, low, block_id, p_zero, base_candidates, ar, symbols, &.{}, loc)) orelse
        return .{ .declined = .out_of_scope };
    const base_ref = try self.emitStep(low, block_id, loc, p_zero, base_just);

    // --- step: forall k; P(k) -> P(succ(k)) --------------------------
    const k: term.Node.Fvar = .{ .name = try self.freshNamed("k"), .sort = nat };
    const k_id = try self.pool.add(.{ .fvar = k });
    const p_k = try self.pool.open(p_closed, k_id);
    const succ_k = try self.pool.addApp(.app, succ_sym, &.{k_id});
    const p_succ_k = try self.pool.open(p_closed, succ_k);
    const step_impl_open = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = p_k, .rhs = p_succ_k } });
    const step_forall = try closeForall(self, step_impl_open, k, nat);

    const fix_k = try self.newBlock(low, try self.freshNamed("induction-step"), block_id, .{ .fix = .{ .v = k } });
    const assume_pk = try self.newBlock(low, try self.freshNamed("given-inductive-hypothesis"), fix_k, .{ .assume = p_k });
    const ih_ref = try self.emitStep(low, assume_pk, loc, p_k, .{ .hypothesis = .{ .id = assume_pk, .loc = loc } });

    // unpack the IH existential witness y0
    const ih_ex = self.pool.get(p_k);
    if (ih_ex != .quant or ih_ex.quant.q != .exists) return .{ .declined = .out_of_scope };
    const y0: term.Node.Fvar = .{ .name = try self.freshNamed("y"), .sort = ih_ex.quant.sort };
    const y0_id = try self.pool.add(.{ .fvar = y0 });
    const ih_body = try self.pool.open(ih_ex.quant.body, y0_id); // the disjunction at y0
    const unpack_block = try self.newBlock(low, try self.freshNamed("with-witness-y"), assume_pk, .{ .unpack = .{ .v = y0, .source = ih_ref } });
    const ih_body_ref = try self.emitStep(low, unpack_block, loc, ih_body, .{ .hypothesis = .{ .id = unpack_block, .loc = loc } });

    // prove P(succ(k)) by case-splitting ih_body; each arm gives a case
    // hypothesis (an equation over k, y0) used as a premise for the witness
    // search on P(succ(k)).
    const step_candidates = try witnessCandidates(self, symbols, y0_id);
    const case_just = (try emitInductionCases(self, low, unpack_block, ih_body, ih_body_ref, p_succ_k, step_candidates, ar, symbols, loc)) orelse
        return .{ .declined = .out_of_scope };
    _ = try self.emitStep(low, unpack_block, loc, p_succ_k, case_just);
    self.closeBlock(low, unpack_block);

    // export P(succ(k)) out of the unpack (exists_elim), the assume
    // (implies_intro), and the fix (forall_intro).
    _ = try self.emitStep(low, assume_pk, loc, p_succ_k, .{ .exists_elim = .{ .id = unpack_block, .loc = loc } });
    self.closeBlock(low, assume_pk);
    _ = try self.emitStep(low, fix_k, loc, step_impl_open, .{ .implies_intro = .{ .id = assume_pk, .loc = loc } });
    self.closeBlock(low, fix_k);
    const step_ref = try self.emitStep(low, block_id, loc, step_forall, .{ .forall_intro = .{ .id = fix_k, .loc = loc } });

    // --- instantiate induction at P ----------------------------------
    const instance = (try instantiateInduction(self, induction_id, &induction_stmt.schema, p_closed, nat, loc)) orelse
        return .{ .declined = .out_of_scope };
    // the instance concludes `forall n; P(n)`, which is exactly the goal
    // (alpha-equal). Cite base and step as the two premises.
    const premises = try self.arena.dupe(kernel.SRef, &.{ base_ref, step_ref });
    _ = x_id;
    return .{ .certified = .{ .schema_instance = .{ .instance = instance, .premises = premises } } };
}

/// Wrap `body` (mentioning fvar `v`) in `forall v.name; …`.
fn closeForall(self: *Elaborator, body: TermId, v: term.Node.Fvar, sort: term.SortId) ElabError!TermId {
    const closed = try self.pool.close(body, v.name);
    return self.pool.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = v.name, .body = closed } });
}

/// Prove `goal` (= P(succ(k))) by an or_elim over `disj` (the IH witness
/// disjunction at y0). Each arm assumes one disjunct — an equation over
/// k, y0 — and proves `goal` by the witness search using that equation as a
/// rewrite premise. Returns the or_elim justification, or null if any arm
/// fails. Handles a right-nested chain of `or` recursively.
fn emitInductionCases(
    self: *Elaborator,
    low: *Lowering,
    parent: kernel.BlockId,
    disj: TermId,
    disj_ref: kernel.SRef,
    goal: TermId,
    candidates: []const TermId,
    ar: ArithRules,
    symbols: presburger_mod.Symbols,
    loc: u32,
) ElabError!?kernel.Justification {
    const node = self.pool.get(disj);
    if (node != .bin or node.bin.op != .or_op) return null;

    // left arm: assume the lhs disjunct, prove goal at some witness.
    const left = try self.newBlock(low, try self.freshNamed("when-even"), parent, .{ .assume = node.bin.lhs });
    const lhyp = try self.emitStep(low, left, loc, node.bin.lhs, .{ .hypothesis = .{ .id = left, .loc = loc } });
    const lprem = try self.arena.dupe(CertPremise, &.{.{ .formula = node.bin.lhs, .step = lhyp, .statement = null, .rule_idx = undefined, .elim = null }});
    const ljust = (try emitExistsWitness(self, low, left, goal, candidates, ar, symbols, lprem, loc)) orelse return null;
    _ = try self.emitStep(low, left, loc, goal, ljust);
    self.closeBlock(low, left);

    // right arm: the rhs disjunct (possibly itself an or, recursed).
    const right = try self.newBlock(low, try self.freshNamed("when-odd"), parent, .{ .assume = node.bin.rhs });
    const rhyp = try self.emitStep(low, right, loc, node.bin.rhs, .{ .hypothesis = .{ .id = right, .loc = loc } });
    const rn = self.pool.get(node.bin.rhs);
    if (rn == .bin and rn.bin.op == .or_op) {
        const inner = (try emitInductionCases(self, low, right, node.bin.rhs, rhyp, goal, candidates, ar, symbols, loc)) orelse return null;
        _ = try self.emitStep(low, right, loc, goal, inner);
    } else {
        const rprem = try self.arena.dupe(CertPremise, &.{.{ .formula = node.bin.rhs, .step = rhyp, .statement = null, .rule_idx = undefined, .elim = null }});
        const rjust = (try emitExistsWitness(self, low, right, goal, candidates, ar, symbols, rprem, loc)) orelse return null;
        _ = try self.emitStep(low, right, loc, goal, rjust);
    }
    self.closeBlock(low, right);

    return .{ .or_elim = .{ .disj = disj_ref, .left = .{ .id = left, .loc = loc }, .right = .{ .id = right, .loc = loc } } };
}

/// Instantiate the `induction` schema at predicate `p_closed` (a body closed
/// over the induction variable), producing the instance formula
/// `P(ZERO) -> (forall k; P(k) -> P(succ(k))) -> forall n; P(n)`.
fn instantiateInduction(self: *Elaborator, induction_id: StatementId, schema: *const Statement.Schema, p_closed: TermId, nat: term.SortId, loc: u32) ElabError!?TermId {
    _ = loc;
    if (schema.params.len != 1) return null;
    const pname = try self.internTok(schema.params[0].name);
    // the schema-arg representation holds the binder as a FREE fvar (substituted at
    // application); `p_closed` is closed over the induction variable, so open it at
    // a fresh fvar and record that name as the parameter.
    const pvar = try self.freshNamed("p");
    const pfvar = try self.pool.add(.{ .fvar = .{ .name = pvar, .sort = nat } });
    const p_open = try self.pool.open(p_closed, pfvar);
    var args_map: SchemaArgs = .empty;
    args_map.put(self.arena, pname, .{ .lambda = .{ .body = p_open, .params = &.{pvar}, .arg_sorts = &.{nat}, .result_sort = .prop } }) catch return error.OutOfMemory;
    const schema_ctx: Ctx = .{ .source = schema.source, .file = schema.file, .diag = @intFromEnum(schema.file) };
    return self.instantiateSchemaCore(induction_id, schema, schema_ctx, &args_map);
}

/// Descend `instance` (a right/left nest of `or`) along `path` to the
/// sub-disjunction at that prefix. `path` is left(false)/right(true) steps.
fn disjunctionAt(self: *Elaborator, instance: TermId, path: []const bool) ElabError!TermId {
    var cur = instance;
    for (path) |go_right| {
        const node = self.pool.get(cur);
        cur = if (go_right) node.bin.rhs else node.bin.lhs;
    }
    return cur;
}

/// If `t` is a ground successor tower over ZERO (`succ^k(ZERO)`), return k.
/// Used to recognize literal coefficients `mul(k, x)` for Farkas scaling.
fn farkasLiteral(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) usize {
    var k: usize = 0;
    var cur = t;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and Elaborator.symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
            k += 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and Elaborator.symIs(node.app.sym, symbols.zero) and node.app.args_len == 0) return k;
        return 0; // not a ground ZERO-tower
    }
}

/// Scan `t` for `mul(<literal>, x)` subterms, collecting the distinct
/// literal coefficients k >= 2 (k = 1 is a no-op scale; k = 0 degenerate).
fn collectScaleLiterals(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId, out: *std.ArrayList(usize)) ElabError!void {
    const node = self.pool.get(t);
    switch (node) {
        .app, .pred => |a| {
            if (Elaborator.symIs(a.sym, symbols.mul) and a.args_len == 2) {
                const args = self.pool.args(a);
                const k = farkasLiteral(self, symbols, args[0]);
                if (k >= 2) {
                    for (out.items) |x| {
                        if (x == k) break;
                    } else try out.append(self.arena, k);
                }
            }
            for (self.pool.args(a)) |arg| try collectScaleLiterals(self, symbols, arg, out);
        },
        .eq => |p| {
            try collectScaleLiterals(self, symbols, p.lhs, out);
            try collectScaleLiterals(self, symbols, p.rhs, out);
        },
        .not => |inner| try collectScaleLiterals(self, symbols, inner, out),
        .bin => |b| {
            try collectScaleLiterals(self, symbols, b.lhs, out);
            try collectScaleLiterals(self, symbols, b.rhs, out);
        },
        .quant => |q| try collectScaleLiterals(self, symbols, q.body, out),
        else => {},
    }
}

/// Is `t` an `add(_, _)` application?
fn isAddSum(self: *Elaborator, symbols: presburger_mod.Symbols, t: TermId) bool {
    const node = self.pool.get(t);
    return node == .app and Elaborator.symIs(node.app.sym, symbols.add) and node.app.args_len == 2;
}

/// The conclusion is `less_than(add(A,B), add(C,D))`. Find base hypotheses
/// proving A<C and B<D, emit their summed edge (A+B < C+D), and append it.
/// Returns null on success, or a non-empty missing-lemma name if a needed
/// lemma is absent (so the caller declines with that reason). Returns an
/// empty slice when the shape simply doesn't match (fall through quietly).
fn trySumEdges(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    loc: u32,
    symbols: presburger_mod.Symbols,
    body: TermId,
    base_count: usize,
    edges: *std.ArrayList(farkas_mod.Edge),
    hyps: *std.ArrayList(OrderHyp),
    node_ids: *std.ArrayList(TermId),
) ElabError!?[]const u8 {
    const cargs = self.pool.args(self.pool.get(body).pred);
    const lhs = self.pool.args(self.pool.get(cargs[0]).app); // [A, B]
    const rhs = self.pool.args(self.pool.get(cargs[1]).app); // [C, D]
    const a = lhs[0];
    const bb = lhs[1];
    const cc = rhs[0];
    const dd = rhs[1];
    // find base hyps A<C and B<D
    var ha: ?OrderHyp = null;
    var hb: ?OrderHyp = null;
    for (hyps.items[0..base_count]) |h| {
        if (self.pool.termOrder(h.lo, a) == .eq and self.pool.termOrder(h.hi, cc) == .eq) ha = h;
        if (self.pool.termOrder(h.lo, bb) == .eq and self.pool.termOrder(h.hi, dd) == .eq) hb = h;
    }
    const first = ha orelse return &.{};
    const second = hb orelse return &.{};

    const apo = (try self.wellKnownFact("additionPreservesOrder", loc)) orelse return "additionPreservesOrder";
    const comm = (try self.wellKnownRule("addIsCommutative", loc)) orelse return "addIsCommutative";
    const transitive = (try self.wellKnownFact("lessThanTransitive", loc)) orelse return "lessThanTransitive";

    const summed = try emitSumEdge(self, low, block, loc, symbols, apo.formula, apo.source, comm, transitive.formula, transitive.source, first, second);
    try edges.append(self.arena, .{
        .lo = try farkasNodeId(self, node_ids, summed.lo),
        .hi = try farkasNodeId(self, node_ids, summed.hi),
    });
    try hyps.append(self.arena, summed);
    return null;
}

/// Emit a SUMMED edge from two order hypotheses ha (p<q) and hb (r<s):
/// prove `less_than(add(p,r), add(q,s))` and return it as an OrderHyp.
/// Follows the verified chain (see tests): lift p<q by +r via
/// additionPreservesOrder and commute to `add(p,r)<add(q,r)`; lift r<s by
/// +q to `add(q,r)<add(q,s)`; chain with lessThanTransitive.
fn emitSumEdge(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    loc: u32,
    symbols: presburger_mod.Symbols,
    apo_formula: TermId, // additionPreservesOrder
    apo_source: simplify_mod.Source,
    comm: simplify_mod.Rule, // addIsCommutative as a rewrite rule
    transitive_formula: TermId,
    transitive_source: simplify_mod.Source,
    ha: OrderHyp,
    hb: OrderHyp,
) ElabError!OrderHyp {
    const add = symbols.add.?;
    const p = ha.lo;
    const q = ha.hi;
    const r = hb.lo;
    const s = hb.hi;

    // additionPreservesOrder binders (a, b, c); body
    //   less_than(a,b) -> less_than(add(c,a), add(c,b)).
    // lift p<q by c:=r -> forall_elim(p, q, r): add(r,p)<add(r,q)
    const apo_rule1 = try self.strippedRule(apo_formula, apo_source);
    const imp1 = try self.emitInstance(low, block, loc, apo_rule1, &.{ p, q, r });
    const lifted1 = self.pool.get(low.steps.items[@intFromEnum(imp1.id)].formula).bin.rhs;
    const rp_lt_rq = try self.emitStep(low, block, loc, lifted1, .{ .modus_ponens = .{ .implication = imp1, .antecedent = ha.ref } });

    // commute add(r,p)=add(p,r) and add(r,q)=add(q,r), rewrite both.
    const rp = try self.pool.addApp(.app, add, &.{ r, p });
    const pr = try self.pool.addApp(.app, add, &.{ p, r });
    const rq = try self.pool.addApp(.app, add, &.{ r, q });
    const qr = try self.pool.addApp(.app, add, &.{ q, r });
    const eq_rp = try emitCommEq(self, low, block, loc, comm, rp, pr); // add(r,p)=add(p,r)
    const eq_rq = try emitCommEq(self, low, block, loc, comm, rq, qr); // add(r,q)=add(q,r)
    // rewrite rp_lt_rq: add(r,p)<add(r,q)  ->  add(p,r)<add(q,r)
    const pr_lt_rq_f = try self.pool.addApp(.pred, symbols.less_than.?, &.{ pr, rq });
    const pr_lt_rq = try self.emitStep(low, block, loc, pr_lt_rq_f, .{ .rewrite = .{ .equation = eq_rp, .target = rp_lt_rq } });
    const pr_lt_qr_f = try self.pool.addApp(.pred, symbols.less_than.?, &.{ pr, qr });
    const pr_lt_qr = try self.emitStep(low, block, loc, pr_lt_qr_f, .{ .rewrite = .{ .equation = eq_rq, .target = pr_lt_rq } });

    // lift r<s by c:=q -> forall_elim(r, s, q): add(q,r)<add(q,s)
    const apo_rule2 = try self.strippedRule(apo_formula, apo_source);
    const imp2 = try self.emitInstance(low, block, loc, apo_rule2, &.{ r, s, q });
    const lifted2 = self.pool.get(low.steps.items[@intFromEnum(imp2.id)].formula).bin.rhs;
    const qr_lt_qs = try self.emitStep(low, block, loc, lifted2, .{ .modus_ponens = .{ .implication = imp2, .antecedent = hb.ref } });

    // chain add(p,r) < add(q,r) < add(q,s) via lessThanTransitive
    const qs = try self.pool.addApp(.app, add, &.{ q, s });
    const tr_rule = try self.strippedRule(transitive_formula, transitive_source);
    const chain = try self.emitInstance(low, block, loc, tr_rule, &.{ pr, qr, qs });
    const chain_inner = self.pool.get(low.steps.items[@intFromEnum(chain.id)].formula).bin.rhs;
    const chain2 = try self.emitStep(low, block, loc, chain_inner, .{ .modus_ponens = .{ .implication = chain, .antecedent = pr_lt_qr } });
    const summed_f = self.pool.get(chain_inner).bin.rhs;
    const summed = try self.emitStep(low, block, loc, summed_f, .{ .modus_ponens = .{ .implication = chain2, .antecedent = qr_lt_qs } });
    return .{ .lo = pr, .hi = qs, .ref = summed };
}

/// Emit `lhs = rhs` where they differ by one addIsCommutative rewrite,
/// using the comm rule instantiated to the right pair.
fn emitCommEq(self: *Elaborator, low: *Lowering, block: kernel.BlockId, loc: u32, comm: simplify_mod.Rule, lhs: TermId, rhs: TermId) ElabError!kernel.SRef {
    // comm: forall a, b; add(a, b) = add(b, a). lhs = add(x, y), want
    // add(x,y) = add(y,x): match a:=x, b:=y -> forall_elim(a:=x, b:=y).
    _ = rhs; // determined by the instance; named for the caller's clarity
    const la = self.pool.args(self.pool.get(lhs).app);
    return self.emitInstance(low, block, loc, comm, &.{ la[0], la[1] });
}

/// For each base order hypothesis and each literal k in `literals`, emit a
/// SCALED edge `less_than(mul(k,lo), mul(k,hi))` via
/// multiplicationPreservesOrder (k = succ(c), so forall_elim at c =
/// succ^{k-1}(ZERO)), appending it to `edges`/`hyps`/`node_ids`. Returns
/// false (declines) if `multiplicationPreservesOrder` or `mul`/`succ`/`zero`
/// are absent. The scaled edges then feed the same fold as base edges.
fn emitScaledEdges(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    loc: u32,
    symbols: presburger_mod.Symbols,
    literals: []const usize,
    base_count: usize,
    edges: *std.ArrayList(farkas_mod.Edge),
    hyps: *std.ArrayList(OrderHyp),
    node_ids: *std.ArrayList(TermId),
) ElabError!bool {
    if (literals.len == 0) return true;
    const succ = symbols.succ orelse return false;
    const zero_sym = symbols.zero orelse return false;
    const mpo = (try self.wellKnownFact("multiplicationPreservesOrder", loc)) orelse return false;
    const zero = try self.pool.addApp(.app, zero_sym, &.{});

    for (literals) |k| {
        // c = succ^{k-1}(ZERO), so succ(c) = k
        var c = zero;
        for (0..k - 1) |_| c = try self.pool.addApp(.app, succ, &.{c});
        for (0..base_count) |bi| {
            const h = hyps.items[bi];
            // multiplicationPreservesOrder binders (a, b, c); body
            //   less_than(a,b) -> less_than(mul(succ(c),a), mul(succ(c),b)).
            // want a:=h.lo, b:=h.hi, c:=c -> forall_elim(h.lo, h.hi, c).
            const rule = try self.strippedRule(mpo.formula, mpo.source);
            const imp = try self.emitInstance(low, block, loc, rule, &.{ h.lo, h.hi, c });
            const concl = self.pool.get(low.steps.items[@intFromEnum(imp.id)].formula).bin.rhs;
            const scaled_ref = try self.emitStep(low, block, loc, concl, .{ .modus_ponens = .{ .implication = imp, .antecedent = h.ref } });
            const scaled = self.pool.get(concl).pred;
            const sargs = self.pool.args(scaled);
            try edges.append(self.arena, .{
                .lo = try farkasNodeId(self, node_ids, sargs[0]),
                .hi = try farkasNodeId(self, node_ids, sargs[1]),
            });
            try hyps.append(self.arena, .{ .lo = sargs[0], .hi = sargs[1], .ref = scaled_ref });
        }
    }
    return true;
}

/// Prove the Farkas conclusion `body` from the order hypotheses, returning
/// the justification of a step proving `body` in `block` (or null to
/// decline). Dispatches on the conclusion shape (see the call site).
fn emitFarkasConclusion(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    loc: u32,
    transitive_formula: TermId,
    transitive_source: simplify_mod.Source,
    less_than: term.SymId,
    body: TermId,
    edges: []const farkas_mod.Edge,
    hyps: []const OrderHyp,
    node_ids: *std.ArrayList(TermId),
) ElabError!?kernel.Justification {
    const cn = self.pool.get(body);
    const is_order = cn == .pred and Elaborator.symIs(cn.pred.sym, less_than) and cn.pred.args_len == 2;

    // (a)/(b) ORDER COMPOSITION: if the conclusion is an order atom
    // less_than(s, t), try to compose a chain s < ... < t directly (a cycle
    // when s == t). This is preferred — no irreflexivity needed.
    if (is_order) {
        const cargs = self.pool.args(cn.pred);
        const from = try farkasNodeId(self, node_ids, cargs[0]);
        const to = try farkasNodeId(self, node_ids, cargs[1]);
        if (try farkas_mod.compose(self.arena, edges, from, to)) |path| {
            // The fold's final `modus_ponens` PROVES the conclusion directly, and
            // the caller emits our returned justification as the concluding step
            // — so emit every step BUT that last one and hand it back, else the
            // caller re-emits an identical duplicate.
            return try foldFinalJustification(self, low, block, loc, transitive_formula, transitive_source, path.chain, hyps);
        }
        // no direct chain: fall through to the infeasibility cap (the
        // hypotheses may be contradictory, proving any conclusion).
    }

    // (c) INFEASIBILITY CAP: fold ANY cycle to less_than(x, x), contradict
    // with lessThanIrreflexive, and `absurd` proves the (arbitrary) `body`
    // — including an order atom that has no direct chain (e.g. a scaled
    // cycle proving less_than(a, a) for a bare a not on the cycle).
    const irreflexive = (try self.wellKnownFact("lessThanIrreflexive", loc)) orelse return null;
    const refutation = (try farkas_mod.refute(self.arena, edges, null)) orelse return null;
    const proof = try emitFarkasFold(self, low, block, loc, transitive_formula, transitive_source, refutation.chain, hyps);
    const cnode = node_ids.items[refutation.node];
    // emitInstance specializes lessThanIrreflexive at cnode to
    // `not less_than(cnode, cnode)`; absurd against the folded
    // `less_than(cnode, cnode)` then proves the (arbitrary) conclusion.
    const irr_rule = try self.strippedRule(irreflexive.formula, irreflexive.source);
    const not_ref = try self.emitInstance(low, block, loc, irr_rule, &.{cnode});
    return .{ .absurd = .{ .s1 = proof, .s2 = not_ref } };
}

/// Intern a term as an abstract Farkas node identity (by structural order).
fn farkasNodeId(self: *Elaborator, list: *std.ArrayList(TermId), t: TermId) ElabError!usize {
    for (list.items, 0..) |x, i| {
        if (self.pool.termOrder(x, t) == .eq) return i;
    }
    try list.append(self.arena, t);
    return list.items.len - 1;
}

/// Fold an order chain (edge indices, each hi linking to the next lo) into
/// a single proof `less_than(chain-first-lo, chain-last-hi)` by composing
/// consecutive hypotheses with lessThanTransitive. Returns the step ref of
/// that proof (the sole hypothesis when the chain has one edge).
fn emitFarkasFold(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    loc: u32,
    transitive_formula: TermId,
    transitive_source: simplify_mod.Source,
    chain: []const usize,
    hyps: []const OrderHyp,
) ElabError!kernel.SRef {
    // running proof `acc_ref`: less_than(acc_lo, acc_hi)
    var acc_ref = hyps[chain[0]].ref;
    const acc_lo = hyps[chain[0]].lo;
    var acc_hi = hyps[chain[0]].hi;

    for (chain[1..]) |idx| {
        const next = hyps[idx];
        // lessThanTransitive has binders `forall a, b, c` over body
        //   less_than(a, b) -> less_than(b, c) -> less_than(a, c).
        // We want a:=acc_lo, b:=acc_hi, c:=next.hi, so specialize in
        // binder order (a, b, c) = (acc_lo, acc_hi, next.hi).
        const rule = try self.strippedRule(transitive_formula, transitive_source);
        const imp3 = try self.emitInstance(low, block, loc, rule, &.{ acc_lo, acc_hi, next.hi });
        // apply to the two order proofs: modus_ponens twice
        const inner = self.pool.get(low.steps.items[@intFromEnum(imp3.id)].formula).bin.rhs;
        const imp2 = try self.emitStep(low, block, loc, inner, .{ .modus_ponens = .{ .implication = imp3, .antecedent = acc_ref } });
        const concl = self.pool.get(inner).bin.rhs;
        acc_ref = try self.emitStep(low, block, loc, concl, .{ .modus_ponens = .{ .implication = imp2, .antecedent = next.ref } });
        acc_hi = next.hi;
    }
    return acc_ref;
}

/// Like `emitFarkasFold`, but for when the caller emits the CONCLUDING step
/// itself (the order-composition path): emit every fold step EXCEPT the final
/// `modus_ponens`, and return THAT as a bare justification. A single-edge chain
/// emits nothing here and returns the hypothesis as-is (via its own step). This
/// avoids the duplicate step returning `emitFarkasFold`'s justification would
/// leave (the fold's last step, plus the caller's identical re-emit).
fn foldFinalJustification(
    self: *Elaborator,
    low: *Lowering,
    block: kernel.BlockId,
    loc: u32,
    transitive_formula: TermId,
    transitive_source: simplify_mod.Source,
    chain: []const usize,
    hyps: []const OrderHyp,
) ElabError!kernel.Justification {
    // a single edge: the conclusion IS the lone hypothesis; the caller emits it.
    if (chain.len == 1) {
        return low.steps.items[@intFromEnum(hyps[chain[0]].ref.id)].just;
    }
    // fold all but the final edge normally, then build (not emit) the last
    // edge's second modus_ponens.
    const prefix = try emitFarkasFold(self, low, block, loc, transitive_formula, transitive_source, chain[0 .. chain.len - 1], hyps);
    const acc_lo = hyps[chain[0]].lo;
    const acc_hi = hyps[chain[chain.len - 2]].hi;
    const next = hyps[chain[chain.len - 1]];
    const rule = try self.strippedRule(transitive_formula, transitive_source);
    const imp3 = try self.emitInstance(low, block, loc, rule, &.{ acc_lo, acc_hi, next.hi });
    const inner = self.pool.get(low.steps.items[@intFromEnum(imp3.id)].formula).bin.rhs;
    const imp2 = try self.emitStep(low, block, loc, inner, .{ .modus_ponens = .{ .implication = imp3, .antecedent = prefix } });
    return .{ .modus_ponens = .{ .implication = imp2, .antecedent = next.ref } };
}

/// For a NAMED theory: does the goal/premises use an arithmetic symbol the
/// theory failed to provide? Returns its (well-known) name if so. A symbol
/// USED in the goal but whose theory-resolved counterpart is null would be
/// treated as an opaque foreign atom — a silent failure the named-theory
/// contract turns into an explicit error. Compares by well-known NAME: the
/// goal states the symbol under some name; if the theory has no symbol of
/// that name (so `symbols.X` is null), it is missing.
fn missingTheorySymbol(self: *Elaborator, goal: TermId, premises: []const TermId, symbols: presburger_mod.Symbols) ElabError!?[]const u8 {
    const wanted = [_]struct { name: []const u8, present: bool }{
        .{ .name = "succ", .present = symbols.succ != null },
        .{ .name = "add", .present = symbols.add != null },
        .{ .name = "mul", .present = symbols.mul != null },
        .{ .name = "less_than", .present = symbols.less_than != null },
    };
    for (wanted) |w| {
        if (w.present) continue;
        const id = self.interner.internString(w.name) catch return error.OutOfMemory;
        if (self.pool.usesSymNamed(self.env, id, goal)) return w.name;
        for (premises) |p| {
            if (self.pool.usesSymNamed(self.env, id, p)) return w.name;
        }
    }
    return null;
}
/// If `t` mentions a REIFIED SCHEMA PARAMETER symbol (branded
/// `opaque-schema-param#<origName>#<counter>` by `checkSchemaBodyOpaque`), return
/// the original parameter name `<origName>`. Recurses into `.app`/`.pred` args.
/// Used to give a specific "over the schema parameter '<name>'" diagnostic
/// instead of leaking the internal symbol.
fn schemaParamName(self: *Elaborator, t: TermId) ?[]const u8 {
    const prefix = "opaque-schema-param#";
    switch (self.pool.get(t)) {
        .app, .pred => |a| {
            const name = self.interner.stringBytes(self.env.sym(a.sym).name);
            if (std.mem.startsWith(u8, name, prefix)) {
                // `opaque-schema-param#<origName>#<counter>` — the middle segment.
                const rest = name[prefix.len..];
                const end = std.mem.lastIndexOfScalar(u8, rest, '#') orelse rest.len;
                return rest[0..end];
            }
            for (self.pool.args(a)) |arg| if (schemaParamName(self, arg)) |n| return n;
            return null;
        },
        .eq => |p| return schemaParamName(self, p.lhs) orelse schemaParamName(self, p.rhs),
        .not => |inner| return schemaParamName(self, inner),
        .bin => |b| return schemaParamName(self, b.lhs) orelse schemaParamName(self, b.rhs),
        .quant => |q| return schemaParamName(self, q.body),
        .bvar, .fvar => return null,
    }
}

/// Walk `t`; for each free variable of `nat_sort` not yet seen, append a
/// `nonneg(fv)` atom to `out`. This is the theory-supplied nonnegativity for the
/// pure-ℤ engine: a ℕ theory (which binds `nonneg`) gets its `x ≥ 0` per free
/// variable; ℤ/ℚ bind no `nonneg` and this never runs.
fn collectNonnegTargets(
    self: *Elaborator,
    t: TermId,
    nat_sort: term.SortId,
    seen: *std.AutoHashMapUnmanaged(StrId, void),
    out: *std.ArrayListUnmanaged(TermId),
    nonneg_sym: term.SymId,
) ElabError!void {
    switch (self.pool.get(t)) {
        .bvar => {},
        .fvar => |v| {
            if (v.sort != nat_sort) return;
            const gop = seen.getOrPut(self.arena, v.name) catch return error.OutOfMemory;
            if (gop.found_existing) return;
            const atom = try self.pool.addApp(.pred, nonneg_sym, &.{t});
            try out.append(self.arena, atom);
        },
        .app, .pred => |a| {
            for (self.pool.args(a)) |arg| try collectNonnegTargets(self, arg, nat_sort, seen, out, nonneg_sym);
        },
        .eq => |p| {
            try collectNonnegTargets(self, p.lhs, nat_sort, seen, out, nonneg_sym);
            try collectNonnegTargets(self, p.rhs, nat_sort, seen, out, nonneg_sym);
        },
        .not => |inner| try collectNonnegTargets(self, inner, nat_sort, seen, out, nonneg_sym),
        .bin => |b| {
            try collectNonnegTargets(self, b.lhs, nat_sort, seen, out, nonneg_sym);
            try collectNonnegTargets(self, b.rhs, nat_sort, seen, out, nonneg_sym);
        },
        .quant => |q| try collectNonnegTargets(self, q.body, nat_sort, seen, out, nonneg_sym),
    }
}

fn arithmeticJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const premises = try self.resolvePremises(low, block_id, c, "arithmetic");

    // `arithmetic(<theory>)` resolves the arithmetic vocabulary + lemmas
    // against the named theory module's scope (regardless of local
    // aliases); bare `arithmetic` resolves against local scope. Scoped to
    // this call — restored on return.
    const saved_theory = self.theory_file;
    defer self.theory_file = saved_theory;
    if (c.schema) |theory_tok| {
        const ns = try self.internTok(theory_tok);
        self.theory_file = self.env.findNamespace(self.file, ns) orelse
            return self.fail(theory_tok.start, "unknown theory '{s}' (not an imported module)", .{self.text(theory_tok)});
    }

    const symbols = try arithmeticSymbols(self);

    // A NAMED theory is asserted complete: every symbol the goal mentions
    // must be provided, else a hard error naming the gap (rather than a
    // silent opaque-atom countermodel). Bare/local is best-effort.
    if (c.schema) |theory_tok| {
        if (try missingTheorySymbol(self, goal, premises, symbols)) |missing| {
            return self.fail(theory_tok.start, "theory '{s}' lacks symbol '{s}' needed by this goal", .{ self.text(theory_tok), missing });
        }
    }

    // proving 'forall x; F' means proving F with x fixed-but-arbitrary:
    // strip the goal's universal Nat prefix so a mixed body still
    // skeletonizes (a quantifier over a mixed body would be one opaque
    // atom). Binder hints name the variables in countermodels; a hint
    // colliding with an existing free variable gets a hygienic name.
    //
    // The engine is pure ℤ (no implicit nonnegativity). If the theory binds a
    // well-known `nonneg` predicate, each stripped variable gets an injected
    // `nonneg(x)` premise — this is how a ℕ theory recovers its x ≥ 0 without
    // the engine assuming it. (Inner quantifier bodies carry their own injected
    // nonneg conjuncts, added below.)
    var injected: std.ArrayListUnmanaged(TermId) = .empty;
    var stripped = goal;
    if (symbols.nat) |nat_sort| {
        while (true) {
            const node = self.pool.get(stripped);
            if (node != .quant or node.quant.q != .forall or node.quant.sort != nat_sort) break;
            var name = node.quant.hint;
            var collides = self.pool.occursFree(stripped, name);
            for (premises) |p| {
                if (self.pool.occursFree(p, name)) collides = true;
            }
            if (collides) name = try self.freshNamed(self.interner.stringBytes(node.quant.hint));
            const fv = try self.pool.add(.{ .fvar = .{ .name = name, .sort = nat_sort } });
            stripped = try self.pool.open(node.quant.body, fv);
        }
    }

    // The engine is pure ℤ (no implicit nonnegativity). If the theory binds a
    // well-known `nonneg` predicate, inject `nonneg(x)` for every free variable
    // of the arithmetic sort in the (stripped) goal and premises — this is how a
    // ℕ theory recovers its x ≥ 0. Covers both goal-quantifier binders (stripped
    // above into free vars) and user-written `fix x` eigenvariables (already free
    // in the goal). ℤ/ℚ bind no nonneg → nothing injected.
    if (symbols.nonneg) |nn| if (symbols.nat) |nat_sort| {
        var seen: std.AutoHashMapUnmanaged(StrId, void) = .empty;
        try collectNonnegTargets(self, stripped, nat_sort, &seen, &injected, nn);
        for (premises) |p| try collectNonnegTargets(self, p, nat_sort, &seen, &injected, nn);
    };

    // hand the engine the cited premises plus any injected nonneg(x) guards.
    const all_premises: []const TermId = if (injected.items.len == 0)
        premises
    else blk: {
        const buf = try self.arena.alloc(TermId, premises.len + injected.items.len);
        @memcpy(buf[0..premises.len], premises);
        @memcpy(buf[premises.len..], injected.items);
        break :blk buf;
    };

    // A reified schema parameter (branded opaque symbol from the schema
    // self-check) must NOT be silently abstracted into a linear atom — that would
    // let a goal over `k` "decide" but never certify. Detect it up front and give
    // the specific "over the schema parameter '<name>'" diagnostic. (Only when
    // certifying: under --fast the accelerated verdict is fine.)
    if (self.verify.certify_arithmetic) {
        if (schemaParamName(self, stripped)) |pname| {
            return self.fail(loc, "arithmetic cannot yet decide this goal over the schema parameter '{s}' (reified opaque while the schema's proof is checked). Certifying an arithmetic step over a schema parameter is currently unsupported but planned; use --fast to accept the accelerated verdict", .{pname});
        }
        for (all_premises) |p| {
            if (schemaParamName(self, p)) |pname| {
                return self.fail(loc, "arithmetic cannot yet decide this goal over the schema parameter '{s}' (reified opaque while the schema's proof is checked). Certifying an arithmetic step over a schema parameter is currently unsupported but planned; use --fast to accept the accelerated verdict", .{pname});
            }
        }
    }

    const verdict = smt_mod.decideMixed(self.arena, self.pool, symbols, all_premises, stripped) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {
            // --fast: DECIDE-only. decideMixed already settled validity; take the
            // accelerated verdict (taint, no certificate) without running the
            // certifiers. A `fallback(<thm>)` still resolves to its manual proof.
            if (!self.verify.certify_arithmetic) {
                if (c.fallback) |fb| return arithmeticFallback(self, low, block_id, fb, goal, c);
                var reasons: [certifiers.len]Reason = undefined;
                @memset(&reasons, .out_of_scope);
                return arithmeticTerminal(self, loc, &reasons);
            }

            // strict: GENERATE a context-free synthetic theorem — the certifier
            // chain builds the proof in a FRESH Lowering (its cited premises are
            // surfaced as hypotheses by the closure), which is wrapped + cited.
            // `body.reasons` captures each link's decline reason for the terminal.
            var body: CertifierBody = .{ .c = c, .symbols = symbols, .loc = loc, .reasons = undefined };
            if (try common.generate(self, low, block_id, loc, "arithmetic", goal, c.refs, &body)) |just| {
                // Case D: the certifier chain discharged this goal on its own, so a
                // `fallback(<thm>)` is REDUNDANT — the fallback exists only for goals
                // arithmetic CANNOT certify (the branch below). Reject it (strict
                // only, by construction — this block is under certify_arithmetic;
                // `--draft` suppresses the hygiene nag).
                if (c.fallback) |fb| {
                    if (!self.verify.draft) return self.fail(fb.start, "'arithmetic' certifies this goal on its own — the fallback '{s}' is unnecessary; drop `fallback({s})`", .{ self.text(fb), self.text(fb) });
                }
                return just;
            }
            // every certifier declined: valid but not certifiable here. A
            // `fallback(<thm>)` cites a manual proof (proven); else hard error
            // (default) listing why each link declined.
            if (c.fallback) |fb| return arithmeticFallback(self, low, block_id, fb, goal, c);
            return arithmeticTerminal(self, loc, &body.reasons);
        },
        .countermodel => |cm| {
            if (!cm.values_found) {
                return self.fail(loc, "arithmetic: not a consequence (no small countermodel found)", .{});
            }
            // a relational atom (=, !=, less_than) that is opaque only
            // because it hides a nonlinear term was never decided
            // arithmetically — report that honestly instead of a
            // countermodel that reads as "your true statement is false".
            // (A genuinely propositional opaque atom, like a foreign
            // predicate `p`, is a legitimate part of a mixed countermodel
            // and is left alone.)
            for (cm.opaques) |lit| {
                if (!looksArithmeticRelation(self, lit.atom, symbols)) continue;
                if (try presburger_mod.outOfFragment(self.arena, self.pool, symbols, lit.atom)) |offending| {
                    // If the offending term is a REIFIED SCHEMA PARAMETER (branded
                    // `opaque-schema-param#<name>#<n>` by checkSchemaBodyOpaque), the
                    // step is inside a schema whose parameter arithmetic can't treat
                    // as a real variable during the opaque wellformedness check. That
                    // is a known, planned-but-unsupported case — say so, naming the
                    // user's parameter, instead of leaking the internal symbol.
                    if (schemaParamName(self, offending)) |pname|
                        return self.fail(loc, "arithmetic cannot yet decide this goal over the schema parameter '{s}' (reified opaque while the schema's proof is checked). Certifying an arithmetic step over a schema parameter is currently unsupported but planned; use --fast to accept the accelerated verdict", .{pname});
                    return self.fail(loc, "arithmetic: '{s}' is outside linear arithmetic", .{try self.renderTerm(offending)});
                }
            }
            // An abstracted opaque subterm (mod(a,b), mul(a,b), f(x)) in the
            // countermodel means the goal genuinely needs reasoning beyond linear
            // arithmetic — its atom values are not independently realizable, so a
            // numeric countermodel would mislead. Report the subterm as outside
            // the fragment instead (naming a reified schema param if that's what
            // it is).
            for (cm.values) |a| {
                if (a.term) |offending| {
                    if (schemaParamName(self, offending)) |pname|
                        return self.fail(loc, "arithmetic cannot yet decide this goal over the schema parameter '{s}' (reified opaque while the schema's proof is checked). Certifying an arithmetic step over a schema parameter is currently unsupported but planned; use --fast to accept the accelerated verdict", .{pname});
                    return self.fail(loc, "arithmetic: '{s}' is outside linear arithmetic", .{try self.renderTerm(offending)});
                }
            }
            if (cm.values.len == 0 and cm.opaques.len == 0) {
                return self.fail(loc, "arithmetic: the statement is false", .{});
            }
            var msg: std.Io.Writer.Allocating = .init(self.arena);
            var count: usize = 0;
            for (cm.values) |a| {
                msg.writer.print("{s}{s} := {d}", .{
                    if (count > 0) ", " else "",
                    Elaborator.displayName(self.interner.stringBytes(a.name)),
                    a.value,
                }) catch return error.OutOfMemory;
                count += 1;
            }
            for (cm.opaques) |lit| {
                msg.writer.print("{s}{s} := {s}", .{
                    if (count > 0) ", " else "",
                    try self.renderTerm(lit.atom),
                    if (lit.value) "true" else "false",
                }) catch return error.OutOfMemory;
                count += 1;
            }
            return self.fail(loc, "arithmetic: false at {s}", .{msg.written()});
        },
        .too_many_atoms => |n| {
            return self.fail(loc, "arithmetic: {d} distinct atoms exceeds the limit of {d}", .{ n, smt_mod.atom_limit });
        },
        .too_large => return self.fail(loc, "arithmetic: decision exceeded the work limit", .{}),
        .overflow => return self.fail(loc, "arithmetic: coefficient overflow", .{}),
    }
}
