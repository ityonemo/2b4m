//! The `assoc_commut` / `assoc_commut_quantified` accelerant (the `ac` tactic):
//! associative-commutative reordering. Proves `s = t` when both are sums over a
//! single operator with the same multiset of opaque atoms, differing only by
//! associativity/commutativity. Each side is re-associated to a right-nested
//! comb, its atoms flattened and bubble-sorted into a canonical order, then the
//! two canonical forms are joined. Kernel-checked in the default path; the bare
//! form has an accelerated `--fast` verdict. Split out of the elaborate
//! monolith; the shared flatten/sort/plan substrate stays as `pub` methods on
//! `Elaborator`.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");
const lexer = @import("../lexer.zig");
const simplify_mod = @import("../simplify.zig");
const presburger_mod = @import("arithmetic/presburger.zig");
const common = @import("_common.zig");

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .eq) {
        if (goal_node == .quant and goal_node.quant.q == .forall) {
            return self.fail(loc, "assoc_commut proves equations; use assoc_commut_quantified for a 'forall …; s = t' goal", .{});
        }
        return self.fail(loc, "assoc_commut proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
    }
    // --fast: acEquation short-circuits to the accelerated verdict (no theorem).
    // strict: wrap the AC-sort certificate as a synthetic theorem (eigenvar
    // closure; the AC triple + pre-rules are globals cited directly).
    if (!self.verify.certify_arithmetic) {
        return acEquation(self, low, block_id, loc, goal, c.args, c.refs);
    }
    var body: EqBody = .{ .args = c.args, .refs = c.refs, .loc = loc };
    return (try common.generate(self, low, block_id, loc, "assoc_commut", goal, &.{}, &body)).?;
}

/// `ac` peeling the forall prefix: fix the binders, run the ac core on the
/// equation body, close with forall_intro. Mirrors simplify_quantified.
pub fn justifyQuantified(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .quant or goal_node.quant.q != .forall) {
        if (goal_node == .eq) {
            return self.fail(loc, "assoc_commut_quantified expects a quantified goal; did you mean assoc_commut?", .{});
        }
        return self.fail(loc, "assoc_commut_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
    }
    const u = try self.peelUniversal(goal, "ac");
    if (self.pool.get(u.body) != .eq) {
        return self.fail(loc, "assoc_commut_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
    }
    if (!self.verify.certify_arithmetic) {
        const opened = try self.openUniversal(low, block_id, u);
        const body_just = try acEquation(self, low, opened.innermost, loc, u.body, c.args, c.refs);
        return self.closeUniversal(low, loc, u, opened.blocks, body_just);
    }
    var body: EqBody = .{ .args = c.args, .refs = c.refs, .loc = loc };
    return (try common.generate(self, low, block_id, loc, "assoc_commut", goal, &.{}, &body)).?;
}

/// The body-emit for ac's closure: AC-sort the (fresh-eigenvar) equation. A
/// still-quantified body is peeled/closed here.
const EqBody = struct {
    args: []const *const ast.Expr,
    refs: []const lexer.Token,
    loc: u32,
    pub fn emit(b: *EqBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!?kernel.Justification {
        if (self.pool.get(body_goal) == .quant and self.pool.get(body_goal).quant.q == .forall) {
            const u = try self.peelUniversal(body_goal, "ac");
            const opened = try self.openUniversal(low, block, u);
            const inner = try acEquation(self, low, opened.innermost, b.loc, u.body, b.args, b.refs);
            return try self.closeUniversal(low, b.loc, u, opened.blocks, inner);
        }
        return try acEquation(self, low, block, b.loc, body_goal, b.args, b.refs);
    }
};

/// The ac core on a bare equation goal `goal` emitted in `block_id`:
/// pick the operator, resolve its AC lemma triple, bubble-sort both sides,
/// emit the join. Shared by `ac` and `ac_quantified`. `refs` are optional
/// pre-normalization lemmas (e.g. distributivity) applied L→R to each side
/// before flattening — so `mul(add(a,b),c) = add(mul(b,c),mul(a,c))` is
/// distributed then AC-sorted.
fn acEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId, args: []const *const ast.Expr, refs: []const lexer.Token) ElabError!kernel.Justification {
    const goal_node = self.pool.get(goal);
    const s0 = goal_node.eq.lhs;
    const t0 = goal_node.eq.rhs;

    // exactly two forms: bare `assoc_commut` (well-known add/mul triple), or
    // `assoc_commut(assoc, comm, swap)` (an explicit AC triple for a custom
    // operator). No partials — 1 or 2 args is an error.
    if (args.len != 0 and args.len != 3) {
        return self.fail(loc, "assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got {d}", .{args.len});
    }
    const explicit = args.len == 3;

    // optional pre-normalization rules (distributivity etc.), resolved from
    // the cited refs and applied L→R to each side before flattening. Their
    // rule indices sit at the FRONT of the combined `rules` array so the
    // AC bubble-sort's indices (assoc=0…) shift after them.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    for (refs) |ref| {
        try rules.append(self.arena, try self.resolveRewriteRule(low, block_id, ref, "assoc_commut"));
    }
    const pre_count = rules.items.len;
    const pre_rules = rules.items[0..pre_count];

    // distribute both sides (L→R with the pre-rules); the AC operator is
    // detected on the distributed LHS. Traces feed emitJoin unchanged.
    const s_pre = simplify_mod.normalize(self.arena, self.pool, self.env, pre_rules, s0, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(loc, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const t_pre = simplify_mod.normalize(self.arena, self.pool, self.env, pre_rules, t0, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(loc, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const s = s_pre.nf;
    const t = t_pre.nf;

    // Resolve the AC triple + its operator. Explicit form: resolve the three
    // cited lemmas and recover the operator from the commutativity lemma's
    // shape (`f(a,b) = f(b,a)` → `f`). Bare form: pick add/mul from the goal
    // LHS head and resolve their well-known triple.
    const assoc_idx = rules.items.len;
    var op_sym: term.SymId = undefined;
    if (explicit) {
        const a_rule = try self.acArgRule(low, block_id, args[0]);
        const c_rule = try self.acArgRule(low, block_id, args[1]);
        const w_rule = try self.acArgRule(low, block_id, args[2]);
        // operator = head symbol of the commutativity lemma's LHS
        const c_lhs = self.pool.get(c_rule.lhs);
        if (c_lhs != .app or c_lhs.app.args_len != 2) {
            return self.fail(Elaborator.exprLoc(args[1]), "assoc_commut: the commutativity lemma must have shape 'f(a, b) = f(b, a)'", .{});
        }
        op_sym = c_lhs.app.sym;
        try rules.append(self.arena, a_rule);
        try rules.append(self.arena, c_rule);
        try rules.append(self.arena, w_rule);
    } else {
        const add_sym = try self.wellKnownSym("add");
        const mul_sym = try self.wellKnownSym("mul");
        const s_head: ?term.SymId = if (self.pool.get(s) == .app) self.pool.get(s).app.sym else null;
        const op: struct { sym: term.SymId, assoc: []const u8, comm: []const u8, swap: []const u8 } = blk: {
            if (add_sym != null and s_head != null and s_head.? == add_sym.?) {
                break :blk .{ .sym = add_sym.?, .assoc = "addIsAssociative", .comm = "addIsCommutative", .swap = "addLeftSwap" };
            }
            if (mul_sym != null and s_head != null and s_head.? == mul_sym.?) {
                break :blk .{ .sym = mul_sym.?, .assoc = "mulIsAssociative", .comm = "mulIsCommutative", .swap = "mulLeftSwap" };
            }
            return self.fail(loc, "assoc_commut reorders an add- or mul-sum; the goal's left side is '{s}'", .{try self.renderTerm(s)});
        };
        op_sym = op.sym;
        // --fast: the ACCELERATED path (bare form only — an explicit triple
        // is checkable, so it always elaborates). Decide AC-equality by
        // comparing the sorted multiset of summands — NO assoc/comm/swap
        // lemmas resolved, so it works on a theory too thin to elaborate,
        // but TRUSTS the operator is associative-commutative (the theory's
        // laws are never checked). That presumption about an uncontrolled
        // symbol is why it is accelerated, not kernel-checked.
        if (!self.verify.certify_arithmetic) {
            var s_leaves: std.ArrayList(TermId) = .empty;
            var t_leaves: std.ArrayList(TermId) = .empty;
            try self.flattenSum(op_sym, s, &s_leaves);
            try self.flattenSum(op_sym, t, &t_leaves);
            self.sortTerms(s_leaves.items);
            self.sortTerms(t_leaves.items);
            const s_nf = try self.buildRightNested(op_sym, s_leaves.items);
            const t_nf = try self.buildRightNested(op_sym, t_leaves.items);
            if (!self.pool.alphaEq(s_nf, t_nf)) {
                return self.fail(loc, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
                    try self.renderTerm(s_nf), try self.renderTerm(t_nf),
                });
            }
            const name = self.interner.internString("assoc_commut") catch return error.OutOfMemory;
            try self.recordAccelerated(name, loc);
            return .{ .accelerated = name };
        }
        // append the well-known triple.
        const assoc = (try self.wellKnownRule(op.assoc, loc)) orelse
            return self.fail(loc, "assoc_commut: needs {s} in scope", .{op.assoc});
        try rules.append(self.arena, assoc);
        const comm = (try self.wellKnownRule(op.comm, loc)) orelse
            return self.fail(loc, "assoc_commut: needs {s} in scope", .{op.comm});
        try rules.append(self.arena, comm);
        const swap = (try self.wellKnownRule(op.swap, loc)) orelse
            return self.fail(loc, "assoc_commut: needs {s} in scope", .{op.swap});
        try rules.append(self.arena, swap);
    }
    const comm_idx = assoc_idx + 1;
    const swap_idx = assoc_idx + 2;

    const ac_symbols: presburger_mod.Symbols = .{ .add = op_sym };

    // per side: re-associate to a right-nested comb, flatten, bubble-sort.
    // `assoc_idx` is where associativity landed after the pre-rules.
    const plan = (try self.acPlan(ac_symbols, rules.items, assoc_idx, comm_idx, swap_idx, op_sym, s)) orelse
        return error.OutOfMemory;
    const plan_t = (try self.acPlan(ac_symbols, rules.items, assoc_idx, comm_idx, swap_idx, op_sym, t)) orelse
        return error.OutOfMemory;
    if (!self.pool.alphaEq(plan.sorted, plan_t.sorted)) {
        return self.fail(loc, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
            try self.renderTerm(plan.sorted), try self.renderTerm(plan_t.sorted),
        });
    }
    // prepend the distribution trace (s0 -> s) so emitJoin replays the full
    // chain s0 -> distributed -> sorted against the combined rules.
    const full_s = try concatTrace(self, s_pre.trace, plan.trace);
    const full_t = try concatTrace(self, t_pre.trace, plan_t.trace);
    return self.emitJoin(low, block_id, loc, rules.items, s0, t0, .{ .nf = plan.sorted, .trace = full_s }, .{ .nf = plan_t.sorted, .trace = full_t });
}

fn concatTrace(self: *Elaborator, a: []const simplify_mod.Rewrite, b: []const simplify_mod.Rewrite) ElabError![]const simplify_mod.Rewrite {
    if (a.len == 0) return b;
    if (b.len == 0) return a;
    var out: std.ArrayList(simplify_mod.Rewrite) = .empty;
    try out.appendSlice(self.arena, a);
    try out.appendSlice(self.arena, b);
    return out.items;
}
