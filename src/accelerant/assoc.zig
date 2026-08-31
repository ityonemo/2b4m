//! The `assoc` / `assoc_quantified` accelerant (associativity-only reorder):
//! proves `s = t` when both are equal by ASSOCIATIVITY ALONE of a single
//! operator — the non-commutative sibling of `assoc_commut`. Right-nests each
//! side (associativity is confluent + terminating, so right-nesting is a
//! canonical form) and compares; no reordering, no commutativity. The
//! associativity lemma is REQUIRED as the sole argument — there is no bare form
//! and no assumption the operator is add/mul; the operator is recovered from
//! the lemma's shape `f(f(a,b),c) = f(a,f(b,c))`. Kernel-checked by default;
//! the accelerated `--fast` path presumes associativity. Split out of the
//! elaborate monolith; the shared flatten/build substrate stays as `pub`
//! methods on `Elaborator`.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");
const simplify_mod = @import("../simplify.zig");
const common = @import("_common.zig");

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .eq) {
        if (goal_node == .quant and goal_node.quant.q == .forall) {
            return self.fail(loc, "assoc proves equations; use assoc_quantified for a 'forall …; s = t' goal", .{});
        }
        return self.fail(loc, "assoc proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
    }
    // --fast: decide-only (accelerated verdict, no theorem). strict: wrap the
    // reassociation certificate as a synthetic theorem (eigenvar-closure; the
    // associativity lemma is a global cited directly).
    if (!self.verify.certify_arithmetic) {
        return assocEquation(self, low, block_id, loc, goal, c.args);
    }
    var body: EqBody = .{ .args = c.args, .loc = loc };
    return (try common.generate(self, low, block_id, loc, "assoc", goal, &.{}, &body)).?;
}

pub fn justifyQuantified(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .quant or goal_node.quant.q != .forall) {
        if (goal_node == .eq) {
            return self.fail(loc, "assoc_quantified expects a quantified goal; did you mean assoc?", .{});
        }
        return self.fail(loc, "assoc_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
    }
    const u = try self.peelUniversal(goal, "assoc");
    if (self.pool.get(u.body) != .eq) {
        return self.fail(loc, "assoc_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
    }
    if (!self.verify.certify_arithmetic) {
        const opened = try self.openUniversal(low, block_id, u);
        const body_just = try assocEquation(self, low, opened.innermost, loc, u.body, c.args);
        return self.closeUniversal(low, loc, u, opened.blocks, body_just);
    }
    var body: EqBody = .{ .args = c.args, .loc = loc };
    return (try common.generate(self, low, block_id, loc, "assoc", goal, &.{}, &body)).?;
}

/// The body-emit for assoc's closure: reassociate the (fresh-eigenvar) equation
/// against the associativity lemma. A still-quantified body is peeled/closed.
const EqBody = struct {
    args: []const *const ast.Expr,
    loc: u32,
    pub fn emit(b: *EqBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!?kernel.Justification {
        if (self.pool.get(body_goal) == .quant and self.pool.get(body_goal).quant.q == .forall) {
            const u = try self.peelUniversal(body_goal, "assoc");
            const opened = try self.openUniversal(low, block, u);
            const inner = try assocEquation(self, low, opened.innermost, b.loc, u.body, b.args);
            return try self.closeUniversal(low, b.loc, u, opened.blocks, inner);
        }
        return try assocEquation(self, low, block, b.loc, body_goal, b.args);
    }
};

fn assocEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId, args: []const *const ast.Expr) ElabError!kernel.Justification {
    // REQUIRED: exactly one argument, the associativity lemma.
    if (args.len != 1) {
        return self.fail(loc, "assoc requires an associativity lemma: assoc(<assocLemma>); got {d} argument(s)", .{args.len});
    }
    const rule = try self.acArgRule(low, block_id, args[0]);
    // the operator is the head of the lemma's LHS `f(f(a,b),c)` → `f`;
    // verify the shape and that LHS and RHS share that head.
    const l = self.pool.get(rule.lhs);
    if (l != .app or l.app.args_len != 2) {
        return self.fail(Elaborator.exprLoc(args[0]), "assoc: the associativity lemma must have shape 'f(f(a, b), c) = f(a, f(b, c))'", .{});
    }
    const op_sym = l.app.sym;
    const r = self.pool.get(rule.rhs);
    if (r != .app or r.app.sym != op_sym) {
        return self.fail(Elaborator.exprLoc(args[0]), "assoc: the associativity lemma's two sides must share the operator", .{});
    }

    const goal_node = self.pool.get(goal);
    const s0 = goal_node.eq.lhs;
    const t0 = goal_node.eq.rhs;

    // one-rule array so emitJoin's rule_idx (0) lines up.
    const rules = [_]simplify_mod.Rule{rule};

    // --fast: the accelerated assoc path. Structurally right-nest both
    // sides over the operator and compare — WITHOUT emitting the kernel
    // rewrite chain, presuming associativity rather than discharging it.
    // Accelerated, not kernel-checked.
    if (!self.verify.certify_arithmetic) {
        var s_leaves: std.ArrayList(TermId) = .empty;
        var t_leaves: std.ArrayList(TermId) = .empty;
        try self.flattenSum(op_sym, s0, &s_leaves);
        try self.flattenSum(op_sym, t0, &t_leaves);
        const s_nf = try self.buildRightNested(op_sym, s_leaves.items);
        const t_nf = try self.buildRightNested(op_sym, t_leaves.items);
        if (!self.pool.alphaEq(s_nf, t_nf)) {
            return self.fail(loc, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
                try self.renderTerm(s_nf), try self.renderTerm(t_nf),
            });
        }
        const name = self.interner.internString("assoc") catch return error.OutOfMemory;
        try self.recordAccelerated(name, loc);
        return .{ .accelerated = name };
    }

    // certify: right-nest each side by the associativity rule (terminating),
    // compare the canonical forms, emit the join.
    const rs = simplify_mod.normalize(self.arena, self.pool, self.env, &rules, s0, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(loc, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = simplify_mod.normalize(self.arena, self.pool, self.env, &rules, t0, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(loc, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        return self.fail(loc, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
            try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
        });
    }
    return self.emitJoin(low, block_id, loc, &rules, s0, t0, rs, rt);
}
