//! The `simplify` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
//! `Accelerant.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../../ast.zig");
const term = @import("../../../term.zig");
const TermId = term.TermId;
const Engine = @import("../../../Engine.zig");
const Walk = @import("../Walk.zig");
const Elab = @import("../Elab.zig");
const Accelerant = @import("../Accelerant.zig");
const EqCert = @import("../EqCert.zig");
const rewrite = @import("rewrite.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const common = @import("common.zig");

/// the `_quantified` variant: a `forall …; s = t` goal, peeled first
quantified: bool,

pub const schema_slot: Accelerant.SchemaSlot = .none;
pub const premise_shape: Accelerant.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

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
    return if (self.quantified) produceSimplifyQuantified(prove, w, goal, c) else produceSimplify(prove, w, goal, c);
}

/// `[using simplify refs…]` — prove an equation goal `s = t` by rewriting BOTH sides to a
/// common normal form using each cited fact as a left→right rewrite rule. Certificate-total:
/// on a shared NF the reflexivity/rewrite/symmetry chain is emitted (via the shared EqCert)
/// as the synthetic schema's proof; on differing NFs or a rewrite-cap overflow it FAILS with
/// the diagnostic. Synthetic schema (specialize-shaped): value params abstract the goal's
/// free (fix-eigenvariable) fvars; LOCAL rule refs become premise antecedents restated by
/// hypothesis; GLOBAL rules are cited inside the cert.
pub fn produceSimplify(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return prove.fail(c.rule.start, "simplify takes no arguments", .{});
    const gn = prove.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return prove.fail(c.rule.start, "simplify proves equations; did you mean simplify_quantified?", .{});
        }
        return prove.fail(c.rule.start, "simplify: goal is not an equation", .{});
    }
    return common.buildSimplify(prove, w, c, goal, &.{});
}

/// `[using simplify_quantified refs…]` — like simplify but the goal is `forall …; s = t`.
/// Peel the ∀ prefix into fresh eigenvariable fvars, run the simplify core on the body
/// equation, and re-generalize: the synthetic schema's proof `fix`es each eigenvariable,
/// proves the body via the EqCert, and `generalize`s back out.
pub fn produceSimplifyQuantified(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return prove.fail(c.rule.start, "simplify_quantified takes no arguments", .{});
    // peel the ∀ prefix into fresh eigenvariables; the body must be an equation.
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var body = goal;
    while (true) {
        const node = prove.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = prove.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{ .name = try prove.freshNamed(if (hint.len > 0) hint else "q"), .sort = node.quant.sort };
        body = try prove.pool.open(node.quant.body, try prove.pool.add(.{ .fvar = fv }));
        try eigen.append(prove.ctx.arena, fv);
    }
    if (eigen.items.len == 0) {
        return prove.fail(c.rule.start, "simplify_quantified expects a quantified goal; did you mean simplify?", .{});
    }
    if (prove.pool.get(body) != .eq) {
        return prove.fail(c.rule.start, "simplify_quantified: the quantified body is not an equation", .{});
    }
    return common.buildSimplify(prove, w, c, body, eigen.items);
}
