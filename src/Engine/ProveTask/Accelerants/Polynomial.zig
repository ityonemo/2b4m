//! The `polynomial` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
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

/// the `_quantified` variant: a `forall …; s = t` goal, peeled first
quantified: bool,

pub const schema_slot: Accelerant.SchemaSlot = .theory_selector;
pub const premise_shape: Accelerant.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

pub fn decide(self: @This(), prove: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    return common.decideFused(self, prove, w, e, goal, c);
}

pub fn certify(self: @This(), prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    return if (self.quantified) producePolynomialQuantified(prove, w, goal, c) else producePolynomial(prove, w, goal, c);
}

/// `[using polynomial(M) ]` — prove an equation goal `s = t` as a ring identity.
pub fn producePolynomial(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return prove.fail(c.rule.start, "polynomial takes no arguments (the theory is the parenthesized selector)", .{});
    const gn = prove.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return prove.fail(c.rule.start, "polynomial proves equations; did you mean polynomial_quantified?", .{});
        }
        return prove.fail(c.rule.start, "polynomial: goal is not an equation", .{});
    }
    return buildPolynomial(prove, w, c, goal, &.{});
}

/// `[using polynomial_quantified(M) ]` — like polynomial but the goal is `forall …; s = t`.
pub fn producePolynomialQuantified(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return prove.fail(c.rule.start, "polynomial_quantified takes no arguments (the theory is the parenthesized selector)", .{});
    const peeled = try common.peelForallEq(prove, goal, c, "polynomial_quantified") orelse return null;
    return buildPolynomial(prove, w, c, peeled.body, peeled.eigen);
}

/// Shared polynomial core over the (possibly ∀-peeled) equation body `eq_goal_raw`. Reads the
/// ring operator syms off the goal, builds the hardcoded rule set + selector-qualified cites,
/// abstracts free caller-locals into params, canonicalizes both sides IN PARAM SPACE, and hands
/// the traces to `finishReorder`. `polynomial` has no LOCAL premises (all its rules are global
/// well-known lemmas cited inside the cert), so `local_prems` is empty.
fn buildPolynomial(prove: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // read the ring operators off the goal (by well-known head NAME — inspecting the goal, not
    // a scope lookup). `add`/`mul` are required; the rest are optional (present iff the goal
    // has them). The theory selector's qualifier is stamped into every emitted cite.
    const goal_ops = (try common.readPolyOps(prove, eq_goal_raw)) orelse
        return prove.fail(c.rule.start, "polynomial: the goal has no add/mul structure", .{});
    // `--fast` declines to EMIT the certificate; the CANONICALIZATION DECISION still runs.
    // Admitting here accepted any add/mul-shaped equation, true or not. `completePolyOps`
    // already parks on an outstanding ident demand (null → blocked), which is exactly what the
    // decision needs — so admit lands after the normal-form comparison below, before
    // `finishReorder` emits the cert. See design/acceleration.md.
    // COMPLETE the vocabulary from the theory (a demand may be outstanding → null, blocked).
    // In ADMIT mode a null is a PARK the dispatch has no channel for, so the read pass must
    // have demanded these already; reaching here parked means it did not.
    const ops = (try completePolyOps(prove, c.schema, goal_ops)) orelse return null;
    const qualifier: StrId = if (c.schema) |s| s.name else .none;
    const pr = try Polynomial.polyRules(prove, ops, qualifier, c.rule.start);

    // abstract free caller-local fvars (an enclosing `fix`) into value params, then canonicalize
    // in PARAM space so the trace + schema body speak `p1, p2, …`. Eigenvariables (the peeled ∀
    // vars) stay free and are re-bound by the `fix` wrapper in finishReorder.
    const ag = try common.abstractGoal(prove, &b, eq_goal_raw, &.{}, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = prove.pool.get(eq_goal).eq;
    const s0 = gn.lhs;
    const t0 = gn.rhs;

    const rs = (try Polynomial.polyCanon(prove, pr, s0)) orelse
        return prove.fail(c.rule.start, "polynomial: could not canonicalize the left side", .{});
    const rt = (try Polynomial.polyCanon(prove, pr, t0)) orelse
        return prove.fail(c.rule.start, "polynomial: could not canonicalize the right side", .{});
    if (!prove.pool.alphaEq(rs.nf, rt.nf)) {
        return prove.fail(c.rule.start, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
            try prove.renderTerm(try common.unabstract(prove, rs.nf, abs)),
            try prove.renderTerm(try common.unabstract(prove, rt.nf, abs)),
        });
    }
    // ADMIT: both sides expanded to the SAME canonical form, so a certificate demonstrably
    // exists — only emitting it is pruned.
    if (prove.admit_mode) {
        prove.producer_premise_refs = null;
        prove.admit_ok = true;
        return null;
    }
    return common.finishReorder(prove, w, &b, c, "polynomial", s0, t0, pr.rules, pr.cites, rs, rt, abs, eigen, &.{});
}

/// COMPLETE a goal's ring vocabulary from the THEORY: the canonicalization can need a symbol
/// the goal never mentions — `ZERO` to cancel an inverse pair (`t + neg(t) → ZERO`), `neg`
/// to expand `sub`, `add` to expand a numeral coefficient (`mul(succ(a), b) → add(…)`) or a
/// `sub`. Deterministic in (goal, selector): only the vocabulary the goal's own operators
/// IMPLY the theory has is demanded (a `neg` implies a ring with `ZERO`; never a probe for
/// optional vocabulary such as `succ` in a field). Resolved by name in the theory namespace
/// (the selector's import, else this proof's); an unfetched symbol racks its FetchTask and
/// returns null with `producer_blocker` set (the step suspends; the producer re-runs). A
/// missing symbol surfaces as that FetchTask's "reference not found" at the step.
fn completePolyOps(prove: *Prove, selector: ?lexer.Token, goal: Polynomial.Ops) Error!?Polynomial.Ops {
    var ops = goal;
    const need_zero = ops.zero == null and (ops.neg != null or ops.sub != null);
    const need_neg = ops.neg == null and ops.sub != null;
    const need_add = ops.add == null and (ops.sub != null or (ops.mul != null and (ops.succ != null or ops.prev != null)));
    if (!need_zero and !need_neg and !need_add) return ops;
    // the theory namespace + file: the selector's import (demanded if unfetched), else ours.
    var ns = prove.ns;
    var file = prove.file;
    if (selector) |sel| {
        const st = prove.ctx.idents.lookup(prove.ctx.io, .{ .namespace = prove.ns, .name = Prove.tokName(sel) }) orelse {
            prove.producer_blocker = try prove.h.rackIndexed(try FetchTask.new(prove.ctx.arena, .{ .file = prove.file, .name = Prove.tokName(sel), .loc = sel.start, .loc_file = prove.file }));
            return null;
        };
        switch (st) {
            .in_flight => |owner| {
                prove.producer_blocker = owner;
                return null;
            },
            .done => |ix| switch (prove.ctx.interner.keyOf(ix)) {
                .import => |m| {
                    ns = m.namespace;
                    file = prove.ctx.interner.keyOf(m.namespace).namespace.file;
                },
                else => return prove.fail(sel.start, "'{s}' is not a theory (an import)", .{prove.text(sel)}),
            },
        }
    }
    if (need_zero) ops.zero = (try demandWellKnown(prove, ns, file, "ZERO", .constant, selector)) orelse return null;
    if (need_neg) ops.neg = (try demandWellKnown(prove, ns, file, "neg", .func, selector)) orelse return null;
    if (need_add) ops.add = (try demandWellKnown(prove, ns, file, "add", .func, selector)) orelse return null;
    return ops;
}

/// A well-known symbol by NAME in the theory namespace `ns` (file `file`): its SymId when
/// fetched (kind-checked; the ambient model applied), else null with `producer_blocker` set
/// (racked or already in flight). Diagnoses a fetched symbol of the wrong kind.
fn demandWellKnown(prove: *Prove, ns: InternPool.Index, file: InternPool.Index, name: []const u8, comptime kind: enum { func, constant }, at: ?lexer.Token) Error!?term.SymId {
    const nid = try common.internStrRt(prove, name);
    const loc: u32 = if (at) |t| t.start else 0;
    const st = prove.ctx.idents.lookup(prove.ctx.io, .{ .namespace = ns, .name = nid }) orelse {
        prove.producer_blocker = try prove.h.rackIndexed(try FetchTask.new(prove.ctx.arena, .{ .file = file, .name = nid, .loc = loc, .loc_file = prove.file }));
        return null;
    };
    const ix = switch (st) {
        .done => |x| prove.ctx.interner.applyModel(prove.model, x),
        .in_flight => |owner| {
            prove.producer_blocker = owner;
            return null;
        },
    };
    const ok = switch (prove.ctx.interner.keyOf(ix)) {
        .func => kind == .func,
        .constant => kind == .constant,
        else => false,
    };
    if (!ok) return prove.fail(loc, "polynomial: the theory's '{s}' is not a {s}", .{ name, if (kind == .func) "function" else "constant" });
    return @enumFromInt(@intFromEnum(ix));
}

test "completePolyOps: a goal with neg but no ZERO demands ZERO from the theory — blocked until fetched, then filled" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try Polynomial.Rig.init(arena, threaded.io());
    const e = try rig.v("e");
    const goal = try rig.eq(try rig.a2(rig.add, e, try rig.a1(rig.neg, e)), e);
    var ops = (try common.readPolyOps(rig.prove, goal)).?;
    try testing.expect(ops.zero == null);
    // ZERO is already fetched in the rig's namespace → completes immediately, no blocker.
    const done = (try completePolyOps(rig.prove, null, ops)).?;
    try testing.expectEqual(rig.zero, done.zero.?);
    try testing.expect(rig.prove.producer_blocker == null);
    // a goal with NO neg never asks for ZERO (the vocabulary the goal implies is all we demand).
    const plain = try rig.eq(try rig.a2(rig.add, e, e), try rig.a2(rig.add, e, e));
    ops = (try common.readPolyOps(rig.prove, plain)).?;
    const done2 = (try completePolyOps(rig.prove, null, ops)).?;
    try testing.expect(done2.zero == null);
}
