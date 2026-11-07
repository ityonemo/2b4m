//! The `tautology` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
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

pub const schema_slot: Accelerant.SchemaSlot = .none;
pub const premise_shape: Accelerant.PremiseShape = .refs_in_order;
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
    _ = self;
    return produceTautology(prove, w, goal, c);
}

/// Build the synthetic schema for `using tautology refs…`, closing a goal that is a
/// PROPOSITIONAL CONSEQUENCE of the cited premises. `smt.tautology` DECIDES validity (an
/// honest oracle — rejects a non-consequence with a countermodel / over-cap with the atom
/// count); on `valid` the truth search REPLAYS as a natural-deduction certificate emitted
/// as AST (`common.TautAst`) — every step re-checked by the kernel.
///
/// The synthetic schema (same shape as specialize): body = `prem0 -> … -> premN -> goal`;
/// proof = nest one `assume prem_i` per premise (restating each hypothesis), then in the
/// innermost context emit the cert. The call site discharges the antecedents with `c.refs`.
///
/// PARAMS: a tautology inside a `fix a { … }` has free caller-local eigenvars in its goal/
/// premises; `abstractGoal` lifts them (shared across goal + premises) into schema value
/// params `p1,p2,…`, mirrored by call-site args — the same machinery `arithmetic` uses. A
/// closed site abstracts nothing (empty params/args, the common case).
pub fn produceTautology(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return prove.fail(c.rule.start, "tautology takes no arguments", .{});
    // ADMIT: the only pre-cert validation is the arg-count; the DECISION (smt.tautology) and the
    // cert build are the expensive path. Skip both under `--fast`.
    // `--fast` declines to EMIT the certificate; the PROPOSITIONAL DECISION still runs — its
    // own comment below says "no --fast escape", which the early admit here silently undid.
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // premises = the cited LOCAL steps' formulae (in ref order — the body's antecedent order).
    const prems = try prove.ctx.arena.alloc(common.TautAst.Prem, c.refs.len);
    for (c.refs, prems) |r, *out| {
        const sref = try prove.resolveStepRef(w, r);
        out.* = .{
            .formula = prove.producerPremiseFormula(sref),
            .label = try prove.freshNamed("prem"), // the restated-hypothesis step (in the block)
            .blk_label = try prove.freshNamed("assume-prem"), // the assume block itself
        };
    }

    // DECIDE. A non-consequence / over-cap is a HARD failure (strict-only — no --fast escape).
    const prem_formulae = try prove.ctx.arena.alloc(TermId, prems.len);
    for (prems, prem_formulae) |p, *out| out.* = p.formula;
    const verdict = smt.tautology(prove.ctx.arena, prove.pool, prem_formulae, goal) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {},
        .too_many_atoms => |n| return prove.fail(c.rule.start, "tautology: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
        .countermodel => |lits| {
            var msg: std.Io.Writer.Allocating = .init(prove.ctx.arena);
            for (lits, 0..) |lit, i| {
                msg.writer.print("{s}{s} := {s}", .{
                    if (i > 0) ", " else "",
                    try prove.renderTerm(lit.atom),
                    if (lit.value) "true" else "false",
                }) catch return error.OutOfMemory;
            }
            return prove.fail(c.rule.start, "tautology: not a propositional consequence; countermodel: {s}", .{msg.written()});
        },
    }

    // ADMIT: the goal is a propositional consequence of the cited premises, so a certificate
    // demonstrably exists — only emitting it is pruned.
    if (prove.admit_mode) {
        prove.producer_premise_refs = null;
        prove.admit_ok = true;
        return null;
    }

    // ABSTRACT the free caller-local eigenvars (an enclosing `fix a { … }` around this step)
    // into schema value params `p1,p2,…`, shared across the goal AND every premise formula (all
    // speak the same `fix` vars). Without this, delaborating the goal/premise to the empty-scope
    // schema body leaves those names unresolvable. The verdict above was decided on the ORIGINAL
    // terms (fvar substitution is uniform, so the propositional structure — atoms + truth table —
    // is identical); the cert is built on the ABSTRACTED terms so its body speaks the params.
    // A closed (no-`fix`) site abstracts nothing — params/args empty, the common case.
    const abstracted = try common.abstractGoal(prove, &b, goal, prem_formulae, &.{});
    const abs = abstracted.abs;
    const goal_p = abstracted.goal_p;
    // rewrite each premise's formula into param space (the cert + the schema antecedents use it).
    const prems_p = try prove.ctx.arena.alloc(common.TautAst.Prem, prems.len);
    for (prems, prems_p) |src, *out| {
        out.* = src;
        out.formula = try common.substFvarsToParams(prove, src.formula, abs);
    }

    // GENERATE the certificate over the param-space goal/premises. Collect the atoms once (the
    // cert's split order), then replay.
    var atom_list: std.ArrayList(TermId) = .empty;
    for (prems_p) |p| smt.collectAtoms(prove.ctx.arena, prove.pool, &atom_list, p.formula) catch return error.OutOfMemory;
    smt.collectAtoms(prove.ctx.arena, prove.pool, &atom_list, goal_p) catch return error.OutOfMemory;

    const assignment = try prove.ctx.arena.alloc(?bool, atom_list.items.len);
    @memset(assignment, null);
    const lit_blocks = try prove.ctx.arena.alloc(?StrId, atom_list.items.len);
    @memset(lit_blocks, null);
    var cert: common.TautAst = .{
        .p = prove,
        .b = &b,
        .goal = goal_p,
        .premises = prems_p,
        .atoms = atom_list.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
    };

    // the innermost block's steps: the whole cert, concluding `goal`.
    var inner: std.ArrayList(ast.Step) = .empty;
    try cert.deriveGoal(&inner);

    // wrap in nested `assume prem_i { restate hyp; … }` blocks, exporting each `->` back out.
    const steps = try common.wrapTautologyPremises(prove, &b, prems_p, goal_p, inner.items);

    // schema body = `prem0 -> … -> goal` (an ordinary proof with no premises just = goal).
    var body_expr = try b.termExpr(goal_p);
    var i: usize = prems_p.len;
    while (i > 0) {
        i -= 1;
        body_expr = try b.implies(try b.termExpr(prems_p[i].formula), body_expr);
    }

    // deterministic hash-name from the FULL proposition `prem0 -> … -> goal` (re-entry stable).
    // The premises' ORDER is part of the identity: the instance's antecedents are discharged
    // positionally against the call site's refs, so two steps with the same premises in a
    // different order are DIFFERENT schemas (an order-blind XOR combine once conflated them —
    // set.b4m's forward/backward union-commutativity halves).
    const prem_formulae_p = try prove.ctx.arena.alloc(TermId, prems_p.len);
    for (prems_p, prem_formulae_p) |p, *f| f.* = p.formula;
    const full_prop = try common.impliesChain(prove, goal_p, prem_formulae_p);
    const hash = Schema.termHash(prove.ctx.interner, prove.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "tautology{{{x}}}", .{hash}));

    // the abstracted eigenvars become the schema's value params (mirrored args at the call site).
    const params = try prove.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |pname, sort, *pp| {
        pp.* = .{ .name = b.tok(pname), .kind = .{ .value = b.sortTok(sort) } };
    }

    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = c.refs,
        .seen = b.seen.items,
        .fvar_binds = try common.fvarBinds(prove, w, abs),
    };
}
