//! The `ext` / `ext_quantified` accelerant (extensionality): proves `LHS = RHS`
//! by instantiating an extensionality lemma at (LHS, RHS) and discharging each
//! pointwise obligation. Two models, read STRUCTURALLY off the resolved lemma:
//! the FUNCTION model closes `apply(f,x) = apply(g,x)` by rewriting with the
//! `<op>Apply` lemmas and joining; the SET model unfolds `member(x, op(...))`
//! via `<op>Member` lemmas and closes propositionally with tautology. The
//! element sort and obligation count come from the lemma's shape, so the tactic
//! is agnostic to the sort's name. Split out of the elaborate monolith; the
//! shared block/step/tautology substrate stays as `pub` methods on `Elaborator`
//! (notably `emitTautologyFrom`, which tautology also uses).

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

const Premise = Elaborator.TautCert.Premise;

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    return extJustification(self, low, block_id, goal, c, false);
}

pub fn justifyQuantified(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    return extJustification(self, low, block_id, goal, c, true);
}

/// The body-emit for ext's closure: prove the (fresh-eigenvar) equation by
/// extensionality. A still-quantified body (from ext_quantified) is peeled and
/// closed here. ext is cert-only (no `--fast` verdict), so this always runs in
/// strict mode.
const EqBody = struct {
    loc: u32,
    pub fn emit(b: *EqBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!?kernel.Justification {
        if (self.pool.get(body_goal) == .quant and self.pool.get(body_goal).quant.q == .forall) {
            const u = try self.peelUniversal(body_goal, "ext");
            const opened = try self.openUniversal(low, block, u);
            const inner = try extEquation(self, low, opened.innermost, u.body, b.loc);
            return try self.closeUniversal(low, b.loc, u, opened.blocks, inner);
        }
        return try extEquation(self, low, block, body_goal, b.loc);
    }
};

/// A resolved extensionality model: the element sort, the extensionality
/// lemma, and — read off the lemma's obligation — the characterization
/// symbol (a `member`-style predicate, or an `apply`-style function).
const ExtModel = struct {
    universe: term.SortId,
    lemma: TermId,
    lemma_source: simplify_mod.Source,
    /// each obligation is `forall x: <elementSort>; <body>`; count = 1 (function)
    /// or 2 (set, the two inclusions). Read from the lemma.
    obligation_count: usize,
};

fn extJustification(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim, quantified: bool) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const saved_theory = self.theory_file;
    defer self.theory_file = saved_theory;
    try self.enterTheory(c);

    // shape validation up front (precise diagnostics); the closure's body-emit
    // peels the quantified form itself.
    if (quantified) {
        const gn = self.pool.get(goal);
        if (gn != .quant or gn.quant.q != .forall) {
            return self.fail(loc, "ext_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
        }
    } else if (self.pool.get(goal) != .eq) {
        return self.fail(loc, "ext proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
    }
    // ext is cert-only (always strict). Wrap the extensionality certificate as a
    // synthetic theorem, eigenvar-closed (the ext + operator lemmas are globals
    // cited directly inside the certificate).
    var body: EqBody = .{ .loc = loc };
    return (try common.generate(self, low, block_id, loc, "ext", goal, &.{}, &body)).?;
}

/// Prove a bare `LHS = RHS` by extensionality. Instantiate the ext lemma at
/// (LHS, RHS), prove each pointwise obligation (fix x → unfold operators →
/// close residue → forall_intro), then modus_ponens the chain to the
/// equation. On any resolution failure, falls back to a located error.
fn extEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, loc: u32) ElabError!kernel.Justification {
    const eq = self.pool.get(goal).eq;
    const model = (try extModel(self, loc)) orelse
        return self.fail(loc, "ext: no extensionality lemma (with an element-sort obligation) in scope", .{});

    // instantiate the ext lemma at (lhs, rhs): forall A, B; … peel two
    // binders with the goal's sides.
    var chain_ref = try self.emitStep(low, block_id, loc, model.lemma, sourceJust(model.lemma_source, loc));
    var chain_formula = model.lemma;
    for ([_]TermId{ eq.lhs, eq.rhs }) |arg| {
        const q = self.pool.get(chain_formula).quant;
        chain_formula = try self.pool.open(q.body, arg);
        chain_ref = try self.emitStep(low, block_id, loc, chain_formula, .{ .forall_elim = .{ .step = chain_ref, .with = arg, .with_loc = loc } });
    }
    // chain_formula is now `Ob1 -> (Ob2 ->) lhs = rhs`. Prove each Obi and
    // modus_ponens; the LAST modus_ponens (proving `lhs = rhs` = the goal)
    // is this tactic's returned justification, not an emitted step.
    for (0..model.obligation_count) |i| {
        const imp = self.pool.get(chain_formula).bin;
        const ob = imp.lhs; // forall x: <elementSort>; body
        const ob_ref = try extObligation(self, low, block_id, ob, model, loc);
        const mp: kernel.Justification = .{ .modus_ponens = .{ .implication = chain_ref, .antecedent = ob_ref } };
        chain_formula = imp.rhs;
        if (i + 1 == model.obligation_count) return mp; // proves the goal
        chain_ref = try self.emitStep(low, block_id, loc, chain_formula, mp);
    }
    // obligation_count == 0: the lemma had no premises (degenerate) — the
    // instantiated chain IS the equation; re-cite it. Unreachable for the
    // set/function models, but keep it total.
    return .{ .forall_elim = .{ .step = chain_ref, .with = eq.rhs, .with_loc = loc } };
}

/// Build the axiom/theorem citation justification for a lemma `Source`
/// resolved via wellKnownFact (which only yields axiom/theorem sources).
fn sourceJust(source: simplify_mod.Source, loc: u32) kernel.Justification {
    return switch (source) {
        .axiom => |a| .{ .axiom_ref = .{ .stmt = a.id, .loc = loc } },
        .theorem => |t| .{ .theorem_ref = .{ .stmt = t.id, .loc = loc } },
        .step => unreachable, // wellKnownFact never returns a step source
    };
}

/// Prove one obligation `forall x: <elementSort>; body`. `fix x`, unfold every
/// operator characterization lemma relevant to `body`, close the residue,
/// forall_intro. Returns the step proving the obligation.
fn extObligation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, ob: TermId, model: ExtModel, loc: u32) ElabError!kernel.SRef {
    const q = self.pool.get(ob).quant; // forall x: <elementSort>; body
    const x: term.Node.Fvar = .{ .name = try self.freshNamed("x"), .sort = model.universe };
    const x_id = try self.pool.add(.{ .fvar = x });
    const body = try self.pool.open(q.body, x_id);
    const fix_b = try self.newBlock(low, try self.freshNamed("ext-element"), block_id, .{ .fix = .{ .v = x } });

    // close the residue, dispatching on its shape:
    //   equation  `apply(f,x) = apply(g,x)`  — FUNCTION model: rewrite by the
    //     operator `<op>Apply` lemmas and join (the equation certifier).
    //   otherwise `member(x,·) -> member(x,·)` — SET model: unfold membership
    //     via `<op>Member` lemmas and close propositionally with tautology.
    const residue = if (self.pool.get(body) == .eq)
        try extFunctionResidue(self, low, fix_b, body, loc)
    else blk: {
        var premises: std.ArrayList(Premise) = .empty;
        try extUnfold(self, low, fix_b, body, x_id, &premises, loc);
        const steps_mark = low.steps.items.len;
        const blocks_mark = low.blocks.items.len;
        break :blk (try self.emitTautologyFrom(low, fix_b, body, premises.items, loc, steps_mark, blocks_mark)) orelse
            return self.fail(loc, "ext: could not close the pointwise obligation propositionally (is the identity true?)", .{});
    };
    _ = try self.emitStep(low, fix_b, loc, body, residue);
    self.closeBlock(low, fix_b);
    return try self.emitStep(low, block_id, loc, ob, .{ .forall_intro = .{ .id = fix_b, .loc = loc } });
}

/// Close a function-model pointwise obligation `apply(f,x) = apply(g,x)`:
/// gather the operator `<op>Apply` rewrite lemmas for every `apply(op(...),x)`
/// on either side, normalize both sides, and emit the rewrite join.
fn extFunctionResidue(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, eq_goal: TermId, loc: u32) ElabError!kernel.Justification {
    const eq = self.pool.get(eq_goal).eq;
    if (self.pool.alphaEq(eq.lhs, eq.rhs)) return .reflexivity;
    // collect every apply-characterization lemma in the theory scope: any
    // axiom/theorem whose stripped LHS is `apply(…, …)`. Enumerating the
    // scope (rather than guessing `<op>Apply` names) handles const heads
    // like `identityFn` (whose lemma is `identityApply`, not `identityFnApply`).
    const rules = try extApplyLemmas(self, loc);
    if (rules.len == 0) {
        return self.fail(loc, "ext: no apply lemmas in scope to unfold '{s}'", .{try self.renderTerm(eq_goal)});
    }
    const rs = simplify_mod.normalize(self.arena, self.pool, self.env, rules, eq.lhs, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(loc, "ext: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = simplify_mod.normalize(self.arena, self.pool, self.env, rules, eq.rhs, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(loc, "ext: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        return self.fail(loc, "ext: pointwise values differ: '{s}' vs '{s}' (is the identity true?)", .{
            try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
        });
    }
    return self.emitJoin(low, block_id, loc, rules, eq.lhs, eq.rhs, rs, rt);
}

/// Every apply-characterization rewrite lemma in the current theory scope:
/// each axiom/theorem whose stripped LHS is `apply(…, …)` (`composeApply`,
/// `identityApply`, …), turned into a rewrite rule. Enumerates the scope so a
/// const head (`identityFn`) is handled without name-guessing.
fn extApplyLemmas(self: *Elaborator, loc: u32) ElabError![]const simplify_mod.Rule {
    const apply_sym = (try self.wellKnownSym("apply")) orelse return &.{};
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    for (self.env.scopeStatements(self.theoryScope())) |sid| {
        const stmt = self.env.statements.items[@intFromEnum(sid)];
        const fact: struct { formula: TermId, source: simplify_mod.Source } = switch (stmt) {
            .axiom => |a| .{ .formula = a.formula, .source = .{ .axiom = .{ .id = sid, .loc = loc } } },
            .theorem => |t| if (t.proven and t.accelerated.len == 0)
                .{ .formula = t.formula, .source = .{ .theorem = .{ .id = sid, .loc = loc } } }
            else
                continue,
            .schema => continue,
        };
        // strip the forall prefix; keep only equations whose lhs is apply(…).
        var body = fact.formula;
        while (self.pool.get(body) == .quant and self.pool.get(body).quant.q == .forall) {
            const qn = self.pool.get(body).quant;
            const fv = try self.pool.add(.{ .fvar = .{ .name = try self.freshNamed("p"), .sort = qn.sort } });
            body = try self.pool.open(qn.body, fv);
        }
        const bn = self.pool.get(body);
        if (bn != .eq) continue;
        const lhs = self.pool.get(bn.eq.lhs);
        if (lhs != .app or lhs.app.sym != apply_sym) continue;
        switch (try self.equationRule(fact.formula, fact.source)) {
            .rule => |r| try rules.append(self.arena, r),
            else => {},
        }
    }
    return rules.items;
}

/// For each `member(x, op(a,b,…))` subterm in `formula`, instantiate the
/// operator's characterization lemma `<op>Member` at (a, b, …, x) and emit
/// it as a premise. Recurses structurally.
fn extUnfold(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, formula: TermId, x_id: TermId, out: *std.ArrayList(Premise), loc: u32) ElabError!void {
    const node = self.pool.get(formula);
    switch (node) {
        .pred => |p| {
            // member(x, s): if s = op(args…), unfold via <op>Member.
            const args = self.pool.args(p);
            if (args.len == 2) {
                const s = args[1];
                const sn = self.pool.get(s);
                if (sn == .app) {
                    try extUnfoldOp(self, low, block_id, sn.app, x_id, out, loc);
                }
            }
        },
        .bin => |b| {
            try extUnfold(self, low, block_id, b.lhs, x_id, out, loc);
            try extUnfold(self, low, block_id, b.rhs, x_id, out, loc);
        },
        .not => |inner| try extUnfold(self, low, block_id, inner, x_id, out, loc),
        else => {},
    }
}

/// Unfold one operator application `op(a, b, …)` appearing as a set: emit
/// `<op>Member` instantiated at (a, b, …, x). Dedups by formula.
fn extUnfoldOp(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, app: term.Node.App, x_id: TermId, out: *std.ArrayList(Premise), loc: u32) ElabError!void {
    const op_name = self.env.sym(app.sym).name;
    const lemma_name = try std.fmt.allocPrint(self.arena, "{s}Member", .{self.interner.stringBytes(op_name)});
    const fact = (try self.wellKnownFact(lemma_name, loc)) orelse return; // no lemma: leave atom opaque
    // instantiate: the lemma is `forall <setargs>; forall x; <iff>`.
    // bind the operator's args, then x.
    var ref = try self.emitStep(low, block_id, loc, fact.formula, sourceJust(fact.source, loc));
    var cur = fact.formula;
    // COPY the arg ids: pool.args aliases pool.extra, which the emitStep/
    // pool.open calls below grow — the slice would dangle (0xAAAAAAAA).
    const op_args = try self.arena.dupe(TermId, self.pool.args(app));
    for (op_args) |a| {
        const qn = self.pool.get(cur);
        if (qn != .quant) return;
        cur = try self.pool.open(qn.quant.body, a);
        ref = try self.emitStep(low, block_id, loc, cur, .{ .forall_elim = .{ .step = ref, .with = a, .with_loc = loc } });
    }
    // now bind x
    const qn = self.pool.get(cur);
    if (qn != .quant) return;
    cur = try self.pool.open(qn.quant.body, x_id);
    ref = try self.emitStep(low, block_id, loc, cur, .{ .forall_elim = .{ .step = ref, .with = x_id, .with_loc = loc } });
    // dedup
    for (out.items) |p| if (self.pool.alphaEq(p.formula, cur)) return;
    try out.append(self.arena, .{ .formula = cur, .ref = ref });
    // recurse into the operator's set arguments (nested operators unfold too)
    for (op_args) |a| {
        const an = self.pool.get(a);
        if (an == .app) try extUnfoldOp(self, low, block_id, an.app, x_id, out, loc);
    }
}

/// Resolve the extensionality model in the current theory scope. Tries
/// `extensionality` then `funcExtensionality`; reads the element sort +
/// obligation count from the lemma's shape. The element sort is derived
/// STRUCTURALLY from the first obligation's binder (`forall x: <sort>; …`),
/// not looked up by name — so the tactic works whatever that sort is called
/// (`Element`, `Universe`, …).
fn extModel(self: *Elaborator, loc: u32) ElabError!?ExtModel {
    const fact = (try self.wellKnownFact("extensionality", loc)) orelse
        (try self.wellKnownFact("funcExtensionality", loc)) orelse return null;
    // count the leading obligations: peel `forall A, B;` then count the
    // `(forall x; …) ->` premises before the `A = B` conclusion.
    var body = fact.formula;
    var peeled: usize = 0;
    while (self.pool.get(body) == .quant and self.pool.get(body).quant.q == .forall and peeled < 2) : (peeled += 1) {
        const fv = try self.pool.add(.{ .fvar = .{ .name = try self.freshNamed("s"), .sort = self.pool.get(body).quant.sort } });
        body = try self.pool.open(self.pool.get(body).quant.body, fv);
    }
    // the element sort is the binder sort of the first obligation
    // `forall x: <elementSort>; …` (lhs of the first implication).
    var universe: ?term.SortId = null;
    var obligations: usize = 0;
    while (self.pool.get(body) == .bin and self.pool.get(body).bin.op == .implies) : (obligations += 1) {
        const premise = self.pool.get(body).bin.lhs;
        if (universe == null and self.pool.get(premise) == .quant) {
            universe = self.pool.get(premise).quant.sort;
        }
        body = self.pool.get(body).bin.rhs;
    }
    return .{ .universe = universe orelse return null, .lemma = fact.formula, .lemma_source = fact.source, .obligation_count = obligations };
}
