//! The `extensionality` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
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
const Engine = @import("../../../Engine.zig");
const Walk = @import("../Walk.zig");
const Elab = @import("../Elab.zig");
const Schema = @import("../Schema.zig");
const Accelerant = @import("../Accelerant.zig");
const EqCert = @import("../EqCert.zig");
const rewrite = @import("rewrite.zig");
const smt = @import("../smt.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const common = @import("common.zig");

/// the `_quantified` variant: a `forall …; s = t` goal, peeled first
quantified: bool,

pub const schema_slot: Accelerant.SchemaSlot = .lemma;
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
    return if (self.quantified) produceExtensionalityQuantified(prove, w, goal, c) else produceExtensionality(prove, w, goal, c);
}

/// `[using extensionality(extLemma) unfold1 unfold2 …]` — prove a bare `s = t` equation by
/// extensionality. See `produceExtensionalityQuantified` for the `forall …; s = t` form.
pub fn produceExtensionality(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.schema == null) return prove.fail(c.rule.start, "extensionality requires an extensionality lemma: [using extensionality(<lemma>) <unfold lemmas>]", .{});
    if (prove.pool.get(goal) != .eq) {
        if (prove.pool.get(goal) == .quant and prove.pool.get(goal).quant.q == .forall) {
            return prove.fail(c.rule.start, "extensionality proves equations; did you mean extensionality_quantified?", .{});
        }
        return prove.fail(c.rule.start, "extensionality proves an equation 's = t'; the goal is not an equation", .{});
    }
    return buildExtensionality(prove, w, c, goal, &.{});
}

/// `[using extensionality_quantified(extLemma) unfold1 …]` — like extensionality but the goal
/// is `forall …; s = t`. Peel the ∀ prefix into fresh eigenvariables, run the core on the body
/// equation, and re-generalize via the `fix`/`generalize` shell.
pub fn produceExtensionalityQuantified(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.schema == null) return prove.fail(c.rule.start, "extensionality_quantified requires an extensionality lemma: [using extensionality_quantified(<lemma>) <unfold lemmas>]", .{});
    const peeled = (try common.peelForallEq(prove, goal, c, "extensionality_quantified")) orelse return null;
    return buildExtensionality(prove, w, c, peeled.body, peeled.eigen);
}

/// A resolved extensionality lemma, read STRUCTURALLY off `c.schema`'s formula: its instantiated
/// obligations (one per pointwise inclusion) + how the cert cites the lemma.
const ExtLemma = struct {
    formula: TermId,
    is_axiom: bool,
    head: lexer.Token,
    /// each obligation `forall x: <elementSort>; body`, instantiated at (s, t) — outermost first.
    obligations: []const TermId,
    /// the element sort (the obligation binder's sort).
    universe: SortId,
};

/// Shared core for both extensionality variants. Instantiate the ext lemma at (s, t), prove each
/// pointwise obligation (`fix x` → unfold → close residue → generalize), then modus_ponens the
/// chain to `s = t`; wrap in the ∀-eigenvariable `fix` shell and package the synthetic schema.
fn buildExtensionality(prove: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    // ADMIT: the goal-shape + ext-lemma-present validation ran in the produce* caller. Everything
    // below RESOLVES the ext lemma + each unfold lemma (resolveFactRef) and builds the cert. Skip
    // under `--fast`.
    // `--fast` declines to EMIT the certificate; the checks BEFORE it still run — for
    // extensionality that is resolving the ext lemma and each cited unfold lemma, and
    // confirming the goal is an equation whose sides the lemma applies to. There is no separate
    // decision to run: `emitExtEquation` both decides and emits, so admit lands immediately
    // after the lemmas resolve (below), which is the furthest point reachable without building
    // the cert. See design/acceleration.md.
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix` at the call site) into value
    // params — the fully-quantified fixtures have none (all free vars are peeled eigenvariables),
    // but a bare `[using extensionality(...)]` over fixed locals would surface them.
    const ag = try common.abstractGoal(prove, &b, eq_goal_raw, &.{}, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const eq = prove.pool.get(eq_goal).eq;
    const s = eq.lhs;
    const t = eq.rhs;

    // resolve the ext lemma (global fact) + instantiate at (s, t).
    const lemma = try resolveExtLemma(prove, c.schema.?, s, t);

    // resolve each cited UNFOLD lemma to its formula (global facts). For the SET model these are
    // `member(x, op(...)) iff …`; for the FUNCTION model `apply(op(...), x) = …` rewrite rules.
    const unfolds = try prove.ctx.arena.alloc(ExtUnfold, c.refs.len);
    for (c.refs, unfolds) |ref, *out| out.* = try resolveUnfold(prove, ref);

    // build the cert steps proving `s = t`. This BOTH decides and emits: buried inside it is
    // `emitExtSetResidue`'s `smt.tautology` on the pointwise obligation, which is the real
    // decision (it is what refutes `union(a, b) = intersection(a, b)`). There is no way to
    // reach that verdict without running the emission, so admit mode runs it too and throws
    // the steps away — the cost is building an AST we discard, which is far cheaper than the
    // alternative of `--fast` accepting a false set identity.
    var body_steps: std.ArrayList(ast.Step) = .empty;
    try emitExtEquation(prove, &b, &body_steps, lemma, unfolds, s, t, c);

    // ADMIT: the pointwise obligation closed, so a certificate demonstrably exists — only
    // packaging it as the synthetic schema is pruned.
    if (prove.admit_mode) {
        prove.producer_premise_refs = null;
        prove.admit_ok = true;
        return null;
    }

    // the inner proposition the cert proves: the equation `s = t` (no local premises — the ext +
    // unfold lemmas are all globals cited inside the cert; a LOCAL cite is unusual but supported
    // via the premises slot below).
    const eq_prop = try prove.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });

    // wrap in `fix` blocks for the ∀ eigenvariables (the quantified variant's re-generalization).
    var steps: []const ast.Step = body_steps.items;
    steps = try common.wrapSimplifyForall(prove, &b, eigen, eq_prop, steps);

    // schema body = the ∀-generalized equation.
    const full_prop = try common.closeOverEigen(prove, eq_prop, eigen);
    const body_expr = try b.termExpr(full_prop);

    const params = try prove.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        pp.* = .{ .name = b.tok(name), .kind = .{ .value = b.sortTok(sort) } };
    }

    const hash = Schema.termHash(prove.ctx.interner, prove.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "extensionality{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = try common.localRefTokens(prove, w, c.refs), // a LOCAL unfold/ext cite, if any
        .seen = b.seen.items,
        .fvar_binds = try common.fvarBinds(prove, w, abs),
    };
}

/// Resolve the extensionality lemma token to its formula and instantiate its `forall A, B;`
/// prefix at (s, t), reading off the leading `(forall x; …) ->` obligations. Requires a GLOBAL
/// axiom/theorem (the ext lemma is never a local step in the fixtures).
fn resolveExtLemma(prove: *Prove, head: lexer.Token, s: TermId, t: TermId) Error!ExtLemma {
    // `citedFactFormula` routes by mode: strict resolves the proven fact, admit mode reads the
    // STATEMENT (no ProveTask racked) so the pre-certificate checks can run under `--fast`.
    const got = try common.citedFactFormula(prove, head);
    const formula = got.formula;
    const is_axiom = got.is_axiom;

    // peel the two structure binders at (s, t).
    var body = formula;
    for ([_]TermId{ s, t }) |arg| {
        const node = prove.pool.get(body);
        if (node != .quant or node.quant.q != .forall) {
            return prove.fail(head.start, "extensionality: '{s}' is not a two-argument universal (forall A, B; …)", .{prove.text(head)});
        }
        body = try prove.pool.open(node.quant.body, arg);
    }
    // count the leading `(forall x; body) ->` obligations before the `s = t` conclusion.
    var obligations: std.ArrayList(TermId) = .empty;
    var universe: ?SortId = null;
    var cur = body;
    while (true) {
        const node = prove.pool.get(cur);
        if (node != .bin or node.bin.op != .implies) break;
        const premise = node.bin.lhs;
        if (prove.pool.get(premise) == .quant and prove.pool.get(premise).quant.q == .forall) {
            if (universe == null) universe = prove.pool.get(premise).quant.sort;
        }
        try obligations.append(prove.ctx.arena, premise);
        cur = node.bin.rhs;
    }
    if (obligations.items.len == 0 or universe == null) {
        return prove.fail(head.start, "extensionality: '{s}' has no pointwise obligation (forall x: <element>; …)", .{prove.text(head)});
    }
    // the residual conclusion must be `s = t`.
    if (prove.pool.get(cur) != .eq or !prove.pool.alphaEq(prove.pool.get(cur).eq.lhs, s) or !prove.pool.alphaEq(prove.pool.get(cur).eq.rhs, t)) {
        return prove.fail(head.start, "extensionality: '{s}' does not conclude the goal equation", .{prove.text(head)});
    }
    return .{ .formula = formula, .is_axiom = is_axiom, .head = head, .obligations = obligations.items, .universe = universe.? };
}

/// A resolved unfold lemma: its formula + how the cert cites it. `set_op`/`fn_op` is the head
/// symbol of the characterized operator (for matching a `member(x, op(...))` / `apply(op(...), x)`
/// subterm to its lemma); null when the lemma has no such head (degenerate).
const ExtUnfold = struct {
    formula: TermId,
    is_axiom: bool,
    head: lexer.Token,
    local: bool,
    /// the operator head symbol this lemma characterizes (read off its stripped LHS).
    op: ?term.SymId,
    /// true = a FUNCTION model rewrite (`apply(op,x) = …`); false = a SET model `member iff`.
    is_eq: bool,
};

fn resolveUnfold(prove: *Prove, ref: lexer.Token) Error!ExtUnfold {
    // ext unfold lemmas are always GLOBAL facts (membership / apply axioms) in practice.
    // `citedFactFormula` routes by mode: strict resolves the proven fact, admit mode reads the
    // STATEMENT (no ProveTask racked) so the pre-certificate checks can run under `--fast`.
    const got = try common.citedFactFormula(prove, ref);
    const formula = got.formula;
    const is_axiom = got.is_axiom;
    // strip the forall prefix; classify by the stripped body shape + read the characterized op.
    var body = formula;
    while (prove.pool.get(body) == .quant and prove.pool.get(body).quant.q == .forall) {
        const q = prove.pool.get(body).quant;
        const fv = try prove.pool.add(.{ .fvar = .{ .name = try prove.freshNamed("u"), .sort = q.sort } });
        body = try prove.pool.open(q.body, fv);
    }
    const bn = prove.pool.get(body);
    var op: ?term.SymId = null;
    var is_eq = false;
    if (bn == .eq) {
        // FUNCTION model: `apply(op(...), x) = …` — the op is the head of the FIRST apply arg.
        is_eq = true;
        const lhs = prove.pool.get(bn.eq.lhs);
        if (lhs == .app and prove.pool.args(lhs.app).len >= 1) {
            const first = prove.pool.get(prove.pool.args(lhs.app)[0]);
            if (first == .app) op = first.app.sym;
        }
    } else {
        // SET model: `member(x, op(...)) iff …` — the op is the head of member's SECOND arg. The
        // iff desugars to a conjunction; the lhs of a conjunct's implication carries `member`.
        is_eq = false;
        op = setUnfoldOp(prove, body);
    }
    return .{ .formula = formula, .is_axiom = is_axiom, .head = ref, .local = false, .op = op, .is_eq = is_eq };
}

/// Read the characterized operator head from a SET unfold lemma body. The `iff` desugars to
/// `(member(x, op(...)) -> R) and (R -> member(x, op(...)))`; find the `member(_, op(...))` atom
/// and return `op`'s head symbol (a const head has no args → still a valid sym).
fn setUnfoldOp(prove: *Prove, body: TermId) ?term.SymId {
    return findMemberOp(prove, body);
}

fn findMemberOp(prove: *Prove, id: TermId) ?term.SymId {
    // walk only through bin/not into pred nodes (the original's restricted recursion), returning
    // the FIRST pred's set-arg head sym (leftmost — bin pushes rhs then lhs so lhs pops first).
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), prove.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, id) catch return null;
    while (stack.pop()) |cur| {
        switch (prove.pool.get(cur)) {
            .pred => |p| {
                const args = prove.pool.args(p);
                if (args.len == 2) {
                    const set = prove.pool.get(args[1]);
                    if (set == .app) return set.app.sym;
                }
            },
            .bin => |bn| {
                stack.append(a, bn.rhs) catch return null;
                stack.append(a, bn.lhs) catch return null;
            },
            .not => |inner| stack.append(a, inner) catch return null,
            else => {},
        }
    }
    return null;
}

/// Emit the extensionality certificate proving `s = t` into `block`: cite the ext lemma,
/// apply_at it at (s, t) to reach `Ob1 -> (Ob2 ->) s = t`, prove each obligation, and
/// modus_ponens the chain. The lemma cite + each obligation step live directly in `block`.
fn emitExtEquation(prove: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), lemma: ExtLemma, unfolds: []const ExtUnfold, s: TermId, t: TermId, c: ast.Step.Claim) Error!void {
    // step 0: cite the ext lemma.
    const law = try prove.freshNamed("extensionality");
    const word: []const u8 = "cite";
    const law_refs = try prove.ctx.arena.alloc(lexer.Token, 1);
    law_refs[0] = lemma.head;
    try block.append(prove.ctx.arena, try b.claimStep(law, try b.termExpr(lemma.formula), .by, try common.internStrRt(prove, word), &.{}, law_refs));

    // apply_at at (s, t): one multi-arg elim peels both structure binders.
    var chain_formula = lemma.formula;
    for ([_]TermId{ s, t }) |arg| {
        chain_formula = try prove.pool.open(prove.pool.get(chain_formula).quant.body, arg);
    }
    const elim_lbl = try prove.freshNamed("extensionality-at-sides");
    const elim_args = try prove.ctx.arena.alloc(*const ast.Expr, 2);
    elim_args[0] = try b.termExpr(s);
    elim_args[1] = try b.termExpr(t);
    try block.append(prove.ctx.arena, try b.claimStep(elim_lbl, try b.termExpr(chain_formula), .by, try prove.internStr("apply_at"), elim_args, try common.oneRef(prove, b, law)));

    // prove each obligation + modus_ponens it into the chain; the last mp proves `s = t`.
    var chain_label = elim_lbl;
    for (lemma.obligations, 0..) |ob, i| {
        const ob_label = try emitExtObligation(prove, b, block, ob, lemma.universe, unfolds, c);
        const imp = prove.pool.get(chain_formula).bin;
        const mp_label = if (i + 1 == lemma.obligations.len) try prove.freshNamed("extensionality-conclusion") else try prove.freshNamed("extensionality-step");
        const mp_refs = try prove.ctx.arena.alloc(lexer.Token, 2);
        mp_refs[0] = b.tok(chain_label);
        mp_refs[1] = b.tok(ob_label);
        try block.append(prove.ctx.arena, try b.claimStep(mp_label, try b.termExpr(imp.rhs), .by, try prove.internStr("modus_ponens"), &.{}, mp_refs));
        chain_formula = imp.rhs;
        chain_label = mp_label;
    }
}

/// Prove one obligation `forall x: <element>; body` — a `fix x { … }` block closing the pointwise
/// residue — then `generalize` it. Returns the label of the generalize step (in `block`).
fn emitExtObligation(prove: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), ob: TermId, universe: SortId, unfolds: []const ExtUnfold, c: ast.Step.Claim) Error!StrId {
    const q = prove.pool.get(ob).quant; // forall x: <element>; body
    const x: term.Node.Fvar = .{ .name = try prove.freshNamed("x"), .sort = universe };
    const x_id = try prove.pool.add(.{ .fvar = x });
    const body = try prove.pool.open(q.body, x_id);

    var fix_steps: std.ArrayList(ast.Step) = .empty;
    if (prove.pool.get(body) == .eq) {
        try emitExtFunctionResidue(prove, b, &fix_steps, body, unfolds, c);
    } else {
        try emitExtSetResidue(prove, b, &fix_steps, body, x_id, unfolds, c);
    }

    // wrap the fix block + generalize out.
    const fix_label = try prove.freshNamed("fix");
    const bname = b.tok(try common.displayName(prove, x.name));
    const fix_step: ast.Step = .{ .label = b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = b.sortTok(universe), .steps = fix_steps.items } } };
    try block.append(prove.ctx.arena, fix_step);

    // the ∀-closed obligation.
    const closed = try prove.pool.close(body, x.name);
    const ob_closed = try prove.pool.add(.{ .quant = .{ .q = .forall, .sort = universe, .hint = x.name, .body = closed } });
    const gen_label = try prove.freshNamed("pointwise-holds-for-all");
    try block.append(prove.ctx.arena, try b.claimStep(gen_label, try b.termExpr(ob_closed), .by, try prove.internStr("generalize"), &.{}, try common.oneRef(prove, b, fix_label)));
    return gen_label;
}

/// FUNCTION model residue: close `apply(f, x) = apply(g, x)` by rewriting BOTH sides with the
/// cited `apply` unfold lemmas to a common normal form and emitting the EqCert join.
fn emitExtFunctionResidue(prove: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), eq_goal: TermId, unfolds: []const ExtUnfold, c: ast.Step.Claim) Error!void {
    const eq = prove.pool.get(eq_goal).eq;
    // build rewrite rules from the cited (equation) unfold lemmas, in citation order.
    var rules: std.ArrayList(rewrite.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    for (unfolds) |u| {
        if (!u.is_eq) return prove.fail(u.head.start, "extensionality: '{s}' is a membership lemma, but the obligation is an equation (function model)", .{prove.text(u.head)});
        const rule = (try common.orientRule(prove, u.formula)) orelse
            return prove.fail(u.head.start, "extensionality: '{s}' is not a usable apply rewrite rule", .{prove.text(u.head)});
        try rules.append(prove.ctx.arena, rule);
        try cites.append(prove.ctx.arena, .{ .global = .{ .head = u.head, .is_axiom = u.is_axiom } });
    }
    const rs = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules.items, eq.lhs, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "extensionality: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules.items, eq.rhs, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "extensionality: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!prove.pool.alphaEq(rs.nf, rt.nf)) {
        return prove.fail(c.rule.start, "extensionality: pointwise values differ: '{s}' vs '{s}' (is the identity true?)", .{
            try prove.renderTerm(rs.nf), try prove.renderTerm(rt.nf),
        });
    }
    var cert: EqCert = .{ .b = b, .pool = prove.pool, .rules = rules.items, .cites = cites.items, .fresh_ctx = prove, .freshFn = common.eqCertFresh };
    _ = try cert.emitJoin(block, eq.lhs, eq.rhs, rs, rt);
}

/// SET model residue: for each `member(x, op(...))` subterm of `body`, instantiate the matching
/// cited membership lemma at (op-args…, x) as a premise step, then close `body` (a `member -> …`
/// implication) propositionally by REUSING the tautology core with those premises.
fn emitExtSetResidue(prove: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), body: TermId, x_id: TermId, unfolds: []const ExtUnfold, c: ast.Step.Claim) Error!void {
    var prems: std.ArrayList(common.TautAst.Prem) = .empty;
    try emitExtUnfoldMembership(prove, b, block, body, x_id, unfolds, &prems);

    // DECIDE + close propositionally over the emitted unfold-instance premises.
    const prem_formulae = try prove.ctx.arena.alloc(TermId, prems.items.len);
    for (prems.items, prem_formulae) |p, *out| out.* = p.formula;
    const verdict = smt.tautology(prove.ctx.arena, prove.pool, prem_formulae, body) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {},
        .too_many_atoms => |n| return prove.fail(c.rule.start, "extensionality: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
        .countermodel => return prove.fail(c.rule.start, "extensionality: could not close the pointwise obligation propositionally (is the identity true?)", .{}),
    }

    // GENERATE the cert: collect atoms (over premises + goal), replay the truth search.
    var atom_list: std.ArrayList(TermId) = .empty;
    for (prem_formulae) |f| smt.collectAtoms(prove.ctx.arena, prove.pool, &atom_list, f) catch return error.OutOfMemory;
    smt.collectAtoms(prove.ctx.arena, prove.pool, &atom_list, body) catch return error.OutOfMemory;

    const assignment = try prove.ctx.arena.alloc(?bool, atom_list.items.len);
    @memset(assignment, null);
    const lit_blocks = try prove.ctx.arena.alloc(?StrId, atom_list.items.len);
    @memset(lit_blocks, null);
    var cert: common.TautAst = .{
        .p = prove,
        .b = b,
        .goal = body,
        .premises = prems.items,
        .atoms = atom_list.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
    };
    try cert.deriveGoal(block);
}

/// Recurse over `body`, and for each `member(x, op(args…))` subterm instantiate the cited
/// membership lemma whose characterized op matches, at (args…, x). Each instance is emitted as a
/// step in `block` and recorded as a tautology premise. Dedups by formula.
fn emitExtUnfoldMembership(prove: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), body: TermId, x_id: TermId, unfolds: []const ExtUnfold, out: *std.ArrayList(common.TautAst.Prem)) Error!void {
    // ITERATIVE (was mutual recursion emitExtUnfoldMembership↔emitExtUnfoldOp). A worklist of
    // `Work` items: a `.membership` walks the body's bin/not/pred skeleton; a `.op` instantiates
    // the membership lemma for one `op(args)` and queues its set-typed args. Items are pushed
    // REVERSED so the leftmost/outermost is processed first — preserving the pre-order,
    // left-to-right premise-collection (+ dedup) order of the recursion. Scratch on ctx.gpa.
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    const Work = union(enum) { membership: TermId, op: term.Node.App };
    var stack: std.ArrayList(Work) = .empty;
    try stack.append(wa, .{ .membership = body });
    while (stack.pop()) |item| switch (item) {
        .membership => |m| {
            switch (prove.pool.get(m)) {
                .pred => |p| {
                    const args = prove.pool.args(p);
                    if (args.len == 2) {
                        const set = prove.pool.get(args[1]);
                        if (set == .app) try stack.append(wa, .{ .op = set.app });
                    }
                },
                .bin => |bn| {
                    try stack.append(wa, .{ .membership = bn.rhs }); // rhs pushed first → lhs first
                    try stack.append(wa, .{ .membership = bn.lhs });
                },
                .not => |inner| try stack.append(wa, .{ .membership = inner }),
                else => {},
            }
        },
        .op => |app| try emitExtUnfoldOp(prove, b, block, app, x_id, unfolds, out, wa, &stack),
    };
}

/// Process ONE `op(args…)` for extensionality unfolding: instantiate the matching cited membership
/// lemma at (args…, x) — cite + apply_at per op-arg then x, dedup + record the premise — and
/// QUEUE the op's set-typed args onto `stack` (nested operators unfold too). Was prove-recursive;
/// now pushes follow-up `.op` work instead. `Work`/`stack` are the driver's (comptime-typed).
fn emitExtUnfoldOp(prove: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), app: term.Node.App, x_id: TermId, unfolds: []const ExtUnfold, out: *std.ArrayList(common.TautAst.Prem), wa: std.mem.Allocator, stack: anytype) Error!void {
    // find the cited lemma characterizing this op head.
    var lemma: ?ExtUnfold = null;
    for (unfolds) |u| {
        if (u.op != null and u.op.? == app.sym) {
            lemma = u;
            break;
        }
    }
    // COPY the op-arg ids (a plain snapshot; app args are arena-owned and stable, so this is
    // only for the local mutation below).
    const op_args = try prove.ctx.arena.dupe(TermId, prove.pool.args(app));
    // helper: queue the op's set-typed (app) args, REVERSED so arg 0 processes first.
    const queueArgs = struct {
        fn f(p: *Prove, oa: []const TermId, wal: std.mem.Allocator, st: anytype) Error!void {
            var i: usize = oa.len;
            while (i > 0) {
                i -= 1;
                const an = p.pool.get(oa[i]);
                if (an == .app) try st.append(wal, .{ .op = an.app });
            }
        }
    }.f;
    const u = lemma orelse {
        // no cited lemma for this op — leave the atom opaque, but unfold set-typed args.
        try queueArgs(prove, op_args, wa, stack);
        return;
    };

    // cite the lemma; apply_at at each op-arg, then at x.
    const cite_label = try prove.freshNamed("membership-lemma");
    const word: []const u8 = "cite";
    const cite_refs = try prove.ctx.arena.alloc(lexer.Token, 1);
    cite_refs[0] = u.head;
    try block.append(prove.ctx.arena, try b.claimStep(cite_label, try b.termExpr(u.formula), .by, try common.internStrRt(prove, word), &.{}, cite_refs));

    var cur = u.formula;
    var cur_label = cite_label;
    var bindings: std.ArrayList(TermId) = .empty;
    for (op_args) |a| try bindings.append(prove.ctx.arena, a);
    try bindings.append(prove.ctx.arena, x_id);
    for (bindings.items) |val| {
        const qn = prove.pool.get(cur);
        if (qn != .quant or qn.quant.q != .forall) {
            return prove.fail(u.head.start, "extensionality: '{s}' is not universal enough to instantiate", .{prove.text(u.head)});
        }
        cur = try prove.pool.open(qn.quant.body, val);
        const lbl = try prove.freshNamed("membership-at-element");
        const arg1 = try prove.ctx.arena.alloc(*const ast.Expr, 1);
        arg1[0] = try b.termExpr(val);
        try block.append(prove.ctx.arena, try b.claimStep(lbl, try b.termExpr(cur), .by, try prove.internStr("apply_at"), arg1, try common.oneRef(prove, b, cur_label)));
        cur_label = lbl;
    }
    // dedup by formula, then record as a premise.
    for (out.items) |pr| if (prove.pool.alphaEq(pr.formula, cur)) return;
    try out.append(prove.ctx.arena, .{ .formula = cur, .label = cur_label, .blk_label = cur_label });

    // queue the operator's set-typed arguments (nested operators unfold too).
    try queueArgs(prove, op_args, wa, stack);
}
