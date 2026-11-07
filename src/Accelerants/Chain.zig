//! The `chain` accelerated tactic — a struct that is one variant of `Accelerants.Tactic`. See
//! `Accelerants.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const TermId = term.TermId;
const kernel = @import("../kernel.zig");
const Engine = @import("../Engine.zig");
const Walk = @import("../Engine/ProveTask/Walk.zig");
const Elab = @import("../Engine/ProveTask/Elab.zig");
const Schema = @import("../Engine/ProveTask/Schema.zig");
const Accelerants = @import("../Accelerants.zig");
const EqCert = @import("EqCert.zig");
const rewrite = @import("rewrite.zig");
const Site = @import("Site.zig");
const Error = Site.Error;
const tokName = Site.tokName;
const common = @import("common.zig");

pub const schema_slot: Accelerants.SchemaSlot = .none;
pub const premise_shape: Accelerants.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

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
    _ = self;
    return produceChain(site, w, e, goal, c);
}

/// A cited equation, prepared for the chain search + cert. `lhs`/`rhs` are its two sides
/// (param-substituted); `body_label` is the step INSIDE the synthetic proof that proves this
/// equation in its cited (forward) orientation — a restated-hypothesis step for a LOCAL ref,
/// or an emitted `[by axiom|theorem …]` step for a GLOBAL one. `local` splits which.
const ChainEq = struct { lhs: TermId, rhs: TermId, body_label: StrId, local: bool, formula: TermId };

/// One edge of the found rewrite path: apply equation `eq_idx` in orientation `forward`
/// (`forward` = lhs→rhs) to reach `result` from its predecessor.
const ChainEdge = struct { eq_idx: usize, forward: bool, result: TermId };

/// `[using chain eq1 eq2 …]` — prove an equality goal `A = Z` from the cited equations used
/// as UNDIRECTED rewrite rules. Where `simplify` orients each equation left→right and reduces
/// to a normal form, `chain` BFS-searches for a rewrite path `A → … → Z`, applying each cited
/// `p = q` (or its `symmetry` flip) via the kernel `rewrite` (which rewrites all occurrences,
/// so congruence is free). Two phases: SEARCH the path purely, then EMIT it as reflexivity +
/// `symmetry`/`rewrite` steps the kernel re-checks — certificate-total, no --fast taint.
///
/// Synthetic schema (simplify-shaped): value params abstract the goal's free (fix-eigenvar)
/// fvars; LOCAL cited equations become premise antecedents restated by hypothesis; GLOBAL
/// equations are cited `[by axiom|theorem …]` INSIDE the synthetic proof.
pub fn produceChain(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    _ = e;
    if (c.args.len != 0) return site.fail(c.rule.start, "chain takes no arguments", .{});
    const gn0 = site.pool.get(goal);
    if (gn0 != .eq) return site.fail(c.rule.start, "chain proves an equation 'A = Z'; the goal is not an equation", .{});
    if (c.refs.len == 0) return site.fail(c.rule.start, "chain needs at least one cited equation", .{});
    // ADMIT: the pre-cert validation (goal is an equation, >=1 ref) is done; everything below
    // RESOLVES the cited equations (resolveFactRef) and runs the BFS connection search. Skip
    // under `--fast`.
    // `--fast` declines to EMIT the certificate; the BFS DECISION (can the cited equations
    // connect the goal's two sides?) still runs. Admit lands just before PHASE 2 below.
    var b: Accelerants.Builder = .{ .arena = site.ctx.arena, .interner = site.ctx.interner, .pool = site.pool, .loc = c.rule.start };

    // RESOLVE each cited equation to its formula + how the synthetic proof cites it (LOCAL =
    // restated hypothesis, GLOBAL = a `[by axiom|theorem]` head step). Kept as raw formulae
    // for the fvar-abstraction pass; the sides are (re)read after substitution below.
    const Prepared = struct { formula: TermId, body_label: StrId, local: bool, head: lexer.Token, is_axiom: bool };
    const prepared = try site.ctx.arena.alloc(Prepared, c.refs.len);
    for (c.refs, prepared) |ref, *out| {
        const is_local = ref.qualifier == InternPool.Index.none and w.findStep(Site.tokName(ref)) != null;
        var formula: TermId = undefined;
        var body_label: StrId = undefined;
        var is_axiom = false;
        if (is_local) {
            const sref = try site.resolveStepRef(w, ref);
            formula = site.producerPremiseFormula(sref);
            body_label = try common.premiseHypLabel(site, ref); // the restated-hypothesis step's label
        } else {
            const got = try common.citedFactFormula(site, ref);
            formula = got.formula;
            body_label = try site.freshNamed("chain-cite"); // the `[by axiom|theorem]` head step
            is_axiom = got.is_axiom;
        }
        if (site.pool.get(formula) != .eq) return site.fail(ref.start, "'{s}' is not an equation", .{site.text(ref)});
        out.* = .{ .formula = formula, .body_label = body_label, .local = is_local, .head = ref, .is_axiom = is_axiom };
    }

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix`) into value params — the
    // goal plus each LOCAL equation formula (a global's formula is closed) speak the param
    // names `p1, p2, …` after substitution. (chain has no ∀-eigenvariables to exclude.)
    var local_pf: std.ArrayList(TermId) = .empty;
    for (prepared) |p| if (p.local) try local_pf.append(site.ctx.arena, p.formula);
    const ag = try common.abstractGoal(site, &b, goal, local_pf.items, &.{});
    const abs = ag.abs;

    const gn = site.pool.get(ag.goal_p).eq;
    const start = gn.lhs;
    const target = gn.rhs;
    const eqs = try site.ctx.arena.alloc(ChainEq, prepared.len);
    for (prepared, eqs) |p, *out| {
        const f = try common.substFvarsToParams(site, p.formula, abs);
        const fn2 = site.pool.get(f).eq;
        out.* = .{ .lhs = fn2.lhs, .rhs = fn2.rhs, .body_label = p.body_label, .local = p.local, .formula = f };
    }

    // PHASE 1 — BFS `start` → `target` over the equations as undirected rewrites. The pool is
    // NOT hash-consed (structurally-equal terms carry distinct TermIds), so a by-id `seen` set
    // would miss reconvergence; canonicalize each rewrite result to an already-seen id when
    // alpha-equal (target first — the common case — then the rest of the frontier).
    var came_from: std.AutoHashMapUnmanaged(TermId, ChainEdge) = .empty;
    var seen: std.AutoHashMapUnmanaged(TermId, void) = .empty;
    var queue: std.ArrayList(TermId) = .empty;
    try queue.append(site.ctx.arena, start);
    try seen.put(site.ctx.arena, start, {});
    var head_i: usize = 0;
    const cap = 4096; // node budget — congruence-free equational chains are tiny
    var found = site.pool.alphaEq(start, target);
    while (head_i < queue.items.len and !found and seen.count() < cap) {
        const curterm = queue.items[head_i];
        head_i += 1;
        for (eqs, 0..) |eq, ei| {
            for ([_]bool{ true, false }) |forward| {
                const from = if (forward) eq.lhs else eq.rhs;
                const to = if (forward) eq.rhs else eq.lhs;
                const raw = try site.pool.rewriteAll(curterm, from, to);
                if (site.pool.alphaEq(raw, curterm)) continue; // no change
                var nxt = raw;
                if (site.pool.alphaEq(raw, target)) {
                    nxt = target;
                } else {
                    var it = seen.keyIterator();
                    while (it.next()) |k| {
                        if (site.pool.alphaEq(raw, k.*)) {
                            nxt = k.*;
                            break;
                        }
                    }
                }
                if (seen.get(nxt) != null) continue; // already reached
                try seen.put(site.ctx.arena, nxt, {});
                try came_from.put(site.ctx.arena, nxt, .{ .eq_idx = ei, .forward = forward, .result = curterm });
                try queue.append(site.ctx.arena, nxt);
                if (site.pool.alphaEq(nxt, target)) {
                    found = true;
                    break;
                }
            }
            if (found) break;
        }
    }
    if (!found) {
        // render over ORIGINAL caller names (undo the param abstraction) for the diagnostic.
        return site.fail(c.rule.start, "chain: cannot connect '{s}' to '{s}' from the cited equations", .{
            try site.renderTerm(try common.unabstract(site, start, abs)),
            try site.renderTerm(try common.unabstract(site, target, abs)),
        });
    }

    // reconstruct the path start → … → target (list of intermediate terms, target last).
    var path: std.ArrayList(TermId) = .empty;
    {
        var t = target;
        while (!site.pool.alphaEq(t, start)) {
            try path.append(site.ctx.arena, t);
            const edge = came_from.get(t) orelse return site.fail(c.rule.start, "chain: internal path reconstruction failed", .{});
            t = edge.result;
        }
    }
    std.mem.reverse(TermId, path.items); // target-first → start-order

    // ADMIT: the search connected start to target, so a certificate demonstrably exists —
    // only emitting it is pruned.
    if (site.admit_mode) {
        site.producer_premise_refs = null;
        site.admit_ok = true;
        return null;
    }

    // PHASE 2 — emit the cert body. GLOBAL equations are cited up front (each once, in ref
    // order) as a `[by axiom|theorem head]` step under the label the search recorded; LOCAL
    // ones are the wrapper's restated hypotheses (their `body_label` = the `prem-…` step).
    var body_steps: std.ArrayList(ast.Step) = .empty;
    for (prepared) |p| if (!p.local) {
        try body_steps.append(site.ctx.arena, try b.claimStep(p.body_label, try b.termExpr(p.formula), .by, try site.internStr("cite"), &.{}, try common.headRef(site, p.head)));
    };
    // reflexivity `start = start`, then one rewrite per path edge (symmetry-flip a backward edge).
    const refl = try site.pool.add(.{ .eq = .{ .lhs = start, .rhs = start } });
    var cur_label = try site.freshNamed("chain");
    try body_steps.append(site.ctx.arena, try b.claimStep(cur_label, try b.termExpr(refl), .by, try site.internStr("reflexivity"), &.{}, &.{}));
    for (path.items) |next_term| {
        const edge = came_from.get(next_term).?;
        const eq = eqs[edge.eq_idx];
        // the equation to cite as the rewrite's rule: forward = as proved; backward = its flip.
        var eq_label = eq.body_label;
        if (!edge.forward) {
            const flipped = try site.pool.add(.{ .eq = .{ .lhs = eq.rhs, .rhs = eq.lhs } });
            eq_label = try site.freshNamed("chain");
            try body_steps.append(site.ctx.arena, try b.claimStep(eq_label, try b.termExpr(flipped), .by, try site.internStr("symmetry"), &.{}, try b.oneRef(eq.body_label)));
        }
        const new_goal = try site.pool.add(.{ .eq = .{ .lhs = start, .rhs = next_term } });
        const lbl = try site.freshNamed("chain");
        const refs = try site.ctx.arena.alloc(lexer.Token, 2);
        refs[0] = b.tok(eq_label); // the equation (kernel `rewrite` rewrites all occurrences)
        refs[1] = b.tok(cur_label); // the running `start = …` target
        try body_steps.append(site.ctx.arena, try b.claimStep(lbl, try b.termExpr(new_goal), .by, try site.internStr("rewrite"), &.{}, refs));
        cur_label = lbl;
    }

    // LOCAL equations are the schema's `->` antecedents (restated + discharged at the call
    // site), in ref order; collect their (cite, param-substituted formula) for the wrapper.
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (eqs) |eq| if (eq.local) {
        try local_cites.append(site.ctx.arena, .{ .local = .{ .hyp = eq.body_label } });
        try local_formulae.append(site.ctx.arena, eq.formula);
    };

    // wrap the cert in nested `assume <local-eq>` blocks (the `->` antecedents), each restating
    // its hypothesis under `body_label` and exporting `prem_i -> … -> (start = target)` out.
    const eq_prop = try site.pool.add(.{ .eq = .{ .lhs = start, .rhs = target } });
    const kept = try common.keptPremises(site, local_cites.items, local_formulae.items, body_steps.items);
    const kept_refs = try common.keptRefTokens(site, w, c.refs, local_cites.items, body_steps.items);
    const steps = try common.wrapSimplifyPremises(site, &b, local_cites.items, local_formulae.items, eq_prop, body_steps.items);

    // schema body proposition = `local-prem0 -> … -> (start = target)`; params already in place.
    const full_prop = try common.impliesChain(site, eq_prop, kept);
    const body_expr = try b.termExpr(full_prop);

    // params from the abstracted free fvars (value params of the fvars' sorts).
    const params = try site.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        pp.* = .{ .name = b.tok(name), .kind = .{ .value = b.sortTok(sort) } };
    }

    // deterministic hash-name from the full proposition (re-entry stable).
    const hash = Schema.termHash(site.ctx.interner, site.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(site.ctx.arena, "chain{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = kept_refs, // the cited premises, discharged at the call site
        .seen = b.seen.items,
        .fvar_binds = try common.fvarBinds(site, w, abs),
    };
}
