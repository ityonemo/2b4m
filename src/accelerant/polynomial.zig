//! The `polynomial` / `polynomial_quantified` accelerant: proves `s = t` when
//! both sides are equal as polynomials over a commutative semiring (add/mul with
//! 0/1). The default path resolves the ring lemmas (distribution, identities,
//! assoc/comm for both operators), canonicalizes each side to a sorted sum of
//! sorted monomials while recording a replayable rewrite trace, and emits a
//! kernel join. The accelerated `--fast` path decides equality by a bare
//! structural semiring normal form, TRUSTING that add/mul form a commutative
//! semiring without citing any theory lemma. Split out of the elaborate
//! monolith; the shared flatten/sort/plan/lift substrate stays as `pub` methods
//! on `Elaborator`.

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
const presburger_mod = @import("arithmetic/presburger.zig");
const common = @import("_common.zig");

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .eq) {
        if (goal_node == .quant and goal_node.quant.q == .forall) {
            return self.fail(loc, "polynomial proves equations; use polynomial_quantified for a 'forall …; s = t' goal", .{});
        }
        return self.fail(loc, "polynomial proves equations; the goal is '{s}'", .{try self.renderTerm(goal)});
    }
    const saved_theory = self.theory_file;
    defer self.theory_file = saved_theory;
    try self.enterTheory(c);
    // --fast: decide-only (accelerated verdict, no theorem). strict: wrap the
    // canonicalization certificate as a context-free synthetic theorem.
    if (!self.verify.certify_arithmetic) {
        return polynomialEquation(self, low, block_id, loc, goal);
    }
    var body: EqBody = .{ .loc = loc };
    return (try common.generate(self, low, block_id, loc, "polynomial", goal, &.{}, &body)).?;
}

/// `polynomial` peeling the forall prefix — mirrors ac_quantified.
pub fn justifyQuantified(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    const goal_node = self.pool.get(goal);
    if (goal_node != .quant or goal_node.quant.q != .forall) {
        if (goal_node == .eq) {
            return self.fail(loc, "polynomial_quantified expects a quantified goal; did you mean polynomial?", .{});
        }
        return self.fail(loc, "polynomial_quantified expects a 'forall …; s = t' goal, got '{s}'", .{try self.renderTerm(goal)});
    }
    const saved_theory = self.theory_file;
    defer self.theory_file = saved_theory;
    try self.enterTheory(c);
    const u = try self.peelUniversal(goal, "poly");
    if (self.pool.get(u.body) != .eq) {
        return self.fail(loc, "polynomial_quantified's body is not an equation: '{s}'", .{try self.renderTerm(u.body)});
    }
    if (!self.verify.certify_arithmetic) {
        const opened = try self.openUniversal(low, block_id, u);
        const body_just = try polynomialEquation(self, low, opened.innermost, loc, u.body);
        return self.closeUniversal(low, loc, u, opened.blocks, body_just);
    }
    var body: EqBody = .{ .loc = loc };
    return (try common.generate(self, low, block_id, loc, "polynomial", goal, &.{}, &body)).?;
}

/// The body-emit for polynomial's closure: prove the (fresh-eigenvar) equation
/// via the canonicalization certificate. A `∀…; s = t` body (from
/// polynomial_quantified) is peeled and closed here, like simplify's emitBody.
const EqBody = struct {
    loc: u32,
    pub fn emit(b: *EqBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!?kernel.Justification {
        if (self.pool.get(body_goal) == .quant and self.pool.get(body_goal).quant.q == .forall) {
            const u = try self.peelUniversal(body_goal, "poly");
            const opened = try self.openUniversal(low, block, u);
            const inner = try polynomialEquation(self, low, opened.innermost, b.loc, u.body);
            return try self.closeUniversal(low, b.loc, u, opened.blocks, inner);
        }
        return try polynomialEquation(self, low, block, b.loc, body_goal);
    }
};

/// The set of well-known rules `polynomial` needs, resolved as one array
/// with named index ranges. Distribution + identity/zero folding are the
/// terminating `normalize` rules; the per-operator triples drive the sorts.
const PolyRules = struct {
    rules: []const simplify_mod.Rule,
    /// distribute + fold rules run via normalize (indices [0, fold_end))
    fold_end: usize,
    mul_assoc: usize,
    mul_comm: usize,
    mul_swap: usize,
    add_assoc: usize,
    add_comm: usize,
    add_swap: usize,
    add_sym: term.SymId,
    mul_sym: term.SymId,
    neg_sym: ?term.SymId,
    zero_sym: ?term.SymId,
};

fn polyRules(self: *Elaborator, loc: u32) ElabError!?PolyRules {
    const add_sym = (try self.wellKnownSym("add")) orelse return null;
    const mul_sym = (try self.wellKnownSym("mul")) orelse return null;
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    // terminating expand/fold rules (distribution shrinks mul-over-add
    // nesting; the identity/zero folds shrink term size), run to fixpoint
    // by `normalize` before either sort.
    const fold_names = [_][]const u8{
        "mulAddDistribLeft", "mulAddDistribRight",
        "mulOneLeft",        "mulOneRight",
        "mulZeroLeft",       "mulZeroRight",
        "addZeroLeft",       "addZeroRight",
    };
    for (fold_names) |nm| {
        const r = (try self.wellKnownRule(nm, loc)) orelse
            return self.fail(loc, "polynomial: needs {s} in scope", .{nm});
        try rules.append(self.arena, r);
    }
    // OPTIONAL neg/sub folds: in a ring theory these push `neg` toward the leaves
    // (negAdd/negSucc/negPrev/negNeg/mulNegLeft/mulNegRight) and eliminate `sub`
    // (definitionOfSubtraction), all shrinking/orienting rewrites that run in the
    // same normalize-to-fixpoint pass. Absent in a pure-ℕ theory (peano has no
    // neg/sub) — skip a null one rather than failing, so polynomial(peano) stays
    // green. `neg(atom)` stays an opaque atom (the coefficient model is unsigned).
    // numeral-coefficient folding via EXPANSION: mulSuccLeft/mulSuccRight expand
    // mul(succ^n(base), x) into a sum of copies of x (each application strips one
    // succ, strictly reducing → terminating). So `mul(TWO, q)` and `add(q, q)`
    // both expand to the same `add(q, q)` — a numeral coefficient dissolves into
    // repeated addition, no bespoke coefficient-collection phase needed. Optional:
    // peano HAS these (they stay as before); a ring theory adds nothing new.
    const optional_fold_names = [_][]const u8{
        "definitionOfSubtraction",
        "negAdd",     "negZero",     "negSucc",     "negPrev", "negNeg",
        "mulNegLeft", "mulNegRight",
        "mulSuccLeft", "mulSuccRight",
    };
    for (optional_fold_names) |nm| {
        if (try self.wellKnownRule(nm, loc)) |r| try rules.append(self.arena, r);
    }
    const fold_end = rules.items.len;
    // additive-inverse cancellation rules (x + neg(x) = 0), resolved by name by
    // cancelInverses; append them (past fold_end so they DON'T run in the
    // distribute/fold normalize) only in a ring theory — cancelInverses itself
    // self-guards when neg/zero are absent, so their absence is harmless.
    if (try self.wellKnownRule("addNegRight", loc)) |r| try rules.append(self.arena, r);
    if (try self.wellKnownRule("addNegLeft", loc)) |r| try rules.append(self.arena, r);
    // the two operator triples (assoc/comm/swap), appended after the folds.
    const triples = [_]struct { assoc: []const u8, comm: []const u8, swap: []const u8 }{
        .{ .assoc = "mulIsAssociative", .comm = "mulIsCommutative", .swap = "mulLeftSwap" },
        .{ .assoc = "addIsAssociative", .comm = "addIsCommutative", .swap = "addLeftSwap" },
    };
    var idx: [6]usize = undefined;
    var w: usize = 0;
    for (triples) |tr| {
        inline for (.{ tr.assoc, tr.comm, tr.swap }) |nm| {
            idx[w] = rules.items.len;
            const r = (try self.wellKnownRule(nm, loc)) orelse
                return self.fail(loc, "polynomial: needs {s} in scope", .{nm});
            try rules.append(self.arena, r);
            w += 1;
        }
    }
    return .{
        .rules = rules.items,
        .fold_end = fold_end,
        .mul_assoc = idx[0], .mul_comm = idx[1], .mul_swap = idx[2],
        .add_assoc = idx[3], .add_comm = idx[4], .add_swap = idx[5],
        .add_sym = add_sym, .mul_sym = mul_sym,
        .neg_sym = try self.wellKnownSym("neg"),
        .zero_sym = try self.wellKnownSym("ZERO"),
    };
}

/// Canonicalize one side to a sorted-sum-of-sorted-monomials normal form,
/// accumulating the full replayable trace against `pr.rules`.
fn polyCanon(self: *Elaborator, pr: PolyRules, x: TermId) ElabError!?simplify_mod.Result {
    // 1) distribute + fold to a flat sum of monomials (terminating). Its
    //    trace is already whole-term (normalize over `x`).
    const fold_rules = pr.rules[0..pr.fold_end];
    const dist = simplify_mod.normalize(self.arena, self.pool, self.env, fold_rules, x, 4000) catch |e| switch (e) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
    try trace.appendSlice(self.arena, dist.trace);

    const add_symbols: presburger_mod.Symbols = .{ .add = pr.add_sym };
    const mul_symbols: presburger_mod.Symbols = .{ .add = pr.mul_sym };

    // 2) RIGHT-NEST the outer sum first (add-associativity only,
    //    terminating). This makes the running term a right-nested comb, so
    //    the `buildComb` contexts used to lift the per-monomial traces
    //    below match the real term shape exactly.
    const add_assoc_only = pr.rules[pr.add_assoc .. pr.add_assoc + 1];
    const rn = simplify_mod.normalize(self.arena, self.pool, self.env, add_assoc_only, dist.nf, 4000) catch |e| switch (e) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    // rebase this single-rule trace's rule_idx to the full-array index.
    for (rn.trace) |rw| {
        var r = rw;
        r.rule_idx = rw.rule_idx + pr.add_assoc;
        try trace.append(self.arena, r);
    }

    // 3) sort each monomial's factors (mul-acPlan), lifting each sub-trace
    //    into the (right-nested) whole-sum context so the chain stays
    //    whole-term.
    var monos: std.ArrayList(TermId) = .empty;
    try self.flattenSum(pr.add_sym, rn.nf, &monos);
    var sorted_monos: std.ArrayList(TermId) = .empty;
    for (monos.items, 0..) |m, i| {
        const mp = (try self.acPlan(mul_symbols, pr.rules, pr.mul_assoc, pr.mul_comm, pr.mul_swap, pr.mul_sym, m)) orelse return null;
        if (mp.trace.len > 0) {
            // context: [sorted_0..sorted_{i-1}] ++ hole ++ [mono_{i+1}..]
            const lifted = try self.liftMonoTrace(add_symbols, sorted_monos.items, monos.items[i + 1 ..], mp.trace, &trace);
            if (!lifted) return null;
        }
        try sorted_monos.append(self.arena, mp.sorted);
    }
    const mono_sum = (try self.buildComb(add_symbols, sorted_monos.items)) orelse return null;

    // 4) bubble-sort the sum of monomials. The sum is already right-nested,
    //    so run only the sort phase (sortTrace), not acPlan's re-nest.
    var leaves: std.ArrayList(TermId) = .empty;
    try self.flattenSum(pr.add_sym, mono_sum, &leaves);
    var sorted = (try self.sortTrace(add_symbols, pr.rules, pr.add_comm, pr.add_swap, .{ .offset = 0, .leaves = leaves.items }, &trace)) orelse return null;

    // 5) cancel additive-inverse monomials (m + neg(m) → 0) in the sorted sum,
    //    emitting addNegRight/addNegLeft + zero-drop rewrites into the trace
    //    (kernel-checked). Reuses the linear engine's cancelInverses on the sum
    //    (monomials are its leaves). `one` is deliberately LEFT NULL: unlike the
    //    arithmetic engine, polynomial does NOT reduce ONE to succ(ZERO), so a
    //    bare `ONE` summand must ride as an opaque LEAF (isOpaqueAtom excludes
    //    symbols.one) — passing one would make parseTower reject a sum containing
    //    ONE and skip the cancellation (e.g. `1 + (t + neg(t))`). succ/prev stay
    //    set so genuine numeral towers still fold. Self-guards when neg/zero absent.
    if (pr.neg_sym != null and pr.zero_sym != null) {
        const cancel_symbols: presburger_mod.Symbols = .{
            .add = pr.add_sym,
            .mul = pr.mul_sym,
            .neg = pr.neg_sym,
            .zero = pr.zero_sym,
            .succ = try self.wellKnownSym("succ"),
            .prev = try self.wellKnownSym("prev"),
        };
        sorted = (try self.cancelInverses(cancel_symbols, pr.rules, pr.add_comm, pr.add_swap, 0, sorted, &trace, 0)) orelse return null;
    }
    return .{ .nf = sorted, .trace = trace.items };
}

fn polynomialEquation(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, goal: TermId) ElabError!kernel.Justification {
    const goal_node = self.pool.get(goal);
    const s0 = goal_node.eq.lhs;
    const t0 = goal_node.eq.rhs;

    // --fast: the accelerated polynomial path. Decide equality by comparing
    // the bare syntactic semiring normal forms — NO theory lemmas consulted,
    // so it works on a theory too thin to elaborate, but it TRUSTS that
    // add/mul are a commutative semiring (the theory's own laws are never
    // checked). That presumption about uncontrolled symbols is exactly why
    // it is accelerated, not kernel-checked. The default path below discharges
    // the same presumption against the kernel.
    if (!self.verify.certify_arithmetic) {
        const add_sym = (try self.wellKnownSym("add")) orelse
            return self.fail(loc, "polynomial: arithmetic vocabulary (add, mul) not in scope", .{});
        const mul_sym = (try self.wellKnownSym("mul")) orelse
            return self.fail(loc, "polynomial: arithmetic vocabulary (add, mul) not in scope", .{});
        const zero_sym = try self.wellKnownSym("ZERO");
        const one_sym = try self.wellKnownSym("ONE");
        const neg_sym = try self.wellKnownSym("neg");
        const sub_sym = try self.wellKnownSym("sub");
        const succ_sym = try self.wellKnownSym("succ");
        const ns = PolyNorm{ .add_sym = add_sym, .mul_sym = mul_sym, .zero_sym = zero_sym, .one_sym = one_sym, .neg_sym = neg_sym, .sub_sym = sub_sym, .succ_sym = succ_sym };
        const ns_s = try polyNormForm(self, ns, s0);
        const ns_t = try polyNormForm(self, ns, t0);
        if (!self.pool.alphaEq(ns_s, ns_t)) {
            return self.fail(loc, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
                try self.renderTerm(ns_s), try self.renderTerm(ns_t),
            });
        }
        const name = self.interner.internString("polynomial") catch return error.OutOfMemory;
        try self.recordAccelerated(name, loc);
        return .{ .accelerated = name };
    }

    // default: the kernel-checked certificate — resolve the ring lemmas,
    // canonicalize both sides recording a replayable trace, and emit the
    // kernel join.
    const pr = (try polyRules(self, loc)) orelse
        return self.fail(loc, "polynomial: arithmetic vocabulary (add, mul) not in scope", .{});

    const rs = (try polyCanon(self, pr, s0)) orelse
        return self.fail(loc, "polynomial: could not canonicalize '{s}'", .{try self.renderTerm(s0)});
    const rt = (try polyCanon(self, pr, t0)) orelse
        return self.fail(loc, "polynomial: could not canonicalize '{s}'", .{try self.renderTerm(t0)});
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        return self.fail(loc, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
            try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
        });
    }
    return self.emitJoin(low, block_id, loc, pr.rules, s0, t0, rs, rt);
}

// -- the accelerated polynomial path's lemma-free canonical form --------
//
// A bare structural semiring normalizer: it flattens/sorts add and mul
// trees ASSUMING commutativity, associativity, distributivity, and 0/1
// identities hold — without resolving or citing any theory lemma. Used only
// by the --fast accelerated path (the default path elaborates via resolved
// lemmas + kernel recheck). Deterministic, so its output is a true canonical
// form; two terms are semiring-equal iff their normal forms are alphaEq.

const PolyNorm = struct {
    add_sym: term.SymId,
    mul_sym: term.SymId,
    zero_sym: ?term.SymId,
    one_sym: ?term.SymId,
    neg_sym: ?term.SymId = null,
    sub_sym: ?term.SymId = null,
    succ_sym: ?term.SymId = null,
};

/// Structural mirror of the strict path's mulSuccLeft/mulSuccRight folds: expand
/// a numeral coefficient `mul(succ(a), b) → add(mul(a,b), b)` (and the right
/// mirror) so `mul(TWO, q)` becomes `add(q, q)`, matching the strict normal form.
/// Bottom-up to fixpoint; each rewrite strips one succ so it terminates.
fn expandSucc(self: *Elaborator, ns: PolyNorm, x: TermId) ElabError!TermId {
    if (ns.succ_sym == null) return x;
    const node = self.pool.get(x);
    if (node != .app) return x;
    if (Elaborator.symIs(node.app.sym, ns.mul_sym) and node.app.args_len == 2) {
        const a = try expandSucc(self, ns, self.pool.args(node.app)[0]);
        const b = try expandSucc(self, ns, self.pool.args(node.app)[1]);
        const an = self.pool.get(a);
        // mul(succ(a'), b) → add(mul(a', b), b)
        if (an == .app and Elaborator.symIs(an.app.sym, ns.succ_sym) and an.app.args_len == 1) {
            const a_inner = self.pool.args(an.app)[0];
            const prod = try expandSucc(self, ns, try self.pool.addApp(.app, ns.mul_sym, &.{ a_inner, b }));
            return try self.pool.addApp(.app, ns.add_sym, &.{ prod, b });
        }
        const bn = self.pool.get(b);
        // mul(a, succ(b')) → add(mul(a, b'), a)
        if (bn == .app and Elaborator.symIs(bn.app.sym, ns.succ_sym) and bn.app.args_len == 1) {
            const b_inner = self.pool.args(bn.app)[0];
            const prod = try expandSucc(self, ns, try self.pool.addApp(.app, ns.mul_sym, &.{ a, b_inner }));
            return try self.pool.addApp(.app, ns.add_sym, &.{ prod, a });
        }
        return try self.pool.addApp(.app, ns.mul_sym, &.{ a, b });
    }
    if (node.app.args_len == 0) return x;
    const args = self.pool.args(node.app);
    var new_args = try self.arena.alloc(TermId, args.len);
    for (args, 0..) |arg, i| new_args[i] = try expandSucc(self, ns, arg);
    return try self.pool.addApp(.app, node.app.sym, new_args);
}

/// Structural mirror of the strict path's neg/sub fold rules, applied WITHOUT
/// citing a lemma (the --fast path decides, it doesn't certify). Rewrites
/// bottom-up to push `neg` toward the leaves and eliminate `sub`, so the mul/add
/// structure underneath is exposed identically to the certified normal form:
///   sub(a,b) → add(a, neg(b));  neg(add u v) → add(neg u, neg v);
///   neg(neg x) → x;  neg(mul a b) → mul(a, neg b);  neg(ZERO) → ZERO.
/// A `neg` wrapping a bare atom is left in place (an opaque neg-atom).
fn pushNeg(self: *Elaborator, ns: PolyNorm, x: TermId) ElabError!TermId {
    const node = self.pool.get(x);
    if (node != .app) return x;
    const sym = node.app.sym;
    // sub(a,b) → add(a, neg(b)), then recurse.
    if (ns.sub_sym != null and Elaborator.symIs(sym, ns.sub_sym) and node.app.args_len == 2) {
        const args = self.pool.args(node.app);
        const a = args[0];
        const b = args[1];
        if (ns.neg_sym) |neg| {
            const nb = try self.pool.addApp(.app, neg, &.{b});
            const rebuilt = try self.pool.addApp(.app, ns.add_sym, &.{ a, nb });
            return pushNeg(self, ns, rebuilt);
        }
    }
    // neg(inner): distribute over the inner structure.
    if (ns.neg_sym != null and Elaborator.symIs(sym, ns.neg_sym) and node.app.args_len == 1) {
        const inner = try pushNeg(self, ns, self.pool.args(node.app)[0]);
        const in = self.pool.get(inner);
        if (in == .app) {
            // neg(add(u,v)) → add(neg u, neg v)
            if (Elaborator.symIs(in.app.sym, ns.add_sym) and in.app.args_len == 2) {
                const ia = self.pool.args(in.app);
                const u = ia[0];
                const v = ia[1];
                const nu = try pushNeg(self, ns, try self.pool.addApp(.app, ns.neg_sym.?, &.{u}));
                const nv = try pushNeg(self, ns, try self.pool.addApp(.app, ns.neg_sym.?, &.{v}));
                return try self.pool.addApp(.app, ns.add_sym, &.{ nu, nv });
            }
            // neg(neg(x)) → x
            if (Elaborator.symIs(in.app.sym, ns.neg_sym) and in.app.args_len == 1) {
                return self.pool.args(in.app)[0];
            }
            // neg(ZERO) → ZERO
            if (ns.zero_sym != null and isSym(self, inner, ns.zero_sym.?)) return inner;
        }
        // neg over a product or a bare atom: keep `neg` OUTSIDE (matching the
        // strict path's mulNegLeft/mulNegRight normal form `neg(mul(...))`); the
        // monomial machinery sorts the factors under the neg and pulls the sign
        // to a top-level wrapper. Only add/neg/zero are pushed through above.
        return try self.pool.addApp(.app, ns.neg_sym.?, &.{inner});
    }
    // otherwise recurse into children, rebuilding.
    if (node.app.args_len == 0) return x;
    const args = self.pool.args(node.app);
    var new_args = try self.arena.alloc(TermId, args.len);
    for (args, 0..) |arg, i| new_args[i] = try pushNeg(self, ns, arg);
    return try self.pool.addApp(.app, sym, new_args);
}

/// Canonicalize `x` to a sorted sum of sorted monomials. Recursion:
/// normalize children, distribute mul over add, sort, fold 0/1.
fn polyNormForm(self: *Elaborator, ns: PolyNorm, x0: TermId) ElabError!TermId {
    // push neg to the leaves / eliminate sub first, so distribution sees the
    // real mul/add structure (mirrors the strict fold set).
    const x = try expandSucc(self, ns, try pushNeg(self, ns, x0));
    // gather the sum's monomials (each a normalized product of atoms),
    // sort by termOrder, drop ZERO terms, rebuild right-nested.
    var raw: std.ArrayList(TermId) = .empty;
    try polyMonomials(self, ns, x, &raw);
    // cancel additive inverses: a monomial `m` and its negation `neg(m)` sum to
    // ZERO and drop out (mirrors the strict cancelInverses phase). A consumed
    // slot is set to null so each partner is used at most once.
    var slots = try self.arena.alloc(?TermId, raw.items.len);
    for (raw.items, 0..) |m, i| slots[i] = m;
    if (ns.neg_sym != null) {
        for (slots, 0..) |si, i| {
            const mi = si orelse continue;
            const neg_mi = try negateMonomial(self, ns, mi);
            for (slots[i + 1 ..], i + 1..) |sj, j| {
                const mj = sj orelse continue;
                if (self.pool.alphaEq(mj, neg_mi)) {
                    slots[i] = null;
                    slots[j] = null;
                    break;
                }
            }
        }
    }
    // drop additive ZEROs and canceled slots
    var kept: std.ArrayList(TermId) = .empty;
    for (slots) |s| {
        const m = s orelse continue;
        if (ns.zero_sym != null and isSym(self, m, ns.zero_sym.?)) continue;
        try kept.append(self.arena, m);
    }
    if (kept.items.len == 0) {
        // empty sum = ZERO (or x itself if no ZERO symbol known)
        if (ns.zero_sym) |z| return try self.pool.addApp(.app, z, &.{});
        return x;
    }
    self.sortTerms(kept.items);
    return try self.buildRightNested(ns.add_sym, kept.items);
}

/// Collect the normalized monomials of `x` (the summands after full
/// distribution), appending to `out`.
fn polyMonomials(self: *Elaborator, ns: PolyNorm, x: TermId, out: *std.ArrayList(TermId)) ElabError!void {
    const node = self.pool.get(x);
    if (node == .app and Elaborator.symIs(node.app.sym, ns.add_sym) and node.app.args_len == 2) {
        const args = self.pool.args(node.app);
        const a0 = args[0];
        const a1 = args[1];
        try polyMonomials(self, ns, a0, out);
        try polyMonomials(self, ns, a1, out);
        return;
    }
    if (node == .app and Elaborator.symIs(node.app.sym, ns.mul_sym) and node.app.args_len == 2) {
        // distribute: (sum of A) * (sum of B) = sum over a in A, b in B of a*b.
        // COPY the arg ids out first: pool.args aliases pool.extra, and the
        // recursion below allocates product terms (polyMonomialProduct ->
        // addApp), which reallocates extra and would dangle the slice.
        const margs = self.pool.args(node.app);
        const m0 = margs[0];
        const m1 = margs[1];
        var left: std.ArrayList(TermId) = .empty;
        var right: std.ArrayList(TermId) = .empty;
        try polyMonomials(self, ns, m0, &left);
        try polyMonomials(self, ns, m1, &right);
        for (left.items) |a| {
            for (right.items) |b| {
                try out.append(self.arena, try polyMonomialProduct(self, ns, a, b));
            }
        }
        return;
    }
    // neg(inner): collect inner's monomials and negate each canonically. After
    // pushNeg, a `neg` wraps only a product-or-atom (never an add), so the inner
    // set is a single sorted monomial; wrapping it in `neg` around the SORTED core
    // matches the strict path's `neg(mul(...))` normal form.
    if (node == .app and ns.neg_sym != null and Elaborator.symIs(node.app.sym, ns.neg_sym) and node.app.args_len == 1) {
        const inner = self.pool.args(node.app)[0];
        var inner_monos: std.ArrayList(TermId) = .empty;
        try polyMonomials(self, ns, inner, &inner_monos);
        for (inner_monos.items) |m| try out.append(self.arena, try negateMonomial(self, ns, m));
        return;
    }
    // an atom (variable, constant, or opaque application): a monomial with
    // one factor. Fold multiplicative identity later; here it stands alone.
    try out.append(self.arena, x);
}

/// Wrap a sorted monomial `m` in `neg`, canonically: neg(neg(x)) → x, and
/// neg(ZERO) → ZERO. Otherwise `neg(m)` (neg outside the sorted core), matching
/// the strict path's mulNegLeft/mulNegRight normal form.
fn negateMonomial(self: *Elaborator, ns: PolyNorm, m: TermId) ElabError!TermId {
    if (ns.neg_sym == null) return m;
    const node = self.pool.get(m);
    if (node == .app and Elaborator.symIs(node.app.sym, ns.neg_sym) and node.app.args_len == 1) {
        return self.pool.args(node.app)[0]; // neg(neg(x)) → x
    }
    if (ns.zero_sym != null and isSym(self, m, ns.zero_sym.?)) return m; // neg(0) → 0
    return try self.pool.addApp(.app, ns.neg_sym.?, &.{m});
}

/// Multiply two already-normalized monomials: flatten both into factor
/// lists, drop ONE factors, ZERO-annihilate, sort, rebuild right-nested.
fn polyMonomialProduct(self: *Elaborator, ns: PolyNorm, a: TermId, b: TermId) ElabError!TermId {
    var factors: std.ArrayList(TermId) = .empty;
    var negative = false;
    negative = (try polyFactors(self, ns, a, &factors)) != negative;
    negative = (try polyFactors(self, ns, b, &factors)) != negative;
    var kept: std.ArrayList(TermId) = .empty;
    for (factors.items) |f| {
        if (ns.zero_sym != null and isSym(self, f, ns.zero_sym.?)) {
            // a ZERO factor annihilates the whole monomial
            return try self.pool.addApp(.app, ns.zero_sym.?, &.{});
        }
        if (ns.one_sym != null and isSym(self, f, ns.one_sym.?)) continue;
        try kept.append(self.arena, f);
    }
    var core: TermId = undefined;
    if (kept.items.len == 0) {
        core = if (ns.one_sym) |o| try self.pool.addApp(.app, o, &.{}) else a;
    } else {
        self.sortTerms(kept.items);
        core = try self.buildRightNested(ns.mul_sym, kept.items);
    }
    // lift the accumulated sign to a single top-level `neg` (matching strict's
    // mulNegLeft/mulNegRight normal form `neg(mul(sorted core))`).
    return if (negative) try negateMonomial(self, ns, core) else core;
}

/// Flatten a mul-tree into its factor list (atoms), peeling `neg` wrappers and
/// returning the accumulated SIGN (true = an odd number of negs were stripped).
/// A `neg(x)` factor contributes its sign and flattens `x`'s factors, so
/// `mul(a, neg(c))` and `neg(mul(a, c))` reduce to the same {a, c} with sign −.
fn polyFactors(self: *Elaborator, ns: PolyNorm, x: TermId, out: *std.ArrayList(TermId)) ElabError!bool {
    const node = self.pool.get(x);
    if (node == .app and Elaborator.symIs(node.app.sym, ns.mul_sym) and node.app.args_len == 2) {
        // copy the arg ids before recursing (pool.args aliases pool.extra,
        // which downstream allocations may grow; see polyMonomials).
        const fargs = self.pool.args(node.app);
        const f0 = fargs[0];
        const f1 = fargs[1];
        const s0 = try polyFactors(self, ns, f0, out);
        const s1 = try polyFactors(self, ns, f1, out);
        return s0 != s1;
    }
    if (node == .app and ns.neg_sym != null and Elaborator.symIs(node.app.sym, ns.neg_sym) and node.app.args_len == 1) {
        const inner_sign = try polyFactors(self, ns, self.pool.args(node.app)[0], out);
        return !inner_sign; // this neg flips the sign
    }
    try out.append(self.arena, x);
    return false;
}

fn isSym(self: *Elaborator, t: TermId, sym: term.SymId) bool {
    const node = self.pool.get(t);
    return node == .app and node.app.sym == sym and node.app.args_len == 0;
}
