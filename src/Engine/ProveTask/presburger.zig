//! TRUSTED ACCELERATED TACTIC: linear (Presburger) arithmetic over Nat (surface
//! rule `arithmetic`; registry entry in ACCELERATION.md).
//!
//! Trust surface: a `.valid` verdict becomes an `.accelerated` kernel step the
//! kernel accepts without a derivation — a bug here can admit a false
//! theorem. Every use is disclosed: the accelerated-tactic name marks the
//! enclosing theorem accelerated (transitively, through citations), the summary
//! line reports it, and `--pure` rejects it. Certificate replay (milestone C2)
//! will shrink this trust surface without changing the surface rule.
//!
//! Engine: compiles premises AND not(goal) into a formula over linear
//! integer atoms — Nat is the nonnegative integers, so every variable
//! carries an implicit >= 0 constraint — then eliminates quantifiers
//! innermost-first with Cooper's algorithm (atoms L >= 0 and
//! modulus | L; equalities and negations are compiled away up front).
//! The ground residue decides satisfiability: SAT means the goal does not
//! follow, and a bounded search recovers small countermodel values for the
//! free variables. Arithmetic is checked i128; blowup hits an explicit work
//! budget. Both failure modes are honest located errors, never verdicts.

const std = @import("std");
const Allocator = std.mem.Allocator;
const StrId = @import("../../InternPool.zig").StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const SymId = term.SymId;
const Pool = term.Pool;

/// The arithmetic vocabulary, resolved by well-known name in the use site's
/// scope. Absent names shrink the fragment; a term outside it is a located
/// error naming the term.
pub const Symbols = struct {
    /// The arithmetic sort's anchor (used only to shape countermodels / bind
    /// binders — NOT a soundness filter: the engine is sort-blind and treats
    /// any non-well-known term as a linear variable ranging over ℤ).
    nat: ?SortId = null,
    zero: ?SymId = null,
    one: ?SymId = null,
    succ: ?SymId = null,
    /// predecessor: prev(x) = x - 1 (ℤ theories; absent for ℕ).
    prev: ?SymId = null,
    add: ?SymId = null,
    mul: ?SymId = null,
    /// unary negation neg(x) = -x and total subtraction sub(a,b) = a - b
    /// (ℤ theories; absent for ℕ, whose sub is truncated monus — NOT linear).
    neg: ?SymId = null,
    sub: ?SymId = null,
    less_than: ?SymId = null,
    /// a well-known nonnegativity predicate nonneg(x) meaning x >= 0. Its
    /// PRESENCE is a theory's request to constrain its variables nonneg: the
    /// engine reads nonneg(x) hypotheses as x >= 0, and the elaborator injects
    /// nonneg(x) per bound variable when this is set. Absent → pure ℤ (no
    /// nonnegativity assumed anywhere).
    nonneg: ?SymId = null,
};

pub const Verdict = union(enum) {
    /// premises AND not(goal) is unsatisfiable: the goal follows
    valid,
    /// concrete falsifying values for the free (fixed) variables, in first
    /// appearance order; empty when the statement is closed and simply false
    countermodel: []const Assignment,
    /// not a consequence, but the bounded search found no small witness
    no_witness,
    /// the named term is outside linear arithmetic
    out_of_fragment: TermId,
    /// quantifier elimination blew past the work budget
    too_large,
    /// an i128 coefficient overflowed
    overflow,
};

/// A falsifying value for a free variable. `term` is set when the "variable" is
/// an abstracted opaque subterm (mod(a,b), f(x)) rather than a named variable —
/// the elaborator uses it to report the subterm as outside the linear fragment
/// instead of surfacing a misleading atom-valued countermodel.
pub const Assignment = struct { name: StrId, value: i128, term: ?TermId = null };

pub const SatResult = union(enum) {
    unsat,
    /// small values for the free variables (empty when there are none)
    sat: []const Assignment,
    /// satisfiable, but the bounded search found no small witness
    sat_no_witness,
    out_of_fragment: TermId,
    too_large,
    overflow,
};

// --- Cooper-replay trace (certificate generation, src/elaborate.zig) ---
//
// The decision procedure above discards the elimination disjunction it builds.
// `trace` re-runs the SAME Cooper elimination on a single `exists y; body`
// goal but RECORDS what it did into `Replay`: the certifier in elaborate.zig
// reads this to emit kernel steps (the ⟸ witness assembly and the ⟹
// induction). Plain data — no TermId, no kernel — so the trusted-engine
// surface stays put and the certifier owns all term/kernel work.

/// A linear form echoed out to the certifier, coefficients indexed by the
/// same free-variable order as `Replay.free_names`.
pub const LinearDump = struct { coeffs: []const i128, konst: i128 };

/// One disjunct of Cooper's `exists y. F <=> OR_j (F_-inf(j) OR OR_b F(b+j))`.
pub const Disjunct = union(enum) {
    /// the minus-infinity residue at offset j (j in 1..D)
    minus_inf: struct { j: i128 },
    /// the boundary probe: witness y := boundaries[b_index] + j
    boundary: struct { b_index: usize, j: i128 },
};

/// The recorded elimination of one `exists y` (Cooper). `delta` is the
/// coefficient LCM (y = delta*x), `period` the divisibility LCM D, and the
/// disjuncts/boundaries reconstruct each witness in the certifier's term pool.
pub const Replay = struct {
    delta: i128,
    period: i128,
    boundaries: []const LinearDump,
    disjuncts: []const Disjunct,
    /// free-variable names (Ctx.free_vars order — first-appearance in the body)
    free_names: []const StrId,
    /// the coefficient index (variable id) of each free var, parallel to
    /// free_names; a boundary's `coeffs[free_ids[p]]` is free var p's weight.
    free_ids: []const u32,
};

pub const TraceResult = union(enum) {
    /// goal was `exists y: Nat; body` over Nat, valid, and traced
    replay: Replay,
    /// not the single-existential shape, or out of the linear fragment
    not_applicable,
};

/// Decide whether `goal` follows from `premises` in Presburger arithmetic.
pub fn decide(arena: Allocator, pool: *Pool, symbols: Symbols, premises: []const TermId, goal: TermId) Allocator.Error!Verdict {
    var ctx: Ctx = .{ .arena = arena, .pool = pool, .symbols = symbols };
    const result = ctx.runSat(premises, goal) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Fail => return ctx.reason.?,
    };
    return switch (result) {
        .unsat => .valid,
        .sat => |values| .{ .countermodel = values },
        .sat_no_witness => .no_witness,
        // runSat reports failures via ctx.reason
        .out_of_fragment, .too_large, .overflow => unreachable,
    };
}

/// Record the Cooper elimination of a single `exists y: Nat; body` goal so the
/// certifier can replay it as kernel steps. Returns `.not_applicable`
/// (never an error verdict) when the goal is not that shape or leaves the
/// linear fragment — the certifier link simply declines and the chain moves on.
pub fn trace(arena: Allocator, pool: *Pool, symbols: Symbols, premises: []const TermId, goal: TermId) Allocator.Error!TraceResult {
    // layer 1 targets premise-free existentials (evenOrOdd has none); a premise
    // set is out of this scope for now.
    if (premises.len != 0) return .not_applicable;
    if (symbols.nat == null) return .not_applicable;

    // the goal must be `exists y: Nat; body`
    const node = pool.get(goal);
    if (node != .quant or node.quant.q != .exists or node.quant.sort != symbols.nat.?) {
        return .not_applicable;
    }

    var ctx: Ctx = .{ .arena = arena, .pool = pool, .symbols = symbols };
    return ctx.runTrace(node.quant) catch |err| switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        // any compilation failure (out of fragment, too_large, overflow) means
        // this link can't certify: decline, don't surface an engine error.
        error.Fail => .not_applicable,
    };
}

/// Is the conjunction of `conjuncts` satisfiable? (The theory side of the
/// SMT combination in src/smt.zig.)
pub fn satisfiable(arena: Allocator, pool: *Pool, symbols: Symbols, conjuncts: []const TermId) Allocator.Error!SatResult {
    var ctx: Ctx = .{ .arena = arena, .pool = pool, .symbols = symbols };
    return ctx.runSat(conjuncts, null) catch |err| switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.Fail => switch (ctx.reason.?) {
            .out_of_fragment => |t| .{ .out_of_fragment = t },
            .too_large => .too_large,
            .overflow => .overflow,
            else => unreachable,
        },
    };
}

/// Is `t` wholly inside the linear fragment? (Classifies atoms for the SMT
/// skeleton. Probing opens quantifier bodies into the pool; the leftover
/// nodes are harmless.)
pub fn inFragment(arena: Allocator, pool: *Pool, symbols: Symbols, t: TermId) Allocator.Error!bool {
    return (try outOfFragment(arena, pool, symbols, t)) == null;
}

/// The first out-of-fragment subterm of `t` (a nonlinear product, a foreign
/// function/predicate), or null when `t` is wholly linear. Used to turn a
/// misleading "false at <opaque> := false" countermodel into an honest
/// "outside linear arithmetic" diagnostic.
pub fn outOfFragment(arena: Allocator, pool: *Pool, symbols: Symbols, t: TermId) Allocator.Error!?TermId {
    var ctx: Ctx = .{ .arena = arena, .pool = pool, .symbols = symbols };
    var bound: usize = 0;
    ctx.countVars(t, &bound);
    ctx.width = bound;
    _ = ctx.formula(t, false) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Fail => return switch (ctx.reason.?) {
            .out_of_fragment => |offending| offending,
            // any other failure (too_large/overflow) is not a fragment issue
            else => null,
        },
    };
    return null;
}

const Error = error{ Fail, OutOfMemory };

const Linear = struct {
    coeffs: []i128, // indexed by variable id; length = the context's width
    konst: i128,
};

const Formula = union(enum) {
    tru,
    fls,
    /// linear >= 0
    ge: Linear,
    /// modulus divides linear (modulus > 0)
    div: Div,
    ndiv: Div,
    conj: Pair,
    disj: Pair,
    quant: struct { q: term.Quantifier, v: u32, body: *const Formula },

    const Pair = struct { lhs: *const Formula, rhs: *const Formula };
    const Div = struct { modulus: i128, linear: Linear };
};

const work_budget = 200_000;
const witness_bound = 64;
const witness_combinations = 200_000;

const Ctx = struct {
    arena: Allocator,
    pool: *Pool,
    symbols: Symbols,
    reason: ?Verdict = null,
    /// variable-vector width: fixed after the pre-scan
    width: usize = 0,
    next_var: u32 = 0,
    /// in-scope names (free variables and opened quantifier binders)
    vars: std.AutoHashMapUnmanaged(StrId, u32) = .empty,
    /// free variables in first appearance order (their ids index `vars`). `term`
    /// is set for an abstracted opaque atom (its source subterm), null for an
    /// ordinary named variable. Opaque atoms are matched STRUCTURALLY (the pool
    /// does not hash-cons, so two syntactically-equal subterms have distinct
    /// TermIds) — see abstractAtom.
    free_vars: std.ArrayList(struct { name: StrId, id: u32, term: ?TermId = null }) = .empty,
    /// names of quantifier binders currently open (opened by formula/runTrace).
    /// A subterm mentioning one of these is a function of an eliminated variable
    /// and must NOT be abstracted as an independent atom — that would be unsound.
    elim_names: std.AutoHashMapUnmanaged(StrId, void) = .empty,
    budget: usize = work_budget,

    fn fail(self: *Ctx, reason: Verdict) Error {
        if (self.reason == null) self.reason = reason;
        return error.Fail;
    }

    /// Satisfiability of `pos` AND (when present) NOT `neg_goal`.
    fn runSat(self: *Ctx, pos: []const TermId, neg_goal: ?TermId) Error!SatResult {
        // pre-scan: an upper bound on the variable count fixes vector width
        var bound: usize = 0;
        for (pos) |p| self.countVars(p, &bound);
        if (neg_goal) |g| self.countVars(g, &bound);
        self.width = bound;

        var f: *const Formula = if (neg_goal) |g| try self.formula(g, true) else try self.node(.tru);
        for (pos) |p| {
            f = try self.node(.{ .conj = .{ .lhs = try self.formula(p, false), .rhs = f } });
        }

        // decide by existentially closing the free variables (a witness is
        // an assignment of the fixed-but-arbitrary variables). Pure ℤ: no
        // nonnegativity guard — any x≥0 the theory needs is already a compiled
        // conjunct (from an injected nonneg(x) hypothesis).
        var closed = f;
        for (self.free_vars.items) |fv| {
            closed = try self.node(.{ .quant = .{
                .q = .exists,
                .v = fv.id,
                .body = closed,
            } });
        }
        const ground = try self.eliminate(closed);
        if (!evalGround(ground)) return .unsat;

        // Not valid. On the DECIDE path (a goal is present): if any opaque
        // subterm was abstracted, the goal genuinely needs reasoning beyond
        // linear arithmetic (an atom-valued countermodel would be misleading —
        // those atoms are not independently realizable), so report the first
        // abstracted subterm as out of fragment. This also keeps the
        // reified-schema-param diagnostic firing. On the SATISFIABILITY path
        // (neg_goal == null, the SMT theory check), opaque atoms are genuinely
        // satisfiable — assign them freely — so do NOT bail here.
        if (neg_goal != null) {
            for (self.free_vars.items) |fv| {
                if (fv.term) |t| return self.fail(.{ .out_of_fragment = t });
            }
        }

        // SAT: search small values of the free variables against the
        // inner-quantifier-free formula for a copy-pasteable witness
        const qf = try self.eliminate(f);
        const values = try self.arena.alloc(i128, self.width);
        @memset(values, 0);
        if (self.witness(qf, 0, values)) {
            const out = try self.arena.alloc(Assignment, self.free_vars.items.len);
            for (self.free_vars.items, out) |fv, *a| {
                a.* = .{ .name = fv.name, .value = values[fv.id], .term = fv.term };
            }
            return .{ .sat = out };
        }
        return .sat_no_witness;
    }

    /// Record the Cooper elimination of `exists y; body` (the `q` binder). The
    /// existential's own variable `y` is opened as a free variable so it can be
    /// eliminated; the goal's other free variables (e.g. the outer `forall x`
    /// eigenvariable) stay free and index the recorded boundaries.
    fn runTrace(self: *Ctx, q: term.Node.Quant) Error!TraceResult {
        // open the existential binder into a free var named by its hint, and
        // pre-scan for the vector width (the opened body's leaves + any nested
        // binders). The +1 covers the eliminated variable itself.
        const fv = try self.pool.add(.{ .fvar = .{ .name = q.hint, .sort = q.sort } });
        const opened = try self.pool.open(q.body, fv);
        var bound: usize = 1;
        self.countVars(opened, &bound);
        self.width = bound;

        // reserve index 0 for the eliminated variable y, so `boundaries` (which
        // drops y's own coefficient) index the remaining free vars by name.
        const y: u32 = self.next_var;
        self.next_var += 1;
        self.vars.put(self.arena, q.hint, y) catch return error.OutOfMemory;
        // y is the elimination target: a subterm mentioning it (e.g. mul(y,y))
        // cannot be soundly abstracted as an atom — abstractAtom will decline,
        // and this trace declines with it.
        self.elim_names.put(self.arena, q.hint, {}) catch return error.OutOfMemory;

        // Pure ℤ: compile the body and trace-eliminate y directly. Any y >= 0 the
        // theory requires is already a conjunct of `body` (from an injected
        // nonneg(y) hypothesis), so no engine-supplied guard is added here.
        const body = try self.formula(opened, false);

        var replay: Replay = .{ .delta = 1, .period = 1, .boundaries = &.{}, .disjuncts = &.{}, .free_names = &.{}, .free_ids = &.{} };
        try self.cooperTraced(y, body, &replay);

        // export the remaining free variables (y is eliminated, not among them)
        // with their coefficient indices so the certifier maps a boundary's
        // coeffs back to the goal's fixed variables.
        const names = try self.arena.alloc(StrId, self.free_vars.items.len);
        const ids = try self.arena.alloc(u32, self.free_vars.items.len);
        for (self.free_vars.items, names, ids) |free, *n, *id| {
            n.* = free.name;
            id.* = free.id;
        }
        replay.free_names = names;
        replay.free_ids = ids;
        return .{ .replay = replay };
    }

    // --- compilation: kernel term -> formula over linear atoms ---

    /// Over-count quantifier binders and leaves for the vector width.
    fn countVars(self: *Ctx, t: TermId, bound: *usize) void {
        switch (self.pool.get(t)) {
            .bvar => {},
            .fvar => bound.* += 1,
            // +1 per app over-provisions width for a possible opaque-atom
            // abstraction (an upper bound is all that is needed); recurse for any
            // vars/atoms in the arguments too.
            .app => |a| {
                bound.* += 1;
                for (self.pool.args(a)) |arg| self.countVars(arg, bound);
            },
            .pred => |a| for (self.pool.args(a)) |arg| self.countVars(arg, bound),
            .eq => |p| {
                self.countVars(p.lhs, bound);
                self.countVars(p.rhs, bound);
            },
            .not => |inner| self.countVars(inner, bound),
            .bin => |b| {
                self.countVars(b.lhs, bound);
                self.countVars(b.rhs, bound);
            },
            .quant => |q| {
                bound.* += 1;
                self.countVars(q.body, bound);
            },
        }
    }

    fn node(self: *Ctx, f: Formula) Error!*const Formula {
        const out = try self.arena.create(Formula);
        out.* = f;
        return out;
    }

    fn blank(self: *Ctx) Error!Linear {
        const coeffs = try self.arena.alloc(i128, self.width);
        @memset(coeffs, 0);
        return .{ .coeffs = coeffs, .konst = 0 };
    }

    fn unit(self: *Ctx, v: u32) Error!Linear {
        var l = try self.blank();
        l.coeffs[v] = 1;
        return l;
    }

    fn addC(self: *Ctx, a: i128, b: i128) Error!i128 {
        return std.math.add(i128, a, b) catch self.fail(.overflow);
    }

    fn mulC(self: *Ctx, a: i128, b: i128) Error!i128 {
        return std.math.mul(i128, a, b) catch self.fail(.overflow);
    }

    /// l + scale * r, freshly allocated
    fn combine(self: *Ctx, l: Linear, scale: i128, r: Linear) Error!Linear {
        var out = try self.blank();
        for (out.coeffs, l.coeffs, r.coeffs) |*o, a, b| {
            o.* = try self.addC(a, try self.mulC(scale, b));
        }
        out.konst = try self.addC(l.konst, try self.mulC(scale, r.konst));
        return out;
    }

    fn shifted(self: *Ctx, l: Linear, delta: i128) Error!Linear {
        return .{ .coeffs = try self.arena.dupe(i128, l.coeffs), .konst = try self.addC(l.konst, delta) };
    }

    fn isConstant(l: Linear) bool {
        for (l.coeffs) |c| {
            if (c != 0) return false;
        }
        return true;
    }

    fn matches(id: SymId, wanted: ?SymId) bool {
        return wanted != null and id == wanted.?;
    }

    /// Abstract an opaque (non-arithmetic) subterm as a fresh linear atom.
    /// STRUCTURALLY equal occurrences share a variable, so f(x) − f(x) cancels
    /// (the pool does not hash-cons, so we scan for an alphaEq match rather than
    /// key on TermId). Sound for validity: proving the goal for an arbitrary
    /// value of the atom proves it for the actual subterm. The per-goal opaque
    /// count is small, so the linear scan is cheap.
    fn abstractAtom(self: *Ctx, t: TermId) Error!Linear {
        // UNSOUND to abstract a subterm that is a function of a quantifier binder
        // being eliminated (e.g. mul(y,y) under `exists y`): the atom's value is
        // not independent of y. Refuse — the goal is genuinely out of fragment.
        if (self.mentionsElim(t)) return self.fail(.{ .out_of_fragment = t });
        for (self.free_vars.items) |fv| {
            if (fv.term) |ot| {
                if (self.pool.alphaEq(ot, t)) return self.unit(fv.id);
            }
        }
        const id = self.next_var;
        try self.free_vars.append(self.arena, .{ .name = @enumFromInt(0), .id = id, .term = t });
        self.next_var += 1;
        return self.unit(id);
    }

    /// Does `t` mention a currently-open quantifier binder (an elimination
    /// target)? Such a subterm cannot be soundly abstracted as an atom.
    fn mentionsElim(self: *Ctx, t: TermId) bool {
        switch (self.pool.get(t)) {
            .bvar => return false,
            .fvar => |v| return self.elim_names.contains(v.name),
            .app, .pred => |a| {
                for (self.pool.args(a)) |arg| if (self.mentionsElim(arg)) return true;
                return false;
            },
            .eq => |p| return self.mentionsElim(p.lhs) or self.mentionsElim(p.rhs),
            .not => |inner| return self.mentionsElim(inner),
            .bin => |b| return self.mentionsElim(b.lhs) or self.mentionsElim(b.rhs),
            .quant => |q| return self.mentionsElim(q.body),
        }
    }

    /// Compile a Nat-sorted term to a linear form.
    fn linearOf(self: *Ctx, t: TermId) Error!Linear {
        switch (self.pool.get(t)) {
            .fvar => |v| {
                // Sort-blind: any free variable is a linear unknown over ℤ. (The
                // theory is responsible for only exposing well-typed goals; a
                // genuinely non-arithmetic term reaches us as an .app/.pred leaf
                // and is abstracted as an opaque atom there, not rejected.)
                const gop = self.vars.getOrPut(self.arena, v.name) catch return error.OutOfMemory;
                if (!gop.found_existing) {
                    gop.value_ptr.* = self.next_var;
                    try self.free_vars.append(self.arena, .{ .name = v.name, .id = self.next_var });
                    self.next_var += 1;
                }
                return self.unit(gop.value_ptr.*);
            },
            .app => |a| {
                const args = self.pool.args(a);
                if (matches(a.sym, self.symbols.zero) and args.len == 0) {
                    return self.blank();
                }
                if (matches(a.sym, self.symbols.one) and args.len == 0) {
                    var l = try self.blank();
                    l.konst = 1;
                    return l;
                }
                if (matches(a.sym, self.symbols.succ) and args.len == 1) {
                    return self.shifted(try self.linearOf(args[0]), 1);
                }
                if (matches(a.sym, self.symbols.prev) and args.len == 1) {
                    return self.shifted(try self.linearOf(args[0]), -1);
                }
                if (matches(a.sym, self.symbols.neg) and args.len == 1) {
                    return self.negated(try self.linearOf(args[0]));
                }
                if (matches(a.sym, self.symbols.sub) and args.len == 2) {
                    const l = try self.linearOf(args[0]);
                    return self.combine(l, -1, try self.linearOf(args[1]));
                }
                if (matches(a.sym, self.symbols.add) and args.len == 2) {
                    const l = try self.linearOf(args[0]);
                    return self.combine(l, 1, try self.linearOf(args[1]));
                }
                if (matches(a.sym, self.symbols.mul) and args.len == 2) {
                    const l = try self.linearOf(args[0]);
                    const r = try self.linearOf(args[1]);
                    if (isConstant(l)) return self.combine(try self.blank(), l.konst, r);
                    if (isConstant(r)) return self.combine(try self.blank(), r.konst, l);
                    // a genuine nonlinear product (both sides variable): abstract
                    // the whole product as one opaque atom.
                    return self.abstractAtom(t);
                }
                // any other app (a foreign function like mod(a,b) or f(x)) is an
                // opaque atom.
                return self.abstractAtom(t);
            },
            // a .pred/.eq/.bin/.quant is never a term position; only leaves and
            // apps reach linearOf. A .bvar would be a bug (unopened binder).
            else => return self.fail(.{ .out_of_fragment = t }),
        }
    }

    /// negation of l: -l
    fn negated(self: *Ctx, l: Linear) Error!Linear {
        return self.combine(try self.blank(), -1, l);
    }

    /// Compile formula `t`; `neg` pushes the pending negation down (the
    /// result is negation-free: not(L >= 0) is -L - 1 >= 0 and so on).
    fn formula(self: *Ctx, t: TermId, neg: bool) Error!*const Formula {
        switch (self.pool.get(t)) {
            .not => |inner| return self.formula(inner, !neg),
            .bin => |b| switch (b.op) {
                .and_op => return self.node(if (neg)
                    .{ .disj = .{ .lhs = try self.formula(b.lhs, true), .rhs = try self.formula(b.rhs, true) } }
                else
                    .{ .conj = .{ .lhs = try self.formula(b.lhs, false), .rhs = try self.formula(b.rhs, false) } }),
                .or_op => return self.node(if (neg)
                    .{ .conj = .{ .lhs = try self.formula(b.lhs, true), .rhs = try self.formula(b.rhs, true) } }
                else
                    .{ .disj = .{ .lhs = try self.formula(b.lhs, false), .rhs = try self.formula(b.rhs, false) } }),
                .implies => return self.node(if (neg)
                    .{ .conj = .{ .lhs = try self.formula(b.lhs, false), .rhs = try self.formula(b.rhs, true) } }
                else
                    .{ .disj = .{ .lhs = try self.formula(b.lhs, true), .rhs = try self.formula(b.rhs, false) } }),
            },
            .eq => |p| {
                const l = try self.linearOf(p.lhs);
                const diff = try self.combine(l, -1, try self.linearOf(p.rhs));
                if (neg) {
                    // diff != 0: diff >= 1 or diff <= -1
                    return self.node(.{ .disj = .{
                        .lhs = try self.node(.{ .ge = try self.shifted(diff, -1) }),
                        .rhs = try self.node(.{ .ge = try self.shifted(try self.negated(diff), -1) }),
                    } });
                }
                return self.node(.{ .conj = .{
                    .lhs = try self.node(.{ .ge = diff }),
                    .rhs = try self.node(.{ .ge = try self.negated(diff) }),
                } });
            },
            .pred => |a| {
                const args = self.pool.args(a);
                if (matches(a.sym, self.symbols.less_than) and args.len == 2) {
                    // a < b: b - a - 1 >= 0 (compile in source order so free
                    // variables are discovered left to right)
                    const lo = try self.linearOf(args[0]);
                    const hi = try self.linearOf(args[1]);
                    const diff = try self.shifted(try self.combine(hi, -1, lo), -1);
                    return self.node(.{ .ge = if (neg) try self.shifted(try self.negated(diff), -1) else diff });
                }
                if (matches(a.sym, self.symbols.nonneg) and args.len == 1) {
                    // nonneg(x): x >= 0. Negated: x <= -1, i.e. -x - 1 >= 0.
                    const x = try self.linearOf(args[0]);
                    return self.node(.{ .ge = if (neg) try self.shifted(try self.negated(x), -1) else x });
                }
                return self.fail(.{ .out_of_fragment = t });
            },
            .quant => |q| {
                // Sort-blind: a binder over ANY sort opens as a ℤ-ranging
                // variable. Nonnegativity, if the theory wants it, arrives as an
                // injected nonneg(x) conjunct in the body (elaborator's job), NOT
                // as an engine-supplied guard.
                const v = self.next_var;
                self.next_var += 1;
                const fv = try self.pool.add(.{ .fvar = .{ .name = q.hint, .sort = q.sort } });
                const opened = try self.pool.open(q.body, fv);
                const saved = self.vars.get(q.hint);
                self.vars.put(self.arena, q.hint, v) catch return error.OutOfMemory;
                // this binder is an elimination target: a subterm mentioning it
                // must not be abstracted as an independent atom.
                const was_elim = self.elim_names.contains(q.hint);
                self.elim_names.put(self.arena, q.hint, {}) catch return error.OutOfMemory;
                const body = try self.formula(opened, neg);
                if (!was_elim) _ = self.elim_names.remove(q.hint);
                if (saved) |s| {
                    self.vars.put(self.arena, q.hint, s) catch return error.OutOfMemory;
                } else {
                    _ = self.vars.remove(q.hint);
                }
                const effective: term.Quantifier = if (neg) switch (q.q) {
                    .forall => .exists,
                    .exists => .forall,
                } else q.q;
                return self.node(.{ .quant = .{ .q = effective, .v = v, .body = body } });
            },
            // a formula leaf that is not an atom of the fragment
            else => return self.fail(.{ .out_of_fragment = t }),
        }
    }

    // --- quantifier elimination (Cooper's algorithm) ---

    fn eliminate(self: *Ctx, f: *const Formula) Error!*const Formula {
        switch (f.*) {
            .tru, .fls, .ge, .div, .ndiv => return f,
            .conj => |p| return self.node(.{ .conj = .{ .lhs = try self.eliminate(p.lhs), .rhs = try self.eliminate(p.rhs) } }),
            .disj => |p| return self.node(.{ .disj = .{ .lhs = try self.eliminate(p.lhs), .rhs = try self.eliminate(p.rhs) } }),
            .quant => |q| {
                const body = try self.eliminate(q.body);
                return switch (q.q) {
                    .exists => self.cooper(q.v, body),
                    .forall => self.negate(try self.cooper(q.v, try self.negate(body))),
                };
            },
        }
    }

    fn negate(self: *Ctx, f: *const Formula) Error!*const Formula {
        return self.node(switch (f.*) {
            .tru => .fls,
            .fls => .tru,
            // not(L >= 0) is -L - 1 >= 0
            .ge => |l| .{ .ge = try self.shifted(try self.negated(l), -1) },
            .div => |d| .{ .ndiv = d },
            .ndiv => |d| .{ .div = d },
            .conj => |p| .{ .disj = .{ .lhs = try self.negate(p.lhs), .rhs = try self.negate(p.rhs) } },
            .disj => |p| .{ .conj = .{ .lhs = try self.negate(p.lhs), .rhs = try self.negate(p.rhs) } },
            .quant => unreachable, // negate only runs on eliminated bodies
        });
    }

    fn lcmC(self: *Ctx, a: i128, b: i128) Error!i128 {
        const ua: u128 = @abs(a);
        const ub: u128 = @abs(b);
        const g = std.math.gcd(ua, ub);
        const left = std.math.cast(i128, ua / g) orelse return self.fail(.overflow);
        const right = std.math.cast(i128, ub) orelse return self.fail(.overflow);
        return self.mulC(left, right);
    }

    fn coefficientLcm(self: *Ctx, f: *const Formula, v: u32, delta: *i128) Error!void {
        switch (f.*) {
            .tru, .fls => {},
            .ge => |l| if (l.coeffs[v] != 0) {
                delta.* = try self.lcmC(delta.*, l.coeffs[v]);
            },
            .div, .ndiv => |d| if (d.linear.coeffs[v] != 0) {
                delta.* = try self.lcmC(delta.*, d.linear.coeffs[v]);
            },
            .conj, .disj => |p| {
                try self.coefficientLcm(p.lhs, v, delta);
                try self.coefficientLcm(p.rhs, v, delta);
            },
            .quant => unreachable, // innermost-first elimination
        }
    }

    /// Scale every atom so v's coefficient becomes +-1 in y-space (y = delta
    /// * v, recorded by conjoining delta | y at the call site).
    fn normalized(self: *Ctx, f: *const Formula, v: u32, delta: i128) Error!*const Formula {
        switch (f.*) {
            .tru, .fls => return f,
            .ge => |l| {
                const a = l.coeffs[v];
                if (a == 0) return f;
                const m = @divExact(delta, @as(i128, @intCast(@abs(a))));
                var out = try self.combine(try self.blank(), m, l);
                out.coeffs[v] = if (a > 0) 1 else -1;
                return self.node(.{ .ge = out });
            },
            .div, .ndiv => |d| {
                const a = d.linear.coeffs[v];
                if (a == 0) return f;
                const m = @divExact(delta, @as(i128, @intCast(@abs(a))));
                // divisibility is sign-blind: normalize the coefficient to +1
                var out = try self.combine(try self.blank(), if (a > 0) m else -m, d.linear);
                out.coeffs[v] = 1;
                const scaled: Formula.Div = .{ .modulus = try self.mulC(d.modulus, m), .linear = out };
                return self.node(if (f.* == .div) .{ .div = scaled } else .{ .ndiv = scaled });
            },
            .conj => |p| return self.node(.{ .conj = .{ .lhs = try self.normalized(p.lhs, v, delta), .rhs = try self.normalized(p.rhs, v, delta) } }),
            .disj => |p| return self.node(.{ .disj = .{ .lhs = try self.normalized(p.lhs, v, delta), .rhs = try self.normalized(p.rhs, v, delta) } }),
            .quant => unreachable,
        }
    }

    fn modulusLcm(self: *Ctx, f: *const Formula, v: u32, d: *i128) Error!void {
        switch (f.*) {
            .tru, .fls, .ge => {},
            .div, .ndiv => |x| if (x.linear.coeffs[v] != 0) {
                d.* = try self.lcmC(d.*, x.modulus);
            },
            .conj, .disj => |p| {
                try self.modulusLcm(p.lhs, v, d);
                try self.modulusLcm(p.rhs, v, d);
            },
            .quant => unreachable,
        }
    }

    /// Boundary terms: each lower bound y + t >= 0 confines a satisfying y
    /// to start at b = -t - 1 (exclusive); Cooper's disjunction probes b + j.
    fn boundaries(self: *Ctx, f: *const Formula, v: u32, out: *std.ArrayList(Linear)) Error!void {
        switch (f.*) {
            .tru, .fls, .div, .ndiv => {},
            .ge => |l| if (l.coeffs[v] == 1) {
                var b = try self.negated(l);
                b.coeffs[v] = 0;
                b.konst = try self.addC(b.konst, -1);
                try out.append(self.arena, b);
            },
            .conj, .disj => |p| {
                try self.boundaries(p.lhs, v, out);
                try self.boundaries(p.rhs, v, out);
            },
            .quant => unreachable,
        }
    }

    fn spend(self: *Ctx) Error!void {
        if (self.budget == 0) return self.fail(.too_large);
        self.budget -= 1;
    }

    /// Substitute y := s (s has no y component) through the formula.
    fn subst(self: *Ctx, f: *const Formula, v: u32, s: Linear) Error!*const Formula {
        switch (f.*) {
            .tru, .fls => return f,
            .ge => |l| {
                const c = l.coeffs[v];
                if (c == 0) return f;
                try self.spend();
                var out = try self.combine(l, c, s);
                out.coeffs[v] = 0;
                return self.node(.{ .ge = out });
            },
            .div, .ndiv => |d| {
                if (d.linear.coeffs[v] == 0) return f;
                try self.spend();
                var out = try self.combine(d.linear, 1, s);
                out.coeffs[v] = 0;
                const sub: Formula.Div = .{ .modulus = d.modulus, .linear = out };
                return self.node(if (f.* == .div) .{ .div = sub } else .{ .ndiv = sub });
            },
            .conj => |p| return self.node(.{ .conj = .{ .lhs = try self.subst(p.lhs, v, s), .rhs = try self.subst(p.rhs, v, s) } }),
            .disj => |p| return self.node(.{ .disj = .{ .lhs = try self.subst(p.lhs, v, s), .rhs = try self.subst(p.rhs, v, s) } }),
            .quant => unreachable,
        }
    }

    /// The minus-infinity residue: lower bounds fail, upper bounds hold, and
    /// only the periodic (divisibility) atoms see y := j.
    fn substInf(self: *Ctx, f: *const Formula, v: u32, j: i128) Error!*const Formula {
        switch (f.*) {
            .tru, .fls => return f,
            .ge => |l| return switch (l.coeffs[v]) {
                0 => f,
                1 => self.node(.fls),
                else => self.node(.tru), // -1: upper bound
            },
            .div, .ndiv => |d| {
                if (d.linear.coeffs[v] == 0) return f;
                try self.spend();
                var out: Linear = .{ .coeffs = try self.arena.dupe(i128, d.linear.coeffs), .konst = try self.addC(d.linear.konst, j) };
                out.coeffs[v] = 0;
                const sub: Formula.Div = .{ .modulus = d.modulus, .linear = out };
                return self.node(if (f.* == .div) .{ .div = sub } else .{ .ndiv = sub });
            },
            .conj => |p| return self.node(.{ .conj = .{ .lhs = try self.substInf(p.lhs, v, j), .rhs = try self.substInf(p.rhs, v, j) } }),
            .disj => |p| return self.node(.{ .disj = .{ .lhs = try self.substInf(p.lhs, v, j), .rhs = try self.substInf(p.rhs, v, j) } }),
            .quant => unreachable,
        }
    }

    /// The numeric prelude shared by `cooper` (decision) and `cooperTraced`
    /// (certificate): scale v's coefficient to +-1, conjoin the stride
    /// `delta | v`, and collect the period D and boundary set B. Both callers
    /// then enumerate the SAME `OR_{j=1..D}(F_-inf(j) OR_{b in B} F(b+j))`; only
    /// what they do with each disjunct differs (fold a node vs. record it).
    const Prepared = struct { g: *const Formula, delta: i128, period: i128, lows: []const Linear };

    fn prepared(self: *Ctx, v: u32, f: *const Formula) Error!Prepared {
        var delta: i128 = 1;
        try self.coefficientLcm(f, v, &delta);
        const norm = try self.normalized(f, v, delta);
        // y = delta * x ranges over the multiples of delta
        const stride = try self.node(.{ .div = .{ .modulus = delta, .linear = try self.unit(v) } });
        const g = try self.node(.{ .conj = .{ .lhs = stride, .rhs = norm } });

        var period: i128 = 1;
        try self.modulusLcm(g, v, &period);
        var lows: std.ArrayList(Linear) = .empty;
        try self.boundaries(g, v, &lows);
        if (period > 4096) return self.fail(.too_large);
        return .{ .g = g, .delta = delta, .period = period, .lows = lows.items };
    }

    /// Eliminate `exists v` from quantifier-free `f` (Cooper):
    ///   exists y. F  <=>  OR_{j=1..D} ( F_minus_inf(j)  OR_{b in B} F(b+j) )
    fn cooper(self: *Ctx, v: u32, f: *const Formula) Error!*const Formula {
        const p = try self.prepared(v, f);
        const d_steps: usize = @intCast(p.period);

        var result: *const Formula = try self.node(.fls);
        for (1..d_steps + 1) |step| {
            const j: i128 = @intCast(step);
            result = try self.node(.{ .disj = .{ .lhs = result, .rhs = try self.substInf(p.g, v, j) } });
            for (p.lows) |b| {
                const probe = try self.shifted(b, j);
                result = try self.node(.{ .disj = .{ .lhs = result, .rhs = try self.subst(p.g, v, probe) } });
            }
        }
        return result;
    }

    /// Certificate twin of `cooper`: same elimination, but instead of folding
    /// the disjuncts into a formula it RECORDS each one (as an offset j and, for
    /// a boundary probe, which boundary) into `out`. The certifier reconstructs
    /// the witnesses `boundaries[i] + j` in its own term pool.
    fn cooperTraced(self: *Ctx, v: u32, f: *const Formula, out: *Replay) Error!void {
        const p = try self.prepared(v, f);
        const d_steps: usize = @intCast(p.period);

        const bounds = try self.arena.alloc(LinearDump, p.lows.len);
        for (p.lows, bounds) |b, *d| d.* = .{ .coeffs = b.coeffs, .konst = b.konst };

        var disjuncts: std.ArrayList(Disjunct) = .empty;
        for (1..d_steps + 1) |step| {
            const j: i128 = @intCast(step);
            try disjuncts.append(self.arena, .{ .minus_inf = .{ .j = j } });
            for (0..p.lows.len) |b_index| {
                try disjuncts.append(self.arena, .{ .boundary = .{ .b_index = b_index, .j = j } });
            }
        }
        out.delta = p.delta;
        out.period = p.period;
        out.boundaries = bounds;
        out.disjuncts = disjuncts.items;
    }

    // --- ground evaluation and countermodel search ---

    fn evalGround(f: *const Formula) bool {
        return switch (f.*) {
            .tru => true,
            .fls => false,
            .ge => |l| l.konst >= 0, // coefficients are all eliminated
            .div => |d| @mod(d.linear.konst, d.modulus) == 0,
            .ndiv => |d| @mod(d.linear.konst, d.modulus) != 0,
            .conj => |p| evalGround(p.lhs) and evalGround(p.rhs),
            .disj => |p| evalGround(p.lhs) or evalGround(p.rhs),
            .quant => unreachable,
        };
    }

    fn valueOf(l: Linear, values: []const i128) i256 {
        var acc: i256 = l.konst;
        for (l.coeffs, values) |c, x| acc += @as(i256, c) * @as(i256, x);
        return acc;
    }

    fn evalAt(f: *const Formula, values: []const i128) bool {
        return switch (f.*) {
            .tru => true,
            .fls => false,
            .ge => |l| valueOf(l, values) >= 0,
            .div => |d| @mod(valueOf(d.linear, values), @as(i256, d.modulus)) == 0,
            .ndiv => |d| @mod(valueOf(d.linear, values), @as(i256, d.modulus)) != 0,
            .conj => |p| evalAt(p.lhs, values) and evalAt(p.rhs, values),
            .disj => |p| evalAt(p.lhs, values) or evalAt(p.rhs, values),
            .quant => unreachable,
        };
    }

    /// Depth-first search of small nonnegative values for the free
    /// variables, smallest sums first per variable.
    fn witness(self: *Ctx, f: *const Formula, index: usize, values: []i128) bool {
        if (index == self.free_vars.items.len) return evalAt(f, values);
        const total = std.math.powi(usize, witness_bound + 1, self.free_vars.items.len) catch witness_combinations + 1;
        const cap: i128 = if (total > witness_combinations) 8 else witness_bound;
        var x: i128 = 0;
        while (x <= cap) : (x += 1) {
            values[self.free_vars.items[index].id] = x;
            if (self.witness(f, index + 1, values)) return true;
        }
        return false;
    }
};

// --- tests ---

const testing = std.testing;

const Rig = struct {
    pool: Pool,
    symbols: Symbols,

    const nat: SortId = @enumFromInt(1);
    const sym_zero: SymId = @enumFromInt(0);
    const sym_succ: SymId = @enumFromInt(1);
    const sym_add: SymId = @enumFromInt(2);
    const sym_less: SymId = @enumFromInt(3);
    const sym_mul: SymId = @enumFromInt(4);
    const sym_nonneg: SymId = @enumFromInt(5);
    const sym_sub: SymId = @enumFromInt(6);
    const sym_neg: SymId = @enumFromInt(7);
    const sym_foreign: SymId = @enumFromInt(8);

    fn init(arena: Allocator) Rig {
        return .{
            .pool = .init(arena),
            .symbols = .{
                .nat = nat,
                .zero = sym_zero,
                .succ = sym_succ,
                .add = sym_add,
                .mul = sym_mul,
                .less_than = sym_less,
                .nonneg = sym_nonneg,
            },
        };
    }

    fn nonneg(self: *Rig, t: TermId) !TermId {
        return self.pool.addApp(.pred, sym_nonneg, &.{t});
    }

    fn zero(self: *Rig) !TermId {
        return self.pool.addApp(.app, sym_zero, &.{});
    }

    fn succ(self: *Rig, t: TermId) !TermId {
        return self.pool.addApp(.app, sym_succ, &.{t});
    }

    fn tower(self: *Rig, n: usize) !TermId {
        var t = try self.zero();
        for (0..n) |_| t = try self.succ(t);
        return t;
    }

    fn add(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.addApp(.app, sym_add, &.{ l, r });
    }

    fn mul(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.addApp(.app, sym_mul, &.{ l, r });
    }

    fn sub(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.addApp(.app, sym_sub, &.{ l, r });
    }

    fn less(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.addApp(.pred, sym_less, &.{ l, r });
    }

    fn eq(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.add(.{ .eq = .{ .lhs = l, .rhs = r } });
    }

    fn fvar(self: *Rig, name: u32) !TermId {
        return self.pool.add(.{ .fvar = .{ .name = @enumFromInt(name), .sort = nat } });
    }

    /// close over the named fvar and wrap in a quantifier
    fn quant(self: *Rig, q: term.Quantifier, name: u32, body: TermId) !TermId {
        const closed = try self.pool.close(body, @enumFromInt(name));
        return self.pool.add(.{ .quant = .{ .q = q, .sort = nat, .hint = @enumFromInt(name), .body = closed } });
    }
};

test "ground: 2 + 3 = 5" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const goal = try r.eq(try r.add(try r.tower(2), try r.tower(3)), try r.tower(5));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .valid);
}

test "pure ℤ: forall b, a: a < a + succ(b) is NOT valid (b may be negative)" {
    // The engine is pure ℤ — no implicit nonnegativity. a < a + b + 1 fails at
    // b = -2, so the raw goal is not a consequence.
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const a = try r.fvar(10);
    const b = try r.fvar(11);
    const body = try r.less(a, try r.add(a, try r.succ(b)));
    const goal = try r.quant(.forall, 11, try r.quant(.forall, 10, body));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v != .valid);
}

test "nonneg(b) premise recovers ℕ: b >= 0 gives a < a + succ(b)" {
    // With the theory-supplied nonneg(b) — the ℕ nonnegativity the engine no
    // longer assumes — the goal is valid again. (nonneg(x) reads as x >= 0.)
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const a = try r.fvar(10);
    const b = try r.fvar(11);
    const premise = try r.nonneg(b);
    const goal = try r.less(a, try r.add(a, try r.succ(b)));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{premise}, goal);
    try testing.expect(v == .valid);
}

test "every number is even or odd (quantified divisibility)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const x = try r.fvar(10);
    const y = try r.fvar(11);
    const even = try r.eq(x, try r.add(y, y));
    const odd = try r.eq(x, try r.succ(try r.add(y, y)));
    const either = try r.pool.add(.{ .bin = .{ .op = .or_op, .lhs = even, .rhs = odd } });
    const goal = try r.quant(.forall, 10, try r.quant(.exists, 11, either));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .valid);
}

test "premise a < b gives a < succ(b)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const a = try r.fvar(10);
    const b = try r.fvar(11);
    const premise = try r.less(a, b);
    const goal = try r.less(a, try r.succ(b));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{premise}, goal);
    try testing.expect(v == .valid);
}

test "free-variable countermodel: a < b is false at a := 0, b := 0" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const goal = try r.less(try r.fvar(10), try r.fvar(11));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .countermodel);
    try testing.expectEqual(2, v.countermodel.len);
    try testing.expectEqual(0, v.countermodel[0].value);
    try testing.expectEqual(0, v.countermodel[1].value);
}

test "nonlinear mul abstracts to an opaque atom (same product cancels)" {
    // mul(a,b) = mul(a,b): both sides abstract to the SAME opaque atom, so the
    // equation is valid (X = X) — the abstraction cancels.
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const product = try r.mul(try r.fvar(10), try r.fvar(11));
    const goal = try r.eq(product, product);
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .valid);
}

test "distinct nonlinear products are distinct atoms → out of fragment" {
    // mul(a,b) = mul(b,a): the two products are DISTINCT opaque atoms, so the
    // goal is not linear-arithmetic-valid; rather than a misleading atom-valued
    // countermodel, report the (first) offending product as out of fragment.
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const a = try r.fvar(10);
    const b = try r.fvar(11);
    const goal = try r.eq(try r.mul(a, b), try r.mul(b, a));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .out_of_fragment);
}

test "opaque atom cancellation is linear: sub(add(a, f), f) = a" {
    // an opaque unary term f(x) abstracts to one atom; add-then-sub cancels it.
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    r.symbols.sub = Rig.sym_sub;
    r.symbols.neg = Rig.sym_neg;
    const a = try r.fvar(10);
    const fx = try r.pool.addApp(.app, Rig.sym_foreign, &.{try r.fvar(11)});
    const goal = try r.eq(try r.sub(try r.add(a, fx), fx), a);
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .valid);
}

test "linear mul by a literal folds" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    // 2 * x = x + x
    const x = try r.fvar(10);
    const goal = try r.quant(.forall, 10, try r.eq(try r.mul(try r.tower(2), x), try r.add(x, x)));
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .valid);
}

test "trichotomy: a < b or a = b or b < a" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const a = try r.fvar(10);
    const b = try r.fvar(11);
    const first = try r.pool.add(.{ .bin = .{ .op = .or_op, .lhs = try r.less(a, b), .rhs = try r.eq(a, b) } });
    const goal = try r.pool.add(.{ .bin = .{ .op = .or_op, .lhs = first, .rhs = try r.less(b, a) } });
    const v = try decide(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(v == .valid);
}

// --- Cooper-replay trace (layer 1) ---

test "trace: parity body has delta 2, period 2" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    // exists y; x = add(y, y) or x = succ(add(y, y))  (x free)
    const x = try r.fvar(10);
    const y = try r.fvar(11);
    const even = try r.eq(x, try r.add(y, y));
    const odd = try r.eq(x, try r.succ(try r.add(y, y)));
    const either = try r.pool.add(.{ .bin = .{ .op = .or_op, .lhs = even, .rhs = odd } });
    const goal = try r.quant(.exists, 11, either);
    const t = try trace(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(t == .replay);
    try testing.expectEqual(@as(i128, 2), t.replay.delta);
    try testing.expectEqual(@as(i128, 2), t.replay.period);
    // x is the single free variable
    try testing.expectEqual(@as(usize, 1), t.replay.free_names.len);
    // the recorded disjunction is nonempty (D * (1 + |B|) probes)
    try testing.expect(t.replay.disjuncts.len >= 2);
}

test "trace: a non-existential goal is not applicable" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    // a < add(a, succ(b)) — no leading exists
    const a = try r.fvar(10);
    const b = try r.fvar(11);
    const goal = try r.less(a, try r.add(a, try r.succ(b)));
    const t = try trace(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(t == .not_applicable);
}

test "trace: a nonlinear existential is not applicable" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    // exists y; mul(y, y) = x  (nonlinear — out of fragment)
    const x = try r.fvar(10);
    const y = try r.fvar(11);
    const goal = try r.quant(.exists, 11, try r.eq(try r.mul(y, y), x));
    const t = try trace(arena_state.allocator(), &r.pool, r.symbols, &.{}, goal);
    try testing.expect(t == .not_applicable);
}
