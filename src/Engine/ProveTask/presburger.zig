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
        if (!try self.evalGround(ground)) return .unsat;

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
        if (try self.witness(qf, values)) {
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

    /// Over-count quantifier binders and leaves for the vector width. Iterative
    /// work-stack over the term tree (was native recursion): traversal order does
    /// not matter — every leaf/binder contributes the same increment. On the
    /// (arena-backed, practically-unreachable) OOM path it over-estimates the
    /// width, which is always safe: width is an upper bound on the variable count.
    fn countVars(self: *Ctx, t: TermId, bound: *usize) void {
        var fb = std.heap.stackFallback(64 * @sizeOf(TermId), self.arena);
        const a = fb.get();
        var stack: std.ArrayList(TermId) = .empty;
        defer stack.deinit(a);
        stack.append(a, t) catch return overCount(bound);
        while (stack.pop()) |cur| {
            switch (self.pool.get(cur)) {
                .bvar => {},
                .fvar => bound.* += 1,
                // +1 per app over-provisions width for a possible opaque-atom
                // abstraction (an upper bound is all that is needed); recurse for
                // any vars/atoms in the arguments too.
                .app => |ap| {
                    bound.* += 1;
                    for (self.pool.args(ap)) |arg| stack.append(a, arg) catch return overCount(bound);
                },
                .pred => |ap| for (self.pool.args(ap)) |arg| stack.append(a, arg) catch return overCount(bound),
                .eq => |p| {
                    stack.append(a, p.lhs) catch return overCount(bound);
                    stack.append(a, p.rhs) catch return overCount(bound);
                },
                .not => |inner| stack.append(a, inner) catch return overCount(bound),
                .bin => |b| {
                    stack.append(a, b.lhs) catch return overCount(bound);
                    stack.append(a, b.rhs) catch return overCount(bound);
                },
                .quant => |q| {
                    bound.* += 1;
                    stack.append(a, q.body) catch return overCount(bound);
                },
            }
        }
    }

    fn overCount(bound: *usize) void {
        bound.* += 1_000_000;
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
    /// target)? Such a subterm cannot be soundly abstracted as an atom. Iterative
    /// work-stack (was native recursion): a disjunction over leaves, so stack
    /// order is irrelevant. OOM conservatively reports "mentions" — that only ever
    /// REFUSES an abstraction (declines a step), never admits a bad one.
    fn mentionsElim(self: *Ctx, t: TermId) bool {
        var fb = std.heap.stackFallback(64 * @sizeOf(TermId), self.arena);
        const a = fb.get();
        var stack: std.ArrayList(TermId) = .empty;
        defer stack.deinit(a);
        stack.append(a, t) catch return true;
        while (stack.pop()) |cur| {
            switch (self.pool.get(cur)) {
                .bvar => {},
                .fvar => |v| if (self.elim_names.contains(v.name)) return true,
                .app, .pred => |ap| for (self.pool.args(ap)) |arg| stack.append(a, arg) catch return true,
                .eq => |p| {
                    stack.append(a, p.lhs) catch return true;
                    stack.append(a, p.rhs) catch return true;
                },
                .not => |inner| stack.append(a, inner) catch return true,
                .bin => |b| {
                    stack.append(a, b.lhs) catch return true;
                    stack.append(a, b.rhs) catch return true;
                },
                .quant => |q| stack.append(a, q.body) catch return true,
            }
        }
        return false;
    }

    /// The arithmetic operator a linear app node combines its children with. A
    /// `.leaf` node has no linear children (constant / fvar / opaque atom) and is
    /// resolved directly; the others recurse on 1 or 2 term children.
    const LinOp = enum { leaf, succ, prev, neg, sub, add, mul };

    /// Classify an app/leaf term for `linearOf` (does NOT register fvars or
    /// abstract atoms — that happens when the node is resolved as a leaf or
    /// rebuilt).
    fn linOp(self: *Ctx, t: TermId) LinOp {
        switch (self.pool.get(t)) {
            .app => |a| {
                const args = self.pool.args(a);
                if (matches(a.sym, self.symbols.succ) and args.len == 1) return .succ;
                if (matches(a.sym, self.symbols.prev) and args.len == 1) return .prev;
                if (matches(a.sym, self.symbols.neg) and args.len == 1) return .neg;
                if (matches(a.sym, self.symbols.sub) and args.len == 2) return .sub;
                if (matches(a.sym, self.symbols.add) and args.len == 2) return .add;
                if (matches(a.sym, self.symbols.mul) and args.len == 2) return .mul;
                return .leaf; // zero/one/foreign app
            },
            else => return .leaf,
        }
    }

    /// Resolve a `.leaf` term (fvar, zero, one, or an opaque app) to a Linear.
    fn linearLeaf(self: *Ctx, t: TermId) Error!Linear {
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
                // any other app (a foreign function like mod(a,b) or f(x)) is an
                // opaque atom.
                return self.abstractAtom(t);
            },
            // a .pred/.eq/.bin/.quant is never a term position; only leaves and
            // apps reach linearOf. A .bvar would be a bug (unopened binder).
            else => return self.fail(.{ .out_of_fragment = t }),
        }
    }

    const LinFrame = struct { t: TermId, op: LinOp, expanded: bool };

    /// Compile a Nat-sorted term to a linear form. Iterative two-color post-order
    /// (was native recursion — a `succ` tower or a deep sum could otherwise
    /// overflow the C stack): a node is first EXPANDED (its term children pushed
    /// deeper, LEFT child on top so it resolves first — free-variable discovery
    /// order is left-to-right, as before), then on its second pop COMBINED from the
    /// child Linears already on `results`. Leaf nodes (constant / fvar / opaque
    /// atom) resolve directly, in the same order the recursion visited them, so
    /// fvar registration and atom abstraction are byte-for-byte identical.
    fn linearOf(self: *Ctx, root: TermId) Error!Linear {
        var fb = std.heap.stackFallback(64 * @sizeOf(LinFrame), self.arena);
        const a = fb.get();
        var work: std.ArrayList(LinFrame) = .empty;
        defer work.deinit(a);
        var results: std.ArrayList(Linear) = .empty;
        defer results.deinit(a);

        try work.append(a, .{ .t = root, .op = self.linOp(root), .expanded = false });
        while (work.pop()) |frame| {
            const args = switch (self.pool.get(frame.t)) {
                .app => |ap| self.pool.args(ap),
                else => &[_]TermId{},
            };
            if (frame.op == .leaf) {
                try results.append(a, try self.linearLeaf(frame.t));
                continue;
            }
            if (!frame.expanded) {
                try work.append(a, .{ .t = frame.t, .op = frame.op, .expanded = true });
                // push children so the LEFTMOST resolves first (pop order): for a
                // binary op push rhs then lhs; for unary just the one child.
                switch (frame.op) {
                    .succ, .prev, .neg => try work.append(a, .{ .t = args[0], .op = self.linOp(args[0]), .expanded = false }),
                    .sub, .add, .mul => {
                        try work.append(a, .{ .t = args[1], .op = self.linOp(args[1]), .expanded = false });
                        try work.append(a, .{ .t = args[0], .op = self.linOp(args[0]), .expanded = false });
                    },
                    .leaf => unreachable,
                }
                continue;
            }
            // rebuild: children Linears are the top of `results`, in original order
            switch (frame.op) {
                .succ => {
                    const l = results.pop().?;
                    try results.append(a, try self.shifted(l, 1));
                },
                .prev => {
                    const l = results.pop().?;
                    try results.append(a, try self.shifted(l, -1));
                },
                .neg => {
                    const l = results.pop().?;
                    try results.append(a, try self.negated(l));
                },
                .sub => {
                    const r = results.pop().?;
                    const l = results.pop().?;
                    try results.append(a, try self.combine(l, -1, r));
                },
                .add => {
                    const r = results.pop().?;
                    const l = results.pop().?;
                    try results.append(a, try self.combine(l, 1, r));
                },
                .mul => {
                    const r = results.pop().?;
                    const l = results.pop().?;
                    if (isConstant(l)) {
                        try results.append(a, try self.combine(try self.blank(), l.konst, r));
                    } else if (isConstant(r)) {
                        try results.append(a, try self.combine(try self.blank(), r.konst, l));
                    } else {
                        // a genuine nonlinear product (both sides variable): abstract
                        // the whole product as one opaque atom. (Its children's
                        // fvars stayed registered, exactly as in the recursion.)
                        try results.append(a, try self.abstractAtom(frame.t));
                    }
                },
                .leaf => unreachable,
            }
        }
        return results.items[0];
    }

    /// negation of l: -l
    fn negated(self: *Ctx, l: Linear) Error!Linear {
        return self.combine(try self.blank(), -1, l);
    }

    /// A frame in the iterative `formula` compiler. `kind` says what to do when
    /// this frame is popped in the REBUILD phase (its children already on the
    /// results stack). `neg` is the pending-negation flag carried per node.
    const FormulaFrame = struct {
        t: TermId,
        neg: bool,
        expanded: bool,
        kind: Kind,
        /// quant-only rebuild state, captured in the expand phase (before the body
        /// is processed) and consumed in the rebuild phase (after).
        quant: QuantState = undefined,

        const Kind = enum { dispatch, bin_and, bin_or, bin_implies, quant };
    };

    const QuantState = struct { v: u32, saved: ?u32, has_saved: bool, was_elim: bool, hint: StrId, effective: term.Quantifier };

    /// Compile formula `t`; `neg` pushes the pending negation down (the result is
    /// negation-free: not(L >= 0) is -L - 1 >= 0 and so on). Iterative two-color
    /// stack (was native recursion): interior nodes (not/bin/quant) push their
    /// children and are re-popped to assemble the result; atom nodes (eq/pred)
    /// compile in place. The quant arm captures its `vars`/`elim_names` save state
    /// on the way DOWN and restores it on the way UP, exactly bracketing the body —
    /// same as the recursion's save/child/restore. Traversal is left-to-right so
    /// free-variable discovery order is preserved.
    fn formula(self: *Ctx, root: TermId, root_neg: bool) Error!*const Formula {
        var fb = std.heap.stackFallback(128 * @sizeOf(FormulaFrame), self.arena);
        const a = fb.get();
        var work: std.ArrayList(FormulaFrame) = .empty;
        defer work.deinit(a);
        var results: std.ArrayList(*const Formula) = .empty;
        defer results.deinit(a);

        try work.append(a, .{ .t = root, .neg = root_neg, .expanded = false, .kind = .dispatch });
        while (work.pop()) |frame| {
            if (frame.expanded) {
                // REBUILD phase: children are on top of `results` in original order.
                switch (frame.kind) {
                    .dispatch => unreachable, // dispatch frames never re-push as expanded
                    .bin_and => {
                        const rhs = results.pop().?;
                        const lhs = results.pop().?;
                        try results.append(a, try self.node(if (frame.neg)
                            .{ .disj = .{ .lhs = lhs, .rhs = rhs } }
                        else
                            .{ .conj = .{ .lhs = lhs, .rhs = rhs } }));
                    },
                    .bin_or => {
                        const rhs = results.pop().?;
                        const lhs = results.pop().?;
                        try results.append(a, try self.node(if (frame.neg)
                            .{ .conj = .{ .lhs = lhs, .rhs = rhs } }
                        else
                            .{ .disj = .{ .lhs = lhs, .rhs = rhs } }));
                    },
                    .bin_implies => {
                        const rhs = results.pop().?;
                        const lhs = results.pop().?;
                        try results.append(a, try self.node(if (frame.neg)
                            .{ .conj = .{ .lhs = lhs, .rhs = rhs } }
                        else
                            .{ .disj = .{ .lhs = lhs, .rhs = rhs } }));
                    },
                    .quant => {
                        const body = results.pop().?;
                        const qs = frame.quant;
                        // restore vars/elim_names to their pre-body state (mirrors
                        // the recursion's post-child cleanup).
                        if (!qs.was_elim) _ = self.elim_names.remove(qs.hint);
                        if (qs.has_saved) {
                            self.vars.put(self.arena, qs.hint, qs.saved.?) catch return error.OutOfMemory;
                        } else {
                            _ = self.vars.remove(qs.hint);
                        }
                        try results.append(a, try self.node(.{ .quant = .{ .q = qs.effective, .v = qs.v, .body = body } }));
                    },
                }
                continue;
            }

            // EXPAND / dispatch phase.
            const t = frame.t;
            const neg = frame.neg;
            switch (self.pool.get(t)) {
                .not => |inner| {
                    // linear: flip neg and re-dispatch the same slot (no result yet)
                    try work.append(a, .{ .t = inner, .neg = !neg, .expanded = false, .kind = .dispatch });
                },
                .bin => |b| {
                    const kind: FormulaFrame.Kind = switch (b.op) {
                        .and_op => .bin_and,
                        .or_op => .bin_or,
                        .implies => .bin_implies,
                    };
                    // child neg values, matching the original per-arm threading.
                    const lhs_neg, const rhs_neg = switch (b.op) {
                        .and_op, .or_op => .{ neg, neg },
                        // implies: non-neg => (NOT lhs) disj rhs; neg => lhs conj (NOT rhs)
                        .implies => if (neg) .{ false, true } else .{ true, false },
                    };
                    try work.append(a, .{ .t = t, .neg = neg, .expanded = true, .kind = kind });
                    // push rhs then lhs so lhs is processed first (result order lhs,rhs)
                    try work.append(a, .{ .t = b.rhs, .neg = rhs_neg, .expanded = false, .kind = .dispatch });
                    try work.append(a, .{ .t = b.lhs, .neg = lhs_neg, .expanded = false, .kind = .dispatch });
                },
                .eq => |p| {
                    const l = try self.linearOf(p.lhs);
                    const diff = try self.combine(l, -1, try self.linearOf(p.rhs));
                    if (neg) {
                        // diff != 0: diff >= 1 or diff <= -1
                        try results.append(a, try self.node(.{ .disj = .{
                            .lhs = try self.node(.{ .ge = try self.shifted(diff, -1) }),
                            .rhs = try self.node(.{ .ge = try self.shifted(try self.negated(diff), -1) }),
                        } }));
                    } else {
                        try results.append(a, try self.node(.{ .conj = .{
                            .lhs = try self.node(.{ .ge = diff }),
                            .rhs = try self.node(.{ .ge = try self.negated(diff) }),
                        } }));
                    }
                },
                .pred => |ap| {
                    const args = self.pool.args(ap);
                    if (matches(ap.sym, self.symbols.less_than) and args.len == 2) {
                        // a < b: b - a - 1 >= 0 (compile in source order so free
                        // variables are discovered left to right)
                        const lo = try self.linearOf(args[0]);
                        const hi = try self.linearOf(args[1]);
                        const diff = try self.shifted(try self.combine(hi, -1, lo), -1);
                        try results.append(a, try self.node(.{ .ge = if (neg) try self.shifted(try self.negated(diff), -1) else diff }));
                    } else if (matches(ap.sym, self.symbols.nonneg) and args.len == 1) {
                        // nonneg(x): x >= 0. Negated: x <= -1, i.e. -x - 1 >= 0.
                        const x = try self.linearOf(args[0]);
                        try results.append(a, try self.node(.{ .ge = if (neg) try self.shifted(try self.negated(x), -1) else x }));
                    } else {
                        return self.fail(.{ .out_of_fragment = t });
                    }
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
                    const effective: term.Quantifier = if (neg) switch (q.q) {
                        .forall => .exists,
                        .exists => .forall,
                    } else q.q;
                    try work.append(a, .{ .t = t, .neg = neg, .expanded = true, .kind = .quant, .quant = .{
                        .v = v,
                        .saved = saved,
                        .has_saved = saved != null,
                        .was_elim = was_elim,
                        .hint = q.hint,
                        .effective = effective,
                    } });
                    try work.append(a, .{ .t = opened, .neg = neg, .expanded = false, .kind = .dispatch });
                },
                // a formula leaf that is not an atom of the fragment
                else => return self.fail(.{ .out_of_fragment = t }),
            }
        }
        return results.items[0];
    }

    // --- generic iterative post-order rebuild over the Formula tree ---
    //
    // The value-building formula transforms below (negate/normalized/subst/
    // substInf/eliminate) were native tree recursion. This shared driver replaces
    // that recursion with an explicit two-color stack (mirrors term.zig's
    // `rebuildWalk`): a node is first EXPANDED (its Formula children pushed
    // deeper), then on its second pop REBUILT from the child results already on a
    // results stack. Only conj/disj/quant have Formula children; every other kind
    // is a leaf as far as the tree walk is concerned (its Linear payload is not a
    // Formula). The comptime `Visitor` supplies:
    //   - `leaf(v, self, f) !?*const Formula` — a result WITHOUT descending (for
    //     tru/fls/ge/div/ndiv, and any interior node it wants to short-circuit);
    //     null = descend and rebuild.
    //   - `rebuild(v, self, f, kids) !*const Formula` — reassemble conj/disj (2
    //     kids) or quant (1 kid) from its rebuilt children, in original order.

    fn formulaChildren(f: *const Formula) usize {
        return switch (f.*) {
            .tru, .fls, .ge, .div, .ndiv => 0,
            .conj, .disj => 2,
            .quant => 1,
        };
    }

    fn rebuildFormula(self: *Ctx, root: *const Formula, visitor: anytype) Error!*const Formula {
        var fb = std.heap.stackFallback(128 * @sizeOf(RebuildFrame), self.arena);
        const a = fb.get();
        var work: std.ArrayList(RebuildFrame) = .empty;
        defer work.deinit(a);
        var results: std.ArrayList(*const Formula) = .empty;
        defer results.deinit(a);

        try work.append(a, .{ .f = root, .expanded = false });
        while (work.pop()) |frame| {
            if (!frame.expanded) {
                if (try visitor.leaf(self, frame.f)) |r| {
                    try results.append(a, r);
                    continue;
                }
                try work.append(a, .{ .f = frame.f, .expanded = true });
                // push children in REVERSE so child 0 is processed first and its
                // result lands first on `results` (rebuild reads original order).
                switch (frame.f.*) {
                    .conj, .disj => |p| {
                        try work.append(a, .{ .f = p.rhs, .expanded = false });
                        try work.append(a, .{ .f = p.lhs, .expanded = false });
                    },
                    .quant => |q| try work.append(a, .{ .f = q.body, .expanded = false }),
                    else => unreachable, // leaf returned null only for interior nodes
                }
            } else {
                const n = formulaChildren(frame.f);
                const kids = results.items[results.items.len - n ..];
                const rebuilt = try visitor.rebuild(self, frame.f, kids);
                results.items.len -= n;
                try results.append(a, rebuilt);
            }
        }
        return results.items[0];
    }

    const RebuildFrame = struct { f: *const Formula, expanded: bool };

    // --- quantifier elimination (Cooper's algorithm) ---

    const EliminateVisitor = struct {
        fn leaf(_: EliminateVisitor, _: *Ctx, f: *const Formula) Error!?*const Formula {
            return switch (f.*) {
                .tru, .fls, .ge, .div, .ndiv => f,
                .conj, .disj, .quant => null,
            };
        }
        fn rebuild(_: EliminateVisitor, self: *Ctx, f: *const Formula, kids: []const *const Formula) Error!*const Formula {
            return switch (f.*) {
                .conj => self.node(.{ .conj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                .disj => self.node(.{ .disj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                .quant => |q| switch (q.q) {
                    // kids[0] is the already-eliminated body (post-order guarantees it)
                    .exists => self.cooper(q.v, kids[0]),
                    .forall => self.negate(try self.cooper(q.v, try self.negate(kids[0]))),
                },
                else => unreachable,
            };
        }
    };

    fn eliminate(self: *Ctx, f: *const Formula) Error!*const Formula {
        return self.rebuildFormula(f, EliminateVisitor{});
    }

    const NegateVisitor = struct {
        fn leaf(_: NegateVisitor, self: *Ctx, f: *const Formula) Error!?*const Formula {
            return switch (f.*) {
                .tru => try self.node(.fls),
                .fls => try self.node(.tru),
                // not(L >= 0) is -L - 1 >= 0
                .ge => |l| try self.node(.{ .ge = try self.shifted(try self.negated(l), -1) }),
                .div => |d| try self.node(.{ .ndiv = d }),
                .ndiv => |d| try self.node(.{ .div = d }),
                .conj, .disj => null,
                .quant => unreachable, // negate only runs on eliminated bodies
            };
        }
        fn rebuild(_: NegateVisitor, self: *Ctx, f: *const Formula, kids: []const *const Formula) Error!*const Formula {
            // conj negates to disj and vice versa
            return switch (f.*) {
                .conj => self.node(.{ .disj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                .disj => self.node(.{ .conj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                else => unreachable,
            };
        }
    };

    fn negate(self: *Ctx, f: *const Formula) Error!*const Formula {
        return self.rebuildFormula(f, NegateVisitor{});
    }

    fn lcmC(self: *Ctx, a: i128, b: i128) Error!i128 {
        const ua: u128 = @abs(a);
        const ub: u128 = @abs(b);
        const g = std.math.gcd(ua, ub);
        const left = std.math.cast(i128, ua / g) orelse return self.fail(.overflow);
        const right = std.math.cast(i128, ub) orelse return self.fail(.overflow);
        return self.mulC(left, right);
    }

    /// Iterative work-stack over the (negation-free) formula tree (was native
    /// recursion): the accumulator is an LCM fold, so visit order is irrelevant.
    fn coefficientLcm(self: *Ctx, f: *const Formula, v: u32, delta: *i128) Error!void {
        var fb = std.heap.stackFallback(64 * @sizeOf(*const Formula), self.arena);
        const a = fb.get();
        var stack: std.ArrayList(*const Formula) = .empty;
        defer stack.deinit(a);
        try stack.append(a, f);
        while (stack.pop()) |cur| {
            switch (cur.*) {
                .tru, .fls => {},
                .ge => |l| if (l.coeffs[v] != 0) {
                    delta.* = try self.lcmC(delta.*, l.coeffs[v]);
                },
                .div, .ndiv => |d| if (d.linear.coeffs[v] != 0) {
                    delta.* = try self.lcmC(delta.*, d.linear.coeffs[v]);
                },
                .conj, .disj => |p| {
                    try stack.append(a, p.lhs);
                    try stack.append(a, p.rhs);
                },
                .quant => unreachable, // innermost-first elimination
            }
        }
    }

    /// Scale every atom so v's coefficient becomes +-1 in y-space (y = delta
    /// * v, recorded by conjoining delta | y at the call site). Iterative
    /// two-color rebuild (was native recursion) — see `rebuildFormula`.
    fn normalized(self: *Ctx, f: *const Formula, v: u32, delta: i128) Error!*const Formula {
        return self.rebuildFormula(f, NormalizedVisitor{ .v = v, .delta = delta });
    }

    const NormalizedVisitor = struct {
        v: u32,
        delta: i128,
        fn leaf(vis: NormalizedVisitor, self: *Ctx, f: *const Formula) Error!?*const Formula {
            switch (f.*) {
                .tru, .fls => return f,
                .ge => |l| {
                    const a = l.coeffs[vis.v];
                    if (a == 0) return f;
                    const m = @divExact(vis.delta, @as(i128, @intCast(@abs(a))));
                    var out = try self.combine(try self.blank(), m, l);
                    out.coeffs[vis.v] = if (a > 0) 1 else -1;
                    return try self.node(.{ .ge = out });
                },
                .div, .ndiv => |d| {
                    const a = d.linear.coeffs[vis.v];
                    if (a == 0) return f;
                    const m = @divExact(vis.delta, @as(i128, @intCast(@abs(a))));
                    // divisibility is sign-blind: normalize the coefficient to +1
                    var out = try self.combine(try self.blank(), if (a > 0) m else -m, d.linear);
                    out.coeffs[vis.v] = 1;
                    const scaled: Formula.Div = .{ .modulus = try self.mulC(d.modulus, m), .linear = out };
                    return try self.node(if (f.* == .div) .{ .div = scaled } else .{ .ndiv = scaled });
                },
                .conj, .disj => return null,
                .quant => unreachable,
            }
        }
        fn rebuild(_: NormalizedVisitor, self: *Ctx, f: *const Formula, kids: []const *const Formula) Error!*const Formula {
            return switch (f.*) {
                .conj => self.node(.{ .conj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                .disj => self.node(.{ .disj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                else => unreachable,
            };
        }
    };

    /// Iterative work-stack over the formula tree (was native recursion): an LCM
    /// fold over the divisibility atoms, so visit order is irrelevant.
    fn modulusLcm(self: *Ctx, f: *const Formula, v: u32, d: *i128) Error!void {
        var fb = std.heap.stackFallback(64 * @sizeOf(*const Formula), self.arena);
        const a = fb.get();
        var stack: std.ArrayList(*const Formula) = .empty;
        defer stack.deinit(a);
        try stack.append(a, f);
        while (stack.pop()) |cur| {
            switch (cur.*) {
                .tru, .fls, .ge => {},
                .div, .ndiv => |x| if (x.linear.coeffs[v] != 0) {
                    d.* = try self.lcmC(d.*, x.modulus);
                },
                .conj, .disj => |p| {
                    try stack.append(a, p.lhs);
                    try stack.append(a, p.rhs);
                },
                .quant => unreachable,
            }
        }
    }

    /// Boundary terms: each lower bound y + t >= 0 confines a satisfying y
    /// to start at b = -t - 1 (exclusive); Cooper's disjunction probes b + j.
    /// Iterative work-stack over the formula tree (was native recursion). Boundary
    /// APPEND ORDER is load-bearing (a boundary's index feeds the certificate
    /// replay), so it must match the original left-to-right, depth-first visit:
    /// push the right child BEFORE the left so the left pops (and appends) first.
    fn boundaries(self: *Ctx, f: *const Formula, v: u32, out: *std.ArrayList(Linear)) Error!void {
        var fb = std.heap.stackFallback(64 * @sizeOf(*const Formula), self.arena);
        const a = fb.get();
        var stack: std.ArrayList(*const Formula) = .empty;
        defer stack.deinit(a);
        try stack.append(a, f);
        while (stack.pop()) |cur| {
            switch (cur.*) {
                .tru, .fls, .div, .ndiv => {},
                .ge => |l| if (l.coeffs[v] == 1) {
                    var b = try self.negated(l);
                    b.coeffs[v] = 0;
                    b.konst = try self.addC(b.konst, -1);
                    try out.append(self.arena, b);
                },
                .conj, .disj => |p| {
                    try stack.append(a, p.rhs);
                    try stack.append(a, p.lhs);
                },
                .quant => unreachable,
            }
        }
    }

    fn spend(self: *Ctx) Error!void {
        if (self.budget == 0) return self.fail(.too_large);
        self.budget -= 1;
    }

    /// Substitute y := s (s has no y component) through the formula. Iterative
    /// two-color rebuild (was native recursion). `spend()` fires once per affected
    /// atom exactly as before; the total is order-independent (it only decrements a
    /// shared budget), so the too_large verdict is unchanged.
    fn subst(self: *Ctx, f: *const Formula, v: u32, s: Linear) Error!*const Formula {
        return self.rebuildFormula(f, SubstVisitor{ .v = v, .s = s });
    }

    const SubstVisitor = struct {
        v: u32,
        s: Linear,
        fn leaf(vis: SubstVisitor, self: *Ctx, f: *const Formula) Error!?*const Formula {
            switch (f.*) {
                .tru, .fls => return f,
                .ge => |l| {
                    const c = l.coeffs[vis.v];
                    if (c == 0) return f;
                    try self.spend();
                    var out = try self.combine(l, c, vis.s);
                    out.coeffs[vis.v] = 0;
                    return try self.node(.{ .ge = out });
                },
                .div, .ndiv => |d| {
                    if (d.linear.coeffs[vis.v] == 0) return f;
                    try self.spend();
                    var out = try self.combine(d.linear, 1, vis.s);
                    out.coeffs[vis.v] = 0;
                    const sub: Formula.Div = .{ .modulus = d.modulus, .linear = out };
                    return try self.node(if (f.* == .div) .{ .div = sub } else .{ .ndiv = sub });
                },
                .conj, .disj => return null,
                .quant => unreachable,
            }
        }
        fn rebuild(_: SubstVisitor, self: *Ctx, f: *const Formula, kids: []const *const Formula) Error!*const Formula {
            return switch (f.*) {
                .conj => self.node(.{ .conj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                .disj => self.node(.{ .disj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                else => unreachable,
            };
        }
    };

    /// The minus-infinity residue: lower bounds fail, upper bounds hold, and
    /// only the periodic (divisibility) atoms see y := j. Iterative two-color
    /// rebuild (was native recursion). `spend()` is order-independent (see subst).
    fn substInf(self: *Ctx, f: *const Formula, v: u32, j: i128) Error!*const Formula {
        return self.rebuildFormula(f, SubstInfVisitor{ .v = v, .j = j });
    }

    const SubstInfVisitor = struct {
        v: u32,
        j: i128,
        fn leaf(vis: SubstInfVisitor, self: *Ctx, f: *const Formula) Error!?*const Formula {
            switch (f.*) {
                .tru, .fls => return f,
                .ge => |l| return switch (l.coeffs[vis.v]) {
                    0 => f,
                    1 => try self.node(.fls),
                    else => try self.node(.tru), // -1: upper bound
                },
                .div, .ndiv => |d| {
                    if (d.linear.coeffs[vis.v] == 0) return f;
                    try self.spend();
                    var out: Linear = .{ .coeffs = try self.arena.dupe(i128, d.linear.coeffs), .konst = try self.addC(d.linear.konst, vis.j) };
                    out.coeffs[vis.v] = 0;
                    const sub: Formula.Div = .{ .modulus = d.modulus, .linear = out };
                    return try self.node(if (f.* == .div) .{ .div = sub } else .{ .ndiv = sub });
                },
                .conj, .disj => return null,
                .quant => unreachable,
            }
        }
        fn rebuild(_: SubstInfVisitor, self: *Ctx, f: *const Formula, kids: []const *const Formula) Error!*const Formula {
            return switch (f.*) {
                .conj => self.node(.{ .conj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                .disj => self.node(.{ .disj = .{ .lhs = kids[0], .rhs = kids[1] } }),
                else => unreachable,
            };
        }
    };

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

    /// Evaluate a ground (variable-free) formula. Iterative two-color post-order
    /// (was native recursion): a node is first EXPANDED (children pushed), then on
    /// its second pop COMBINED from the two child booleans already on `vals`.
    /// and/or are computed strictly (both children evaluated) — over
    /// side-effect-free evaluation this is identical to the original short-circuit
    /// `and`/`or` over recursive calls. OOM now propagates (was infallible), which
    /// only the unreachable true-OOM path can trigger; callers already handle it.
    fn evalGround(self: *Ctx, root: *const Formula) Error!bool {
        return self.evalFormula(root, &.{});
    }

    fn evalAt(self: *Ctx, root: *const Formula, values: []const i128) Error!bool {
        return self.evalFormula(root, values);
    }

    const EvalFrame = struct { f: *const Formula, expanded: bool };

    /// Shared iterative evaluator for `evalGround` (values = &.{}) and `evalAt`.
    /// A leaf's truth is computed directly; conj/disj pop their two child results.
    fn evalFormula(self: *Ctx, root: *const Formula, values: []const i128) Error!bool {
        var fb = std.heap.stackFallback(128 * @sizeOf(EvalFrame), self.arena);
        const a = fb.get();
        var work: std.ArrayList(EvalFrame) = .empty;
        defer work.deinit(a);
        var vals: std.ArrayList(bool) = .empty;
        defer vals.deinit(a);
        try work.append(a, .{ .f = root, .expanded = false });
        while (work.pop()) |frame| {
            switch (frame.f.*) {
                .tru => try vals.append(a, true),
                .fls => try vals.append(a, false),
                .ge => |l| try vals.append(a, atValue(l, values) >= 0),
                .div => |d| try vals.append(a, @mod(atValue(d.linear, values), @as(i256, d.modulus)) == 0),
                .ndiv => |d| try vals.append(a, @mod(atValue(d.linear, values), @as(i256, d.modulus)) != 0),
                .conj, .disj => |p| {
                    if (!frame.expanded) {
                        try work.append(a, .{ .f = frame.f, .expanded = true });
                        try work.append(a, .{ .f = p.lhs, .expanded = false });
                        try work.append(a, .{ .f = p.rhs, .expanded = false });
                    } else {
                        // both children are on `vals`; a strict and/or is
                        // order-insensitive, so which was popped first is immaterial.
                        const b = vals.pop().?;
                        const c = vals.pop().?;
                        try vals.append(a, if (frame.f.* == .conj) (b and c) else (b or c));
                    }
                },
                .quant => unreachable,
            }
        }
        return vals.items[0];
    }

    /// Value of a linear form under `values` (empty = ground: only the constant,
    /// since a ground formula's coefficients are all eliminated).
    fn atValue(l: Linear, values: []const i128) i256 {
        if (values.len == 0) return l.konst;
        return valueOf(l, values);
    }

    fn valueOf(l: Linear, values: []const i128) i256 {
        var acc: i256 = l.konst;
        for (l.coeffs, values) |c, x| acc += @as(i256, c) * @as(i256, x);
        return acc;
    }

    /// Depth-first search of small nonnegative values for the free variables,
    /// smallest per variable first. Was native recursion nesting one loop per free
    /// variable (depth = number of free vars); rewritten as an explicit odometer
    /// over the levels. `cap` is constant across the whole search (it depends only
    /// on the free-var count), so it is computed once. Enumeration order is
    /// preserved: level 0 is the outermost loop, incremented last.
    fn witness(self: *Ctx, f: *const Formula, values: []i128) Error!bool {
        const n = self.free_vars.items.len;
        if (n == 0) return self.evalAt(f, values);
        const total = std.math.powi(usize, witness_bound + 1, n) catch witness_combinations + 1;
        const cap: i128 = if (total > witness_combinations) 8 else witness_bound;

        // xs[level] is the current trial value at that level; start the whole
        // vector at 0 (matches the recursion's first descent to all-zero).
        var fb = std.heap.stackFallback(64 * @sizeOf(i128), self.arena);
        const a = fb.get();
        const xs = try a.alloc(i128, n);
        defer a.free(xs);
        @memset(xs, 0);
        for (0..n) |level| values[self.free_vars.items[level].id] = 0;

        while (true) {
            if (try self.evalAt(f, values)) return true;
            // advance the odometer: increment the DEEPEST level first (level n-1),
            // carrying to shallower levels — this reproduces the nested-loop order
            // where the innermost variable varies fastest.
            var level: usize = n;
            while (level > 0) {
                level -= 1;
                if (xs[level] < cap) {
                    xs[level] += 1;
                    values[self.free_vars.items[level].id] = xs[level];
                    break;
                }
                // this level rolled over: reset it and carry to the next-shallower
                xs[level] = 0;
                values[self.free_vars.items[level].id] = 0;
                if (level == 0) return false; // all levels exhausted
            }
        }
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
            .pool = .init(arena, arena),
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
