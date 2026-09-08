//! Propositional tautology decider — the pure boolean core of the `tautology`
//! accelerant (surface rule `tautology`; registry entry in ACCELERATION.md).
//!
//! This is the DECISION half: it settles whether a goal follows propositionally
//! from its premises (a real, cheap oracle) and, on a non-consequence, hands back
//! a countermodel. The strict PROOF half — replaying the truth search as a
//! kernel-checked natural-deduction certificate — lives in `Prove.zig`'s
//! `produceTautology` (it consumes `collectAtoms`/`eval` from here).
//!
//! Engine: atoms are the maximal subformulas that are not and/or/not/implies
//! (predicates, equations, quantified formulas — all opaque). The decision is a
//! recursive truth search for a model of premises AND not(goal): three-valued
//! (Kleene) evaluation prunes decided branches, splitting on the first
//! undetermined atom (DPLL in the original no-clause-form sense). Sound and
//! complete over the atoms; the hard cap keeps the worst case tiny.
//!
//! DEMAND-ENGINE PROVENANCE: recovered from the W5-dropped `src/accelerant/
//! arithmetic/smt.zig`, trimmed to the pure-propositional surface. The mixed
//! DPLL(T) combination (`decideMixed`/`Mixed`) and its Presburger theory calls
//! are NOT ported here — they return with the arithmetic accelerant (a later
//! slice); this file has no theory dependency.

const std = @import("std");
const Allocator = std.mem.Allocator;
const term = @import("../../term.zig");
const TermId = term.TermId;
const Pool = term.Pool;
const presburger = @import("presburger.zig");

pub const atom_limit = 16;

pub const Verdict = union(enum) {
    /// premises AND not(goal) is unsatisfiable: the goal follows
    valid,
    /// a satisfying assignment of premises AND not(goal), in atom
    /// discovery order (premises left to right, then the goal)
    countermodel: []const Lit,
    /// the distinct-atom count, past atom_limit
    too_many_atoms: usize,
};

pub const Lit = struct { atom: TermId, value: bool };

/// Decide whether `goal` follows propositionally from `premises`.
pub fn tautology(arena: Allocator, pool: *const Pool, premises: []const TermId, goal: TermId) Allocator.Error!Verdict {
    var atoms: std.ArrayList(TermId) = .empty;
    for (premises) |p| try collectAtoms(arena, pool, &atoms, p);
    try collectAtoms(arena, pool, &atoms, goal);
    if (atoms.items.len > atom_limit) return .{ .too_many_atoms = atoms.items.len };

    var assignment = [_]?bool{null} ** atom_limit;
    if (search(pool, atoms.items, premises, goal, assignment[0..atoms.items.len])) {
        const lits = try arena.alloc(Lit, atoms.items.len);
        for (atoms.items, assignment[0..atoms.items.len], lits) |atom, value, *lit| {
            // an atom left undetermined cannot affect the verdict: any value
            // completes the model (three-valued truth is monotone)
            lit.* = .{ .atom = atom, .value = value orelse false };
        }
        return .{ .countermodel = lits };
    }
    return .valid;
}

pub fn collectAtoms(arena: Allocator, pool: *const Pool, atoms: *std.ArrayList(TermId), f: TermId) Allocator.Error!void {
    switch (pool.get(f)) {
        .bin => |b| {
            try collectAtoms(arena, pool, atoms, b.lhs);
            try collectAtoms(arena, pool, atoms, b.rhs);
        },
        .not => |inner| try collectAtoms(arena, pool, atoms, inner),
        else => {
            for (atoms.items) |a| {
                if (pool.alphaEq(a, f)) return;
            }
            try atoms.append(arena, f);
        },
    }
}

fn atomIndex(pool: *const Pool, atoms: []const TermId, f: TermId) usize {
    for (atoms, 0..) |a, i| {
        if (pool.alphaEq(a, f)) return i;
    }
    unreachable; // collectAtoms visited every leaf
}

/// Three-valued (Kleene) evaluation: null = undetermined under the partial
/// assignment. A non-null result holds under EVERY completion. (Public for
/// the certificate emitter, which replays this evaluation as kernel steps.)
pub fn eval(pool: *const Pool, atoms: []const TermId, assignment: []const ?bool, f: TermId) ?bool {
    switch (pool.get(f)) {
        .not => |inner| {
            const v = eval(pool, atoms, assignment, inner) orelse return null;
            return !v;
        },
        .bin => |b| {
            const l = eval(pool, atoms, assignment, b.lhs);
            const r = eval(pool, atoms, assignment, b.rhs);
            return switch (b.op) {
                .and_op => if (l == false or r == false) false else if (l == true and r == true) true else null,
                .or_op => if (l == true or r == true) true else if (l == false and r == false) false else null,
                .implies => if (l == false or r == true) true else if (l == true and r == false) false else null,
            };
        },
        else => return assignment[atomIndex(pool, atoms, f)],
    }
}

/// Is there an assignment making every premise true and the goal false?
/// On success the (possibly partial) model is left in `assignment`.
fn search(pool: *const Pool, atoms: []const TermId, premises: []const TermId, goal: TermId, assignment: []?bool) bool {
    var decided = true;
    for (premises) |p| {
        if (eval(pool, atoms, assignment, p)) |v| {
            if (!v) return false; // a premise is refuted: dead branch
        } else {
            decided = false;
        }
    }
    if (eval(pool, atoms, assignment, goal)) |g| {
        if (g) return false; // the goal holds: this branch cannot falsify it
    } else {
        decided = false;
    }
    if (decided) return true;
    // split on the first undetermined atom (one exists: something was null)
    const i = for (assignment, 0..) |v, i| {
        if (v == null) break i;
    } else unreachable;
    assignment[i] = true;
    if (search(pool, atoms, premises, goal, assignment)) return true;
    assignment[i] = false;
    if (search(pool, atoms, premises, goal, assignment)) return true;
    assignment[i] = null;
    return false;
}

// --- mixed propositional + linear-arithmetic decision (the arithmetic accelerant's SMT core) ---

pub const theory_call_limit = 2000;

pub const MixedVerdict = union(enum) {
    valid,
    countermodel: Counter,
    too_many_atoms: usize,
    too_large,
    overflow,

    pub const Counter = struct {
        /// truth values of the opaque atoms in the falsifying model
        opaques: []const Lit,
        /// small values for the arithmetic variables
        values: []const presburger.Assignment,
        /// false when the theory side is satisfiable but the bounded search
        /// found no small values to display
        values_found: bool,
    };
};

/// Decide whether `goal` follows from `premises` in the combination of
/// propositional logic and linear arithmetic.
pub fn decideMixed(arena: Allocator, pool: *Pool, symbols: presburger.Symbols, premises: []const TermId, goal: TermId) Allocator.Error!MixedVerdict {
    var atoms: std.ArrayList(TermId) = .empty;
    for (premises) |p| try collectAtoms(arena, pool, &atoms, p);
    try collectAtoms(arena, pool, &atoms, goal);
    if (atoms.items.len > atom_limit) return .{ .too_many_atoms = atoms.items.len };

    const is_theory = try arena.alloc(bool, atoms.items.len);
    for (atoms.items, is_theory) |a, *k| k.* = try presburger.inFragment(arena, pool, symbols, a);

    var ctx: Mixed = .{
        .arena = arena,
        .pool = pool,
        .symbols = symbols,
        .atoms = atoms.items,
        .is_theory = is_theory,
        .premises = premises,
        .goal = goal,
    };
    var assignment = [_]?bool{null} ** atom_limit;
    const found = ctx.search(assignment[0..atoms.items.len]) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Fail => return ctx.err.?,
    };
    if (!found) return .valid;

    var opaques: std.ArrayList(Lit) = .empty;
    for (atoms.items, is_theory, assignment[0..atoms.items.len]) |a, th, v| {
        if (!th) try opaques.append(arena, .{ .atom = a, .value = v orelse false });
    }
    return .{ .countermodel = .{
        .opaques = opaques.items,
        .values = ctx.values,
        .values_found = ctx.values_found,
    } };
}

const Mixed = struct {
    arena: Allocator,
    pool: *Pool,
    symbols: presburger.Symbols,
    atoms: []const TermId,
    is_theory: []const bool,
    premises: []const TermId,
    goal: TermId,
    theory_calls: usize = 0,
    values: []const presburger.Assignment = &.{},
    values_found: bool = true,
    err: ?MixedVerdict = null,

    const Error = error{ Fail, OutOfMemory };

    /// Like the propositional `search`, but a decided skeleton model must
    /// also survive the theory check to count.
    fn search(self: *Mixed, assignment: []?bool) Error!bool {
        var decided = true;
        for (self.premises) |p| {
            if (eval(self.pool, self.atoms, assignment, p)) |v| {
                if (!v) return false;
            } else {
                decided = false;
            }
        }
        if (eval(self.pool, self.atoms, assignment, self.goal)) |g| {
            if (g) return false;
        } else {
            decided = false;
        }
        if (decided) return self.theoryCheck(assignment);
        const i = for (assignment, 0..) |v, i| {
            if (v == null) break i;
        } else unreachable;
        assignment[i] = true;
        if (try self.search(assignment)) return true;
        assignment[i] = false;
        if (try self.search(assignment)) return true;
        assignment[i] = null;
        return false;
    }

    fn theoryCheck(self: *Mixed, assignment: []const ?bool) Error!bool {
        var literals: std.ArrayList(TermId) = .empty;
        for (self.atoms, self.is_theory, assignment) |a, th, v| {
            if (!th) continue;
            const value = v orelse continue; // undetermined: unconstrained
            try literals.append(self.arena, if (value) a else try self.pool.add(.{ .not = a }));
        }
        if (literals.items.len == 0) return true; // purely boolean model
        if (self.theory_calls == theory_call_limit) {
            self.err = .too_large;
            return error.Fail;
        }
        self.theory_calls += 1;
        const result = presburger.satisfiable(self.arena, self.pool, self.symbols, literals.items) catch return error.OutOfMemory;
        switch (result) {
            .unsat => return false, // theory refutes this skeleton model
            .sat => |values| {
                self.values = values;
                return true;
            },
            .sat_no_witness => {
                self.values_found = false;
                return true;
            },
            // atoms were classified with the same compiler that runs here
            .out_of_fragment => unreachable,
            .too_large => {
                self.err = .too_large;
                return error.Fail;
            },
            .overflow => {
                self.err = .overflow;
                return error.Fail;
            },
        }
    }
};

// --- tests ---

const testing = std.testing;

const Rig = struct {
    pool: Pool,

    fn init(arena: Allocator) Rig {
        return .{ .pool = .init(arena, arena) };
    }

    /// nth 0-ary predicate atom
    fn atom(self: *Rig, n: u32) !TermId {
        return self.pool.addApp(.pred, @enumFromInt(n), &.{});
    }

    fn implies(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.add(.{ .bin = .{ .op = .implies, .lhs = l, .rhs = r } });
    }

    fn orOp(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.add(.{ .bin = .{ .op = .or_op, .lhs = l, .rhs = r } });
    }

    fn andOp(self: *Rig, l: TermId, r: TermId) !TermId {
        return self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = l, .rhs = r } });
    }

    fn notOp(self: *Rig, t: TermId) !TermId {
        return self.pool.add(.{ .not = t });
    }
};

test "pierce's law is valid" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const p = try r.atom(0);
    const q = try r.atom(1);
    // ((p -> q) -> p) -> p
    const pierce = try r.implies(try r.implies(try r.implies(p, q), p), p);
    const v = try tautology(arena_state.allocator(), &r.pool, &.{}, pierce);
    try testing.expect(v == .valid);
}

test "p -> q has the countermodel p := true, q := false" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const p = try r.atom(0);
    const q = try r.atom(1);
    const v = try tautology(arena_state.allocator(), &r.pool, &.{}, try r.implies(p, q));
    try testing.expect(v == .countermodel);
    try testing.expectEqual(2, v.countermodel.len);
    try testing.expectEqual(true, v.countermodel[0].value); // p
    try testing.expectEqual(false, v.countermodel[1].value); // q
}

test "modus ponens as consequence: {p, p -> q} |= q" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const p = try r.atom(0);
    const q = try r.atom(1);
    const v = try tautology(arena_state.allocator(), &r.pool, &.{ p, try r.implies(p, q) }, q);
    try testing.expect(v == .valid);
}

test "de morgan: not (p or q) -> (not p and not q)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const p = try r.atom(0);
    const q = try r.atom(1);
    const f = try r.implies(
        try r.notOp(try r.orOp(p, q)),
        try r.andOp(try r.notOp(p), try r.notOp(q)),
    );
    const v = try tautology(arena_state.allocator(), &r.pool, &.{}, f);
    try testing.expect(v == .valid);
}

test "seventeen distinct atoms overflow the cap" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    var f = try r.atom(0);
    for (1..17) |n| f = try r.orOp(f, try r.atom(@intCast(n)));
    const v = try tautology(arena_state.allocator(), &r.pool, &.{}, f);
    try testing.expectEqual(Verdict{ .too_many_atoms = 17 }, v);
}

test "alpha-equivalent quantified subformulas are one atom" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    // (forall x; p(x)) -> (forall y; p(y)) — same atom, hence valid
    const nat: term.SortId = @enumFromInt(1);
    const b0 = try r.pool.add(.{ .bvar = 0 });
    const px = try r.pool.addApp(.pred, @enumFromInt(0), &.{b0});
    const hint_x: @import("../../InternPool.zig").StrId = @enumFromInt(1);
    const hint_y: @import("../../InternPool.zig").StrId = @enumFromInt(2);
    const qx = try r.pool.add(.{ .quant = .{ .q = .forall, .sort = nat, .hint = hint_x, .body = px } });
    const qy = try r.pool.add(.{ .quant = .{ .q = .forall, .sort = nat, .hint = hint_y, .body = px } });
    const v = try tautology(arena_state.allocator(), &r.pool, &.{}, try r.implies(qx, qy));
    try testing.expect(v == .valid);
}

test "mixed skeleton: theory literals decide, opaque atoms report" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var r = Rig.init(arena_state.allocator());
    const nat: term.SortId = @enumFromInt(1);
    const sym_succ: term.SymId = @enumFromInt(10);
    const sym_less: term.SymId = @enumFromInt(11);
    const symbols: presburger.Symbols = .{ .nat = nat, .succ = sym_succ, .less_than = sym_less };
    const p = try r.atom(0);
    const a = try r.pool.add(.{ .fvar = .{ .name = @enumFromInt(1), .sort = nat } });
    const succ_a = try r.pool.addApp(.app, sym_succ, &.{a});

    // p or a < succ(a): the theory refutes every skeleton model
    const holds = try r.orOp(p, try r.pool.addApp(.pred, sym_less, &.{ a, succ_a }));
    const valid = try decideMixed(arena_state.allocator(), &r.pool, symbols, &.{}, holds);
    try testing.expect(valid == .valid);

    // p or succ(a) < a: countermodel mixes a value and an opaque atom
    const fails = try r.orOp(p, try r.pool.addApp(.pred, sym_less, &.{ succ_a, a }));
    const bad = try decideMixed(arena_state.allocator(), &r.pool, symbols, &.{}, fails);
    try testing.expect(bad == .countermodel);
    try testing.expectEqual(1, bad.countermodel.opaques.len);
    try testing.expectEqual(false, bad.countermodel.opaques[0].value);
    try testing.expectEqual(1, bad.countermodel.values.len);
    try testing.expectEqual(0, bad.countermodel.values[0].value);
}
