//! The `simplify` tactic engine: first-order matching and innermost
//! rewriting over kernel terms.
//!
//! PURE, certificate-producing from day one — this module only computes the
//! normal forms and the rewrite trace; the elaborator turns the trace into
//! ordinary kernel steps (reflexivity / forall_elim / rewrite) that the
//! kernel checks like hand-written ones. Nothing here is trusted.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const env_mod = @import("env.zig");
const Env = env_mod.Env;
const StatementId = env_mod.StatementId;
const kernel = @import("kernel.zig");

/// A rewrite rule prepared from a (possibly forall-prefixed) equation,
/// oriented left -> right. Binders are opened as fresh pattern fvars
/// ('#'-names, unlexable, so they can never collide with proof terms).
pub const Rule = struct {
    source: Source,
    /// outermost-first, matching the forall nesting of `formula`
    binders: []const Binder,
    lhs: TermId,
    rhs: TermId,
    /// the full quantified formula (cited when emitting the certificate)
    formula: TermId,
};

pub const Binder = struct { fvar: StrId, sort: SortId };

pub const Source = union(enum) {
    axiom: struct { id: StatementId, loc: u32 },
    theorem: struct { id: StatementId, loc: u32 },
    /// an equation already proven as a step in the current proof
    step: kernel.SRef,
};

/// One rewrite: the whole term before/after, and the rule instance that
/// licensed it (equation inst_lhs = inst_rhs at the matched bindings).
pub const Rewrite = struct {
    before: TermId,
    after: TermId,
    rule_idx: usize,
    /// one per rule binder, outermost-first
    bindings: []const TermId,
    inst_lhs: TermId,
    inst_rhs: TermId,
};

pub const Result = struct {
    nf: TermId,
    trace: []const Rewrite,
};

pub const Error = error{ Limit, OutOfMemory };

/// Rewrite `start` with `rules` (in citation order, innermost-leftmost) to a
/// fixpoint, recording every rewrite. `cap` bounds total rewrites.
pub fn normalize(
    arena: Allocator,
    pool: *term.Pool,
    environment: *const Env,
    rules: []const Rule,
    start: TermId,
    cap: usize,
) Error!Result {
    var trace: std.ArrayList(Rewrite) = .empty;
    var current = start;
    while (try findRewrite(arena, pool, environment, rules, current)) |rw| {
        if (trace.items.len >= cap) return error.Limit;
        try trace.append(arena, rw);
        current = rw.after;
    }
    return .{ .nf = current, .trace = trace.items };
}

/// Find the innermost-leftmost rewrite in `t`, or null at normal form.
/// Returns the rewritten version of `t` plus the licensing instance.
fn findRewrite(
    arena: Allocator,
    pool: *term.Pool,
    environment: *const Env,
    rules: []const Rule,
    t: TermId,
) Error!?Rewrite {
    // children first (innermost)
    switch (pool.get(t)) {
        .app => |a| {
            // pool.args() aliases the pool's extra buffer, which the
            // recursive calls below may grow (poisoning the old buffer) —
            // copy the ids out first
            const args = try arena.dupe(TermId, pool.args(a));
            for (args, 0..) |arg, i| {
                if (try findRewrite(arena, pool, environment, rules, arg)) |child| {
                    const new_args = try arena.dupe(TermId, args);
                    new_args[i] = child.after;
                    const rebuilt = try pool.addApp(.app, a.sym, new_args);
                    return .{
                        .before = t,
                        .after = rebuilt,
                        .rule_idx = child.rule_idx,
                        .bindings = child.bindings,
                        .inst_lhs = child.inst_lhs,
                        .inst_rhs = child.inst_rhs,
                    };
                }
            }
        },
        else => {},
    }
    // then this position, rules in citation order
    for (rules, 0..) |rule, ri| {
        const bound = try arena.alloc(?TermId, rule.binders.len);
        @memset(bound, null);
        if (matchPattern(pool, environment, rule, rule.lhs, t, bound)) {
            const bindings = try arena.alloc(TermId, rule.binders.len);
            for (bound, bindings) |b, *out| out.* = b.?; // prep guarantees all binders occur in lhs
            var inst_rhs = rule.rhs;
            for (rule.binders, bindings) |b, val| {
                inst_rhs = try pool.substFvar(inst_rhs, b.fvar, val);
            }
            return .{
                .before = t,
                .after = inst_rhs,
                .rule_idx = ri,
                .bindings = bindings,
                .inst_lhs = t,
                .inst_rhs = inst_rhs,
            };
        }
    }
    return null;
}

/// One-way syntactic match of `pattern` (rule binders = wildcards) against
/// `t`, with consistent bindings and sort checks. Handles formula structure
/// too (certificate emitters match whole rule bodies), but not binders:
/// quantified patterns never match.
fn matchPattern(
    pool: *term.Pool,
    environment: *const Env,
    rule: Rule,
    pattern: TermId,
    t: TermId,
    bound: []?TermId,
) bool {
    switch (pool.get(pattern)) {
        .fvar => |v| {
            if (binderIndex(rule, v.name)) |i| {
                if (bound[i]) |prev| return pool.alphaEq(prev, t);
                if (termSort(pool, environment, t) != v.sort) return false;
                // a binding must be locally closed: a loose bound variable
                // would escape its binder through the instantiation
                if (looseBvar(pool, t, 0)) return false;
                bound[i] = t;
                return true;
            }
            // a constant fvar from the enclosing scope: exact occurrence only
            const tn = pool.get(t);
            return tn == .fvar and tn.fvar.name == v.name;
        },
        .bvar => |i| {
            const tn = pool.get(t);
            return tn == .bvar and tn.bvar == i;
        },
        .quant => |q| {
            const tn = pool.get(t);
            return tn == .quant and tn.quant.q == q.q and tn.quant.sort == q.sort and
                matchPattern(pool, environment, rule, q.body, tn.quant.body, bound);
        },
        .app => |a| {
            const tn = pool.get(t);
            if (tn != .app or tn.app.sym != a.sym or tn.app.args_len != a.args_len) return false;
            for (pool.args(a), pool.args(tn.app)) |pa, ta| {
                if (!matchPattern(pool, environment, rule, pa, ta, bound)) return false;
            }
            return true;
        },
        .pred => |a| {
            const tn = pool.get(t);
            if (tn != .pred or tn.pred.sym != a.sym or tn.pred.args_len != a.args_len) return false;
            for (pool.args(a), pool.args(tn.pred)) |pa, ta| {
                if (!matchPattern(pool, environment, rule, pa, ta, bound)) return false;
            }
            return true;
        },
        .eq => |p| {
            const tn = pool.get(t);
            return tn == .eq and
                matchPattern(pool, environment, rule, p.lhs, tn.eq.lhs, bound) and
                matchPattern(pool, environment, rule, p.rhs, tn.eq.rhs, bound);
        },
        .not => |inner| {
            const tn = pool.get(t);
            return tn == .not and matchPattern(pool, environment, rule, inner, tn.not, bound);
        },
        .bin => |b| {
            const tn = pool.get(t);
            return tn == .bin and tn.bin.op == b.op and
                matchPattern(pool, environment, rule, b.lhs, tn.bin.lhs, bound) and
                matchPattern(pool, environment, rule, b.rhs, tn.bin.rhs, bound);
        },
    }
}

/// Match a rule's full lhs (or any pattern with the rule's binders as
/// wildcards) against `t`; returns the complete binding vector in binder
/// order, or null. For certificate emitters that plan a rewrite at a known
/// position and need the forall_elim arguments.
pub fn matchRule(arena: Allocator, pool: *term.Pool, environment: *const Env, rule: Rule, pattern: TermId, t: TermId) Allocator.Error!?[]const TermId {
    const bound = try arena.alloc(?TermId, rule.binders.len);
    @memset(bound, null);
    if (!matchPattern(pool, environment, rule, pattern, t, bound)) return null;
    const out = try arena.alloc(TermId, rule.binders.len);
    for (bound, out) |b, *o| o.* = b orelse return null; // some binder unused
    return out;
}

fn looseBvar(pool: *const term.Pool, t: TermId, depth: u16) bool {
    switch (pool.get(t)) {
        .bvar => |i| return i >= depth,
        .fvar => return false,
        .app, .pred => |a| {
            for (pool.args(a)) |arg| {
                if (looseBvar(pool, arg, depth)) return true;
            }
            return false;
        },
        .eq => |p| return looseBvar(pool, p.lhs, depth) or looseBvar(pool, p.rhs, depth),
        .not => |inner| return looseBvar(pool, inner, depth),
        .bin => |b| return looseBvar(pool, b.lhs, depth) or looseBvar(pool, b.rhs, depth),
        .quant => |q| return looseBvar(pool, q.body, depth + 1),
    }
}

fn binderIndex(rule: Rule, name: StrId) ?usize {
    for (rule.binders, 0..) |b, i| {
        if (b.fvar == name) return i;
    }
    return null;
}

fn termSort(pool: *const term.Pool, environment: *const Env, t: TermId) SortId {
    return switch (pool.get(t)) {
        .fvar => |v| v.sort,
        .app => |a| environment.sym(a.sym).result,
        else => .prop, // non-term: never matches a term-sorted binder
    };
}

// --- tests ---

const testing = std.testing;

const Rig = struct {
    interner: *InternPool,
    pool: *term.Pool,
    environment: *Env,
    nat: SortId,
    add: term.SymId,
    succ: term.SymId,
    zero: term.SymId,
};

fn buildRig(arena: Allocator) !Rig {
    const interner = try arena.create(InternPool);
    interner.* = .init(arena);
    const environment = try arena.create(Env);
    environment.* = try .init(arena, interner);
    const file = try environment.newFile();
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);

    const nat = try environment.addSort(file, try interner.internString("Nat"), 0);
    const nat2 = try arena.dupe(SortId, &.{ nat, nat });
    const nat1 = try arena.dupe(SortId, &.{nat});
    const add = try environment.addSym(file, .{
        .name = try interner.internString("add"),
        .kind = .app,
        .arg_sorts = nat2,
        .result = nat,
        .guard = null,
        .param_names = &.{},
        .loc = 0,
    });
    const succ = try environment.addSym(file, .{
        .name = try interner.internString("succ"),
        .kind = .app,
        .arg_sorts = nat1,
        .result = nat,
        .guard = null,
        .param_names = &.{},
        .loc = 0,
    });
    const zero = try environment.addSym(file, .{
        .name = try interner.internString("ZERO"),
        .kind = .app,
        .arg_sorts = &.{},
        .result = nat,
        .guard = null,
        .param_names = &.{},
        .loc = 0,
    });
    return .{ .interner = interner, .pool = pool, .environment = environment, .nat = nat, .add = add, .succ = succ, .zero = zero };
}

/// rule: add(ZERO, b) = b  (pattern var b)
fn zeroRule(arena: Allocator, r: *Rig) !Rule {
    const b = try r.interner.internString("p#b");
    const bv = try r.pool.add(.{ .fvar = .{ .name = b, .sort = r.nat } });
    const z = try r.pool.addApp(.app, r.zero, &.{});
    const lhs = try r.pool.addApp(.app, r.add, &.{ z, bv });
    const binders = try arena.dupe(Binder, &.{.{ .fvar = b, .sort = r.nat }});
    return .{
        .source = .{ .axiom = .{ .id = @enumFromInt(0), .loc = 0 } },
        .binders = binders,
        .lhs = lhs,
        .rhs = bv,
        .formula = lhs, // unused by the engine
    };
}

/// rule: add(succ(a), b) = succ(add(a, b))
fn succRule(arena: Allocator, r: *Rig) !Rule {
    const a = try r.interner.internString("p#a");
    const b = try r.interner.internString("p#b");
    const av = try r.pool.add(.{ .fvar = .{ .name = a, .sort = r.nat } });
    const bv = try r.pool.add(.{ .fvar = .{ .name = b, .sort = r.nat } });
    const sa = try r.pool.addApp(.app, r.succ, &.{av});
    const lhs = try r.pool.addApp(.app, r.add, &.{ sa, bv });
    const inner = try r.pool.addApp(.app, r.add, &.{ av, bv });
    const rhs = try r.pool.addApp(.app, r.succ, &.{inner});
    const binders = try arena.dupe(Binder, &.{ .{ .fvar = a, .sort = r.nat }, .{ .fvar = b, .sort = r.nat } });
    return .{
        .source = .{ .axiom = .{ .id = @enumFromInt(0), .loc = 0 } },
        .binders = binders,
        .lhs = lhs,
        .rhs = rhs,
        .formula = lhs,
    };
}

test "ground arithmetic normalizes: 2 + 1 -> 3" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var r = try buildRig(arena);

    const z = try r.pool.addApp(.app, r.zero, &.{});
    const one = try r.pool.addApp(.app, r.succ, &.{z});
    const two = try r.pool.addApp(.app, r.succ, &.{one});
    const three = try r.pool.addApp(.app, r.succ, &.{two});
    const sum = try r.pool.addApp(.app, r.add, &.{ two, one });

    const rules = [_]Rule{ try succRule(arena, &r), try zeroRule(arena, &r) };
    const res = try normalize(arena, r.pool, r.environment, &rules, sum, 100);
    try testing.expect(r.pool.alphaEq(res.nf, three));
    try testing.expectEqual(3, res.trace.len); // succ, succ, zero
}

test "non-linear pattern add(k, k) binds consistently" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var r = try buildRig(arena);

    // rule: add(k, k) = ZERO (nonsense, but exercises consistency)
    const k = try r.interner.internString("p#k");
    const kv = try r.pool.add(.{ .fvar = .{ .name = k, .sort = r.nat } });
    const lhs = try r.pool.addApp(.app, r.add, &.{ kv, kv });
    const z = try r.pool.addApp(.app, r.zero, &.{});
    const binders = try arena.dupe(Binder, &.{.{ .fvar = k, .sort = r.nat }});
    const rule: Rule = .{
        .source = .{ .axiom = .{ .id = @enumFromInt(0), .loc = 0 } },
        .binders = binders,
        .lhs = lhs,
        .rhs = z,
        .formula = lhs,
    };

    const one = try r.pool.addApp(.app, r.succ, &.{z});
    const same = try r.pool.addApp(.app, r.add, &.{ one, one });
    const diff = try r.pool.addApp(.app, r.add, &.{ one, z });

    const res_same = try normalize(arena, r.pool, r.environment, &.{rule}, same, 10);
    try testing.expect(r.pool.alphaEq(res_same.nf, z));
    const res_diff = try normalize(arena, r.pool, r.environment, &.{rule}, diff, 10);
    try testing.expect(r.pool.alphaEq(res_diff.nf, diff)); // no rewrite
}

test "cycling rules hit the cap" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var r = try buildRig(arena);

    // succ(k) = succ(k) would not loop (after == before is still a rewrite —
    // build a real two-rule cycle: succ(k) -> add(ZERO, k)'s successor? use:
    // rule1: succ(k) = add(k, ZERO); rule2: add(k, ZERO) = succ(k)
    const k = try r.interner.internString("p#k");
    const kv = try r.pool.add(.{ .fvar = .{ .name = k, .sort = r.nat } });
    const z = try r.pool.addApp(.app, r.zero, &.{});
    const sk = try r.pool.addApp(.app, r.succ, &.{kv});
    const akz = try r.pool.addApp(.app, r.add, &.{ kv, z });
    const binders = try arena.dupe(Binder, &.{.{ .fvar = k, .sort = r.nat }});
    const rule1: Rule = .{ .source = .{ .axiom = .{ .id = @enumFromInt(0), .loc = 0 } }, .binders = binders, .lhs = sk, .rhs = akz, .formula = sk };
    const rule2: Rule = .{ .source = .{ .axiom = .{ .id = @enumFromInt(0), .loc = 0 } }, .binders = binders, .lhs = akz, .rhs = sk, .formula = akz };

    const start = try r.pool.addApp(.app, r.succ, &.{z});
    try testing.expectError(error.Limit, normalize(arena, r.pool, r.environment, &.{ rule1, rule2 }, start, 50));
}
