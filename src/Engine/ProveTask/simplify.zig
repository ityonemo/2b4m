//! The `simplify` tactic's MATH CORE: first-order matching and innermost rewriting over
//! kernel terms. PURE and certificate-producing — this module only computes the normal
//! forms + the rewrite trace; the accelerant producer (`Prove.produceSimplify` via the
//! shared `EqCert`) turns the trace into ordinary AST proof steps the kernel re-checks.
//! Nothing here is trusted.
//!
//! DEMAND-WORLD PORT: the old core imported `env.zig` (deleted) — only to read an app's
//! RESULT sort in `termSort`. That single dependency is now `InternPool.symResult`; a
//! `term.SymId` is the same integer as its InternPool `Index` (the pool stores minted
//! symbol Indexes verbatim), so the map is a bit-cast. `Source` is retired: a rule's
//! origin lives in the producer (a resolved SRef / fact Index), not here.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;

/// A rewrite rule prepared from a (possibly forall-prefixed) equation, oriented left ->
/// right. Binders are opened as fresh pattern fvars (unlexable `#`-mangled names, so they
/// can never collide with proof terms).
pub const Rule = struct {
    /// outermost-first, matching the forall nesting of the source formula
    binders: []const Binder,
    lhs: TermId,
    rhs: TermId,
    /// the full quantified formula (the producer cites it when emitting the certificate)
    formula: TermId,
};

pub const Binder = struct { fvar: StrId, sort: SortId };

/// One rewrite: the whole term before/after, and the rule instance that licensed it
/// (equation inst_lhs = inst_rhs at the matched bindings).
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

/// Rewrite `start` with `rules` (in citation order, innermost-leftmost) to a fixpoint,
/// recording every rewrite. `cap` bounds total rewrites (a looping rule set → error.Limit).
pub fn normalize(
    arena: Allocator,
    pool: *term.Pool,
    interner: *const InternPool,
    rules: []const Rule,
    start: TermId,
    cap: usize,
) Error!Result {
    var trace: std.ArrayList(Rewrite) = .empty;
    var current = start;
    while (try findRewrite(arena, pool, interner, rules, current)) |rw| {
        if (trace.items.len >= cap) return error.Limit;
        try trace.append(arena, rw);
        current = rw.after;
    }
    return .{ .nf = current, .trace = trace.items };
}

/// Find the innermost-leftmost rewrite in `t`, or null at normal form. Returns the
/// rewritten version of `t` plus the licensing instance.
fn findRewrite(
    arena: Allocator,
    pool: *term.Pool,
    interner: *const InternPool,
    rules: []const Rule,
    t: TermId,
) Error!?Rewrite {
    // children first (innermost)
    switch (pool.get(t)) {
        .app => |a| {
            // pool.args() aliases the pool's extra buffer, which the recursive calls below
            // may grow (poisoning the old buffer) — copy the ids out first.
            const args = try arena.dupe(TermId, pool.args(a));
            for (args, 0..) |arg, i| {
                if (try findRewrite(arena, pool, interner, rules, arg)) |child| {
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
        if (matchPattern(pool, interner, rule, rule.lhs, t, bound)) {
            const bindings = try arena.alloc(TermId, rule.binders.len);
            for (bound, bindings) |b, *out| out.* = b.?; // prep guarantees every binder occurs in lhs
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

/// One-way syntactic match of `pattern` (rule binders = wildcards) against `t`, with
/// consistent bindings and sort checks. Handles formula structure too (emitters match whole
/// rule bodies), but not binders: quantified patterns never match.
fn matchPattern(
    pool: *term.Pool,
    interner: *const InternPool,
    rule: Rule,
    pattern: TermId,
    t: TermId,
    bound: []?TermId,
) bool {
    switch (pool.get(pattern)) {
        .fvar => |v| {
            if (binderIndex(rule, v.name)) |i| {
                if (bound[i]) |prev| return pool.alphaEq(prev, t);
                if (termSort(pool, interner, t) != v.sort) return false;
                // a binding must be locally closed: a loose bound variable would escape its
                // binder through the instantiation.
                if (looseBvar(pool, t, 0)) return false;
                bound[i] = t;
                return true;
            }
            // a constant fvar from the enclosing scope: exact occurrence only.
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
                matchPattern(pool, interner, rule, q.body, tn.quant.body, bound);
        },
        .app => |a| {
            const tn = pool.get(t);
            if (tn != .app or tn.app.sym != a.sym or tn.app.args_len != a.args_len) return false;
            for (pool.args(a), pool.args(tn.app)) |pa, ta| {
                if (!matchPattern(pool, interner, rule, pa, ta, bound)) return false;
            }
            return true;
        },
        .pred => |a| {
            const tn = pool.get(t);
            if (tn != .pred or tn.pred.sym != a.sym or tn.pred.args_len != a.args_len) return false;
            for (pool.args(a), pool.args(tn.pred)) |pa, ta| {
                if (!matchPattern(pool, interner, rule, pa, ta, bound)) return false;
            }
            return true;
        },
        .eq => |p| {
            const tn = pool.get(t);
            return tn == .eq and
                matchPattern(pool, interner, rule, p.lhs, tn.eq.lhs, bound) and
                matchPattern(pool, interner, rule, p.rhs, tn.eq.rhs, bound);
        },
        .not => |inner| {
            const tn = pool.get(t);
            return tn == .not and matchPattern(pool, interner, rule, inner, tn.not, bound);
        },
        .bin => |b| {
            const tn = pool.get(t);
            return tn == .bin and tn.bin.op == b.op and
                matchPattern(pool, interner, rule, b.lhs, tn.bin.lhs, bound) and
                matchPattern(pool, interner, rule, b.rhs, tn.bin.rhs, bound);
        },
    }
}

/// Match a rule's full lhs (or any pattern with the rule's binders as wildcards) against
/// `t`; returns the complete binding vector in binder order, or null. For the certificate
/// emitter, which plans a rewrite at a known position and needs the forall_elim arguments.
pub fn matchRule(arena: Allocator, pool: *term.Pool, interner: *const InternPool, rule: Rule, pattern: TermId, t: TermId) Allocator.Error!?[]const TermId {
    const bound = try arena.alloc(?TermId, rule.binders.len);
    @memset(bound, null);
    if (!matchPattern(pool, interner, rule, pattern, t, bound)) return null;
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

/// A term's sort, for the binder sort-check. An app/pred's sort is its symbol's result sort
/// (via `InternPool.symResult`); a `term.SymId` is the same integer as its InternPool
/// `Index`. Non-term structure never matches a term-sorted binder (returns `.prop`).
fn termSort(pool: *const term.Pool, interner: *const InternPool, t: TermId) SortId {
    return switch (pool.get(t)) {
        .fvar => |v| v.sort,
        .app => |a| @enumFromInt(@intFromEnum(interner.symResult(@enumFromInt(@intFromEnum(a.sym))))),
        else => .prop, // non-term: never matches a term-sorted binder
    };
}

// --- tests ---

const testing = std.testing;

const Rig = struct {
    interner: *InternPool,
    pool: *term.Pool,
    nat: SortId,
    add: term.SymId,
    succ: term.SymId,
    zero: term.SymId,
};

/// Mint a nullary/unary/binary `Nat`-valued symbol through the InternPool, returning it as a
/// `term.SymId` (the pool's symbol handle IS its InternPool Index, bit-for-bit).
fn mintNatFn(ip: *InternPool, name: []const u8, arity: usize, nat: InternPool.Index) !term.SymId {
    const nm = try ip.internString(name);
    const args = try ip.arena.alloc(InternPool.Index, arity);
    @memset(args, nat);
    const sig = try ip.get(.{ .sig = .{ .result = nat, .result_refined = .none, .args = args } });
    const pnames = try ip.arena.alloc(InternPool.Index, arity);
    for (pnames, 0..) |*p, i| p.* = try ip.internString(try std.fmt.allocPrint(ip.arena, "a{d}", .{i}));
    const ix = try ip.mintFunc(.{ .sig = sig, .guard = InternPool.no_term, .param_names = pnames, .name = nm, .loc = 0 });
    return @enumFromInt(@intFromEnum(ix));
}

fn buildRig(arena: Allocator) !Rig {
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);

    const nat_ix = try interner.mintSort(.{ .name = try interner.internString("Nat"), .loc = 0, .refinement = null });
    const nat: SortId = @enumFromInt(@intFromEnum(nat_ix));
    const add = try mintNatFn(interner, "add", 2, nat_ix);
    const succ = try mintNatFn(interner, "succ", 1, nat_ix);
    const zero = try mintNatFn(interner, "ZERO", 0, nat_ix);
    return .{ .interner = interner, .pool = pool, .nat = nat, .add = add, .succ = succ, .zero = zero };
}

/// rule: add(ZERO, b) = b  (pattern var b)
fn zeroRule(arena: Allocator, r: *Rig) !Rule {
    const b = try r.interner.internString("p#b");
    const bv = try r.pool.add(.{ .fvar = .{ .name = b, .sort = r.nat } });
    const z = try r.pool.addApp(.app, r.zero, &.{});
    const lhs = try r.pool.addApp(.app, r.add, &.{ z, bv });
    const binders = try arena.dupe(Binder, &.{.{ .fvar = b, .sort = r.nat }});
    return .{ .binders = binders, .lhs = lhs, .rhs = bv, .formula = lhs };
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
    return .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = lhs };
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
    const res = try normalize(arena, r.pool, r.interner, &rules, sum, 100);
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
    const rule: Rule = .{ .binders = binders, .lhs = lhs, .rhs = z, .formula = lhs };

    const one = try r.pool.addApp(.app, r.succ, &.{z});
    const same = try r.pool.addApp(.app, r.add, &.{ one, one });
    const diff = try r.pool.addApp(.app, r.add, &.{ one, z });

    const res_same = try normalize(arena, r.pool, r.interner, &.{rule}, same, 10);
    try testing.expect(r.pool.alphaEq(res_same.nf, z));
    const res_diff = try normalize(arena, r.pool, r.interner, &.{rule}, diff, 10);
    try testing.expect(r.pool.alphaEq(res_diff.nf, diff)); // no rewrite
}

test "cycling rules hit the cap" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var r = try buildRig(arena);

    // a real two-rule cycle: succ(k) -> add(k, ZERO); add(k, ZERO) -> succ(k).
    const k = try r.interner.internString("p#k");
    const kv = try r.pool.add(.{ .fvar = .{ .name = k, .sort = r.nat } });
    const z = try r.pool.addApp(.app, r.zero, &.{});
    const sk = try r.pool.addApp(.app, r.succ, &.{kv});
    const akz = try r.pool.addApp(.app, r.add, &.{ kv, z });
    const binders = try arena.dupe(Binder, &.{.{ .fvar = k, .sort = r.nat }});
    const rule1: Rule = .{ .binders = binders, .lhs = sk, .rhs = akz, .formula = sk };
    const rule2: Rule = .{ .binders = binders, .lhs = akz, .rhs = sk, .formula = akz };

    const start = try r.pool.addApp(.app, r.succ, &.{z});
    try testing.expectError(error.Limit, normalize(arena, r.pool, r.interner, &.{ rule1, rule2 }, start, 50));
}
