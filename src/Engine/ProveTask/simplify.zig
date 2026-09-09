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
///
/// Was native recursion over term depth; now an explicit DFS stack. INVARIANT (the whole
/// point of innermost-leftmost): a node tries the rules on ITSELF only after ALL its
/// children — left to right, each subtree exhaustively — have failed. A frame holds a
/// node + its (copied) args + the index of the child currently being searched; a child
/// subtree failing pops its frame and advances the parent's index; a HIT bubbles up by
/// rebuilding each ancestor's app with the active child slot replaced (innermost ancestor
/// first — the recursion's unwind order). Frame scratch on the pool's GPA; `bindings`
/// (returned in the Rewrite) stays on `arena`.
fn findRewrite(
    arena: Allocator,
    pool: *term.Pool,
    interner: *const InternPool,
    rules: []const Rule,
    t: TermId,
) Error!?Rewrite {
    var scratch: std.heap.ArenaAllocator = .init(pool.gpa);
    defer scratch.deinit();
    const sa = scratch.allocator();

    const Frame = struct { t: TermId, sym: term.SymId, args: []const TermId, i: usize };
    var stack: std.ArrayList(Frame) = .empty;

    // push a frame for `id`: an app's args are copied out up front (pool.args() aliases the
    // pool's extra buffer, which rebuilds/substs below may grow, poisoning the old slice).
    const push = struct {
        fn go(sa_: Allocator, pool_: *term.Pool, stack_: *std.ArrayList(Frame), id: TermId) Error!void {
            switch (pool_.get(id)) {
                .app => |a| try stack_.append(sa_, .{ .t = id, .sym = a.sym, .args = try sa_.dupe(TermId, pool_.args(a)), .i = 0 }),
                else => try stack_.append(sa_, .{ .t = id, .sym = undefined, .args = &.{}, .i = 0 }),
            }
        }
    }.go;
    try push(sa, pool, &stack, t);

    while (stack.items.len > 0) {
        const f = &stack.items[stack.items.len - 1];
        if (f.i < f.args.len) {
            // children first (innermost): descend into the current child. The parent's `i`
            // stays on this slot until the child subtree fails (it is the rebuild slot on a hit).
            try push(sa, pool, &stack, f.args[f.i]);
            continue;
        }
        // all children failed (or a leaf): try this position, rules in citation order.
        const here = f.t; // copy out — the bubble loop pops frames, invalidating `f`.
        if (try matchRulesAt(arena, pool, interner, rules, here)) |hit| {
            // bubble up: rebuild each ancestor's app with its active child slot replaced.
            var rw = hit;
            _ = stack.pop();
            while (stack.pop()) |anc| {
                const new_args = try sa.dupe(TermId, anc.args);
                new_args[anc.i] = rw.after;
                const rebuilt = try pool.addApp(.app, anc.sym, new_args);
                rw = .{
                    .before = anc.t,
                    .after = rebuilt,
                    .rule_idx = rw.rule_idx,
                    .bindings = rw.bindings,
                    .inst_lhs = rw.inst_lhs,
                    .inst_rhs = rw.inst_rhs,
                };
            }
            return rw;
        }
        // no rewrite anywhere in this subtree: pop, advance the parent to its next child.
        _ = stack.pop();
        if (stack.items.len > 0) stack.items[stack.items.len - 1].i += 1;
    }
    return null;
}

/// Try every rule at position `t` (citation order); the licensing instance on a match.
fn matchRulesAt(
    arena: Allocator,
    pool: *term.Pool,
    interner: *const InternPool,
    rules: []const Rule,
    t: TermId,
) Error!?Rewrite {
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
/// Match `pattern` (with `rule`'s binders as wildcards) against `t`, filling `bound`. Iterative
/// parallel two-tree walk (was native recursion) over a work-stack of `(pattern, term)` pairs that
/// must ALL match (a conjunction — stack order irrelevant; the `bound` re-encounter check is
/// order-independent). Scratch on the pool's GPA. OOM → no match (simplify just declines a rule).
fn matchPattern(
    pool: *term.Pool,
    interner: *const InternPool,
    rule: Rule,
    pattern: TermId,
    t: TermId,
    bound: []?TermId,
) bool {
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf([2]TermId), pool.gpa);
    const al = fb.get();
    var stack: std.ArrayList([2]TermId) = .empty;
    defer stack.deinit(al);
    stack.append(al, .{ pattern, t }) catch return false;
    while (stack.pop()) |pair| {
        const pat = pair[0];
        const term_id = pair[1];
        switch (pool.get(pat)) {
            .fvar => |v| {
                if (binderIndex(rule, v.name)) |i| {
                    if (bound[i]) |prev| {
                        if (!pool.alphaEq(prev, term_id)) return false;
                        continue;
                    }
                    if (termSort(pool, interner, term_id) != v.sort) return false;
                    // a binding must be locally closed: a loose bound var would escape its binder.
                    if (looseBvar(pool, term_id, 0)) return false;
                    bound[i] = term_id;
                    continue;
                }
                // a constant fvar from the enclosing scope: exact occurrence only.
                const tn = pool.get(term_id);
                if (!(tn == .fvar and tn.fvar.name == v.name)) return false;
            },
            .bvar => |i| {
                const tn = pool.get(term_id);
                if (!(tn == .bvar and tn.bvar == i)) return false;
            },
            .quant => |q| {
                const tn = pool.get(term_id);
                if (!(tn == .quant and tn.quant.q == q.q and tn.quant.sort == q.sort)) return false;
                stack.append(al, .{ q.body, tn.quant.body }) catch return false;
            },
            .app => |a| {
                const tn = pool.get(term_id);
                if (tn != .app or tn.app.sym != a.sym or tn.app.args_len != a.args_len) return false;
                for (pool.args(a), pool.args(tn.app)) |pa, ta| stack.append(al, .{ pa, ta }) catch return false;
            },
            .pred => |a| {
                const tn = pool.get(term_id);
                if (tn != .pred or tn.pred.sym != a.sym or tn.pred.args_len != a.args_len) return false;
                for (pool.args(a), pool.args(tn.pred)) |pa, ta| stack.append(al, .{ pa, ta }) catch return false;
            },
            .eq => |p| {
                const tn = pool.get(term_id);
                if (tn != .eq) return false;
                stack.append(al, .{ p.lhs, tn.eq.lhs }) catch return false;
                stack.append(al, .{ p.rhs, tn.eq.rhs }) catch return false;
            },
            .not => |inner| {
                const tn = pool.get(term_id);
                if (tn != .not) return false;
                stack.append(al, .{ inner, tn.not }) catch return false;
            },
            .bin => |b| {
                const tn = pool.get(term_id);
                if (!(tn == .bin and tn.bin.op == b.op)) return false;
                stack.append(al, .{ b.lhs, tn.bin.lhs }) catch return false;
                stack.append(al, .{ b.rhs, tn.bin.rhs }) catch return false;
            },
        }
    }
    return true;
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

/// Does `t` have a loose (dangling) bvar at index >= `depth`? Iterative work-stack of
/// `(term, depth)` pairs (was native recursion) — depth-safe; `depth` increments into a quant
/// body. Scratch stack on the pool's GPA. OOM → conservatively "loose" (a false "loose" only ever
/// makes simplify DECLINE to apply a rule, never misapplies one).
fn looseBvar(pool: *const term.Pool, t: TermId, depth: u16) bool {
    const Frame = struct { id: TermId, depth: u16 };
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(Frame), pool.gpa);
    const a = fb.get();
    var stack: std.ArrayList(Frame) = .empty;
    defer stack.deinit(a);
    stack.append(a, .{ .id = t, .depth = depth }) catch return true;
    while (stack.pop()) |f| {
        const node = pool.get(f.id);
        switch (node) {
            .bvar => |i| if (i >= f.depth) return true,
            .fvar => {},
            .quant => |q| stack.append(a, .{ .id = q.body, .depth = f.depth + 1 }) catch return true,
            .app, .pred => |ap| for (pool.args(ap)) |arg| {
                stack.append(a, .{ .id = arg, .depth = f.depth }) catch return true;
            },
            .eq => |p| {
                stack.append(a, .{ .id = p.lhs, .depth = f.depth }) catch return true;
                stack.append(a, .{ .id = p.rhs, .depth = f.depth }) catch return true;
            },
            .not => |inner| stack.append(a, .{ .id = inner, .depth = f.depth }) catch return true,
            .bin => |b| {
                stack.append(a, .{ .id = b.lhs, .depth = f.depth }) catch return true;
                stack.append(a, .{ .id = b.rhs, .depth = f.depth }) catch return true;
            },
        }
    }
    return false;
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
    pool.* = .init(arena, arena);

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
