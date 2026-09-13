//! Schema — the shared types + identity hash for schema instantiation (Step 12). A leaf
//! module both Prove and Elab import, so `SchemaArg`/`SchemaArgs` don't create a
//! Prove↔Elab import cycle.
//!
//! A `SchemaArgs` maps each schema PARAM NAME to the argument bound at an instantiation:
//!   - a VALUE param (`t: Nat`) → `.value` of the elaborated arg term + its sort.
//!   - an N-ary GENERATOR param (`P: T -> Prop`) → `.lambda`: a body term with the lambda
//!     binders KEPT FREE as hygienic fvars (`params[i]`); application beta-reduces via
//!     `substFvar`. (The kernel has no lambda node — schema application is term-level
//!     substitution, exactly as the old eager elaborator did it.)
//!
//! The INSTANCE-IDENTITY HASH keys the synthetic per-instance fact `<schema>{<hash>}` in
//! FactKV, so two textually-identical instantiations DEDUP to one proved fact. It hashes
//! `(schema name, arg terms)`, alpha-consistently:
//!   - quantifier HINTS are ignored (as `term.Pool.alphaEq` does).
//!   - a lambda arg's KEPT-FREE param fvars are canonicalized BY POSITION, not by their
//!     hygienic identity — so `(fun y => goal(y))` and `(fun z => goal(z))` (distinct fresh
//!     fvars each elaboration) hash equal.
//! The SCHEMA NAME is folded in so a (astronomically rare) collision is user-fixable by
//! RENAMING the schema. THE HASH IS PURE ADDRESSING, NEVER TRUSTED: the per-instance fact
//! stores its own reified formula and the kernel `schema_instance` arm re-matches THAT
//! against the citing claim — a collision can only cause a spurious rejection (fixable via
//! rename), never a false accept. See the plan's "Soundness of the hash" invariant.

const std = @import("std");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;

pub const SchemaArg = union(enum) {
    /// a value param's argument: the elaborated term + its (source) sort.
    value: struct { id: TermId, sort: SortId },
    /// an N-ary generator param's argument: a body with `params` kept free (hygienic
    /// fvars); beta-reduced at application by `substFvar`-ing each param with an actual.
    lambda: struct {
        body: TermId,
        params: []const StrId,
        arg_sorts: []const SortId,
        result_sort: SortId,
    },
};

/// param name -> the argument bound to it at an instantiation.
pub const SchemaArgs = std.AutoHashMapUnmanaged(StrId, SchemaArg);

/// The instance-identity hash over `(schema_name, args-in-param-order)`. `params` is the
/// schema's param names IN ORDER (so the hash is order-stable and independent of the
/// hashmap's iteration order). `pool` is the scratchpad the arg terms live in.
pub fn instanceHash(pool: *const term.Pool, schema_name: StrId, params: []const StrId, args: *const SchemaArgs) u64 {
    var h = std.hash.Wyhash.init(0);
    std.hash.autoHash(&h, @intFromEnum(schema_name));
    for (params) |pname| {
        const arg = args.get(pname).?;
        switch (arg) {
            .value => |v| {
                h.update("v");
                std.hash.autoHash(&h, @intFromEnum(v.sort));
                hashTerm(pool, &h, v.id, &.{});
            },
            .lambda => |l| {
                h.update("l");
                for (l.arg_sorts) |s| std.hash.autoHash(&h, @intFromEnum(s));
                std.hash.autoHash(&h, @intFromEnum(l.result_sort));
                // the body's kept-free param fvars canonicalize BY POSITION (l.params[i] -> i)
                hashTerm(pool, &h, l.body, l.params);
            },
        }
    }
    return h.final();
}

/// Alpha-consistent structural hash of a term. `canon` is the lambda-param fvar list whose
/// members hash by their POSITION in `canon` (not their StrId); any other fvar hashes by
/// its actual name. Quantifier hints are ignored (mirrors `alphaEq`).
/// Hash a term into `h`, alpha-invariantly (bound vars by de-Bruijn index, hint ignored) with
/// lambda-params canonicalized by position (`canon`). ITERATIVE PRE-ORDER (was native recursion)
/// — depth-safe. The hash SEQUENCE must match the old recursion EXACTLY (it addresses a schema
/// instance), so: pop a node, hash its scalars (tag first, as before), then push its children
/// REVERSED so child 0 hashes next — reproducing pre-order. Scratch stack on the pool's GPA.
fn hashTerm(pool: *const term.Pool, h: *std.hash.Wyhash, id: TermId, canon: []const StrId) void {
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), pool.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, id) catch @panic("hashTerm: OOM"); // pure hashing; no sound fallback
    while (stack.pop()) |cur| {
        const node = pool.get(cur);
        std.hash.autoHash(h, @intFromEnum(std.meta.activeTag(node)));
        switch (node) {
            .bvar => |i| std.hash.autoHash(h, i),
            .fvar => |v| {
                std.hash.autoHash(h, @intFromEnum(v.sort));
                if (indexOfName(canon, v.name)) |pos| {
                    h.update("#"); // a canonicalized lambda-param fvar
                    std.hash.autoHash(h, pos);
                } else {
                    h.update("@"); // an ordinary fvar (caller eigenvar / ground): hash its name
                    std.hash.autoHash(h, @intFromEnum(v.name));
                }
            },
            .app, .pred => |ap| {
                std.hash.autoHash(h, @intFromEnum(ap.sym));
                std.hash.autoHash(h, ap.args.len);
                pushRev(&stack, a, pool.args(ap));
            },
            .eq => |p| pushRev(&stack, a, &.{ p.lhs, p.rhs }),
            .not => |t| stack.append(a, t) catch @panic("hashTerm: OOM"),
            .bin => |b| {
                std.hash.autoHash(h, @intFromEnum(b.op));
                pushRev(&stack, a, &.{ b.lhs, b.rhs });
            },
            .quant => |q| {
                std.hash.autoHash(h, @intFromEnum(q.q));
                std.hash.autoHash(h, @intFromEnum(q.sort));
                // hint deliberately ignored (alpha-equal terms hash equal)
                stack.append(a, q.body) catch @panic("hashTerm: OOM");
            },
        }
    }
}

/// Push children REVERSED so child 0 pops next (pre-order preservation).
fn pushRev(stack: *std.ArrayList(TermId), a: std.mem.Allocator, kids: []const TermId) void {
    var i: usize = kids.len;
    while (i > 0) {
        i -= 1;
        stack.append(a, kids[i]) catch @panic("hashTerm: OOM");
    }
}

fn indexOfName(canon: []const StrId, name: StrId) ?usize {
    for (canon, 0..) |c, i| if (c == name) return i;
    return null;
}

/// A structural (alpha-consistent) hash of one term — for deriving a deterministic,
/// re-entry-stable synthetic-schema name from an accelerant's head formula.
pub fn termHash(pool: *const term.Pool, id: TermId) u64 {
    var h = std.hash.Wyhash.init(0);
    hashTerm(pool, &h, id, &.{});
    return h.final();
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;

test "instanceHash: value args — equal terms hash equal, distinct terms differ" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    var pool = term.Pool.init(arena, arena);

    const nat: SortId = @enumFromInt(10);
    const zero_sym: term.SymId = @enumFromInt(20);
    const succ_sym: term.SymId = @enumFromInt(21);
    const schema = try interner.internString("zeroLike");
    const t = try interner.internString("t");

    const zero = try pool.addApp(.app, zero_sym, &.{});
    const succ_zero = try pool.addApp(.app, succ_sym, &.{zero});

    // two independent SchemaArgs both binding t := ZERO
    var a1: SchemaArgs = .empty;
    try a1.put(arena, t, .{ .value = .{ .id = zero, .sort = nat } });
    var a2: SchemaArgs = .empty;
    const zero2 = try pool.addApp(.app, zero_sym, &.{}); // a DISTINCT node, same structure
    try a2.put(arena, t, .{ .value = .{ .id = zero2, .sort = nat } });
    // one binding t := succ(ZERO)
    var a3: SchemaArgs = .empty;
    try a3.put(arena, t, .{ .value = .{ .id = succ_zero, .sort = nat } });

    const params = [_]StrId{t};
    const h1 = instanceHash(&pool, schema, &params, &a1);
    const h2 = instanceHash(&pool, schema, &params, &a2);
    const h3 = instanceHash(&pool, schema, &params, &a3);
    try testing.expectEqual(h1, h2); // ZERO ≡ ZERO (structural), same hash
    try testing.expect(h1 != h3); // ZERO vs succ(ZERO) differ
}

test "instanceHash: lambda args — fresh param fvars canonicalize by position" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    var pool = term.Pool.init(arena, arena);

    const t: SortId = @enumFromInt(10);
    const goal: term.SymId = @enumFromInt(30);
    const schema = try interner.internString("everywhereGoal");
    const p = try interner.internString("prop");

    // arg 1: (fun y => goal(y)) with hygienic fvar "#3"
    const y3 = try interner.internString("#3");
    const body1 = try pool.addApp(.pred, goal, &.{try pool.add(.{ .fvar = .{ .name = y3, .sort = t } })});
    // arg 2: (fun z => goal(z)) with a DIFFERENT hygienic fvar "#7"
    const y7 = try interner.internString("#7");
    const body2 = try pool.addApp(.pred, goal, &.{try pool.add(.{ .fvar = .{ .name = y7, .sort = t } })});

    const arg_sorts = [_]SortId{t};
    var a1: SchemaArgs = .empty;
    try a1.put(arena, p, .{ .lambda = .{ .body = body1, .params = &.{y3}, .arg_sorts = &arg_sorts, .result_sort = .prop } });
    var a2: SchemaArgs = .empty;
    try a2.put(arena, p, .{ .lambda = .{ .body = body2, .params = &.{y7}, .arg_sorts = &arg_sorts, .result_sort = .prop } });

    const params = [_]StrId{p};
    try testing.expectEqual(
        instanceHash(&pool, schema, &params, &a1),
        instanceHash(&pool, schema, &params, &a2),
    ); // distinct fresh param fvars, same position → same hash
}

test "instanceHash: the schema name is folded in (rename escape hatch)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    var pool = term.Pool.init(arena, arena);

    const nat: SortId = @enumFromInt(10);
    const zero = try pool.addApp(.app, @enumFromInt(20), &.{});
    const t = try interner.internString("t");
    const params = [_]StrId{t};
    var a: SchemaArgs = .empty;
    try a.put(arena, t, .{ .value = .{ .id = zero, .sort = nat } });

    const foo = try interner.internString("foo");
    const foo2 = try interner.internString("fooOopsHashCollision");
    try testing.expect(
        instanceHash(&pool, foo, &params, &a) != instanceHash(&pool, foo2, &params, &a),
    ); // same args, different schema name → different hash
}
