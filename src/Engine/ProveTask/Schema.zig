//! Schema — the shared types + identity hash for schema instantiation (Step 12). A leaf
//! module both Prove and Elab import, so `SchemaArg`/`SchemaArgs` don't create a
//! Prove↔Elab import cycle.
//!
//! A `SchemaArgs` maps each schema PARAM NAME to the argument bound at an instantiation:
//!   - a VALUE param (`t: Nat`) → `.value` of the elaborated arg term + its sort.
//!   - an N-ary GENERATOR param (`P(T)`) → `.lambda`: a body term with the lambda
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
pub fn instanceHash(ip: *const InternPool, pool: *const term.Pool, schema_name: StrId, params: []const StrId, args: *const SchemaArgs) u64 {
    var h = std.hash.Wyhash.init(0);
    // the schema's name BYTES — a StrId is allocation-ordered even though content-deduped.
    h.update(ip.stringBytes(schema_name));
    for (params) |pname| {
        const arg = args.get(pname).?;
        switch (arg) {
            .value => |v| {
                h.update("v");
                hashEntity(ip, &h, v.sort);
                hashTerm(ip, pool, &h, v.id, &.{});
            },
            .lambda => |l| {
                h.update("l");
                for (l.arg_sorts) |s| hashEntity(ip, &h, s);
                hashEntity(ip, &h, l.result_sort);
                // the body's kept-free param fvars canonicalize BY POSITION (l.params[i] -> i)
                hashTerm(ip, pool, &h, l.body, l.params);
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
/// Hash an ENTITY (sort/const/func/pred) by its `(name, loc)` rather than its `Index`.
///
/// Those Items are MINTED, not deduped (InternPool.Key), so their `Index` is
/// `@enumFromInt(items.len)` at first demand — allocation-ordered, hence dependent on the
/// demand schedule. Hashing the raw Index made `instanceHash` NONDETERMINISTIC: the same
/// instantiation keyed to a different `Schema{<hash>}` run to run, so one instantiation could
/// mint TWO instances and a citer could bind to the wrong one. `(name, loc)` is fixed by the
/// source. See drafts/schema-instance-crosstalk.b4m.
fn hashEntity(ip: *const InternPool, h: *std.hash.Wyhash, id: anytype) void {
    const ix: InternPool.Index = @enumFromInt(@intFromEnum(id));
    // RESERVED slots (`Index.none`, and the low sentinels `SortId.prop` and friends) are not
    // minted Items and have no name: they are fixed by the pool's layout, so the raw value IS
    // stable and is what we hash.
    if (!ip.isNamedItem(ix)) {
        h.update("~");
        std.hash.autoHash(h, @intFromEnum(ix));
        return;
    }
    // the NAME BYTES, not its StrId: `intern` dedupes by content but still allocates
    // `@enumFromInt(items.len)`, so the id for the same text depends on what was interned
    // BEFORE it — demand order again. Bytes plus the source `loc` are what the source fixes.
    h.update(ip.stringBytes(ip.nameOf(ix)));
    std.hash.autoHash(h, ip.locOf(ix));
}

fn hashTerm(ip: *const InternPool, pool: *const term.Pool, h: *std.hash.Wyhash, id: TermId, canon: []const StrId) void {
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
                hashEntity(ip, h, v.sort);
                if (indexOfName(canon, v.name)) |pos| {
                    h.update("#"); // a canonicalized lambda-param fvar
                    std.hash.autoHash(h, pos);
                } else {
                    h.update("@"); // an ordinary fvar (caller eigenvar / ground): hash its name
                    h.update(ip.stringBytes(v.name));
                }
            },
            .app, .pred => |ap| {
                hashEntity(ip, h, ap.sym);
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
/// re-entry-stable synthetic-schema name from an accelerant's head formula. Entities hash by
/// `(name, loc)`, not by `Index`, so the name is stable ACROSS RUNS as well as across
/// re-entry (see `hashEntity`).
pub fn termHash(ip: *const InternPool, pool: *const term.Pool, id: TermId) u64 {
    var h = std.hash.Wyhash.init(0);
    hashTerm(ip, pool, &h, id, &.{});
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

    // MINT REAL entities: `hashEntity` resolves `(nameOf, locOf)`, so a fabricated Index
    // would not be a named Item at all. Minting also makes the test exercise the real path.
    const nat_ix = try interner.mintSort(.{ .name = try interner.internString("Nat"), .loc = 1 });
    const nat: SortId = @enumFromInt(@intFromEnum(nat_ix));
    const zero_ix = try interner.mintConstant(.{ .sort = nat_ix, .name = try interner.internString("ZERO"), .loc = 2 });
    const zero_sym: term.SymId = @enumFromInt(@intFromEnum(zero_ix));
    const succ_ix = try interner.mintConstant(.{ .sort = nat_ix, .name = try interner.internString("succ"), .loc = 3 });
    const succ_sym: term.SymId = @enumFromInt(@intFromEnum(succ_ix));
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
    const h1 = instanceHash(interner, &pool, schema, &params, &a1);
    const h2 = instanceHash(interner, &pool, schema, &params, &a2);
    const h3 = instanceHash(interner, &pool, schema, &params, &a3);
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

    const t_ix = try interner.mintSort(.{ .name = try interner.internString("T"), .loc = 1 });
    const t: SortId = @enumFromInt(@intFromEnum(t_ix));
    const goal_ix = try interner.mintConstant(.{ .sort = t_ix, .name = try interner.internString("goal"), .loc = 2 });
    const goal: term.SymId = @enumFromInt(@intFromEnum(goal_ix));
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
        instanceHash(interner, &pool, schema, &params, &a1),
        instanceHash(interner, &pool, schema, &params, &a2),
    ); // distinct fresh param fvars, same position → same hash
}

test "instanceHash: the schema name is folded in (rename escape hatch)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    var pool = term.Pool.init(arena, arena);

    const nat_ix = try interner.mintSort(.{ .name = try interner.internString("Nat"), .loc = 1 });
    const nat: SortId = @enumFromInt(@intFromEnum(nat_ix));
    const zero_ix = try interner.mintConstant(.{ .sort = nat_ix, .name = try interner.internString("ZERO"), .loc = 2 });
    const zero = try pool.addApp(.app, @enumFromInt(@intFromEnum(zero_ix)), &.{});
    const t = try interner.internString("t");
    const params = [_]StrId{t};
    var a: SchemaArgs = .empty;
    try a.put(arena, t, .{ .value = .{ .id = zero, .sort = nat } });

    const foo = try interner.internString("foo");
    const foo2 = try interner.internString("fooOopsHashCollision");
    try testing.expect(
        instanceHash(interner, &pool, foo, &params, &a) != instanceHash(interner, &pool, foo2, &params, &a),
    ); // same args, different schema name → different hash
}

// REGRESSION: the hash must depend on an entity's (name, loc), NOT on its Index.
//
// Entities are MINTED, not deduped, so an Index is allocation-ordered and therefore
// demand-order dependent. Hashing it made `instanceHash` nondeterministic across runs: one
// instantiation could key to two different `Schema{<hash>}` names and a citer bind to the
// wrong instance. Measured before the fix on drafts/schema-instance-crosstalk.b4m: 4 distinct
// hashes in 5 runs.
//
// Mint the SAME declaration (same name, same loc) in two pools at DIFFERENT indices — which
// is exactly what a different demand order produces — and require equal hashes.
test "instanceHash: an entity hashes by (name, loc), not by its minted Index" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const t_name = "T";
    const c_name = "c";

    var hashes: [2]u64 = undefined;
    // run 0 mints the sort FIRST; run 1 mints decoys first, so the same decl lands at a
    // different Index. The hash must not notice.
    for (0..2) |run| {
        const ip = try arena.create(InternPool);
        ip.* = try .init(arena);
        var pool = term.Pool.init(arena, arena);

        if (run == 1) {
            // decoys: shift every later Index along
            _ = try ip.mintSort(.{ .name = try ip.internString("Decoy1"), .loc = 90 });
            _ = try ip.mintSort(.{ .name = try ip.internString("Decoy2"), .loc = 91 });
        }

        const t_ix = try ip.mintSort(.{ .name = try ip.internString(t_name), .loc = 7 });
        const c_ix = try ip.mintConstant(.{ .sort = t_ix, .name = try ip.internString(c_name), .loc = 8 });
        const arg = try pool.addApp(.app, @enumFromInt(@intFromEnum(c_ix)), &.{});

        const pname = try ip.internString("p");
        var args: SchemaArgs = .empty;
        try args.put(arena, pname, .{ .value = .{ .id = arg, .sort = @enumFromInt(@intFromEnum(t_ix)) } });

        const params = [_]StrId{pname};
        hashes[run] = instanceHash(ip, &pool, try ip.internString("sch"), &params, &args);
    }

    try testing.expectEqual(hashes[0], hashes[1]);
}
