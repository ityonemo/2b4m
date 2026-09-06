//! Pure Farkas-style refutation for the difference-logic fragment: given a
//! set of strict-order hypotheses `less_than(s_i, t_i)` over abstract nodes,
//! find the combination that is INFEASIBLE — a cycle `x < ... < x`, which is a
//! contradiction with irreflexivity. This is the shape the single-(in)equality
//! order certifier cannot do: it combines SEVERAL hypotheses.
//!
//! This module is a PURE computation — no term pool, no elaborator, no kernel.
//! Nodes are opaque `usize` identities (the caller maps its terms to them);
//! edges are `less_than` hypotheses by index. The output is an ordered chain of
//! hypothesis indices forming a cycle, which the emitter replays as a
//! `lessThanTransitive` fold closed by `lessThanIrreflexive` + `absurd`.
//!
//! The difference-logic case has all-1 Farkas multipliers (each hypothesis
//! used once). The general case — coefficient scaling over `mul`-by-literal
//! bounds — is handled by the LINEAR engine below (`refuteLinear`): each
//! hypothesis compiles to a strict linear constraint `Σ cᵢ·xᵢ + k > 0`, and
//! Fourier-Motzkin elimination finds nonnegative integer multipliers λⱼ with
//! `Σ λⱼ·Lⱼ ≡ constant ≤ 0` — an infeasibility certificate. The emitter scales
//! each hypothesis by its λ (`multiplicationPreservesOrder`) and sums them
//! (`additionPreservesOrder`) to the contradiction.

const std = @import("std");
const Allocator = std.mem.Allocator;

/// A strict-order hypothesis `less_than(lo, hi)` between two abstract nodes.
pub const Edge = struct { lo: usize, hi: usize };

/// A refutation: the hypotheses (by index into the input `edges`) whose
/// transitive composition forms a cycle `node < ... < node`. Following the
/// chain, each edge's `hi` is the next edge's `lo`, and the last edge's `hi`
/// equals the first edge's `lo` — so the fold proves `less_than(node, node)`,
/// contradicting irreflexivity.
pub const Refutation = struct {
    /// hypothesis indices in chain order (>= 1 entry; a single self-loop
    /// `less_than(x, x)` is already the contradiction)
    chain: []const usize,
    /// the node the cycle closes on (chain start == chain end)
    node: usize,
};

/// Find a cycle among the order edges: a sequence of edges e0, e1, ... where
/// hi(e_k) == lo(e_{k+1}) and hi(last) == lo(first). Returns the shortest such
/// cycle found by BFS, or null if the edges are satisfiable (no cycle — a
/// strict partial order has no cycles). When `through` is non-null, only a
/// cycle closing on that specific node counts (the caller's conclusion is
/// `less_than(through, through)`, so the contradiction must land on it). Pure;
/// allocates only working state in `arena`.
pub fn refute(arena: Allocator, edges: []const Edge, through: ?usize) Allocator.Error!?Refutation {
    // a self-loop less_than(x, x) is an immediate contradiction
    for (edges, 0..) |e, i| {
        if (e.lo == e.hi and (through == null or through.? == e.lo)) {
            return .{ .chain = try arena.dupe(usize, &.{i}), .node = e.lo };
        }
    }

    // candidate start nodes: just `through` if constrained, else every node.
    if (through) |t| {
        if (try cycleFrom(arena, edges, t)) |chain| return .{ .chain = chain, .node = t };
        return null;
    }
    var starts = std.AutoHashMap(usize, void).init(arena);
    for (edges) |e| {
        try starts.put(e.lo, {});
        try starts.put(e.hi, {});
    }
    var it = starts.keyIterator();
    while (it.next()) |start_ptr| {
        const start = start_ptr.*;
        if (try cycleFrom(arena, edges, start)) |chain| {
            return .{ .chain = chain, .node = start };
        }
    }
    return null;
}

/// A directed path `from < ... < to` composed from the order edges (each hi
/// links to the next lo). Used for order-composition goals `a < ... < z ->
/// less_than(a, z)` — no cycle, no irreflexivity, just transitivity.
pub const Path = struct { chain: []const usize };

/// Find a directed path from `from` to `to` through the order edges (a strict
/// chain `from < ... < to`), or null if none. When from == to this is a cycle
/// (delegates to cycleFrom). Pure.
pub fn compose(arena: Allocator, edges: []const Edge, from: usize, to: usize) Allocator.Error!?Path {
    if (from == to) {
        if (try cycleFrom(arena, edges, from)) |chain| return .{ .chain = chain };
        return null;
    }
    if (try pathFrom(arena, edges, from, to)) |chain| return .{ .chain = chain };
    return null;
}

/// BFS from `from` following edges forward; return the edge-index trail of the
/// shortest walk reaching `to`, or null if none.
fn pathFrom(arena: Allocator, edges: []const Edge, from: usize, to: usize) Allocator.Error!?[]const usize {
    const Node = struct { at: usize, trail: []const usize };
    var queue: std.ArrayList(Node) = .empty;
    var visited = std.AutoHashMap(usize, void).init(arena);
    try visited.put(from, {});
    for (edges, 0..) |e, i| {
        if (e.lo != from) continue;
        const trail = try arena.dupe(usize, &.{i});
        if (e.hi == to) return trail;
        if (!visited.contains(e.hi)) try queue.append(arena, .{ .at = e.hi, .trail = trail });
    }
    var head: usize = 0;
    while (head < queue.items.len) : (head += 1) {
        const cur = queue.items[head];
        if (visited.contains(cur.at)) continue;
        try visited.put(cur.at, {});
        for (edges, 0..) |e, i| {
            if (e.lo != cur.at) continue;
            const next_trail = try arena.alloc(usize, cur.trail.len + 1);
            @memcpy(next_trail[0..cur.trail.len], cur.trail);
            next_trail[cur.trail.len] = i;
            if (e.hi == to) return next_trail;
            if (!visited.contains(e.hi)) try queue.append(arena, .{ .at = e.hi, .trail = next_trail });
        }
    }
    return null;
}

/// BFS from `start` following edges forward; return the edge-index trail of the
/// shortest walk that returns to `start`, or null if none.
fn cycleFrom(arena: Allocator, edges: []const Edge, start: usize) Allocator.Error!?[]const usize {
    const Node = struct { at: usize, trail: []const usize };
    var queue: std.ArrayList(Node) = .empty;
    // seed: every edge leaving `start`
    for (edges, 0..) |e, i| {
        if (e.lo != start) continue;
        const trail = try arena.dupe(usize, &.{i});
        if (e.hi == start) return trail; // one-edge cycle (shouldn't happen: self-loop handled)
        try queue.append(arena, .{ .at = e.hi, .trail = trail });
    }

    var head: usize = 0;
    // visited nodes (other than start) to keep BFS finite and shortest-first
    var visited = std.AutoHashMap(usize, void).init(arena);
    while (head < queue.items.len) : (head += 1) {
        const cur = queue.items[head];
        if (visited.contains(cur.at)) continue;
        try visited.put(cur.at, {});
        for (edges, 0..) |e, i| {
            if (e.lo != cur.at) continue;
            const next_trail = try arena.alloc(usize, cur.trail.len + 1);
            @memcpy(next_trail[0..cur.trail.len], cur.trail);
            next_trail[cur.trail.len] = i;
            if (e.hi == start) return next_trail; // closed the cycle
            if (!visited.contains(e.hi)) {
                try queue.append(arena, .{ .at = e.hi, .trail = next_trail });
            }
        }
    }
    return null;
}

// -- tests ------------------------------------------------------------------

test "two-cycle a<b, b<a is refuted" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    // nodes: a=0, b=1
    const edges = [_]Edge{ .{ .lo = 0, .hi = 1 }, .{ .lo = 1, .hi = 0 } };
    const r = (try refute(a.allocator(), &edges, null)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 2), r.chain.len);
    // the chain closes on its start node
    try std.testing.expectEqual(edges[r.chain[0]].lo, r.node);
    try std.testing.expectEqual(edges[r.chain[r.chain.len - 1]].hi, r.node);
}

test "three-cycle a<b, b<c, c<a is refuted" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    const edges = [_]Edge{ .{ .lo = 0, .hi = 1 }, .{ .lo = 1, .hi = 2 }, .{ .lo = 2, .hi = 0 } };
    const r = (try refute(a.allocator(), &edges, null)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 3), r.chain.len);
    // verify it is a genuine chain: each hi links to the next lo, closing up
    var node = edges[r.chain[0]].lo;
    for (r.chain) |idx| {
        try std.testing.expectEqual(node, edges[idx].lo);
        node = edges[idx].hi;
    }
    try std.testing.expectEqual(r.node, node);
}

test "self-loop less_than(x,x) is an immediate contradiction" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    const edges = [_]Edge{ .{ .lo = 5, .hi = 5 } };
    const r = (try refute(a.allocator(), &edges, null)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 1), r.chain.len);
    try std.testing.expectEqual(@as(usize, 5), r.node);
}

test "acyclic chain a<b, b<c is satisfiable (no refutation)" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    const edges = [_]Edge{ .{ .lo = 0, .hi = 1 }, .{ .lo = 1, .hi = 2 } };
    try std.testing.expect((try refute(a.allocator(), &edges, null)) == null);
}

test "compose finds a path a<b<c for the composition goal a<c" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    // a=0, b=1, c=2: edges 0<1, 1<2 ; compose 0 -> 2
    const edges = [_]Edge{ .{ .lo = 0, .hi = 1 }, .{ .lo = 1, .hi = 2 } };
    const p = (try compose(a.allocator(), &edges, 0, 2)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 2), p.chain.len);
    // verify it is a genuine path 0 -> ... -> 2
    var node: usize = 0;
    for (p.chain) |idx| {
        try std.testing.expectEqual(node, edges[idx].lo);
        node = edges[idx].hi;
    }
    try std.testing.expectEqual(@as(usize, 2), node);
}

test "compose declines when no path connects from to to" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    const edges = [_]Edge{ .{ .lo = 0, .hi = 1 }, .{ .lo = 2, .hi = 3 } };
    try std.testing.expect((try compose(a.allocator(), &edges, 0, 3)) == null);
}

test "compose from==to reduces to a cycle" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    const edges = [_]Edge{ .{ .lo = 0, .hi = 1 }, .{ .lo = 1, .hi = 0 } };
    const p = (try compose(a.allocator(), &edges, 0, 0)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 2), p.chain.len);
}

test "irrelevant extra edges don't prevent finding the cycle" {
    var a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer a.deinit();
    // a<b, b<a is the cycle; c<d, d<e are noise
    const edges = [_]Edge{
        .{ .lo = 10, .hi = 11 },
        .{ .lo = 0, .hi = 1 },
        .{ .lo = 11, .hi = 12 },
        .{ .lo = 1, .hi = 0 },
    };
    const r = (try refute(a.allocator(), &edges, null)) orelse return error.TestUnexpectedResult;
    // the found cycle uses only the 0<->1 pair
    var node = edges[r.chain[0]].lo;
    for (r.chain) |idx| {
        try std.testing.expectEqual(node, edges[idx].lo);
        node = edges[idx].hi;
    }
    try std.testing.expectEqual(r.node, node);
    try std.testing.expect(node == 0 or node == 1);
}
