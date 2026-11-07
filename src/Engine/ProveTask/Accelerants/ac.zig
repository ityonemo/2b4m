//! The AC / succ-tower SUBSTRATE: flatten a sum or product to leaves, sort them, re-nest
//! right, cancel inverse pairs under a `succ` tower, and build the rewrite trace that
//! certifies the reordering. Used by the AC reorderers (`assoc_commut`), the polynomial
//! canonicalizer and the arithmetic certifiers alike, so it sits BELOW all of them: it depends
//! only on the rewrite engine, the vocabulary table and the certificate writer.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("../../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const SymId = term.SymId;
const EqCert = @import("../EqCert.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const testing = std.testing;
const rewrite = @import("rewrite.zig");
const Symbols = @import("symbols.zig").Symbols;

/// Build the associativity / commutativity / swap triple for `op_sym` as HARDCODED rewrite
/// shapes (no facts.lookup), appending to `rules`/`cites` in the order assoc, comm, swap. The
/// cites name the well-known lemmas BARE (resolved in the proof's namespace by the generated
/// schema's ProveTask + kernel-checked). Shapes:
///   assoc: f(f(a,b),c) = f(a,f(b,c));  comm: f(a,b) = f(b,a);  swap: f(x,f(y,r)) = f(y,f(x,r))
pub fn pushACTriple(prove: *Prove, rules: *std.ArrayList(rewrite.Rule), cites: *std.ArrayList(EqCert.RuleCite), op_sym: term.SymId, sort: term.SortId, assoc_name: []const u8, comm_name: []const u8, swap_name: []const u8, loc: u32) Error!void {
    // assoc: f(f(a,b),c) = f(a,f(b,c))
    {
        const a = try freshACFvar(prove, sort);
        const b = try freshACFvar(prove, sort);
        const cc = try freshACFvar(prove, sort);
        const binders = try prove.ctx.arena.dupe(rewrite.Binder, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = b.name, .sort = sort }, .{ .fvar = cc.name, .sort = sort } });
        const lhs = try prove.pool.addApp(.app, op_sym, &.{ try prove.pool.addApp(.app, op_sym, &.{ a.t, b.t }), cc.t });
        const rhs = try prove.pool.addApp(.app, op_sym, &.{ a.t, try prove.pool.addApp(.app, op_sym, &.{ b.t, cc.t }) });
        try pushHardcoded(prove, rules, cites, binders, lhs, rhs, assoc_name, loc);
    }
    // comm: f(a,b) = f(b,a)
    {
        const a = try freshACFvar(prove, sort);
        const b = try freshACFvar(prove, sort);
        const binders = try prove.ctx.arena.dupe(rewrite.Binder, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = b.name, .sort = sort } });
        const lhs = try prove.pool.addApp(.app, op_sym, &.{ a.t, b.t });
        const rhs = try prove.pool.addApp(.app, op_sym, &.{ b.t, a.t });
        try pushHardcoded(prove, rules, cites, binders, lhs, rhs, comm_name, loc);
    }
    // swap: f(x,f(y,r)) = f(y,f(x,r))
    {
        const x = try freshACFvar(prove, sort);
        const y = try freshACFvar(prove, sort);
        const r = try freshACFvar(prove, sort);
        const binders = try prove.ctx.arena.dupe(rewrite.Binder, &.{ .{ .fvar = x.name, .sort = sort }, .{ .fvar = y.name, .sort = sort }, .{ .fvar = r.name, .sort = sort } });
        const lhs = try prove.pool.addApp(.app, op_sym, &.{ x.t, try prove.pool.addApp(.app, op_sym, &.{ y.t, r.t }) });
        const rhs = try prove.pool.addApp(.app, op_sym, &.{ y.t, try prove.pool.addApp(.app, op_sym, &.{ x.t, r.t }) });
        try pushHardcoded(prove, rules, cites, binders, lhs, rhs, swap_name, loc);
    }
}

/// A fresh AC pattern fvar of `sort`.
pub fn freshACFvar(prove: *Prove, sort: term.SortId) Error!struct { name: StrId, t: TermId } {
    const name = try prove.freshNamed("p#");
    return .{ .name = name, .t = try prove.pool.add(.{ .fvar = .{ .name = name, .sort = sort } }) };
}

/// Append one hardcoded rule (binders + lhs/rhs + its ∀-quantified formula) with a BARE cite
/// naming `name_text` (resolved by the generated ProveTask; is_axiom = placeholder).
pub fn pushHardcoded(prove: *Prove, rules: *std.ArrayList(rewrite.Rule), cites: *std.ArrayList(EqCert.RuleCite), binders: []const rewrite.Binder, lhs: TermId, rhs: TermId, name_text: []const u8, loc: u32) Error!void {
    // ∀-quantify eq(lhs,rhs) over binders, outermost = binders[0] (matches emitInstance).
    var formula = try prove.pool.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        const closed = try prove.pool.close(formula, binders[i].fvar);
        formula = try prove.pool.add(.{ .quant = .{ .q = .forall, .sort = binders[i].sort, .hint = binders[i].fvar, .body = closed } });
    }
    const name = prove.ctx.interner.internString(name_text) catch return error.OutOfMemory;
    try rules.append(prove.ctx.arena, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = formula });
    try cites.append(prove.ctx.arena, .{
        .global = .{
            // stamp the call-site loc so a "reference not found" on the emitted cite points at the
            // `assoc_commut` step, not 1:1.
            .head = .{ .tag = .identifier, .start = loc, .end = loc, .name = name, .qualifier = .none },
            .is_axiom = false,
        },
    });
}

/// `succ^n(comb)` for n≥0, `prev^|n|(comb)` for n<0 (needs ℤ `prev`; null for ℕ negatives).
pub fn buildArithTowerSigned(prove: *Prove, offset: i128, comb: TermId, symbols: Symbols) Error!?TermId {
    var cur = comb;
    if (offset >= 0) {
        const succ = symbols.succ orelse return if (offset == 0) comb else null;
        var n = offset;
        while (n > 0) : (n -= 1) cur = try prove.pool.addApp(.app, succ, &.{cur});
        return cur;
    }
    const prev = symbols.prev orelse return null;
    var n = -offset;
    while (n > 0) : (n -= 1) cur = try prove.pool.addApp(.app, prev, &.{cur});
    return cur;
}

/// Flatten an `op`-tree into its atom summands (any maximal subterm that is not itself an
/// `op(_, _)`), left-to-right.
pub fn flattenSum(prove: *Prove, op_sym: term.SymId, id: TermId, out: *std.ArrayList(TermId)) Error!void {
    // flatten a nested `op(op(a,b),c)` sum into `out` in LEFT-TO-RIGHT leaf order. Iterative work-
    // stack (was native recursion); order-sensitive → push the two args REVERSED (a1 then a0) so a0
    // pops + is emitted first, matching the recursion's lhs-before-rhs.
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = prove.pool.get(cur);
        if (node == .app and node.app.sym == op_sym and node.app.args.len == 2) {
            const args = prove.pool.args(node.app);
            try stack.append(wa, args[1]); // rhs pushed first → pops second
            try stack.append(wa, args[0]); // lhs pushed second → pops first
        } else {
            try out.append(prove.ctx.arena, cur); // a leaf summand
        }
    }
}

/// Build a right-nested `op(l0, op(l1, … ln))` comb from the leaves (non-empty).
pub fn buildRightNested(prove: *Prove, op_sym: term.SymId, leaves: []const TermId) Error!TermId {
    var cur = leaves[leaves.len - 1];
    var i = leaves.len - 1;
    while (i > 0) {
        i -= 1;
        cur = try prove.pool.addApp(.app, op_sym, &.{ leaves[i], cur });
    }
    return cur;
}

/// In-place insertion sort by `termOrder` (stable, small lists).
pub fn sortTerms(prove: *Prove, items: []TermId) void {
    var i: usize = 1;
    while (i < items.len) : (i += 1) {
        const v = items[i];
        var j = i;
        while (j > 0 and prove.pool.termOrder(items[j - 1], v) == .gt) : (j -= 1) {
            items[j] = items[j - 1];
        }
        items[j] = v;
    }
}

pub const AcPlan = struct { sorted: TermId, trace: []const rewrite.Rewrite };

/// Re-associate `start` to a right-nested comb (via associativity only, terminating), then
/// bubble-sort its atoms into canonical `termOrder`, accumulating one trace. `assoc_idx` is
/// the rule-array index of the associativity rule (after the distribute pre-rules); `comm_idx`
/// / `swap_idx` the commutativity / swap rules. A succ/prev TOWER prefix (the pre-rules float
/// succ/prev to the root: `succ(add(…))`) is stripped first and the sum sorted UNDER it — every
/// emitted rewrite still names the whole tower, as the kernel's `rewrite` requires.
pub fn acPlan(prove: *Prove, symbols: Symbols, rules: []const rewrite.Rule, assoc_idx: usize, comm_idx: usize, swap_idx: usize, start: TermId) Error!?AcPlan {
    const op_sym = symbols.add.?; // the reordered operator (the AC vocabulary's `add` slot)
    // phase 1: right-nest via associativity ONLY (a single-rule slice, terminating).
    const assoc_only = rules[assoc_idx .. assoc_idx + 1];
    const rn = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, assoc_only, start, 1000) catch |e| switch (e) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    // phase 2: strip the tower, flatten the right-nested comb under it, and bubble-sort.
    const tower = stripTower(prove, symbols, rn.nf);
    var leaves: std.ArrayList(TermId) = .empty;
    try flattenSum(prove, op_sym, tower.inner, &leaves);
    var trace: std.ArrayList(rewrite.Rewrite) = .empty;
    // phase-1 normalized over the single-rule slice, so its trace rule_idx is 0-relative;
    // rebase it to the full-array index.
    for (rn.trace) |rw| {
        var r = rw;
        r.rule_idx = rw.rule_idx + assoc_idx;
        try trace.append(prove.ctx.arena, r);
    }
    const sorted = (try sortTrace(prove, symbols, rules, comm_idx, swap_idx, op_sym, tower.offset, leaves.items, &trace)) orelse return null;
    return .{ .sorted = sorted, .trace = trace.items };
}

/// A term split into its succ/prev prefix (signed count) and the term underneath.
pub const StrippedTower = struct { offset: i128, inner: TermId };

/// Peel `succ^j(prev^k(inner))` (in any interleaving) off the root: the signed offset and
/// the inner term. A theory without succ/prev never strips (offset 0, inner = the term).
pub fn stripTower(prove: *Prove, symbols: Symbols, t: TermId) StrippedTower {
    var offset: i128 = 0;
    var cur = t;
    while (true) {
        const node = prove.pool.get(cur);
        if (node != .app or node.app.args.len != 1) break;
        if (symIs(node.app.sym, symbols.succ)) {
            offset += 1;
        } else if (symIs(node.app.sym, symbols.prev)) {
            offset -= 1;
        } else break;
        cur = prove.pool.args(node.app)[0];
    }
    return .{ .offset = offset, .inner = cur };
}

/// Bubble-sort a comb's summands, appending one rewrite per adjacent swap (the swap lemma
/// inside the comb, the commutativity lemma for the final pair). The comb sits under the
/// tower `succ^offset(…)`: each rewrite's before/after is the whole tower. Returns the sorted
/// whole, or null when a fabricated rewrite fails to match its lemma. `leaves` is mutated.
pub fn sortTrace(
    prove: *Prove,
    symbols: Symbols,
    rules: []const rewrite.Rule,
    comm_idx: usize,
    swap_idx: usize,
    op_sym: term.SymId,
    offset: i128,
    leaves_in: []const TermId,
    trace: *std.ArrayList(rewrite.Rewrite),
) Error!?TermId {
    const leaves = try prove.ctx.arena.dupe(TermId, leaves_in);
    var whole = (try buildArithTowerSigned(prove, offset, try buildRightNested(prove, op_sym, leaves), symbols)) orelse return null;
    if (leaves.len > 1) {
        for (0..leaves.len - 1) |pass| {
            for (0..leaves.len - 1 - pass) |i| {
                if (prove.pool.termOrder(leaves[i], leaves[i + 1]) != .gt) continue;
                // the FINAL adjacent pair is a bare `op(x, y)` → commutativity; an interior
                // pair sits at the head of a longer tail `op(x, op(y, r))` → the swap lemma.
                const tail_pair = i + 2 == leaves.len;
                const rule_idx = if (tail_pair) comm_idx else swap_idx;
                const sub_before = try buildRightNested(prove, op_sym, leaves[i..]);
                std.mem.swap(TermId, &leaves[i], &leaves[i + 1]);
                const sub_after = try buildRightNested(prove, op_sym, leaves[i..]);
                const after = (try buildArithTowerSigned(prove, offset, try buildRightNested(prove, op_sym, leaves), symbols)) orelse return null;
                const rule = rules[rule_idx];
                const bindings = (try rewrite.matchRule(prove.ctx.arena, prove.pool, prove.ctx.interner, rule, rule.lhs, sub_before)) orelse return null;
                try trace.append(prove.ctx.arena, .{
                    .before = whole,
                    .after = after,
                    .rule_idx = rule_idx,
                    .bindings = bindings,
                    .inst_lhs = sub_before,
                    .inst_rhs = sub_after,
                });
                whole = after;
            }
        }
    }
    return whole;
}

pub const Tower = struct { offset: i128, leaves: []const TermId };

pub fn symIs(id: term.SymId, want: ?term.SymId) bool {
    return want != null and id == want.?;
}

/// If `t` is a numeral (succ^n(ZERO), prev^n(ZERO), or neg of one) return its signed value.
pub fn numeralValue(self: *Prove, symbols: Symbols, t: TermId) ?i128 {
    var cur = t;
    var sign: i128 = 1;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and symIs(node.app.sym, symbols.neg) and node.app.args.len == 1) {
            sign = -sign;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    var mag: i128 = 0;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and symIs(node.app.sym, symbols.succ) and node.app.args.len == 1) {
            mag += 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and symIs(node.app.sym, symbols.prev) and node.app.args.len == 1) {
            mag -= 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    const node = self.pool.get(cur);
    if (node == .app and symIs(node.app.sym, symbols.zero) and node.app.args.len == 0)
        return sign * mag;
    return null;
}

/// Parse succ^j(prev^k(right-nested sum)) with numeral summands folded into a signed offset.
pub fn parseTower(self: *Prove, symbols: Symbols, t: TermId) Allocator.Error!?Tower {
    var offset: i128 = 0;
    var cur = t;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and symIs(node.app.sym, symbols.succ) and node.app.args.len == 1) {
            offset += 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and symIs(node.app.sym, symbols.prev) and node.app.args.len == 1) {
            offset -= 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    var leaves: std.ArrayList(TermId) = .empty;
    while (true) {
        const node = self.pool.get(cur);
        if (numeralValue(self, symbols, cur)) |v| {
            offset += v;
            break;
        }
        if (isTowerLeaf(self, symbols, cur)) {
            try leaves.append(self.ctx.arena, cur);
            break;
        }
        if (node != .app) return null;
        if (symIs(node.app.sym, symbols.add) and node.app.args.len == 2) {
            const args = self.pool.args(node.app);
            const a0 = args[0];
            const a1 = args[1];
            if (numeralValue(self, symbols, a0)) |v| {
                offset += v;
                cur = a1;
                continue;
            }
            if (!isTowerLeaf(self, symbols, a0)) return null;
            try leaves.append(self.ctx.arena, a0);
            cur = a1;
            continue;
        }
        return null;
    }
    return .{ .offset = offset, .leaves = leaves.items };
}

/// A tower summand leaf: an fvar, an opaque atom, or `neg(<leaf>)`.
pub fn isTowerLeaf(self: *Prove, symbols: Symbols, t: TermId) bool {
    // LINEAR recursion (only ever descends into neg's single arg) — a plain loop, depth-safe.
    var cur = t;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .fvar) return true;
        if (node == .app and symIs(node.app.sym, symbols.neg) and node.app.args.len == 1) {
            cur = self.pool.args(node.app)[0]; // peel neg, keep going
            continue;
        }
        return isOpaqueAtom(self, symbols, cur);
    }
}

/// An opaque atom: an application whose head is NOT part of the sum structure.
pub fn isOpaqueAtom(self: *Prove, symbols: Symbols, t: TermId) bool {
    const node = self.pool.get(t);
    if (node != .app) return false;
    const sym = node.app.sym;
    return !(symIs(sym, symbols.add) or symIs(sym, symbols.succ) or
        symIs(sym, symbols.prev) or symIs(sym, symbols.neg) or
        symIs(sym, symbols.sub) or symIs(sym, symbols.zero) or
        symIs(sym, symbols.one));
}

pub fn buildComb(self: *Prove, symbols: Symbols, leaves: []const TermId) Allocator.Error!?TermId {
    if (leaves.len == 0) {
        const zero = symbols.zero orelse return null;
        return try self.pool.addApp(.app, zero, &.{});
    }
    var cur = leaves[leaves.len - 1];
    var i = leaves.len - 1;
    while (i > 0) {
        i -= 1;
        const add_sym = symbols.add orelse return null;
        cur = try self.pool.addApp(.app, add_sym, &.{ leaves[i], cur });
    }
    return cur;
}

pub fn buildTower(self: *Prove, symbols: Symbols, succs: usize, comb: TermId) Allocator.Error!?TermId {
    var cur = comb;
    for (0..succs) |_| {
        const succ_sym = symbols.succ orelse return null;
        cur = try self.pool.addApp(.app, succ_sym, &.{cur});
    }
    return cur;
}

/// A SIGNED tower: succ^n(comb) for n ≥ 0, prev^|n|(comb) for n < 0.
pub fn buildTowerSigned(self: *Prove, symbols: Symbols, offset: i128, comb: TermId) Allocator.Error!?TermId {
    if (offset >= 0) return buildTower(self, symbols, @intCast(offset), comb);
    const prev_sym = symbols.prev orelse return null;
    var cur = comb;
    var n = -offset;
    while (n > 0) : (n -= 1) cur = try self.pool.addApp(.app, prev_sym, &.{cur});
    return cur;
}

/// buildComb but with a trailing ZERO base: l0 + (l1 + ... + (l_{n-1} + 0)).
pub fn buildCombWithZeroTail(self: *Prove, symbols: Symbols, leaves: []const TermId) Allocator.Error!?TermId {
    const zero = try self.pool.addApp(.app, symbols.zero orelse return null, &.{});
    var cur = zero;
    var i = leaves.len;
    while (i > 0) {
        i -= 1;
        cur = try self.pool.addApp(.app, symbols.add orelse return null, &.{ leaves[i], cur });
    }
    return cur;
}

/// Emit one adjacent swap of `order[pos]` / `order[pos+1]` in the tower `succ^k(sum(order))`.
pub fn emitSwap(
    self: *Prove,
    symbols: Symbols,
    rules: []const rewrite.Rule,
    comm_idx: ?usize,
    swap_idx: ?usize,
    offset: i128,
    order: []TermId,
    pos: usize,
    whole: TermId,
    trace: *std.ArrayList(rewrite.Rewrite),
) Allocator.Error!?TermId {
    const tail_pair = pos + 2 == order.len;
    const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse return null;
    const sub_before = (try buildComb(self, symbols, order[pos..])) orelse return null;
    std.mem.swap(TermId, &order[pos], &order[pos + 1]);
    const sub_after = (try buildComb(self, symbols, order[pos..])) orelse return null;
    const after = (try buildTowerSigned(self, symbols, offset, (try buildComb(self, symbols, order)) orelse return null)) orelse return null;
    const rule = rules[rule_idx];
    const bindings = (try rewrite.matchRule(self.ctx.arena, self.pool, self.ctx.interner, rule, rule.lhs, sub_before)) orelse return null;
    try trace.append(self.ctx.arena, .{ .before = whole, .after = after, .rule_idx = rule_idx, .bindings = bindings, .inst_lhs = sub_before, .inst_rhs = sub_after });
    return after;
}

/// Cancel additive-inverse pairs in a sorted tower `succ^k(sum)`; the tower (its offset k) is
/// re-parsed from `whole` each round, and every emitted rewrite rebuilds the WHOLE tower. The
/// neg-cancel rule indices are located by scanning `rules` for the addNegRight/addNegLeft/
/// addZeroLeft/addZeroRight cite heads (a structural scan over the hardcoded set — the fold
/// rules past fold_end and the fold prefix). `pub` so the arithmetic additive normalizer
/// (arithCanon) reuses the SAME bubble-to-adjacent cancellation (a non-adjacent inverse pair
/// `x … neg(x)` is bubbled together before cancelling) rather than relying on sort adjacency,
/// which misses pairs separated by another summand.
pub fn cancelInverses(
    self: *Prove,
    symbols: Symbols,
    rules: []const rewrite.Rule,
    comm_idx: ?usize,
    swap_idx: ?usize,
    whole0: TermId,
    trace: *std.ArrayList(rewrite.Rewrite),
) Allocator.Error!?TermId {
    if (symbols.neg == null or symbols.add == null or symbols.zero == null) return whole0;
    // Locate the four cancellation/zero-drop rules by their fabricated shape against the
    // hardcoded set (no name lookup — match the rule bodies structurally).
    const neg_right_idx = findNegCancel(self, rules, symbols, .right) orelse return whole0;
    const neg_left_idx = findNegCancel(self, rules, symbols, .left) orelse return whole0;
    const zero_left = findZeroDrop(self, rules, symbols, .left);
    const zero_right = findZeroDrop(self, rules, symbols, .right);

    var whole = whole0;
    outer: while (true) {
        const tower = (try parseTower(self, symbols, whole)) orelse return whole;
        const offset = tower.offset;
        const leaves = tower.leaves;
        var pair: ?struct { i: usize, j: usize } = null;
        for (leaves, 0..) |lj, j| {
            const nj = self.pool.get(lj);
            if (nj != .app or !symIs(nj.app.sym, symbols.neg)) continue;
            const inner = self.pool.args(nj.app)[0];
            for (leaves, 0..) |li, i| {
                if (i == j) continue;
                if (self.pool.alphaEq(li, inner)) {
                    pair = .{ .i = i, .j = j };
                    break;
                }
            }
            if (pair != null) break;
        }
        const p = pair orelse return whole;

        var order = try self.ctx.arena.dupe(TermId, leaves);
        var lo = p.i;
        var hi = p.j;
        if (lo > hi) {
            const tmp = lo;
            lo = hi;
            hi = tmp;
        }
        const n = order.len;
        var pos = hi;
        while (pos + 1 < n) : (pos += 1) {
            whole = (try emitSwap(self, symbols, rules, comm_idx, swap_idx, offset, order, pos, whole, trace)) orelse return null;
        }
        pos = lo;
        while (pos + 1 < n - 1) : (pos += 1) {
            whole = (try emitSwap(self, symbols, rules, comm_idx, swap_idx, offset, order, pos, whole, trace)) orelse return null;
        }
        const xpos = n - 2;
        const left = order[xpos];
        const right = order[xpos + 1];
        const rule_idx: usize = if (self.pool.alphaEq(right, try self.pool.addApp(.app, symbols.neg.?, &.{left})))
            neg_right_idx
        else if (self.pool.alphaEq(left, try self.pool.addApp(.app, symbols.neg.?, &.{right})))
            neg_left_idx
        else
            return null;

        const before_cancel = whole;
        const zero = try self.pool.addApp(.app, symbols.zero.?, &.{});
        const pair_term = try self.pool.addApp(.app, symbols.add.?, &.{ left, right });
        const neg_rule = rules[rule_idx];
        const neg_bindings = (try rewrite.matchRule(self.ctx.arena, self.pool, self.ctx.interner, neg_rule, neg_rule.lhs, pair_term)) orelse return null;
        const reduced = order[0..xpos];
        const comb0 = (try buildCombWithZeroTail(self, symbols, reduced)) orelse return null;
        const after_cancel = (try buildTowerSigned(self, symbols, offset, comb0)) orelse return null;
        try trace.append(self.ctx.arena, .{ .before = before_cancel, .after = after_cancel, .rule_idx = rule_idx, .bindings = neg_bindings, .inst_lhs = pair_term, .inst_rhs = zero });
        whole = after_cancel;

        const zl = zero_left orelse return null;
        const zr = zero_right orelse return null;
        const zero_rules = [_]rewrite.Rule{ rules[zl], rules[zr] };
        const zres = rewrite.normalize(self.ctx.arena, self.pool, self.ctx.interner, &zero_rules, whole, 1000) catch return null;
        for (zres.trace) |rw| {
            var r = rw;
            r.rule_idx = if (rw.rule_idx == 0) zl else zr;
            try trace.append(self.ctx.arena, r);
        }
        whole = zres.nf;
        continue :outer;
    }
}

/// Find the addNegRight (`add(a, neg(a)) = 0`) / addNegLeft (`add(neg(a), a) = 0`) rule index
/// by matching the fabricated inverse-pair pattern against each rule's lhs (structural, no
/// name lookup). `side` picks which orientation the neg sits on.
pub fn findNegCancel(self: *Prove, rules: []const rewrite.Rule, symbols: Symbols, side: enum { left, right }) ?usize {
    for (rules, 0..) |rule, i| {
        const n = self.pool.get(rule.lhs);
        if (n != .app or !symIs(n.app.sym, symbols.add.?) or n.app.args.len != 2) continue;
        // rhs must be a bare ZERO
        const rn = self.pool.get(rule.rhs);
        if (rn != .app or !symIs(rn.app.sym, symbols.zero.?) or rn.app.args.len != 0) continue;
        const args = self.pool.args(n.app);
        const a0 = args[0];
        const a1 = args[1];
        // right: add(x, neg(x));  left: add(neg(x), x)
        const neg_arg = if (side == .right) a1 else a0;
        const pos_arg = if (side == .right) a0 else a1;
        const nn = self.pool.get(neg_arg);
        if (nn != .app or !symIs(nn.app.sym, symbols.neg.?) or nn.app.args.len != 1) continue;
        if (self.pool.alphaEq(self.pool.args(nn.app)[0], pos_arg)) return i;
    }
    return null;
}

/// Find the addZeroLeft (`add(0, a) = a`) / addZeroRight (`add(a, 0) = a`) rule index by
/// structural match (the ZERO factor's side selects left/right).
pub fn findZeroDrop(self: *Prove, rules: []const rewrite.Rule, symbols: Symbols, side: enum { left, right }) ?usize {
    for (rules, 0..) |rule, i| {
        const n = self.pool.get(rule.lhs);
        if (n != .app or !symIs(n.app.sym, symbols.add.?) or n.app.args.len != 2) continue;
        const args = self.pool.args(n.app);
        const zero_arg = if (side == .left) args[0] else args[1];
        const rest_arg = if (side == .left) args[1] else args[0];
        const zn = self.pool.get(zero_arg);
        if (zn != .app or !symIs(zn.app.sym, symbols.zero.?) or zn.app.args.len != 0) continue;
        // rhs must be the rest arg (the surviving fvar)
        if (self.pool.alphaEq(rule.rhs, rest_arg)) return i;
    }
    return null;
}

// --- tests ----------------------------------------------------------------------------
