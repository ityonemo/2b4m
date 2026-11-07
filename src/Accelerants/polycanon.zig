//! The `polynomial` tactic's RING CANONICALIZER. `polyCanon` rewrites one side of an
//! equation to a sorted-sum-of-sorted-monomials normal form, accumulating a replayable
//! rewrite trace; the tactic (`Polynomial.zig`) canonicalizes both sides and, if the normal
//! forms agree, hands the rules + cites + traces to the shared `EqCert.emitJoin`.
//!
//! The ring rewrite rules are HARDCODED shapes built from the goal's operator SymIds
//! (`polyRules`), never fetched by well-known name: there are NO lookups and NO existence
//! checks here — an operator absent from the goal is an Optional the CALLER left null, and
//! gating a rule on it is pure goal-structure inspection. Sits on the AC/tower substrate
//! (`ac.zig`) and the rewrite engine (`rewrite.zig`); nothing above it is imported.

const std = @import("std");
const term = @import("../term.zig");
const TermId = term.TermId;
const StrId = @import("../InternPool.zig").StrId;
const rewrite = @import("rewrite.zig");
const EqCert = @import("EqCert.zig");
const Site = @import("Site.zig");
const InternPool = @import("../InternPool.zig");
const ac = @import("ac.zig");
const testrig = @import("testrig.zig");
const Symbols = @import("symbols.zig").Symbols;
const testing = std.testing;

const Error = error{OutOfMemory};

/// Narrow a `Site.Error` (which carries `error.Recover` for diagnostic-emitting call sites) to
/// this module's OutOfMemory-only set. The reused Site methods (`freshNamed`,
/// `ac.flattenSum`, `ac.acPlan`) never emit a diagnostic — they only allocate — so `Recover` is
/// unreachable in practice; this keeps polyRules/polyCanon's declared error set OOM-only.
fn narrow(v: anytype) Error!@typeInfo(@TypeOf(v)).error_union.payload {
    return v catch |err| switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.Recover => unreachable,
    };
}

/// The ring operator SymIds read off the goal (then COMPLETED from the theory — see
/// completePolyOps) + the operand sort for pattern fvars. `add`/`mul` are each optional:
/// a ring identity in ONE operator (`neg(add(a,b)) = add(neg(a),neg(b))`; `mul(e,k) =
/// mul(neg(e),neg(k))`) is a polynomial identity whose canonicalization never touches the
/// other, and the rules/phases mentioning it are simply not applicable. At least one is set.
pub const Ops = struct {
    add: ?term.SymId,
    mul: ?term.SymId,
    zero: ?term.SymId,
    one: ?term.SymId,
    neg: ?term.SymId,
    sub: ?term.SymId,
    succ: ?term.SymId,
    prev: ?term.SymId,
    sort: term.SortId, // operand sort for freshly-built pattern fvars
};

/// A hardcoded ring rewrite rule set + how the emitted cert cites each rule (the well-known
/// lemma name, carried as a token whose `.qualifier` is the theory selector — set by the
/// CALLER via `qualifier`), plus the named index layout `polyCanon` reads back.
pub const PolyRules = struct {
    rules: []const rewrite.Rule,
    cites: []const EqCert.RuleCite, // parallel to rules; each .global{ head, is_axiom }
    fold_end: usize,
    /// the operator triples' indices — null when that operator is absent from `ops`.
    mul_assoc: ?usize,
    mul_comm: ?usize,
    mul_swap: ?usize,
    add_assoc: ?usize,
    add_comm: ?usize,
    add_swap: ?usize,
    ops: Ops,
};

// -- pattern / rule construction -------------------------------------------------------

/// Mint a fresh pattern fvar term (`p#N` of the operand sort) + return {StrId, TermId}.
fn freshFvar(self: *Site, ops: Ops) Error!struct { name: StrId, term: TermId } {
    const name = try narrow(self.freshNamed("p#"));
    const t = try self.pool.add(.{ .fvar = .{ .name = name, .sort = ops.sort } });
    return .{ .name = name, .term = t };
}

/// Wrap an eq(lhs, rhs) over `binders` (occurrence order) in `forall`s, outermost = binders[0].
fn quantifyRule(self: *Site, binders: []const rewrite.Binder, lhs: TermId, rhs: TermId) Error!TermId {
    var body = try self.pool.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
    // close innermost-first (last binder becomes the innermost quant) so the outer quant is
    // binders[0] — matching emitInstance's outermost-first apply_at walk.
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        const b = binders[i];
        const closed = try self.pool.close(body, b.fvar);
        body = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = b.sort, .hint = b.fvar, .body = closed } });
    }
    return body;
}

fn app(self: *Site, sym: term.SymId, args: []const TermId) Error!TermId {
    return self.pool.addApp(.app, sym, args);
}

/// A hardcoded ring rule + the cite naming its well-known lemma, accumulated together.
const RuleAcc = struct {
    rules: std.ArrayList(rewrite.Rule) = .empty,
    cites: std.ArrayList(EqCert.RuleCite) = .empty,
    /// the call-site loc stamped into every cite head, so a "reference not found" on a generated
    /// lemma cite points at the `polynomial` step (not 1:1).
    loc: u32 = 0,

    fn push(acc: *RuleAcc, self: *Site, rule: rewrite.Rule, name: StrId, qualifier: StrId) Error!void {
        try acc.rules.append(self.ctx.arena, rule);
        try acc.cites.append(self.ctx.arena, .{ .global = .{
            .head = .{ .tag = .identifier, .start = acc.loc, .end = acc.loc, .name = name, .qualifier = qualifier },
            .is_axiom = false,
        } });
    }
};

fn binder(name: StrId, ops: Ops) rewrite.Binder {
    return .{ .fvar = name, .sort = ops.sort };
}

/// Build the hardcoded ring rule set (patterns constructed from `ops`, fresh pattern fvars via
/// `Site.freshNamed`) + the parallel cites, all cited in the theory namespace `qualifier`.
/// The index layout (fold_end + the two operator triples) matches the deleted `polyRules`.
pub fn polyRules(self: *Site, ops: Ops, qualifier: StrId, loc: u32) Error!PolyRules {
    var acc: RuleAcc = .{ .loc = loc };
    const nm = struct {
        fn f(p: *Site, comptime s: []const u8) Error!StrId {
            return p.ctx.interner.internString(s) catch error.OutOfMemory;
        }
    }.f;

    // -- fold rules [0 .. fold_end) — distribution + identity/zero folding. Each rule is
    //    built only when every operator it mentions is present in `ops` (a one-operator goal
    //    has no distribution to do; a goal without ZERO has no zero-fold). ------------------
    if (ops.add != null and ops.mul != null) {
        const add = ops.add.?;
        const mul = ops.mul.?;
        // mulAddDistribLeft: mul(a, add(b, c)) = add(mul(a, b), mul(a, c))
        {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const c = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
            const lhs = try app(self, mul, &.{ a.term, try app(self, add, &.{ b.term, c.term }) });
            const rhs = try app(self, add, &.{ try app(self, mul, &.{ a.term, b.term }), try app(self, mul, &.{ a.term, c.term }) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulAddDistribLeft"), qualifier);
        }
        // mulAddDistribRight: mul(add(a, b), c) = add(mul(a, c), mul(b, c))
        {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const c = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
            const lhs = try app(self, mul, &.{ try app(self, add, &.{ a.term, b.term }), c.term });
            const rhs = try app(self, add, &.{ try app(self, mul, &.{ a.term, c.term }), try app(self, mul, &.{ b.term, c.term }) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulAddDistribRight"), qualifier);
        }
    }
    // identity/zero folds: each needs its constant AND its operator (skipped otherwise).
    try pushIdentityFold(self, &acc, ops, qualifier, .mul_one_left);
    try pushIdentityFold(self, &acc, ops, qualifier, .mul_one_right);
    try pushIdentityFold(self, &acc, ops, qualifier, .mul_zero_left);
    try pushIdentityFold(self, &acc, ops, qualifier, .mul_zero_right);
    try pushIdentityFold(self, &acc, ops, qualifier, .add_zero_left);
    try pushIdentityFold(self, &acc, ops, qualifier, .add_zero_right);

    // -- OPTIONAL ring folds (gated on goal-present operators) -----------------------
    if (ops.sub != null and ops.neg != null and ops.add != null) {
        // definitionOfSubtraction: sub(a, b) = add(a, neg(b))
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
        const lhs = try app(self, ops.sub.?, &.{ a.term, b.term });
        const rhs = try app(self, ops.add.?, &.{ a.term, try app(self, ops.neg.?, &.{b.term}) });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "definitionOfSubtraction"), qualifier);
    }
    if (ops.neg) |neg| {
        // negAdd: neg(add(a, b)) = add(neg(a), neg(b))
        if (ops.add) |add| {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
            const lhs = try app(self, neg, &.{try app(self, add, &.{ a.term, b.term })});
            const rhs = try app(self, add, &.{ try app(self, neg, &.{a.term}), try app(self, neg, &.{b.term}) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "negAdd"), qualifier);
        }
        // negZero: neg(ZERO) = ZERO  (only if ZERO present)
        if (ops.zero) |zero| {
            const z0 = try app(self, zero, &.{});
            const z1 = try app(self, zero, &.{});
            const lhs = try app(self, neg, &.{z0});
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = z1, .formula = try quantifyRule(self, binders, lhs, z1) }, try nm(self, "negZero"), qualifier);
        }
        // negSucc / negPrev: only when both succ and prev present (ℤ)
        if (ops.succ != null and ops.prev != null) {
            // negSucc: neg(succ(a)) = prev(neg(a))
            {
                const a = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
                const lhs = try app(self, neg, &.{try app(self, ops.succ.?, &.{a.term})});
                const rhs = try app(self, ops.prev.?, &.{try app(self, neg, &.{a.term})});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "negSucc"), qualifier);
            }
            // negPrev: neg(prev(a)) = succ(neg(a))
            {
                const a = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
                const lhs = try app(self, neg, &.{try app(self, ops.prev.?, &.{a.term})});
                const rhs = try app(self, ops.succ.?, &.{try app(self, neg, &.{a.term})});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "negPrev"), qualifier);
            }
        }
        // negNeg: neg(neg(a)) = a
        {
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, neg, &.{try app(self, neg, &.{a.term})});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "negNeg"), qualifier);
        }
        if (ops.mul) |mul| {
            // mulNegLeft: mul(neg(a), b) = neg(mul(a, b))
            {
                const a = try freshFvar(self, ops);
                const b = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
                const lhs = try app(self, mul, &.{ try app(self, neg, &.{a.term}), b.term });
                const rhs = try app(self, neg, &.{try app(self, mul, &.{ a.term, b.term })});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulNegLeft"), qualifier);
            }
            // mulNegRight: mul(a, neg(b)) = neg(mul(a, b))
            {
                const a = try freshFvar(self, ops);
                const b = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
                const lhs = try app(self, mul, &.{ a.term, try app(self, neg, &.{b.term}) });
                const rhs = try app(self, neg, &.{try app(self, mul, &.{ a.term, b.term })});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulNegRight"), qualifier);
            }
        }
    }
    if (ops.succ != null and ops.mul != null and ops.add != null) {
        const succ = ops.succ.?;
        const mul = ops.mul.?;
        const add = ops.add.?;
        // mulSuccLeft: mul(succ(a), b) = add(mul(a, b), b)
        {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
            const lhs = try app(self, mul, &.{ try app(self, succ, &.{a.term}), b.term });
            const rhs = try app(self, add, &.{ try app(self, mul, &.{ a.term, b.term }), b.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulSuccLeft"), qualifier);
        }
        // mulSuccRight: mul(a, succ(b)) = add(mul(a, b), a)
        {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
            const lhs = try app(self, mul, &.{ a.term, try app(self, succ, &.{b.term}) });
            const rhs = try app(self, add, &.{ try app(self, mul, &.{ a.term, b.term }), a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulSuccRight"), qualifier);
        }
    }

    const fold_end = acc.rules.items.len;

    // -- additive-inverse cancellation (past fold_end) ------------------------------
    if (ops.neg != null and ops.zero != null and ops.add != null) {
        const neg = ops.neg.?;
        const zero = ops.zero.?;
        const add = ops.add.?;
        // addNegRight: add(a, neg(a)) = ZERO
        {
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ a.term, try app(self, neg, &.{a.term}) });
            const rhs = try app(self, zero, &.{});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "addNegRight"), qualifier);
        }
        // addNegLeft: add(neg(a), a) = ZERO
        {
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ try app(self, neg, &.{a.term}), a.term });
            const rhs = try app(self, zero, &.{});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "addNegLeft"), qualifier);
        }
    }

    // -- the operator triples (assoc / comm / swap), each only for a present operator --
    var mul_assoc: ?usize = null;
    if (ops.mul != null) {
        mul_assoc = acc.rules.items.len;
        try pushTriple(self, &acc, ops, qualifier, .mul);
    }
    var add_assoc: ?usize = null;
    if (ops.add != null) {
        add_assoc = acc.rules.items.len;
        try pushTriple(self, &acc, ops, qualifier, .add);
    }

    return .{
        .rules = acc.rules.items,
        .cites = acc.cites.items,
        .fold_end = fold_end,
        .mul_assoc = mul_assoc,
        .mul_comm = if (mul_assoc) |i| i + 1 else null,
        .mul_swap = if (mul_assoc) |i| i + 2 else null,
        .add_assoc = add_assoc,
        .add_comm = if (add_assoc) |i| i + 1 else null,
        .add_swap = if (add_assoc) |i| i + 2 else null,
        .ops = ops,
    };
}

const IdentityFold = enum { mul_one_left, mul_one_right, mul_zero_left, mul_zero_right, add_zero_left, add_zero_right };

/// Push one identity/zero fold rule. The identity/zero constants are read from `ops` — a fold
/// naming a const the goal lacks is simply skipped (the const's absence means the pattern
/// couldn't occur in the goal anyway; it does NOT shift the required index layout because the
/// distribution rules [0,1] are always present and the folds run to fixpoint by set).
fn pushIdentityFold(self: *Site, acc: *RuleAcc, ops: Ops, qualifier: StrId, which: IdentityFold) Error!void {
    const nm = struct {
        fn f(p: *Site, comptime s: []const u8) Error!StrId {
            return p.ctx.interner.internString(s) catch error.OutOfMemory;
        }
    }.f;
    switch (which) {
        .mul_one_left => {
            const one = ops.one orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, mul, &.{ try app(self, one, &.{}), a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "mulOneLeft"), qualifier);
        },
        .mul_one_right => {
            const one = ops.one orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, mul, &.{ a.term, try app(self, one, &.{}) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "mulOneRight"), qualifier);
        },
        .mul_zero_left => {
            const zero = ops.zero orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const z0 = try app(self, zero, &.{});
            const z1 = try app(self, zero, &.{});
            const lhs = try app(self, mul, &.{ z0, a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = z1, .formula = try quantifyRule(self, binders, lhs, z1) }, try nm(self, "mulZeroLeft"), qualifier);
        },
        .mul_zero_right => {
            const zero = ops.zero orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const z0 = try app(self, zero, &.{});
            const z1 = try app(self, zero, &.{});
            const lhs = try app(self, mul, &.{ a.term, z0 });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = z1, .formula = try quantifyRule(self, binders, lhs, z1) }, try nm(self, "mulZeroRight"), qualifier);
        },
        .add_zero_left => {
            const zero = ops.zero orelse return;
            const add = ops.add orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ try app(self, zero, &.{}), a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "addZeroLeft"), qualifier);
        },
        .add_zero_right => {
            const zero = ops.zero orelse return;
            const add = ops.add orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ a.term, try app(self, zero, &.{}) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "addZeroRight"), qualifier);
        },
    }
}

/// Push the [assoc, comm, swap] triple for the `add` or `mul` operator, in that order.
fn pushTriple(self: *Site, acc: *RuleAcc, ops: Ops, qualifier: StrId, comptime op: enum { add, mul }) Error!void {
    const sym = if (op == .add) ops.add.? else ops.mul.?;
    const assoc_nm = if (op == .add) "addIsAssociative" else "mulIsAssociative";
    const comm_nm = if (op == .add) "addIsCommutative" else "mulIsCommutative";
    const swap_nm = if (op == .add) "addLeftSwap" else "mulLeftSwap";
    const nm = struct {
        fn f(p: *Site, s: []const u8) Error!StrId {
            return p.ctx.interner.internString(s) catch error.OutOfMemory;
        }
    }.f;
    // assoc: op(op(a, b), c) = op(a, op(b, c))
    {
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const c = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
        const lhs = try app(self, sym, &.{ try app(self, sym, &.{ a.term, b.term }), c.term });
        const rhs = try app(self, sym, &.{ a.term, try app(self, sym, &.{ b.term, c.term }) });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, assoc_nm), qualifier);
    }
    // comm: op(a, b) = op(b, a)
    {
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
        const lhs = try app(self, sym, &.{ a.term, b.term });
        const rhs = try app(self, sym, &.{ b.term, a.term });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, comm_nm), qualifier);
    }
    // swap: op(a, op(b, c)) = op(b, op(a, c))
    {
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const c = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(rewrite.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
        const lhs = try app(self, sym, &.{ a.term, try app(self, sym, &.{ b.term, c.term }) });
        const rhs = try app(self, sym, &.{ b.term, try app(self, sym, &.{ a.term, c.term }) });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, swap_nm), qualifier);
    }
}

// -- canonicalization (ported from the deleted polyCanon) ------------------------------

fn symsFrom(ops: Ops, comptime which: enum { add, mul }) Symbols {
    return .{ .add = if (which == .add) ops.add else ops.mul };
}

/// Right-nest `x` under the add-associativity rule alone (a terminating normalization),
/// appending the re-indexed trace. `x` when there is no `add` (nothing to nest).
fn rightNestSum(self: *Site, pr: PolyRules, x: TermId, trace: *std.ArrayList(rewrite.Rewrite)) Error!?TermId {
    const add_assoc = pr.add_assoc orelse return x;
    const rules = pr.rules[add_assoc .. add_assoc + 1];
    const rn = rewrite.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules, x, 4000) catch |err| switch (err) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    for (rn.trace) |rw| {
        var r = rw;
        r.rule_idx = rw.rule_idx + add_assoc;
        try trace.append(self.ctx.arena, r);
    }
    return rn.nf;
}

/// Canonicalize `x` to a sorted-sum-of-sorted-monomials NF + the replayable trace over
/// `pr.rules`. Null on cap overflow / unhandled shape (caller then FAILS the accelerant).
pub fn polyCanon(self: *Site, pr: PolyRules, x: TermId) Error!?rewrite.Result {
    const ops = pr.ops;
    // 1) distribute + fold to a flat sum of monomials (terminating). Its trace is already
    //    whole-term (normalize over `x`).
    const fold_rules = pr.rules[0..pr.fold_end];
    const dist = rewrite.normalize(self.ctx.arena, self.pool, self.ctx.interner, fold_rules, x, 4000) catch |err| switch (err) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    var trace: std.ArrayList(rewrite.Rewrite) = .empty;
    try trace.appendSlice(self.ctx.arena, dist.trace);

    const add_symbols = symsFrom(ops, .add);
    const mul_symbols = symsFrom(ops, .mul);

    // 2) RIGHT-NEST the outer sum first (add-associativity only, terminating), so the running
    //    term is a right-nested comb and the ac.buildComb contexts below match exactly. Without
    //    `add` the whole term is ONE monomial: the sum phases (2, 4, 5) have a single leaf.
    const nested = (try rightNestSum(self, pr, dist.nf, &trace)) orelse return null;

    // 3) sort each monomial's factors (mul-ac.acPlan), lifting each sub-trace into the
    //    (right-nested) whole-sum context so the chain stays whole-term. Without `mul` a
    //    monomial is an atom (nothing to sort).
    var monos: std.ArrayList(TermId) = .empty;
    if (ops.add) |add| try narrow(ac.flattenSum(self, add, nested, &monos)) else try monos.append(self.ctx.arena, nested);
    var sorted_monos: std.ArrayList(TermId) = .empty;
    for (monos.items, 0..) |m, i| {
        if (pr.mul_assoc == null) {
            try sorted_monos.append(self.ctx.arena, m);
            continue;
        }
        // a NEGATED monomial `neg(m)` (the neg-folds pushed every neg outward to the summand):
        // its factors are sorted INSIDE the neg — a cross-term pair `a·b + neg(b·a)` only
        // cancels if both copies are canonical — and the sort trace is lifted through `neg(·)`.
        var wrap: ?term.SymId = null;
        var body = m;
        if (ops.neg) |neg| {
            const mn = self.pool.get(m);
            if (mn == .app and mn.app.sym == neg and mn.app.args.len == 1) {
                wrap = neg;
                body = self.pool.args(mn.app)[0];
            }
        }
        // ac.acPlan reads symbols.add.? as the reordered operator — pass mul in that slot.
        const mp = (try narrow(ac.acPlan(self, mul_symbols, pr.rules, pr.mul_assoc.?, pr.mul_comm.?, pr.mul_swap.?, body))) orelse return null;
        if (mp.trace.len > 0) {
            // lifted into the whole-sum context (a one-leaf comb when there is no `add`).
            const lifted = try liftMonoTrace(self, add_symbols, sorted_monos.items, monos.items[i + 1 ..], wrap, mp.trace, &trace);
            if (!lifted) return null;
        }
        try sorted_monos.append(self.ctx.arena, if (wrap) |w| try self.pool.addApp(.app, w, &.{mp.sorted}) else mp.sorted);
    }
    if (ops.add == null) return .{ .nf = sorted_monos.items[0], .trace = trace.items };
    const mono_sum = (try ac.buildComb(self, add_symbols, sorted_monos.items)) orelse return null;

    // 4) bubble-sort the sum of monomials (already right-nested → sort phase only).
    var leaves: std.ArrayList(TermId) = .empty;
    try narrow(ac.flattenSum(self, ops.add.?, mono_sum, &leaves));
    var sorted = (try sortTraceTower(self, add_symbols, pr.rules, pr.add_comm.?, pr.add_swap.?, .{ .offset = 0, .leaves = leaves.items }, &trace)) orelse return null;

    // 5) cancel additive-inverse monomials (m + neg(m) → 0) in the sorted sum. `one` is
    //    deliberately LEFT NULL: polynomial does NOT reduce ONE to succ(ZERO), so a bare ONE
    //    summand must ride as an opaque LEAF. succ/prev stay set so numeral towers still fold.
    if (ops.neg != null and ops.zero != null) {
        const cancel_symbols: Symbols = .{
            .add = ops.add,
            .mul = ops.mul,
            .neg = ops.neg,
            .zero = ops.zero,
            .succ = ops.succ,
            .prev = ops.prev,
        };
        sorted = (try ac.cancelInverses(self, cancel_symbols, pr.rules, pr.add_comm.?, pr.add_swap.?, sorted, &trace)) orelse return null;
    }
    return .{ .nf = sorted, .trace = trace.items };
}

// -- the tower substrate (ported PRIVATE from the deleted elaborate.zig) ----------------

/// Lift a sub-term trace into whole-term context (ported liftMonoTrace): the rewritten
/// monomial sits in the hole between `before` and `after` in the sum comb — wrapped in
/// `wrap(·)` (a negated summand) when given.
fn liftMonoTrace(
    self: *Site,
    add_symbols: Symbols,
    before: []const TermId,
    after: []const TermId,
    wrap: ?term.SymId,
    sub_trace: []const rewrite.Rewrite,
    out: *std.ArrayList(rewrite.Rewrite),
) Error!bool {
    var slots: std.ArrayList(TermId) = .empty;
    try slots.appendSlice(self.ctx.arena, before);
    const hole = slots.items.len;
    try slots.append(self.ctx.arena, sub_trace[0].before); // placeholder, overwritten per entry
    try slots.appendSlice(self.ctx.arena, after);
    for (sub_trace) |rw| {
        slots.items[hole] = if (wrap) |w| try self.pool.addApp(.app, w, &.{rw.before}) else rw.before;
        const w_before = (try ac.buildComb(self, add_symbols, slots.items)) orelse return false;
        slots.items[hole] = if (wrap) |w| try self.pool.addApp(.app, w, &.{rw.after}) else rw.after;
        const w_after = (try ac.buildComb(self, add_symbols, slots.items)) orelse return false;
        try out.append(self.ctx.arena, .{
            .before = w_before,
            .after = w_after,
            .rule_idx = rw.rule_idx,
            .bindings = rw.bindings,
            .inst_lhs = rw.inst_lhs,
            .inst_rhs = rw.inst_rhs,
        });
    }
    return true;
}

/// Bubble-sort a tower's summands, appending one rewrite per adjacent swap (tower-based sort,
/// the deleted elaborate.zig `ac.sortTrace` — NOT Prove's leaf-based one). Null when a needed
/// sort lemma index is absent or a shape assumption fails.
fn sortTraceTower(
    self: *Site,
    symbols: Symbols,
    rules: []const rewrite.Rule,
    comm_idx: ?usize,
    swap_idx: ?usize,
    tower: ac.Tower,
    trace: *std.ArrayList(rewrite.Rewrite),
) Error!?TermId {
    const leaves = try self.ctx.arena.dupe(TermId, tower.leaves);
    var whole = (try ac.buildTowerSigned(self, symbols, tower.offset, (try ac.buildComb(self, symbols, leaves)) orelse return null)) orelse return null;
    if (leaves.len > 1) {
        for (0..leaves.len - 1) |pass| {
            for (0..leaves.len - 1 - pass) |i| {
                if (self.pool.termOrder(leaves[i], leaves[i + 1]) != .gt) continue;
                const tail_pair = i + 2 == leaves.len;
                const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse return null;
                const sub_before = (try ac.buildComb(self, symbols, leaves[i..])) orelse return null;
                std.mem.swap(TermId, &leaves[i], &leaves[i + 1]);
                const sub_after = (try ac.buildComb(self, symbols, leaves[i..])) orelse return null;
                const after = (try ac.buildTowerSigned(self, symbols, tower.offset, (try ac.buildComb(self, symbols, leaves)) orelse return null)) orelse return null;
                const rule = rules[rule_idx];
                const bindings = (try rewrite.matchRule(self.ctx.arena, self.pool, self.ctx.interner, rule, rule.lhs, sub_before)) orelse return null;
                try trace.append(self.ctx.arena, .{
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

/// Test helper: an `Ops` over the rig's integer sort with only the named symbols set.
fn opsOf(rig: testrig.Rig, add: ?term.SymId, mul: ?term.SymId, neg: ?term.SymId, zero: ?term.SymId) Ops {
    return .{ .add = add, .mul = mul, .zero = zero, .one = null, .neg = neg, .sub = null, .succ = null, .prev = null, .sort = rig.int };
}

test "polyRules: an add-only op set builds the add triple and neg-folds but NO mul rules" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.site, opsOf(rig, rig.add, null, rig.neg, null), .none, 0);
    try testing.expect(pr.add_assoc != null);
    try testing.expect(pr.mul_assoc == null);
    // every rule's pattern mentions only add/neg: no rule head is `mul`.
    for (pr.rules) |r| {
        const n = rig.site.pool.get(r.lhs);
        if (n == .app) try testing.expect(n.app.sym != rig.mul);
    }
}

test "polyCanon: an add-only identity canonicalizes — neg(add(a, b)) ≡ add(neg(a), neg(b))" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.site, opsOf(rig, rig.add, null, rig.neg, null), .none, 0);
    const a = try rig.v("a");
    const b = try rig.v("b");
    const lhs = try rig.a1(rig.neg, try rig.a2(rig.add, a, b));
    const rhs = try rig.a2(rig.add, try rig.a1(rig.neg, a), try rig.a1(rig.neg, b));
    const rs = (try polyCanon(rig.site, pr, lhs)).?;
    const rt = (try polyCanon(rig.site, pr, rhs)).?;
    try testing.expect(rig.site.pool.alphaEq(rs.nf, rt.nf));
}

test "polyCanon: a mul-only identity canonicalizes — mul(mul(d, k), m) ≡ mul(k, mul(d, m))" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.site, opsOf(rig, null, rig.mul, null, null), .none, 0);
    try testing.expect(pr.add_assoc == null);
    const d = try rig.v("d");
    const k = try rig.v("k");
    const m = try rig.v("m");
    const lhs = try rig.a2(rig.mul, try rig.a2(rig.mul, d, k), m);
    const rhs = try rig.a2(rig.mul, k, try rig.a2(rig.mul, d, m));
    const rs = (try polyCanon(rig.site, pr, lhs)).?;
    const rt = (try polyCanon(rig.site, pr, rhs)).?;
    try testing.expect(rig.site.pool.alphaEq(rs.nf, rt.nf));
}

test "polyCanon: an inverse pair cancels when ZERO is supplied by the theory, not the goal — add(x, add(t, neg(t))) ≡ x" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    // the goal mentions no ZERO; the op set carries the theory's ZERO (completePolyOps' job).
    const pr = try polyRules(rig.site, opsOf(rig, rig.add, rig.mul, rig.neg, rig.zero), .none, 0);
    const x = try rig.v("x");
    const t = try rig.a2(rig.mul, try rig.v("a"), try rig.v("r"));
    const lhs = try rig.a2(rig.add, x, try rig.a2(rig.add, t, try rig.a1(rig.neg, t)));
    const rs = (try polyCanon(rig.site, pr, lhs)).?;
    const rt = (try polyCanon(rig.site, pr, x)).?;
    try testing.expect(rig.site.pool.alphaEq(rs.nf, rt.nf));
}

test "polyCanon: a cross-term cancels — the monomial INSIDE neg(…) gets its factors sorted too: add(mul(a, b), neg(mul(b, a))) ≡ ZERO" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.site, opsOf(rig, rig.add, rig.mul, rig.neg, rig.zero), .none, 0);
    const a = try rig.v("a");
    const b = try rig.v("b");
    const lhs = try rig.a2(rig.add, try rig.a2(rig.mul, a, b), try rig.a1(rig.neg, try rig.a2(rig.mul, b, a)));
    const zero = try rig.site.pool.addApp(.app, rig.zero, &.{});
    const rs = (try polyCanon(rig.site, pr, lhs)).?;
    const rt = (try polyCanon(rig.site, pr, zero)).?;
    try testing.expect(rig.site.pool.alphaEq(rs.nf, rt.nf));
    // and with NO surrounding sum: neg(mul(b, a)) alone canonicalizes like neg(mul(a, b)).
    const n1 = (try polyCanon(rig.site, pr, try rig.a1(rig.neg, try rig.a2(rig.mul, b, a)))).?;
    const n2 = (try polyCanon(rig.site, pr, try rig.a1(rig.neg, try rig.a2(rig.mul, a, b)))).?;
    try testing.expect(rig.site.pool.alphaEq(n1.nf, n2.nf));
}

/// Read the ring operator SymIds off `eq_goal` (an equation) by scanning for apps whose head
/// NAME is a well-known ring operator. At least ONE of `add`/`mul` is required (null return
/// otherwise — a goal with neither is no polynomial); each is optional on its own, a ring
/// identity in one operator being a polynomial identity in that operator. The operand sort
/// (for freshly-built rule-pattern fvars) is the equation's lhs sort.
pub fn readPolyOps(site: *Site, eq_goal: TermId) Error!?Ops {
    const eqn = site.pool.get(eq_goal);
    if (eqn != .eq) return null;
    var found: Ops = .{
        .add = null,
        .mul = null,
        .zero = null,
        .one = null,
        .neg = null,
        .sub = null,
        .succ = null,
        .prev = null,
        .sort = @enumFromInt(@intFromEnum(site.termSort(eqn.eq.lhs))),
    };
    var have_add = false;
    var have_mul = false;
    try collectPolyOps(site, eq_goal, &found, &have_add, &have_mul);
    if (!have_add and !have_mul) return null;
    return found;
}

/// A symbol's WELL-KNOWN name for vocabulary matching: under a TRANSFER the goal's syms are
/// TARGET images (`tadd`), but the well-known vocabulary (add/mul/…) is the SOURCE theory's —
/// reverse-map through the overlay to the source symbol's name.
pub fn vocabName(site: *Site, ix: InternPool.Index) []const u8 {
    if (site.model != InternPool.Index.none and site.model != .universe) {
        var cur = site.model;
        while (true) {
            const m = site.ctx.interner.keyOf(cur).model;
            for (m.overlay) |mp| if (mp.tgt == ix and mp.src != ix)
                return site.ctx.interner.stringBytes(site.ctx.interner.nameOf(mp.src));
            if (cur == m.parent) break;
            cur = m.parent;
        }
    }
    return site.ctx.interner.stringBytes(site.ctx.interner.nameOf(ix));
}

/// Recursively match each app head's well-known NAME, filling `ops`. Pure goal inspection.
pub fn collectPolyOps(site: *Site, id: TermId, ops: *Ops, have_add: *bool, have_mul: *bool) Error!void {
    // iterative single-tree collector (was native recursion). Records the polynomial vocabulary
    // ops by well-known name; field-setting is order-independent so a plain work-stack suffices.
    var scratch: std.heap.ArenaAllocator = .init(site.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = site.pool.get(cur);
        if (node == .app) {
            const a = node.app;
            const name = vocabName(site, @enumFromInt(@intFromEnum(a.sym)));
            if (std.mem.eql(u8, name, "add")) {
                ops.add = a.sym;
                have_add.* = true;
            } else if (std.mem.eql(u8, name, "mul")) {
                ops.mul = a.sym;
                have_mul.* = true;
            } else if (std.mem.eql(u8, name, "ZERO")) {
                ops.zero = a.sym;
            } else if (std.mem.eql(u8, name, "ONE")) {
                ops.one = a.sym;
            } else if (std.mem.eql(u8, name, "neg")) {
                ops.neg = a.sym;
            } else if (std.mem.eql(u8, name, "sub")) {
                ops.sub = a.sym;
            } else if (std.mem.eql(u8, name, "succ")) {
                ops.succ = a.sym;
            } else if (std.mem.eql(u8, name, "prev")) {
                ops.prev = a.sym;
            }
        }
        // `.pred` is NOT descended (the original had no `.pred` arm — only app/eq/bin/not/quant).
        switch (node) {
            .app, .eq, .bin, .not, .quant => try site.pool.pushChildren(&stack, wa, node),
            else => {},
        }
    }
}

test "readPolyOps: an add-only goal reads add (and neg), leaves mul absent" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const a = try rig.v("a");
    const b = try rig.v("b");
    // neg(add(a, b)) = add(neg(a), neg(b))
    const goal = try rig.eq(try rig.a1(rig.neg, try rig.a2(rig.add, a, b)), try rig.a2(rig.add, try rig.a1(rig.neg, a), try rig.a1(rig.neg, b)));
    const ops = (try readPolyOps(rig.site, goal)).?;
    try testing.expectEqual(rig.add, ops.add.?);
    try testing.expect(ops.mul == null);
    try testing.expectEqual(rig.neg, ops.neg.?);
    try testing.expect(ops.zero == null);
}

test "readPolyOps: a mul-only goal reads mul, leaves add absent; a goal with neither is no polynomial" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const e = try rig.v("e");
    const k = try rig.v("k");
    // mul(e, k) = mul(neg(e), neg(k))
    const goal = try rig.eq(try rig.a2(rig.mul, e, k), try rig.a2(rig.mul, try rig.a1(rig.neg, e), try rig.a1(rig.neg, k)));
    const ops = (try readPolyOps(rig.site, goal)).?;
    try testing.expectEqual(rig.mul, ops.mul.?);
    try testing.expect(ops.add == null);
    // neg(e) = neg(k): no ring operator at all → not a polynomial goal.
    const bare = try rig.eq(try rig.a1(rig.neg, e), try rig.a1(rig.neg, k));
    try testing.expect((try readPolyOps(rig.site, bare)) == null);
}
