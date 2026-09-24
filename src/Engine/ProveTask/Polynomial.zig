//! Polynomial — the `polynomial` accelerant's ring canonicalization core (leaf module).
//!
//! MECHANICAL PORT of the deleted eager `polyCanon` + its tower substrate, with ONE design
//! change: the ring rewrite rules are HARDCODED shapes built from the goal's operator SymIds
//! (`polyRules`), NOT fetched by well-known name. There are NO lookups and NO existence checks
//! here — an operator that isn't present in the goal is an Optional the CALLER left null, and
//! gating a rule on it is pure goal-structure inspection.
//!
//! `polyCanon` canonicalizes one side of an equation to a sorted-sum-of-sorted-monomials
//! normal form, accumulating a replayable rewrite trace over the hardcoded rule set. The
//! caller (`Prove.producePolynomial`) canonicalizes both sides and, if the NFs agree, hands
//! the rules + cites + traces to the shared `EqCert.emitJoin`.

const std = @import("std");
const term = @import("../../term.zig");
const TermId = term.TermId;
const StrId = @import("../../InternPool.zig").StrId;
const simplify_mod = @import("simplify.zig");
const presburger_mod = @import("presburger.zig");
const EqCert = @import("EqCert.zig");
const Prove = @import("Prove.zig");
const Context = @import("../../Context.zig");
const Engine = @import("../../Engine.zig");
const InternPool = @import("../../InternPool.zig");
const lexer = @import("../../lexer.zig");

const Error = error{OutOfMemory};

/// Narrow a `Prove.Error` (which carries `error.Recover` for diagnostic-emitting call sites) to
/// this module's OutOfMemory-only set. The reused Prove substrate methods (`freshNamed`,
/// `flattenSum`, `acPlan`) never emit a diagnostic — they only allocate — so `Recover` is
/// unreachable in practice; this keeps polyRules/polyCanon's declared error set OOM-only.
fn narrow(v: anytype) Error!@typeInfo(@TypeOf(v)).error_union.payload {
    return v catch |e| switch (e) {
        error.OutOfMemory => error.OutOfMemory,
        error.Recover => unreachable,
    };
}

/// The ring operator SymIds read off the goal (then COMPLETED from the theory — see
/// Prove.completePolyOps) + the operand sort for pattern fvars. `add`/`mul` are each optional:
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
    rules: []const simplify_mod.Rule,
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
fn freshFvar(self: *Prove, ops: Ops) Error!struct { name: StrId, term: TermId } {
    const name = try narrow(self.freshNamed("p#"));
    const t = try self.pool.add(.{ .fvar = .{ .name = name, .sort = ops.sort } });
    return .{ .name = name, .term = t };
}

/// Wrap an eq(lhs, rhs) over `binders` (occurrence order) in `forall`s, outermost = binders[0].
fn quantifyRule(self: *Prove, binders: []const simplify_mod.Binder, lhs: TermId, rhs: TermId) Error!TermId {
    var body = try self.pool.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
    // close innermost-first (last binder becomes the innermost quant) so the outer quant is
    // binders[0] — matching emitInstance's outermost-first forall_elim walk.
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        const b = binders[i];
        const closed = try self.pool.close(body, b.fvar);
        body = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = b.sort, .hint = b.fvar, .body = closed } });
    }
    return body;
}

fn app(self: *Prove, sym: term.SymId, args: []const TermId) Error!TermId {
    return self.pool.addApp(.app, sym, args);
}

/// A hardcoded ring rule + the cite naming its well-known lemma, accumulated together.
const RuleAcc = struct {
    rules: std.ArrayList(simplify_mod.Rule) = .empty,
    cites: std.ArrayList(EqCert.RuleCite) = .empty,
    /// the call-site loc stamped into every cite head, so a "reference not found" on a generated
    /// lemma cite points at the `polynomial` step (not 1:1).
    loc: u32 = 0,

    fn push(acc: *RuleAcc, self: *Prove, rule: simplify_mod.Rule, name: StrId, qualifier: StrId) Error!void {
        try acc.rules.append(self.ctx.arena, rule);
        try acc.cites.append(self.ctx.arena, .{ .global = .{
            .head = .{ .tag = .identifier, .start = acc.loc, .end = acc.loc, .name = name, .qualifier = qualifier },
            .is_axiom = false,
        } });
    }
};

fn binder(name: StrId, ops: Ops) simplify_mod.Binder {
    return .{ .fvar = name, .sort = ops.sort };
}

/// Build the hardcoded ring rule set (patterns constructed from `ops`, fresh pattern fvars via
/// `Prove.freshNamed`) + the parallel cites, all cited in the theory namespace `qualifier`.
/// The index layout (fold_end + the two operator triples) matches the deleted `polyRules`.
pub fn polyRules(self: *Prove, ops: Ops, qualifier: StrId, loc: u32) Error!PolyRules {
    var acc: RuleAcc = .{ .loc = loc };
    const nm = struct {
        fn f(p: *Prove, comptime s: []const u8) Error!StrId {
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
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
            const lhs = try app(self, mul, &.{ a.term, try app(self, add, &.{ b.term, c.term }) });
            const rhs = try app(self, add, &.{ try app(self, mul, &.{ a.term, b.term }), try app(self, mul, &.{ a.term, c.term }) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulAddDistribLeft"), qualifier);
        }
        // mulAddDistribRight: mul(add(a, b), c) = add(mul(a, c), mul(b, c))
        {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const c = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
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
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
        const lhs = try app(self, ops.sub.?, &.{ a.term, b.term });
        const rhs = try app(self, ops.add.?, &.{ a.term, try app(self, ops.neg.?, &.{b.term}) });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "definitionOfSubtraction"), qualifier);
    }
    if (ops.neg) |neg| {
        // negAdd: neg(add(a, b)) = add(neg(a), neg(b))
        if (ops.add) |add| {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
            const lhs = try app(self, neg, &.{try app(self, add, &.{ a.term, b.term })});
            const rhs = try app(self, add, &.{ try app(self, neg, &.{a.term}), try app(self, neg, &.{b.term}) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "negAdd"), qualifier);
        }
        // negZero: neg(ZERO) = ZERO  (only if ZERO present)
        if (ops.zero) |zero| {
            const z0 = try app(self, zero, &.{});
            const z1 = try app(self, zero, &.{});
            const lhs = try app(self, neg, &.{z0});
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = z1, .formula = try quantifyRule(self, binders, lhs, z1) }, try nm(self, "negZero"), qualifier);
        }
        // negSucc / negPrev: only when both succ and prev present (ℤ)
        if (ops.succ != null and ops.prev != null) {
            // negSucc: neg(succ(a)) = prev(neg(a))
            {
                const a = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
                const lhs = try app(self, neg, &.{try app(self, ops.succ.?, &.{a.term})});
                const rhs = try app(self, ops.prev.?, &.{try app(self, neg, &.{a.term})});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "negSucc"), qualifier);
            }
            // negPrev: neg(prev(a)) = succ(neg(a))
            {
                const a = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
                const lhs = try app(self, neg, &.{try app(self, ops.prev.?, &.{a.term})});
                const rhs = try app(self, ops.succ.?, &.{try app(self, neg, &.{a.term})});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "negPrev"), qualifier);
            }
        }
        // negNeg: neg(neg(a)) = a
        {
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, neg, &.{try app(self, neg, &.{a.term})});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "negNeg"), qualifier);
        }
        if (ops.mul) |mul| {
            // mulNegLeft: mul(neg(a), b) = neg(mul(a, b))
            {
                const a = try freshFvar(self, ops);
                const b = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
                const lhs = try app(self, mul, &.{ try app(self, neg, &.{a.term}), b.term });
                const rhs = try app(self, neg, &.{try app(self, mul, &.{ a.term, b.term })});
                try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulNegLeft"), qualifier);
            }
            // mulNegRight: mul(a, neg(b)) = neg(mul(a, b))
            {
                const a = try freshFvar(self, ops);
                const b = try freshFvar(self, ops);
                const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
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
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
            const lhs = try app(self, mul, &.{ try app(self, succ, &.{a.term}), b.term });
            const rhs = try app(self, add, &.{ try app(self, mul, &.{ a.term, b.term }), b.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "mulSuccLeft"), qualifier);
        }
        // mulSuccRight: mul(a, succ(b)) = add(mul(a, b), a)
        {
            const a = try freshFvar(self, ops);
            const b = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
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
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ a.term, try app(self, neg, &.{a.term}) });
            const rhs = try app(self, zero, &.{});
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, "addNegRight"), qualifier);
        }
        // addNegLeft: add(neg(a), a) = ZERO
        {
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
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
fn pushIdentityFold(self: *Prove, acc: *RuleAcc, ops: Ops, qualifier: StrId, which: IdentityFold) Error!void {
    const nm = struct {
        fn f(p: *Prove, comptime s: []const u8) Error!StrId {
            return p.ctx.interner.internString(s) catch error.OutOfMemory;
        }
    }.f;
    switch (which) {
        .mul_one_left => {
            const one = ops.one orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, mul, &.{ try app(self, one, &.{}), a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "mulOneLeft"), qualifier);
        },
        .mul_one_right => {
            const one = ops.one orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, mul, &.{ a.term, try app(self, one, &.{}) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "mulOneRight"), qualifier);
        },
        .mul_zero_left => {
            const zero = ops.zero orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const z0 = try app(self, zero, &.{});
            const z1 = try app(self, zero, &.{});
            const lhs = try app(self, mul, &.{ z0, a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = z1, .formula = try quantifyRule(self, binders, lhs, z1) }, try nm(self, "mulZeroLeft"), qualifier);
        },
        .mul_zero_right => {
            const zero = ops.zero orelse return;
            const mul = ops.mul orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const z0 = try app(self, zero, &.{});
            const z1 = try app(self, zero, &.{});
            const lhs = try app(self, mul, &.{ a.term, z0 });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = z1, .formula = try quantifyRule(self, binders, lhs, z1) }, try nm(self, "mulZeroRight"), qualifier);
        },
        .add_zero_left => {
            const zero = ops.zero orelse return;
            const add = ops.add orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ try app(self, zero, &.{}), a.term });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "addZeroLeft"), qualifier);
        },
        .add_zero_right => {
            const zero = ops.zero orelse return;
            const add = ops.add orelse return;
            const a = try freshFvar(self, ops);
            const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{binder(a.name, ops)});
            const lhs = try app(self, add, &.{ a.term, try app(self, zero, &.{}) });
            try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = a.term, .formula = try quantifyRule(self, binders, lhs, a.term) }, try nm(self, "addZeroRight"), qualifier);
        },
    }
}

/// Push the [assoc, comm, swap] triple for the `add` or `mul` operator, in that order.
fn pushTriple(self: *Prove, acc: *RuleAcc, ops: Ops, qualifier: StrId, comptime op: enum { add, mul }) Error!void {
    const sym = if (op == .add) ops.add.? else ops.mul.?;
    const assoc_nm = if (op == .add) "addIsAssociative" else "mulIsAssociative";
    const comm_nm = if (op == .add) "addIsCommutative" else "mulIsCommutative";
    const swap_nm = if (op == .add) "addLeftSwap" else "mulLeftSwap";
    const nm = struct {
        fn f(p: *Prove, s: []const u8) Error!StrId {
            return p.ctx.interner.internString(s) catch error.OutOfMemory;
        }
    }.f;
    // assoc: op(op(a, b), c) = op(a, op(b, c))
    {
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const c = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
        const lhs = try app(self, sym, &.{ try app(self, sym, &.{ a.term, b.term }), c.term });
        const rhs = try app(self, sym, &.{ a.term, try app(self, sym, &.{ b.term, c.term }) });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, assoc_nm), qualifier);
    }
    // comm: op(a, b) = op(b, a)
    {
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops) });
        const lhs = try app(self, sym, &.{ a.term, b.term });
        const rhs = try app(self, sym, &.{ b.term, a.term });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, comm_nm), qualifier);
    }
    // swap: op(a, op(b, c)) = op(b, op(a, c))
    {
        const a = try freshFvar(self, ops);
        const b = try freshFvar(self, ops);
        const c = try freshFvar(self, ops);
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ binder(a.name, ops), binder(b.name, ops), binder(c.name, ops) });
        const lhs = try app(self, sym, &.{ a.term, try app(self, sym, &.{ b.term, c.term }) });
        const rhs = try app(self, sym, &.{ b.term, try app(self, sym, &.{ a.term, c.term }) });
        try acc.push(self, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = try quantifyRule(self, binders, lhs, rhs) }, try nm(self, swap_nm), qualifier);
    }
}

// -- canonicalization (ported from the deleted polyCanon) ------------------------------

fn symsFrom(ops: Ops, comptime which: enum { add, mul }) presburger_mod.Symbols {
    return .{ .add = if (which == .add) ops.add else ops.mul };
}

/// Right-nest `x` under the add-associativity rule alone (a terminating normalization),
/// appending the re-indexed trace. `x` when there is no `add` (nothing to nest).
fn rightNestSum(self: *Prove, pr: PolyRules, x: TermId, trace: *std.ArrayList(simplify_mod.Rewrite)) Error!?TermId {
    const add_assoc = pr.add_assoc orelse return x;
    const rules = pr.rules[add_assoc .. add_assoc + 1];
    const rn = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules, x, 4000) catch |e| switch (e) {
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
pub fn polyCanon(self: *Prove, pr: PolyRules, x: TermId) Error!?simplify_mod.Result {
    const ops = pr.ops;
    // 1) distribute + fold to a flat sum of monomials (terminating). Its trace is already
    //    whole-term (normalize over `x`).
    const fold_rules = pr.rules[0..pr.fold_end];
    const dist = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, fold_rules, x, 4000) catch |e| switch (e) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
    try trace.appendSlice(self.ctx.arena, dist.trace);

    const add_symbols = symsFrom(ops, .add);
    const mul_symbols = symsFrom(ops, .mul);

    // 2) RIGHT-NEST the outer sum first (add-associativity only, terminating), so the running
    //    term is a right-nested comb and the buildComb contexts below match exactly. Without
    //    `add` the whole term is ONE monomial: the sum phases (2, 4, 5) have a single leaf.
    const nested = (try rightNestSum(self, pr, dist.nf, &trace)) orelse return null;

    // 3) sort each monomial's factors (mul-acPlan), lifting each sub-trace into the
    //    (right-nested) whole-sum context so the chain stays whole-term. Without `mul` a
    //    monomial is an atom (nothing to sort).
    var monos: std.ArrayList(TermId) = .empty;
    if (ops.add) |add| try narrow(self.flattenSum(add, nested, &monos)) else try monos.append(self.ctx.arena, nested);
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
        // Prove.acPlan reads symbols.add.? as the reordered operator — pass mul in that slot.
        const mp = (try narrow(self.acPlan(mul_symbols, pr.rules, pr.mul_assoc.?, pr.mul_comm.?, pr.mul_swap.?, body))) orelse return null;
        if (mp.trace.len > 0) {
            // lifted into the whole-sum context (a one-leaf comb when there is no `add`).
            const lifted = try liftMonoTrace(self, add_symbols, sorted_monos.items, monos.items[i + 1 ..], wrap, mp.trace, &trace);
            if (!lifted) return null;
        }
        try sorted_monos.append(self.ctx.arena, if (wrap) |w| try self.pool.addApp(.app, w, &.{mp.sorted}) else mp.sorted);
    }
    if (ops.add == null) return .{ .nf = sorted_monos.items[0], .trace = trace.items };
    const mono_sum = (try buildComb(self, add_symbols, sorted_monos.items)) orelse return null;

    // 4) bubble-sort the sum of monomials (already right-nested → sort phase only).
    var leaves: std.ArrayList(TermId) = .empty;
    try narrow(self.flattenSum(ops.add.?, mono_sum, &leaves));
    var sorted = (try sortTraceTower(self, add_symbols, pr.rules, pr.add_comm.?, pr.add_swap.?, .{ .offset = 0, .leaves = leaves.items }, &trace)) orelse return null;

    // 5) cancel additive-inverse monomials (m + neg(m) → 0) in the sorted sum. `one` is
    //    deliberately LEFT NULL: polynomial does NOT reduce ONE to succ(ZERO), so a bare ONE
    //    summand must ride as an opaque LEAF. succ/prev stay set so numeral towers still fold.
    if (ops.neg != null and ops.zero != null) {
        const cancel_symbols: presburger_mod.Symbols = .{
            .add = ops.add,
            .mul = ops.mul,
            .neg = ops.neg,
            .zero = ops.zero,
            .succ = ops.succ,
            .prev = ops.prev,
        };
        sorted = (try cancelInverses(self, cancel_symbols, pr.rules, pr.add_comm.?, pr.add_swap.?, sorted, &trace)) orelse return null;
    }
    return .{ .nf = sorted, .trace = trace.items };
}

// -- the tower substrate (ported PRIVATE from the deleted elaborate.zig) ----------------

const Tower = struct { offset: i128, leaves: []const TermId };

fn symIs(id: term.SymId, want: ?term.SymId) bool {
    return want != null and id == want.?;
}

/// Lift a sub-term trace into whole-term context (ported liftMonoTrace): the rewritten
/// monomial sits in the hole between `before` and `after` in the sum comb — wrapped in
/// `wrap(·)` (a negated summand) when given.
fn liftMonoTrace(
    self: *Prove,
    add_symbols: presburger_mod.Symbols,
    before: []const TermId,
    after: []const TermId,
    wrap: ?term.SymId,
    sub_trace: []const simplify_mod.Rewrite,
    out: *std.ArrayList(simplify_mod.Rewrite),
) Error!bool {
    var slots: std.ArrayList(TermId) = .empty;
    try slots.appendSlice(self.ctx.arena, before);
    const hole = slots.items.len;
    try slots.append(self.ctx.arena, sub_trace[0].before); // placeholder, overwritten per entry
    try slots.appendSlice(self.ctx.arena, after);
    for (sub_trace) |rw| {
        slots.items[hole] = if (wrap) |w| try self.pool.addApp(.app, w, &.{rw.before}) else rw.before;
        const w_before = (try buildComb(self, add_symbols, slots.items)) orelse return false;
        slots.items[hole] = if (wrap) |w| try self.pool.addApp(.app, w, &.{rw.after}) else rw.after;
        const w_after = (try buildComb(self, add_symbols, slots.items)) orelse return false;
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

/// If `t` is a numeral (succ^n(ZERO), prev^n(ZERO), or neg of one) return its signed value.
fn numeralValue(self: *Prove, symbols: presburger_mod.Symbols, t: TermId) ?i128 {
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
fn parseTower(self: *Prove, symbols: presburger_mod.Symbols, t: TermId) Error!?Tower {
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
fn isTowerLeaf(self: *Prove, symbols: presburger_mod.Symbols, t: TermId) bool {
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
fn isOpaqueAtom(self: *Prove, symbols: presburger_mod.Symbols, t: TermId) bool {
    const node = self.pool.get(t);
    if (node != .app) return false;
    const sym = node.app.sym;
    return !(symIs(sym, symbols.add) or symIs(sym, symbols.succ) or
        symIs(sym, symbols.prev) or symIs(sym, symbols.neg) or
        symIs(sym, symbols.sub) or symIs(sym, symbols.zero) or
        symIs(sym, symbols.one));
}

fn buildComb(self: *Prove, symbols: presburger_mod.Symbols, leaves: []const TermId) Error!?TermId {
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

fn buildTower(self: *Prove, symbols: presburger_mod.Symbols, succs: usize, comb: TermId) Error!?TermId {
    var cur = comb;
    for (0..succs) |_| {
        const succ_sym = symbols.succ orelse return null;
        cur = try self.pool.addApp(.app, succ_sym, &.{cur});
    }
    return cur;
}

/// A SIGNED tower: succ^n(comb) for n ≥ 0, prev^|n|(comb) for n < 0.
fn buildTowerSigned(self: *Prove, symbols: presburger_mod.Symbols, offset: i128, comb: TermId) Error!?TermId {
    if (offset >= 0) return buildTower(self, symbols, @intCast(offset), comb);
    const prev_sym = symbols.prev orelse return null;
    var cur = comb;
    var n = -offset;
    while (n > 0) : (n -= 1) cur = try self.pool.addApp(.app, prev_sym, &.{cur});
    return cur;
}

/// buildComb but with a trailing ZERO base: l0 + (l1 + ... + (l_{n-1} + 0)).
fn buildCombWithZeroTail(self: *Prove, symbols: presburger_mod.Symbols, leaves: []const TermId) Error!?TermId {
    const zero = try self.pool.addApp(.app, symbols.zero orelse return null, &.{});
    var cur = zero;
    var i = leaves.len;
    while (i > 0) {
        i -= 1;
        cur = try self.pool.addApp(.app, symbols.add orelse return null, &.{ leaves[i], cur });
    }
    return cur;
}

/// Bubble-sort a tower's summands, appending one rewrite per adjacent swap (tower-based sort,
/// the deleted elaborate.zig `sortTrace` — NOT Prove's leaf-based one). Null when a needed
/// sort lemma index is absent or a shape assumption fails.
fn sortTraceTower(
    self: *Prove,
    symbols: presburger_mod.Symbols,
    rules: []const simplify_mod.Rule,
    comm_idx: ?usize,
    swap_idx: ?usize,
    tower: Tower,
    trace: *std.ArrayList(simplify_mod.Rewrite),
) Error!?TermId {
    const leaves = try self.ctx.arena.dupe(TermId, tower.leaves);
    var whole = (try buildTowerSigned(self, symbols, tower.offset, (try buildComb(self, symbols, leaves)) orelse return null)) orelse return null;
    if (leaves.len > 1) {
        for (0..leaves.len - 1) |pass| {
            for (0..leaves.len - 1 - pass) |i| {
                if (self.pool.termOrder(leaves[i], leaves[i + 1]) != .gt) continue;
                const tail_pair = i + 2 == leaves.len;
                const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse return null;
                const sub_before = (try buildComb(self, symbols, leaves[i..])) orelse return null;
                std.mem.swap(TermId, &leaves[i], &leaves[i + 1]);
                const sub_after = (try buildComb(self, symbols, leaves[i..])) orelse return null;
                const after = (try buildTowerSigned(self, symbols, tower.offset, (try buildComb(self, symbols, leaves)) orelse return null)) orelse return null;
                const rule = rules[rule_idx];
                const bindings = (try simplify_mod.matchRule(self.ctx.arena, self.pool, self.ctx.interner, rule, rule.lhs, sub_before)) orelse return null;
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

/// Emit one adjacent swap of `order[pos]` / `order[pos+1]` in the tower `succ^k(sum(order))`.
fn emitSwap(
    self: *Prove,
    symbols: presburger_mod.Symbols,
    rules: []const simplify_mod.Rule,
    comm_idx: ?usize,
    swap_idx: ?usize,
    offset: i128,
    order: []TermId,
    pos: usize,
    whole: TermId,
    trace: *std.ArrayList(simplify_mod.Rewrite),
) Error!?TermId {
    const tail_pair = pos + 2 == order.len;
    const rule_idx = (if (tail_pair) comm_idx else swap_idx) orelse return null;
    const sub_before = (try buildComb(self, symbols, order[pos..])) orelse return null;
    std.mem.swap(TermId, &order[pos], &order[pos + 1]);
    const sub_after = (try buildComb(self, symbols, order[pos..])) orelse return null;
    const after = (try buildTowerSigned(self, symbols, offset, (try buildComb(self, symbols, order)) orelse return null)) orelse return null;
    const rule = rules[rule_idx];
    const bindings = (try simplify_mod.matchRule(self.ctx.arena, self.pool, self.ctx.interner, rule, rule.lhs, sub_before)) orelse return null;
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
    symbols: presburger_mod.Symbols,
    rules: []const simplify_mod.Rule,
    comm_idx: ?usize,
    swap_idx: ?usize,
    whole0: TermId,
    trace: *std.ArrayList(simplify_mod.Rewrite),
) Error!?TermId {
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
        const neg_bindings = (try simplify_mod.matchRule(self.ctx.arena, self.pool, self.ctx.interner, neg_rule, neg_rule.lhs, pair_term)) orelse return null;
        const reduced = order[0..xpos];
        const comb0 = (try buildCombWithZeroTail(self, symbols, reduced)) orelse return null;
        const after_cancel = (try buildTowerSigned(self, symbols, offset, comb0)) orelse return null;
        try trace.append(self.ctx.arena, .{ .before = before_cancel, .after = after_cancel, .rule_idx = rule_idx, .bindings = neg_bindings, .inst_lhs = pair_term, .inst_rhs = zero });
        whole = after_cancel;

        const zl = zero_left orelse return null;
        const zr = zero_right orelse return null;
        const zero_rules = [_]simplify_mod.Rule{ rules[zl], rules[zr] };
        const zres = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, &zero_rules, whole, 1000) catch return null;
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
fn findNegCancel(self: *Prove, rules: []const simplify_mod.Rule, symbols: presburger_mod.Symbols, side: enum { left, right }) ?usize {
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
fn findZeroDrop(self: *Prove, rules: []const simplify_mod.Rule, symbols: presburger_mod.Symbols, side: enum { left, right }) ?usize {
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

const testing = std.testing;

/// A unit-test RIG: a real Context over one inline ring theory (`Int` with ZERO/add/mul/neg),
/// its symbols FETCHED through the engine, and a standalone `Prove` whose pool the tests build
/// goal terms in. Shared by the polynomial unit tests here and the op-reader tests in Prove.
pub const Rig = struct {
    ctx: *Context,
    eng: *Engine,
    h: *Engine.Handle,
    prove: *Prove,
    file: InternPool.Index,
    ns: InternPool.Index,
    int: term.SortId,
    zero: term.SymId,
    add: term.SymId,
    mul: term.SymId,
    neg: term.SymId,
    succ: term.SymId,

    pub const source =
        \\sort Int
        \\const ZERO: Int
        \\func add(a: Int, b: Int) => Int
        \\func mul(a: Int, b: Int) => Int
        \\func neg(a: Int) => Int
        \\func succ(a: Int) => Int
    ;

    pub fn init(arena: std.mem.Allocator, io: std.Io) !Rig {
        const FetchTask = @import("../FetchTask.zig");
        const ctx = try FetchTask.fixtureCtx(arena, io, "/t/ring.bpa", source);
        const file = try ctx.fileIndex("/t/ring.bpa");
        const ns = try ctx.interner.namespace(.universe, file);
        const eng = try arena.create(Engine);
        eng.* = Engine.init(arena, ctx, ctx.io);
        for ([_][]const u8{ "Int", "ZERO", "add", "mul", "neg", "succ" }) |n| {
            _ = try eng.rack(try FetchTask.new(arena, .{ .file = file, .name = try ctx.interner.internString(n), .loc = 0 }));
        }
        try eng.run();
        try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);
        const h = try arena.create(Engine.Handle);
        h.* = .{ .engine = eng, .self_index = @enumFromInt(0) };
        const prove = try Prove.init(ctx, h, source, file, ns);
        return .{
            .ctx = ctx,
            .eng = eng,
            .h = h,
            .prove = prove,
            .file = file,
            .ns = ns,
            .int = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "Int"))),
            .zero = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "ZERO"))),
            .add = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "add"))),
            .mul = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "mul"))),
            .neg = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "neg"))),
            .succ = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "succ"))),
        };
    }

    fn lookup(ctx: *Context, ns: InternPool.Index, name: []const u8) !InternPool.Index {
        return ctx.idents.lookup(ctx.io, .{ .namespace = ns, .name = try ctx.interner.internString(name) }).?.done;
    }

    /// A free variable of the ring sort.
    pub fn v(self: Rig, name: []const u8) !TermId {
        return self.prove.pool.add(.{ .fvar = .{ .name = try self.ctx.interner.internString(name), .sort = self.int } });
    }
    pub fn a2(self: Rig, sym: term.SymId, x: TermId, y: TermId) !TermId {
        return self.prove.pool.addApp(.app, sym, &.{ x, y });
    }
    pub fn a1(self: Rig, sym: term.SymId, x: TermId) !TermId {
        return self.prove.pool.addApp(.app, sym, &.{x});
    }
    pub fn eq(self: Rig, l: TermId, r: TermId) !TermId {
        return self.prove.pool.add(.{ .eq = .{ .lhs = l, .rhs = r } });
    }
    pub fn opsOf(self: Rig, add: ?term.SymId, mul: ?term.SymId, neg: ?term.SymId, zero: ?term.SymId) Ops {
        return .{ .add = add, .mul = mul, .zero = zero, .one = null, .neg = neg, .sub = null, .succ = null, .prev = null, .sort = self.int };
    }
};

test "polyRules: an add-only op set builds the add triple and neg-folds but NO mul rules" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.prove, rig.opsOf(rig.add, null, rig.neg, null), .none, 0);
    try testing.expect(pr.add_assoc != null);
    try testing.expect(pr.mul_assoc == null);
    // every rule's pattern mentions only add/neg: no rule head is `mul`.
    for (pr.rules) |r| {
        const n = rig.prove.pool.get(r.lhs);
        if (n == .app) try testing.expect(n.app.sym != rig.mul);
    }
}

test "polyCanon: an add-only identity canonicalizes — neg(add(a, b)) ≡ add(neg(a), neg(b))" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.prove, rig.opsOf(rig.add, null, rig.neg, null), .none, 0);
    const a = try rig.v("a");
    const b = try rig.v("b");
    const lhs = try rig.a1(rig.neg, try rig.a2(rig.add, a, b));
    const rhs = try rig.a2(rig.add, try rig.a1(rig.neg, a), try rig.a1(rig.neg, b));
    const rs = (try polyCanon(rig.prove, pr, lhs)).?;
    const rt = (try polyCanon(rig.prove, pr, rhs)).?;
    try testing.expect(rig.prove.pool.alphaEq(rs.nf, rt.nf));
}

test "polyCanon: a mul-only identity canonicalizes — mul(mul(d, k), m) ≡ mul(k, mul(d, m))" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.prove, rig.opsOf(null, rig.mul, null, null), .none, 0);
    try testing.expect(pr.add_assoc == null);
    const d = try rig.v("d");
    const k = try rig.v("k");
    const m = try rig.v("m");
    const lhs = try rig.a2(rig.mul, try rig.a2(rig.mul, d, k), m);
    const rhs = try rig.a2(rig.mul, k, try rig.a2(rig.mul, d, m));
    const rs = (try polyCanon(rig.prove, pr, lhs)).?;
    const rt = (try polyCanon(rig.prove, pr, rhs)).?;
    try testing.expect(rig.prove.pool.alphaEq(rs.nf, rt.nf));
}

test "polyCanon: an inverse pair cancels when ZERO is supplied by the theory, not the goal — add(x, add(t, neg(t))) ≡ x" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try Rig.init(arena, threaded.io());
    // the goal mentions no ZERO; the op set carries the theory's ZERO (completePolyOps' job).
    const pr = try polyRules(rig.prove, rig.opsOf(rig.add, rig.mul, rig.neg, rig.zero), .none, 0);
    const x = try rig.v("x");
    const t = try rig.a2(rig.mul, try rig.v("a"), try rig.v("r"));
    const lhs = try rig.a2(rig.add, x, try rig.a2(rig.add, t, try rig.a1(rig.neg, t)));
    const rs = (try polyCanon(rig.prove, pr, lhs)).?;
    const rt = (try polyCanon(rig.prove, pr, x)).?;
    try testing.expect(rig.prove.pool.alphaEq(rs.nf, rt.nf));
}

test "polyCanon: a cross-term cancels — the monomial INSIDE neg(…) gets its factors sorted too: add(mul(a, b), neg(mul(b, a))) ≡ ZERO" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try Rig.init(arena, threaded.io());
    const pr = try polyRules(rig.prove, rig.opsOf(rig.add, rig.mul, rig.neg, rig.zero), .none, 0);
    const a = try rig.v("a");
    const b = try rig.v("b");
    const lhs = try rig.a2(rig.add, try rig.a2(rig.mul, a, b), try rig.a1(rig.neg, try rig.a2(rig.mul, b, a)));
    const zero = try rig.prove.pool.addApp(.app, rig.zero, &.{});
    const rs = (try polyCanon(rig.prove, pr, lhs)).?;
    const rt = (try polyCanon(rig.prove, pr, zero)).?;
    try testing.expect(rig.prove.pool.alphaEq(rs.nf, rt.nf));
    // and with NO surrounding sum: neg(mul(b, a)) alone canonicalizes like neg(mul(a, b)).
    const n1 = (try polyCanon(rig.prove, pr, try rig.a1(rig.neg, try rig.a2(rig.mul, b, a)))).?;
    const n2 = (try polyCanon(rig.prove, pr, try rig.a1(rig.neg, try rig.a2(rig.mul, a, b)))).?;
    try testing.expect(rig.prove.pool.alphaEq(n1.nf, n2.nf));
}
