//! The TRUSTED kernel. Soundness of the whole system reduces to this file
//! (plus term.zig's substitution calculus). It checks concrete many-sorted
//! FOL proofs: a flat list of steps grouped into Fitch blocks.
//!
//! The kernel re-validates everything it depends on — reference accessibility,
//! block closure, hypothesis formulas, eigenvariable conditions, term sorts —
//! and does NOT trust the elaborator's lowering beyond the type structure of
//! its input.
//!
//! Eigenvariable discipline (deliberately conservative): the eigenvariable of
//! a fix/unpack block must not occur free in any step formula or block
//! hypothesis outside that block's subtree, anywhere earlier in the proof.
//! This over-approximates the textbook side condition (it may reject a valid
//! proof that reuses a variable *name* in a disjoint sibling subproof, since
//! eigenvariables are identified here by their interned name) but can never
//! accept an invalid one. The elaborator keeps this over-approximation from
//! biting by binding each fix/unpack var to a fresh disambiguated identity
//! `x#<n>` (the demand prover's hygienic binder minting), so sibling `fix x`
//! blocks produce distinct eigenvariables the kernel never conflates; the
//! `#<n>` is trimmed away on render, so proofs still read `x`.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const Diagnostics = @import("diagnostics.zig");
const print = @import("print.zig");

pub const StepId = enum(u32) { _ };
pub const BlockId = enum(u32) { _ };

/// step reference + where it was written (for precise diagnostics)
pub const SRef = struct { id: StepId, loc: u32 };
pub const BRef = struct { id: BlockId, loc: u32 };

pub const Block = struct {
    parent: ?BlockId, // null only for the root block
    label: StrId,
    kind: Kind,
    /// step-index range [first, last); equal means empty
    first_step: u32,
    last_step: u32,

    pub const Kind = union(enum) {
        root,
        assume: TermId,
        /// `fix h` (∀-intro subproof). A PREDICATED fix (`fix h: H`, H = G where inH)
        /// carries `guard = inH(h)` — available as the block's hypothesis, and made
        /// the antecedent of the `forall_intro` conclusion (`∀h; inH(h) -> body`).
        fix: struct { v: term.Node.Fvar, guard: ?TermId = null },
        unpack: struct { v: term.Node.Fvar, source: SRef },
    };
};

pub const Step = struct {
    formula: TermId,
    just: Justification,
    block: BlockId,
    label: StrId,
    loc: u32,
};

pub const Justification = union(enum) {
    hypothesis: BRef,
    /// `stmt` is the cited fact's POOL `Index` (a `.fact` Item). The kernel re-reads its
    /// kind + formula from the pool — it does not trust the lowering's copy.
    axiom_ref: struct { stmt: InternPool.Index, loc: u32 },
    theorem_ref: struct { stmt: InternPool.Index, loc: u32 },
    modus_ponens: struct { implication: SRef, antecedent: SRef },
    implies_intro: BRef,
    forall_intro: BRef,
    forall_elim: struct { step: SRef, with: TermId, with_loc: u32 },
    exists_intro: struct { step: SRef, witness: TermId, witness_loc: u32 },
    exists_elim: BRef,
    and_intro: struct { left: SRef, right: SRef },
    and_elim_left: SRef,
    and_elim_right: SRef,
    or_intro_left: SRef,
    or_intro_right: SRef,
    or_elim: struct { disj: SRef, left: BRef, right: BRef },
    not_intro: struct { block: BRef, s1: SRef, s2: SRef },
    absurd: struct { s1: SRef, s2: SRef },
    double_negation: SRef,
    reflexivity,
    /// from a proven `x = y`, conclude `y = x`
    symmetry: SRef,
    rewrite: struct { equation: SRef, target: SRef },
    /// Propositional analogue of `rewrite`: from a biconditional `(P -> Q) and
    /// (Q -> P)` (what `P iff Q` desugars to) and a `target`, conclude the claim
    /// obtained by replacing occurrences of the sub-PROPOSITION `P` with `Q`.
    /// Sound because `iff` is a full congruence in classical FOL; the same
    /// congruence walker (`rewriteMatches`) is reused, with `P`/`Q` as props.
    iff_rewrite: struct { biconditional: SRef, target: SRef },
    /// A monomorphized schema instance (elaborator-licensed: instantiation of
    /// a stored form at written-down arguments is the system's comptime axiom
    /// rule; proof-carrying schemas were re-checked at this instance before
    /// lowering). The kernel still checks the premise-peeling: each premise
    /// must match the instance's next antecedent, in order.
    schema_instance: struct { instance: TermId, premises: []const SRef },
    /// An accelerated verdict (elaborator-licensed): the named decision
    /// procedure accepted the claim, and there is no derivation to check. Trust
    /// is disclosed rather than established — the elaborator marks the
    /// enclosing theorem accelerated under this tactic name (transitively,
    /// through citations), the summary reports it, and --pure rejects the
    /// step. Registry: ACCELERATION.md.
    accelerated: StrId,
};

pub const Proof = struct {
    steps: []const Step,
    blocks: []const Block, // blocks[0] is the root
};

pub const Kernel = struct {
    arena: Allocator,
    pool: *term.Pool,
    interner: *const InternPool,
    sink: *Diagnostics.Sink,
    /// The file this kernel run's diagnostics belong to — a value, not ambient sink state
    /// (see diagnostics.zig).
    file: u32 = 0,

    const Fail = error{ Invalid, OutOfMemory };

    /// Check `proof` establishes `goal`. On failure exactly one diagnostic is
    /// recorded and false is returned.
    pub fn check(self: *Kernel, proof: Proof, goal: TermId, goal_loc: u32) Allocator.Error!bool {
        self.checkInner(proof, goal, goal_loc) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Invalid => return false,
        };
        return true;
    }

    fn checkInner(self: *Kernel, proof: Proof, goal: TermId, goal_loc: u32) Fail!void {
        for (proof.steps, 0..) |*step, i| {
            try self.checkStep(proof, step, @intCast(i));
        }
        // the conclusion is the last step of the root block
        var conclusion: ?*const Step = null;
        var it = proof.steps.len;
        while (it > 0) {
            it -= 1;
            if (proof.steps[it].block == @as(BlockId, @enumFromInt(0))) {
                conclusion = &proof.steps[it];
                break;
            }
        }
        const conc = conclusion orelse {
            return self.fail(goal_loc, "proof has no concluding step", .{});
        };
        if (!self.pool.alphaEq(conc.formula, goal)) {
            return self.fail(conc.loc, "proof concludes '{s}' but the theorem states '{s}'", .{
                try self.render(conc.formula), try self.render(goal),
            });
        }
    }

    fn fail(self: *Kernel, loc: u32, comptime fmt: []const u8, args: anytype) Fail {
        self.sink.add(self.file, loc, fmt, args) catch return error.OutOfMemory;
        return error.Invalid;
    }

    fn render(self: *Kernel, id: TermId) Allocator.Error![]const u8 {
        return print.render(self.arena, self.pool, self.interner, id);
    }

    fn str(self: *const Kernel, id: StrId) []const u8 {
        return self.interner.stringBytes(id);
    }

    /// The cited fact's pool payload; rejects a forged non-fact Index.
    fn factOf(self: *Kernel, stmt: InternPool.Index, loc: u32) Fail!InternPool.Key.Fact {
        const key = self.interner.keyOf(stmt);
        if (key != .fact) return self.fail(loc, "internal: citation does not reference a fact", .{});
        return key.fact;
    }

    fn sortName(self: *const Kernel, sort: SortId) []const u8 {
        return self.interner.sortName(@enumFromInt(@intFromEnum(sort)));
    }

    fn block(proof: Proof, id: BlockId) *const Block {
        return &proof.blocks[@intFromEnum(id)];
    }

    fn stepAt(proof: Proof, id: StepId) *const Step {
        return &proof.steps[@intFromEnum(id)];
    }

    fn isAncestorOrSelf(proof: Proof, a: BlockId, b: BlockId) bool {
        var cur: ?BlockId = b;
        while (cur) |c| {
            if (c == a) return true;
            cur = block(proof, c).parent;
        }
        return false;
    }

    /// A step may cite step `r` only if `r` precedes it and `r`'s block still
    /// encloses it (no reaching into closed subproofs).
    fn checkStepRef(self: *Kernel, proof: Proof, r: SRef, i: u32, at: BlockId) Fail!*const Step {
        if (@intFromEnum(r.id) >= i) {
            return self.fail(r.loc, "reference does not precede this step", .{});
        }
        const s = stepAt(proof, r.id);
        if (!isAncestorOrSelf(proof, s.block, at)) {
            return self.fail(r.loc, "'{s}' is not accessible from this step (closed subproof)", .{self.str(s.label)});
        }
        return s;
    }

    /// A block-conclusion rule may cite block `r` only if the block is closed
    /// (all its steps precede this one), it is not an ancestor of the current
    /// step, and its parent still encloses the current step.
    fn checkClosedBlockRef(self: *Kernel, proof: Proof, r: BRef, i: u32, at: BlockId) Fail!*const Block {
        const b = block(proof, r.id);
        if (b.kind == .root) return self.fail(r.loc, "cannot cite the proof body as a subproof", .{});
        if (isAncestorOrSelf(proof, r.id, at)) {
            return self.fail(r.loc, "cannot conclude from subproof '{s}' while inside it", .{self.str(b.label)});
        }
        if (b.last_step > i) {
            return self.fail(r.loc, "subproof '{s}' is not closed before this step", .{self.str(b.label)});
        }
        if (!isAncestorOrSelf(proof, b.parent.?, at)) {
            return self.fail(r.loc, "'{s}' is not accessible from this step (closed subproof)", .{self.str(b.label)});
        }
        if (b.first_step == b.last_step) {
            return self.fail(r.loc, "subproof '{s}' is empty", .{self.str(b.label)});
        }
        return b;
    }

    /// Formula of the last step belonging to `b` ITSELF (not a nested
    /// subblock). Null when the block's only content is nested subproofs —
    /// such a block has nothing to discharge.
    fn lastFormula(proof: Proof, b: *const Block) ?TermId {
        var i = b.last_step;
        while (i > b.first_step) {
            i -= 1;
            const s = proof.steps[i];
            if (s.block == blockIdOf(proof, b)) return s.formula;
        }
        return null;
    }

    fn requireLastFormula(self: *Kernel, proof: Proof, b: *const Block, loc: u32) Fail!TermId {
        return lastFormula(proof, b) orelse
            self.fail(loc, "subproof '{s}' has no concluding step of its own", .{self.str(b.label)});
    }

    fn blockIdOf(proof: Proof, b: *const Block) BlockId {
        const idx = (@intFromPtr(b) - @intFromPtr(proof.blocks.ptr)) / @sizeOf(Block);
        return @enumFromInt(idx);
    }

    /// The hypothesis a block makes available. fix-blocks have none.
    fn hypFormula(self: *Kernel, proof: Proof, b: *const Block, loc: u32) Fail!TermId {
        switch (b.kind) {
            .assume => |f| return f,
            .unpack => |u| {
                const src = stepAt(proof, u.source.id);
                const node = self.pool.get(src.formula);
                if (node != .quant or node.quant.q != .exists) {
                    return self.fail(u.source.loc, "unpack source '{s}' is not an existential: '{s}'", .{
                        self.str(src.label), try self.render(src.formula),
                    });
                }
                const v = try self.pool.add(.{ .fvar = u.v });
                return self.pool.open(node.quant.body, v);
            },
            .fix => |f| {
                // a PREDICATED fix surfaces its guard `inH(h)` as the hypothesis;
                // a plain fix has none.
                if (f.guard) |g| return g;
                return self.fail(loc, "subproof '{s}' has no hypothesis", .{self.str(b.label)});
            },
            .root => return self.fail(loc, "subproof '{s}' has no hypothesis", .{self.str(b.label)}),
        }
    }

    fn inSubtree(proof: Proof, b: BlockId, root_: BlockId) bool {
        return isAncestorOrSelf(proof, root_, b);
    }

    /// Conservative eigenvariable check (see file comment): `name` must not
    /// occur free in any step formula or block hypothesis outside subtree(B)
    /// earlier than step `i`.
    fn checkEigen(self: *Kernel, proof: Proof, b_id: BlockId, name: StrId, i: u32, loc: u32) Fail!void {
        for (proof.steps[0..i]) |s| {
            if (inSubtree(proof, s.block, b_id)) continue;
            if (self.pool.occursFree(s.formula, name)) {
                return self.fail(loc, "eigenvariable '{s}' occurs free in step '{s}' outside the subproof; rename it", .{
                    self.str(name), self.str(s.label),
                });
            }
        }
        for (proof.blocks, 0..) |ob, idx| {
            if (ob.first_step >= i) continue;
            if (inSubtree(proof, @enumFromInt(idx), b_id)) continue;
            const hyp: TermId = switch (ob.kind) {
                .assume => |f| f,
                else => continue, // unpack hyps derive from step formulas, already scanned
            };
            if (self.pool.occursFree(hyp, name)) {
                return self.fail(loc, "eigenvariable '{s}' occurs free in the hypothesis of '{s}' outside the subproof; rename it", .{
                    self.str(name), self.str(ob.label),
                });
            }
        }
    }

    /// Sort of a term (not a formula). Rejects props and loose bound
    /// variables at ANY depth (the substitution calculus requires
    /// instantiation terms to be locally closed).
    /// The sort of term `id`, VALIDATING every sub-term is well-formed (an app's args are terms, no
    /// loose bvar, no proposition-in-term-position). Iterative work-stack (was native recursion) —
    /// a deeply-nested `f(f(…))` term can't overflow the kernel's C stack. Every node is checked;
    /// the RESULT sort is the ROOT node's (computed first, before descending). Scratch on the
    /// kernel arena (this is a validation pass; a term this deep is already pathological).
    fn sortOfTerm(self: *Kernel, id: TermId, loc: u32) Fail!SortId {
        var scratch: std.heap.ArenaAllocator = .init(self.arena);
        defer scratch.deinit();
        const a = scratch.allocator();
        var stack: std.ArrayList(TermId) = .empty;
        // compute the root's sort up front (also validates the root node kind); then validate the
        // whole subtree via the stack.
        const root_sort: SortId = switch (self.pool.get(id)) {
            .fvar => |v| v.sort,
            .app => |ap| @enumFromInt(@intFromEnum(self.interner.symResult(@enumFromInt(@intFromEnum(ap.sym))))),
            .bvar => return self.fail(loc, "internal: term argument has a loose bound variable", .{}),
            else => return self.fail(loc, "expected a term, got the proposition '{s}'", .{try self.render(id)}),
        };
        try stack.append(a, id);
        while (stack.pop()) |cur| {
            switch (self.pool.get(cur)) {
                .fvar => {}, // a valid leaf term
                .app => |ap| for (self.pool.args(ap)) |arg| try stack.append(a, arg),
                .bvar => return self.fail(loc, "internal: term argument has a loose bound variable", .{}),
                else => return self.fail(loc, "expected a term, got the proposition '{s}'", .{try self.render(cur)}),
            }
        }
        return root_sort;
    }

    fn claimMismatch(self: *Kernel, step: *const Step, comptime rule: []const u8, derived: TermId) Fail {
        return self.fail(step.loc, "step claims '{s}' but " ++ rule ++ " derives '{s}'", .{
            self.render(step.formula) catch return error.OutOfMemory,
            self.render(derived) catch return error.OutOfMemory,
        });
    }

    fn requireClaim(self: *Kernel, step: *const Step, comptime rule: []const u8, derived: TermId) Fail!void {
        if (!self.pool.alphaEq(step.formula, derived)) {
            return self.claimMismatch(step, rule, derived);
        }
    }

    fn checkStep(self: *Kernel, proof: Proof, step: *const Step, i: u32) Fail!void {
        const at = step.block;
        switch (step.just) {
            .hypothesis => |r| {
                const b = block(proof, r.id);
                if (!isAncestorOrSelf(proof, r.id, at)) {
                    return self.fail(r.loc, "hypothesis '{s}' is not an enclosing subproof", .{self.str(b.label)});
                }
                const hyp = try self.hypFormula(proof, b, r.loc);
                try self.requireClaim(step, "the hypothesis", hyp);
            },
            .axiom_ref => |r| {
                // the cited fact is re-read from the POOL: kind tag checked, its durable
                // formula copied into the working pool for the alpha-comparison. A fact
                // being interned at all means it was established (interned ⇒ proven).
                const fact = try self.factOf(r.stmt, r.loc);
                if (fact.kind != .axiom) {
                    return self.fail(r.loc, "'{s}' is not an axiom", .{self.str(fact.name)});
                }
                const formula = try self.pool.copyIn(self.interner, fact.formula);
                try self.requireClaim(step, "the axiom", formula);
            },
            .theorem_ref => |r| {
                const fact = try self.factOf(r.stmt, r.loc);
                if (fact.kind != .theorem) {
                    return self.fail(r.loc, "'{s}' is not a theorem", .{self.str(fact.name)});
                }
                const formula = try self.pool.copyIn(self.interner, fact.formula);
                try self.requireClaim(step, "the theorem", formula);
            },
            .modus_ponens => |r| {
                const imp = try self.checkStepRef(proof, r.implication, i, at);
                const ante = try self.checkStepRef(proof, r.antecedent, i, at);
                const node = self.pool.get(imp.formula);
                if (node != .bin or node.bin.op != .implies) {
                    return self.fail(r.implication.loc, "modus_ponens expects an implication, got '{s}'", .{
                        try self.render(imp.formula),
                    });
                }
                if (!self.pool.alphaEq(ante.formula, node.bin.lhs)) {
                    return self.fail(r.antecedent.loc, "modus_ponens: expected antecedent '{s}', got '{s}'", .{
                        try self.render(node.bin.lhs), try self.render(ante.formula),
                    });
                }
                try self.requireClaim(step, "modus_ponens", node.bin.rhs);
            },
            .implies_intro => |r| {
                const b = try self.checkClosedBlockRef(proof, r, i, at);
                if (b.kind != .assume) {
                    return self.fail(r.loc, "implies_intro requires an assume subproof", .{});
                }
                const derived = try self.pool.add(.{ .bin = .{
                    .op = .implies,
                    .lhs = b.kind.assume,
                    .rhs = try self.requireLastFormula(proof, b, r.loc),
                } });
                try self.requireClaim(step, "implies_intro", derived);
            },
            .forall_intro => |r| {
                const b = try self.checkClosedBlockRef(proof, r, i, at);
                if (b.kind != .fix) {
                    return self.fail(r.loc, "forall_intro requires a fix subproof", .{});
                }
                const v = b.kind.fix.v;
                try self.checkEigen(proof, r.id, v.name, i, r.loc);
                // a PREDICATED fix concludes `∀h; guard(h) -> last` — the guard
                // becomes the antecedent (over the same eigenvariable). A plain fix
                // concludes `∀h; last`.
                var inner = try self.requireLastFormula(proof, b, r.loc);
                if (b.kind.fix.guard) |g| {
                    inner = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = g, .rhs = inner } });
                }
                const body = try self.pool.close(inner, v.name);
                const derived = try self.pool.add(.{ .quant = .{
                    .q = .forall,
                    .sort = v.sort,
                    .hint = v.name,
                    .body = body,
                } });
                try self.requireClaim(step, "forall_intro", derived);
            },
            .forall_elim => |r| {
                const src = try self.checkStepRef(proof, r.step, i, at);
                const node = self.pool.get(src.formula);
                if (node != .quant or node.quant.q != .forall) {
                    return self.fail(r.step.loc, "forall_elim expects a universal, got '{s}'", .{
                        try self.render(src.formula),
                    });
                }
                const with_sort = try self.sortOfTerm(r.with, r.with_loc);
                if (with_sort != node.quant.sort) {
                    return self.fail(r.with_loc, "expected sort '{s}', got '{s}'", .{
                        self.sortName(node.quant.sort), self.sortName(with_sort),
                    });
                }
                const derived = try self.pool.open(node.quant.body, r.with);
                try self.requireClaim(step, "forall_elim", derived);
            },
            .exists_intro => |r| {
                const src = try self.checkStepRef(proof, r.step, i, at);
                const node = self.pool.get(step.formula);
                if (node != .quant or node.quant.q != .exists) {
                    return self.fail(step.loc, "exists_intro must claim an existential, not '{s}'", .{
                        try self.render(step.formula),
                    });
                }
                const wit_sort = try self.sortOfTerm(r.witness, r.witness_loc);
                if (wit_sort != node.quant.sort) {
                    return self.fail(r.witness_loc, "expected sort '{s}', got '{s}'", .{
                        self.sortName(node.quant.sort), self.sortName(wit_sort),
                    });
                }
                const expected = try self.pool.open(node.quant.body, r.witness);
                if (!self.pool.alphaEq(src.formula, expected)) {
                    return self.fail(r.step.loc, "exists_intro: expected '{s}', got '{s}'", .{
                        try self.render(expected), try self.render(src.formula),
                    });
                }
            },
            .exists_elim => |r| {
                const b = try self.checkClosedBlockRef(proof, r, i, at);
                if (b.kind != .unpack) {
                    return self.fail(r.loc, "exists_elim requires an unpack subproof", .{});
                }
                const u = b.kind.unpack;
                // validate the source is a well-formed accessible existential
                _ = try self.checkStepRef(proof, u.source, b.first_step, block(proof, r.id).parent.?);
                _ = try self.hypFormula(proof, b, r.loc);
                const conclusion = try self.requireLastFormula(proof, b, r.loc);
                if (self.pool.occursFree(conclusion, u.v.name)) {
                    return self.fail(r.loc, "witness '{s}' escapes its subproof in '{s}'", .{
                        self.str(u.v.name), try self.render(conclusion),
                    });
                }
                try self.checkEigen(proof, r.id, u.v.name, i, r.loc);
                try self.requireClaim(step, "exists_elim", conclusion);
            },
            .and_intro => |r| {
                const l = try self.checkStepRef(proof, r.left, i, at);
                const rt = try self.checkStepRef(proof, r.right, i, at);
                const derived = try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = l.formula, .rhs = rt.formula } });
                try self.requireClaim(step, "and_intro", derived);
            },
            .and_elim_left, .and_elim_right => |r| {
                const src = try self.checkStepRef(proof, r, i, at);
                const node = self.pool.get(src.formula);
                if (node != .bin or node.bin.op != .and_op) {
                    return self.fail(r.loc, "expects a conjunction, got '{s}'", .{try self.render(src.formula)});
                }
                const derived = if (step.just == .and_elim_left) node.bin.lhs else node.bin.rhs;
                try self.requireClaim(step, "and_elim", derived);
            },
            .or_intro_left, .or_intro_right => |r| {
                const src = try self.checkStepRef(proof, r, i, at);
                const node = self.pool.get(step.formula);
                if (node != .bin or node.bin.op != .or_op) {
                    return self.fail(step.loc, "or_intro must claim a disjunction, not '{s}'", .{
                        try self.render(step.formula),
                    });
                }
                const side = if (step.just == .or_intro_left) node.bin.lhs else node.bin.rhs;
                if (!self.pool.alphaEq(side, src.formula)) {
                    return self.fail(r.loc, "or_intro: expected '{s}', got '{s}'", .{
                        try self.render(side), try self.render(src.formula),
                    });
                }
            },
            .or_elim => |r| {
                const disj = try self.checkStepRef(proof, r.disj, i, at);
                const node = self.pool.get(disj.formula);
                if (node != .bin or node.bin.op != .or_op) {
                    return self.fail(r.disj.loc, "or_elim expects a disjunction, got '{s}'", .{
                        try self.render(disj.formula),
                    });
                }
                inline for (.{ .{ r.left, node.bin.lhs }, .{ r.right, node.bin.rhs } }) |case| {
                    const b = try self.checkClosedBlockRef(proof, case[0], i, at);
                    if (b.kind != .assume or !self.pool.alphaEq(b.kind.assume, case[1])) {
                        return self.fail(case[0].loc, "or_elim: subproof must assume '{s}'", .{
                            try self.render(case[1]),
                        });
                    }
                    const b_conc = try self.requireLastFormula(proof, b, case[0].loc);
                    if (!self.pool.alphaEq(b_conc, step.formula)) {
                        return self.fail(case[0].loc, "or_elim: subproof concludes '{s}', not '{s}'", .{
                            try self.render(b_conc), try self.render(step.formula),
                        });
                    }
                }
            },
            .not_intro => |r| {
                const b = try self.checkClosedBlockRef(proof, r.block, i, at);
                if (b.kind != .assume) {
                    return self.fail(r.block.loc, "not_intro requires an assume subproof", .{});
                }
                // SOUNDNESS: the contradictory steps must be available at the
                // END of the cited subproof — i.e. in it or an enclosing scope
                // — NOT inside a deeper nested assumption, whose hypothesis
                // the contradiction would silently depend on.
                inline for (.{ r.s1, r.s2 }) |sr| {
                    if (@intFromEnum(sr.id) >= i) {
                        return self.fail(sr.loc, "reference does not precede this step", .{});
                    }
                    if (!isAncestorOrSelf(proof, stepAt(proof, sr.id).block, r.block.id)) {
                        return self.fail(sr.loc, "not_intro: '{s}' is not accessible at the conclusion of the cited subproof", .{
                            self.str(stepAt(proof, sr.id).label),
                        });
                    }
                }
                try self.checkContradiction(proof, r.s1, r.s2);
                const derived = try self.pool.add(.{ .not = b.kind.assume });
                try self.requireClaim(step, "not_intro", derived);
            },
            .absurd => |r| {
                _ = try self.checkStepRef(proof, r.s1, i, at);
                _ = try self.checkStepRef(proof, r.s2, i, at);
                try self.checkContradiction(proof, r.s1, r.s2);
                // from a contradiction, anything follows: claim stands
            },
            .double_negation => |r| {
                const src = try self.checkStepRef(proof, r, i, at);
                const outer = self.pool.get(src.formula);
                if (outer != .not or self.pool.get(outer.not) != .not) {
                    return self.fail(r.loc, "double_negation expects 'not not P', got '{s}'", .{
                        try self.render(src.formula),
                    });
                }
                try self.requireClaim(step, "double_negation", self.pool.get(outer.not).not);
            },
            .reflexivity => {
                const node = self.pool.get(step.formula);
                if (node != .eq or !self.pool.alphaEq(node.eq.lhs, node.eq.rhs)) {
                    return self.fail(step.loc, "reflexivity requires a claim of the form 't = t', got '{s}'", .{
                        try self.render(step.formula),
                    });
                }
            },
            .symmetry => |r| {
                const src = try self.checkStepRef(proof, r, i, at);
                const node = self.pool.get(src.formula);
                if (node != .eq) {
                    return self.fail(r.loc, "symmetry expects an equation, got '{s}'", .{
                        try self.render(src.formula),
                    });
                }
                const swapped = try self.pool.add(.{ .eq = .{ .lhs = node.eq.rhs, .rhs = node.eq.lhs } });
                try self.requireClaim(step, "symmetry", swapped);
            },
            // the claim stands on the named accelerated tactic's verdict; nothing to check
            .accelerated => {},
            .schema_instance => |r| {
                var cur = r.instance;
                for (r.premises) |pr| {
                    const ps = try self.checkStepRef(proof, pr, i, at);
                    const node = self.pool.get(cur);
                    if (node != .bin or node.bin.op != .implies) {
                        return self.fail(pr.loc, "schema instance '{s}' has no antecedent left for this premise", .{
                            try self.render(cur),
                        });
                    }
                    if (!self.pool.alphaEq(ps.formula, node.bin.lhs)) {
                        return self.fail(pr.loc, "instantiate: expected premise '{s}', got '{s}'", .{
                            try self.render(node.bin.lhs), try self.render(ps.formula),
                        });
                    }
                    cur = node.bin.rhs;
                }
                try self.requireClaim(step, "instantiate", cur);
            },
            .rewrite => |r| {
                const eq_step = try self.checkStepRef(proof, r.equation, i, at);
                const target = try self.checkStepRef(proof, r.target, i, at);
                const node = self.pool.get(eq_step.formula);
                if (node != .eq) {
                    return self.fail(r.equation.loc, "rewrite expects an equation, got '{s}'", .{
                        try self.render(eq_step.formula),
                    });
                }
                // Bidirectional: a true equation `a = b` licenses substitution in
                // EITHER direction (equality is symmetric — this is `symmetry`
                // then `rewrite` folded into one rule, so it proves nothing new).
                // Try lhs->rhs, then rhs->lhs.
                if (!self.rewriteMatches(target.formula, step.formula, node.eq.lhs, node.eq.rhs) and
                    !self.rewriteMatches(target.formula, step.formula, node.eq.rhs, node.eq.lhs))
                {
                    return self.fail(step.loc, "rewrite cannot derive '{s}' from '{s}' using '{s}' (tried both orientations)", .{
                        try self.render(step.formula),
                        try self.render(target.formula),
                        try self.render(eq_step.formula),
                    });
                }
            },
            .iff_rewrite => |r| {
                const bicond_step = try self.checkStepRef(proof, r.biconditional, i, at);
                const target = try self.checkStepRef(proof, r.target, i, at);
                // require the desugared biconditional shape `(P -> Q) and (Q -> P)`
                // and extract P, Q. (`P iff Q` always desugars to exactly this.)
                const pq = self.iffSides(bicond_step.formula) orelse {
                    return self.fail(r.biconditional.loc, "iff_rewrite expects a biconditional '(P -> Q) and (Q -> P)', got '{s}'", .{
                        try self.render(bicond_step.formula),
                    });
                };
                // replace sub-proposition P with Q at any position (subformula
                // congruence — the SAME walker as `=`-rewrite, props not terms).
                // Bidirectional: `P iff Q` licenses replacing P by Q OR Q by P
                // (a biconditional is symmetric — like the `=`-rewrite case).
                if (!self.rewriteMatches(target.formula, step.formula, pq.p, pq.q) and
                    !self.rewriteMatches(target.formula, step.formula, pq.q, pq.p))
                {
                    return self.fail(step.loc, "iff_rewrite cannot derive '{s}' from '{s}' using '{s}' (tried both orientations)", .{
                        try self.render(step.formula),
                        try self.render(target.formula),
                        try self.render(bicond_step.formula),
                    });
                }
            },
        }
    }

    fn checkContradiction(self: *Kernel, proof: Proof, r1: SRef, r2: SRef) Fail!void {
        const s1 = stepAt(proof, r1.id);
        const s2 = stepAt(proof, r2.id);
        const n2 = self.pool.get(s2.formula);
        if (n2 != .not or !self.pool.alphaEq(n2.not, s1.formula)) {
            return self.fail(r2.loc, "'{s}' and '{s}' are not contradictory", .{
                try self.render(s1.formula), try self.render(s2.formula),
            });
        }
    }

    /// If `id` is a biconditional `(P -> Q) and (Q -> P)` (what `P iff Q`
    /// desugars to — matching antecedents/consequents), return its sides
    /// `{ p, q }`; otherwise null. Used by `iff_rewrite` to license replacing
    /// the sub-proposition P by Q.
    fn iffSides(self: *Kernel, id: TermId) ?struct { p: TermId, q: TermId } {
        const n = self.pool.get(id);
        if (n != .bin or n.bin.op != .and_op) return null;
        const l = self.pool.get(n.bin.lhs);
        const r = self.pool.get(n.bin.rhs);
        if (l != .bin or l.bin.op != .implies) return null;
        if (r != .bin or r.bin.op != .implies) return null;
        // left `P -> Q`, right must be `Q -> P`
        if (!self.pool.alphaEq(l.bin.lhs, r.bin.rhs)) return null;
        if (!self.pool.alphaEq(l.bin.rhs, r.bin.lhs)) return null;
        return .{ .p = l.bin.lhs, .q = l.bin.rhs };
    }

    /// `claimed` differs from `target` only by replacing occurrences of `a`
    /// with `b` at some positions. `a`/`b` are locally closed, so matching
    /// under binders needs no shifting.
    /// Does `claimed` result from rewriting SOME occurrences of `a`→`b` inside `target` (a
    /// congruence walk)? Iterative parallel two-tree walk (was native recursion) over a work-stack
    /// of `(target, claimed)` pairs that must ALL match (a conjunction — stack order irrelevant).
    /// At each pair: accept if identical, or if it's the rewrite site (`target≡a ∧ claimed≡b`);
    /// else require same node kind + push congruent children. A mismatch short-circuits false.
    /// Soundness core — this gates every `[by rewrite]`. Scratch on the kernel arena; OOM →
    /// conservatively `false` (a failed rewrite-match only ever REJECTS a step).
    fn rewriteMatches(self: *Kernel, target: TermId, claimed: TermId, a: TermId, b: TermId) bool {
        var scratch: std.heap.ArenaAllocator = .init(self.arena);
        defer scratch.deinit();
        const al = scratch.allocator();
        var stack: std.ArrayList([2]TermId) = .empty;
        stack.append(al, .{ target, claimed }) catch return false;
        while (stack.pop()) |pair| {
            const t = pair[0];
            const c = pair[1];
            if (self.pool.alphaEq(t, c)) continue; // this position unchanged by the rewrite
            if (self.pool.alphaEq(t, a) and self.pool.alphaEq(c, b)) continue; // the rewrite site
            const tn = self.pool.get(t);
            const cn = self.pool.get(c);
            if (std.meta.activeTag(tn) != std.meta.activeTag(cn)) return false;
            switch (tn) {
                .bvar, .fvar => return false, // alphaEq already covered equality
                .app => if (!self.pushRewriteApp(&stack, al, tn.app, cn.app)) return false,
                .pred => if (!self.pushRewriteApp(&stack, al, tn.pred, cn.pred)) return false,
                .eq => |p| {
                    stack.append(al, .{ p.lhs, cn.eq.lhs }) catch return false;
                    stack.append(al, .{ p.rhs, cn.eq.rhs }) catch return false;
                },
                .not => |tt| stack.append(al, .{ tt, cn.not }) catch return false,
                .bin => |x| {
                    if (x.op != cn.bin.op) return false;
                    stack.append(al, .{ x.lhs, cn.bin.lhs }) catch return false;
                    stack.append(al, .{ x.rhs, cn.bin.rhs }) catch return false;
                },
                .quant => |q| {
                    if (q.q != cn.quant.q or q.sort != cn.quant.sort) return false;
                    stack.append(al, .{ q.body, cn.quant.body }) catch return false;
                },
            }
        }
        return true;
    }

    /// Two apps are congruent for rewriting iff same sym + arity; push their arg pairs. Returns
    /// false (no push) on a sym/arity mismatch.
    fn pushRewriteApp(self: *Kernel, stack: *std.ArrayList([2]TermId), al: std.mem.Allocator, x: term.Node.App, y: term.Node.App) bool {
        if (x.sym != y.sym or x.args.len != y.args.len) return false;
        for (self.pool.args(x), self.pool.args(y)) |ax, ay| stack.append(al, .{ ax, ay }) catch return false;
        return true;
    }
};

// --- adversarial tests: forged proofs fed directly to the kernel API ---
// The elaborator cannot produce these; the kernel must reject them anyway.

const testing = std.testing;

const Rig = struct {
    interner: *InternPool,
    pool: *term.Pool,
    sink: *Diagnostics.Sink,
    nat: SortId,
    d: term.SymId, // pred d(nat)
    p: term.SymId, // pred p

    fn kernel(self: *Rig, arena: Allocator) Kernel {
        return .{
            .arena = arena,
            .pool = self.pool,
            .interner = self.interner,
            .sink = self.sink,
        };
    }

    /// Mint an axiom fact from a working-pool formula (reify -> mintFact).
    fn mintAxiom(self: *Rig, name: []const u8, formula: TermId) !InternPool.Index {
        const off = try self.pool.reify(formula, self.interner);
        return self.interner.mintFact(.axiom, off, try self.interner.internString(name), 0);
    }
};

fn buildRig(arena: Allocator) !Rig {
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena, arena);
    const sink = try arena.create(Diagnostics.Sink);
    sink.* = .init(arena);

    const nat_ix = try interner.mintSort(.{ .name = try interner.internString("nat"), .loc = 0, .refinement = null });
    const nat_args = [_]InternPool.Index{nat_ix};
    const d_sig = try interner.intern(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &nat_args } });
    const d_ix = try interner.mintPred(.{
        .sig = d_sig,
        .guard = InternPool.no_term,
        .param_names = &.{},
        .name = try interner.internString("d"),
        .loc = 0,
    });
    const p_sig = try interner.intern(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &.{} } });
    const p_ix = try interner.mintPred(.{
        .sig = p_sig,
        .guard = InternPool.no_term,
        .param_names = &.{},
        .name = try interner.internString("p"),
        .loc = 0,
    });
    return .{
        .interner = interner,
        .pool = pool,
        .sink = sink,
        .nat = @enumFromInt(@intFromEnum(nat_ix)),
        .d = @enumFromInt(@intFromEnum(d_ix)),
        .p = @enumFromInt(@intFromEnum(p_ix)),
    };
}

fn expectRejected(rig: *Rig, arena: Allocator, proof: Proof, goal: TermId, msg_prefix: []const u8) !void {
    var k = rig.kernel(arena);
    const ok = try k.check(proof, goal, 0);
    try testing.expect(!ok);
    try testing.expectEqual(1, rig.sink.list.items.len);
    const msg = rig.sink.list.items[0].message;
    try testing.expect(std.mem.startsWith(u8, msg, msg_prefix));
}

test "forged proof: eigenvariable leak is rejected" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var rig = try buildRig(arena);

    // forged axiom about a FREE variable x (elaborator could never make one)
    const x_name = try rig.interner.internString("x");
    const x = try rig.pool.add(.{ .fvar = .{ .name = x_name, .sort = rig.nat } });
    const dx = try rig.pool.addApp(.pred, rig.d, &.{x});
    const leak_stmt = try rig.mintAxiom("leak", dx);

    // forall x: nat. d(x) — the "generalization" the leak would license
    const body = try rig.pool.close(dx, x_name);
    const goal = try rig.pool.add(.{ .quant = .{ .q = .forall, .sort = rig.nat, .hint = x_name, .body = body } });

    const s0 = try rig.interner.internString("s0");
    const s1 = try rig.interner.internString("s1");
    const s2 = try rig.interner.internString("s2");
    const fixb = try rig.interner.internString("fixb");
    const blocks = [_]Block{
        .{ .parent = null, .label = s0, .kind = .root, .first_step = 0, .last_step = 3 },
        .{ .parent = @enumFromInt(0), .label = fixb, .kind = .{ .fix = .{ .v = .{ .name = x_name, .sort = rig.nat } } }, .first_step = 1, .last_step = 2 },
    };
    const steps = [_]Step{
        // d(x) cited in the ROOT — x is pinned outside the subproof
        .{ .formula = dx, .just = .{ .axiom_ref = .{ .stmt = leak_stmt, .loc = 0 } }, .block = @enumFromInt(0), .label = s0, .loc = 0 },
        // d(x) inside the fix-block over the SAME x
        .{ .formula = dx, .just = .{ .axiom_ref = .{ .stmt = leak_stmt, .loc = 0 } }, .block = @enumFromInt(1), .label = s1, .loc = 0 },
        // the illegal generalization
        .{ .formula = goal, .just = .{ .forall_intro = .{ .id = @enumFromInt(1), .loc = 0 } }, .block = @enumFromInt(0), .label = s2, .loc = 0 },
    };
    try expectRejected(&rig, arena, .{ .steps = &steps, .blocks = &blocks }, goal, "eigenvariable 'x' occurs free");
}

test "forged proof: citing into a closed subproof is rejected" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var rig = try buildRig(arena);

    const p_id = try rig.pool.addApp(.pred, rig.p, &.{});
    const s0 = try rig.interner.internString("s0");
    const s1 = try rig.interner.internString("s1");
    const asm_b = try rig.interner.internString("asm");
    const blocks = [_]Block{
        .{ .parent = null, .label = s0, .kind = .root, .first_step = 0, .last_step = 2 },
        .{ .parent = @enumFromInt(0), .label = asm_b, .kind = .{ .assume = p_id }, .first_step = 0, .last_step = 1 },
    };
    const steps = [_]Step{
        // p inside the assume-block (fine on its own)
        .{ .formula = p_id, .just = .{ .hypothesis = .{ .id = @enumFromInt(1), .loc = 0 } }, .block = @enumFromInt(1), .label = s0, .loc = 0 },
        // root step steals p from the closed subproof
        .{ .formula = p_id, .just = .{ .and_elim_left = .{ .id = @enumFromInt(0), .loc = 0 } }, .block = @enumFromInt(0), .label = s1, .loc = 0 },
    };
    try expectRejected(&rig, arena, .{ .steps = &steps, .blocks = &blocks }, p_id, "'s0' is not accessible");
}

test "forged proof: forward/self reference is rejected" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var rig = try buildRig(arena);

    const p_id = try rig.pool.addApp(.pred, rig.p, &.{});
    const s0 = try rig.interner.internString("s0");
    const blocks = [_]Block{
        .{ .parent = null, .label = s0, .kind = .root, .first_step = 0, .last_step = 1 },
    };
    const steps = [_]Step{
        .{ .formula = p_id, .just = .{ .double_negation = .{ .id = @enumFromInt(0), .loc = 0 } }, .block = @enumFromInt(0), .label = s0, .loc = 0 },
    };
    try expectRejected(&rig, arena, .{ .steps = &steps, .blocks = &blocks }, p_id, "reference does not precede");
}

test "symmetry: swaps a proven equation; a mismatched claim is rejected" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var rig = try buildRig(arena);

    const x = try rig.pool.add(.{ .fvar = .{ .name = try rig.interner.internString("x"), .sort = rig.nat } });
    const y = try rig.pool.add(.{ .fvar = .{ .name = try rig.interner.internString("y"), .sort = rig.nat } });
    const xx = try rig.pool.add(.{ .eq = .{ .lhs = x, .rhs = x } });
    const y_eq_x = try rig.pool.add(.{ .eq = .{ .lhs = y, .rhs = x } });
    const s0 = try rig.interner.internString("s0");
    const s1 = try rig.interner.internString("s1");
    const blocks = [_]Block{
        .{ .parent = null, .label = s0, .kind = .root, .first_step = 0, .last_step = 2 },
    };

    // valid: reflexivity proves x = x, symmetry swaps it to x = x
    var k = rig.kernel(arena);
    const ok_steps = [_]Step{
        .{ .formula = xx, .just = .reflexivity, .block = @enumFromInt(0), .label = s0, .loc = 0 },
        .{ .formula = xx, .just = .{ .symmetry = .{ .id = @enumFromInt(0), .loc = 0 } }, .block = @enumFromInt(0), .label = s1, .loc = 0 },
    };
    try testing.expect(try k.check(.{ .steps = &ok_steps, .blocks = &blocks }, xx, 0));

    // forged: cite x = x but claim y = x (not the swap of x = x, which is x = x)
    const bad_steps = [_]Step{
        .{ .formula = xx, .just = .reflexivity, .block = @enumFromInt(0), .label = s0, .loc = 0 },
        .{ .formula = y_eq_x, .just = .{ .symmetry = .{ .id = @enumFromInt(0), .loc = 0 } }, .block = @enumFromInt(0), .label = s1, .loc = 0 },
    };
    try expectRejected(&rig, arena, .{ .steps = &bad_steps, .blocks = &blocks }, y_eq_x, "step claims");
}

test "forged proof: discharging a subproof from inside itself is rejected" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var rig = try buildRig(arena);

    const p_id = try rig.pool.addApp(.pred, rig.p, &.{});
    const p_imp_p = try rig.pool.add(.{ .bin = .{ .op = .implies, .lhs = p_id, .rhs = p_id } });
    const s0 = try rig.interner.internString("s0");
    const asm_b = try rig.interner.internString("asm");
    const blocks = [_]Block{
        .{ .parent = null, .label = s0, .kind = .root, .first_step = 0, .last_step = 1 },
        .{ .parent = @enumFromInt(0), .label = asm_b, .kind = .{ .assume = p_id }, .first_step = 0, .last_step = 1 },
    };
    const steps = [_]Step{
        .{ .formula = p_imp_p, .just = .{ .implies_intro = .{ .id = @enumFromInt(1), .loc = 0 } }, .block = @enumFromInt(1), .label = s0, .loc = 0 },
    };
    try expectRejected(&rig, arena, .{ .steps = &steps, .blocks = &blocks }, p_imp_p, "cannot conclude from subproof");
}
