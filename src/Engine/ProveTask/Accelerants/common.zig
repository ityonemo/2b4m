//! Shared substrate for the accelerated tactics: goal abstraction, premise bookkeeping, the
//! AC flatten/sort machinery, and the synthetic-proof helpers more than one tactic uses.
//! A namespace, not a type: every fn takes the driving `*Prove` as its first argument.

const std = @import("std");
const ast = @import("../../../ast.zig");
const lexer = @import("../../../lexer.zig");
const InternPool = @import("../../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const kernel = @import("../../../kernel.zig");
const Walk = @import("../Walk.zig");
const RefScan = @import("../RefScan.zig");
const Elab = @import("../Elab.zig");
const Schema = @import("../Schema.zig");
const Accelerant = @import("../Accelerant.zig");
const EqCert = @import("../EqCert.zig");
const rewrite = @import("rewrite.zig");
const smt = @import("../smt.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const tokName = Prove.tokName;
const testing = std.testing;
const testrig = @import("testrig.zig");

/// Build the synthetic schema's PROOF for specialize: prove `ants[0] -> … -> consequent`
/// from the head. Structure: assume each antecedent (nested blocks), and in the innermost
/// context walk the head interleaving apply_at(param) and modus_ponens(the matching
/// assumed antecedent) to reach `consequent`; then discharge back out through each block.
/// A GLOBAL head is cited (axiom/theorem); a LOCAL head is antecedent #0 (assumed, restated
/// by hypothesis). Handles the contiguous case (no interior `->`) as the ants-empty subset.
pub fn buildSpecializeProof(prove: *Prove, b: *Accelerant.Builder, head: lexer.Token, head_local: bool, head_formula: TermId, pnames: []const StrId, ants: []const TermId, consequent: TermId) Error![]const ast.Step {
    // labels for each assumed antecedent's block + its hypothesis restatement.
    const ablk = try prove.ctx.arena.alloc(StrId, ants.len);
    const ahyp = try prove.ctx.arena.alloc(StrId, ants.len);
    for (0..ants.len) |i| {
        ablk[i] = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "assume-ant{d}", .{i}));
        ahyp[i] = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "ant{d}", .{i}));
    }

    // the INNERMOST steps: cite/restate the head, then interleave elim/mp to `consequent`.
    var inner: std.ArrayList(ast.Step) = .empty;
    const law = try b.intern("the-head-law");
    if (head_local) {
        // head is antecedent #0 — restate it by hypothesis on its block.
        try inner.append(prove.ctx.arena, try b.claimStep(law, try b.termExpr(head_formula), .by, try prove.internStr("hypothesis"), &.{}, try oneRef(prove, b, ablk[0])));
    } else {
        try inner.append(prove.ctx.arena, try b.claimStep(law, try b.termExpr(head_formula), .by, try internStrRt(prove, "cite"), &.{}, try headRef(prove, head)));
    }
    // walk the head, emitting a apply_at step per binder and a modus_ponens step per `->`
    // (discharged by the matching assumed antecedent). `cur`/`cur_label` track the running
    // step; `ai` indexes params, `hi` indexes antecedents (offset past the local-head one).
    var cur = head_formula;
    var cur_label = law;
    var hi: usize = @intFromBool(head_local); // ant0 is the head itself for a local head
    var pi: usize = 0; // param index
    var stepn: u32 = 0;
    while (true) {
        const node = prove.pool.get(cur);
        if (node == .quant and node.quant.q == .forall and pi < pnames.len) {
            const pf = try prove.pool.add(.{ .fvar = .{ .name = pnames[pi], .sort = node.quant.sort } });
            const opened = try prove.pool.open(node.quant.body, pf);
            const lbl = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "elim{d}", .{stepn}));
            const arg1 = try prove.ctx.arena.alloc(*const ast.Expr, 1);
            arg1[0] = try b.nameExpr(pnames[pi]);
            try inner.append(prove.ctx.arena, try b.claimStep(lbl, try b.termExpr(opened), .by, try prove.internStr("apply_at"), arg1, try oneRef(prove, b, cur_label)));
            cur = opened;
            cur_label = lbl;
            pi += 1;
            stepn += 1;
        } else if (node == .bin and node.bin.op == .implies and hi < ants.len) {
            const lbl = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "mp{d}", .{stepn}));
            const refs2 = try prove.ctx.arena.alloc(lexer.Token, 2);
            refs2[0] = b.tok(cur_label);
            refs2[1] = b.tok(ahyp[hi]);
            try inner.append(prove.ctx.arena, try b.claimStep(lbl, try b.termExpr(node.bin.rhs), .by, try prove.internStr("modus_ponens"), &.{}, refs2));
            cur = node.bin.rhs;
            cur_label = lbl;
            hi += 1;
            stepn += 1;
        } else break;
    }
    // the innermost block's LAST step (cur_label) IS `consequent`; wrap up below.
    // now wrap `inner` in nested assume blocks (innermost = ants[last]) + discharge out.
    // build from the innermost outward.
    var body_steps = try inner.toOwnedSlice(prove.ctx.arena);
    var i: usize = ants.len;
    while (i > 0) {
        i -= 1;
        // the block's body: restate THIS level's hypothesis (unless it's the local head's
        // ant0, already restated as `law` in the innermost steps), then the inner body.
        const needs_restate = !(head_local and i == 0);
        var blk_body: []const ast.Step = body_steps;
        if (needs_restate) {
            var bb = try std.ArrayList(ast.Step).initCapacity(prove.ctx.arena, body_steps.len + 1);
            bb.appendAssumeCapacity(try b.claimStep(ahyp[i], try b.termExpr(ants[i]), .by, try prove.internStr("hypothesis"), &.{}, try oneRef(prove, b, ablk[i])));
            bb.appendSliceAssumeCapacity(body_steps);
            blk_body = bb.items;
        }
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, try b.assumeStep(ablk[i], try b.termExpr(ants[i]), blk_body));
        // export this level: `ants[i] -> <what the block concluded>`.
        const exported = try impliesFrom(b, ants[i..ants.len], consequent);
        try lvl.append(prove.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "export{d}", .{i})),
            exported,
            .by,
            try prove.internStr("discharge"),
            &.{},
            try oneRef(prove, b, ablk[i]),
        ));
        body_steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }
    return body_steps;
}

fn impliesFrom(b: *Accelerant.Builder, ants: []const TermId, consequent: TermId) Error!*const ast.Expr {
    var acc = try b.termExpr(consequent);
    var i: usize = ants.len;
    while (i > 0) {
        i -= 1;
        acc = try b.implies(try b.termExpr(ants[i]), acc);
    }
    return acc;
}

/// A single-token ref slice (arena) for a synthetic step's `refs`.
pub fn oneRef(prove: *Prove, b: *Accelerant.Builder, name: StrId) Error![]const lexer.Token {
    const r = try prove.ctx.arena.alloc(lexer.Token, 1);
    r[0] = b.tok(name);
    return r;
}

/// The head's own ref token (for a global head-cite step): reuse the head token verbatim.
pub fn headRef(prove: *Prove, head: lexer.Token) Error![]const lexer.Token {
    const r = try prove.ctx.arena.alloc(lexer.Token, 1);
    r[0] = head;
    return r;
}

/// Intern a runtime rule string (axiom/theorem chosen at runtime).
pub fn internStrRt(prove: *Prove, s: []const u8) Error!StrId {
    return prove.ctx.interner.internString(s) catch error.OutOfMemory;
}

/// Wrap the innermost cert `inner` (which concludes `goal`) in nested `assume prem_i { … }`
/// blocks (innermost = the last premise), restating each hypothesis and exporting `prem_i ->
/// …` with `discharge` out through each level — the shape `buildSpecializeProof` uses.
/// With no premises the cert steps are the proof body verbatim.
pub fn wrapTautologyPremises(prove: *Prove, b: *Accelerant.Builder, prems: []const TautAst.Prem, goal: TermId, inner: []const ast.Step) Error![]const ast.Step {
    var body_steps = inner;
    var i: usize = prems.len;
    while (i > 0) {
        i -= 1;
        // this level's block: restate its hypothesis, then the inner body.
        var blk_body = try std.ArrayList(ast.Step).initCapacity(prove.ctx.arena, body_steps.len + 1);
        blk_body.appendAssumeCapacity(try b.claimStep(prems[i].label, try b.termExpr(prems[i].formula), .by, try prove.internStr("hypothesis"), &.{}, try oneRef(prove, b, prems[i].blk_label)));
        blk_body.appendSliceAssumeCapacity(body_steps);
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, try b.assumeStep(prems[i].blk_label, try b.termExpr(prems[i].formula), blk_body.items));
        // export: `prem_i -> prem_{i+1} -> … -> goal`.
        var exported = try b.termExpr(goal);
        var j: usize = prems.len;
        while (j > i) {
            j -= 1;
            exported = try b.implies(try b.termExpr(prems[j].formula), exported);
        }
        try lvl.append(prove.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try prove.freshNamed("export"),
            exported,
            .by,
            try prove.internStr("discharge"),
            &.{},
            try oneRef(prove, b, prems[i].blk_label),
        ));
        body_steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }
    return body_steps;
}

/// The truth-search certificate, emitted as AST steps. A faithful port of the eager
/// `TautCert` (which emitted kernel steps into a shared `Lowering`): every recursive site
/// that opened a kernel block instead builds a fresh `assume { … }` AST block here. The
/// step vocabulary is identical (excluded-middle split per atom → `common_conclusion`; leaves derive
/// the goal structurally or `ex_falso` a refuted premise). No step budget (strict-only: the
/// cert MUST build for a `valid` verdict — an unbuildable one is an internal bug, not a
/// fallback). `theoryLeaf` (arithmetic) is DROPPED — pure propositional never needs it.
pub const TautAst = struct {
    p: *Prove,
    b: *Accelerant.Builder,
    goal: TermId,
    premises: []const Prem,
    atoms: []const TermId,
    assignment: []?bool,
    /// per atom: the assume-block LABEL whose hypothesis is the (positive/negative) literal
    lit_blocks: []?StrId,

    /// A cited premise surfaced as an antecedent: its formula + its restated-hypothesis label.
    pub const Prem = struct {
        formula: TermId,
        /// the label of the restated `[by hypothesis]` step inside the enclosing assume block
        label: StrId,
        /// the assume block's own label (referenced by the hypothesis / discharge steps)
        blk_label: StrId,
    };

    const CertError = Error;

    pub fn pool(self: *const TautAst) *term.Pool {
        return self.p.pool;
    }

    pub fn eval(self: *const TautAst, f: TermId) ?bool {
        return smt.eval(self.pool(), self.atoms, self.assignment, f);
    }

    /// The assume-block label whose hypothesis is the literal for atom `f` (assigned, else
    /// eval could not have decided the branch that calls this).
    pub fn litBlock(self: *const TautAst, f: TermId) StrId {
        for (self.atoms, self.lit_blocks) |a, blk| {
            if (self.pool().alphaEq(a, f)) return blk.?;
        }
        unreachable; // every leaf is a collected atom
    }

    /// Append a claim step proving `formula` by `rule` citing `refs` (given as labels); return
    /// its fresh label. The variadic `refs` are label StrIds, wrapped as tokens here.
    pub fn emit(self: *TautAst, block: *std.ArrayList(ast.Step), formula: TermId, rule: []const u8, refs: []const StrId) CertError!StrId {
        const toks = try self.p.ctx.arena.alloc(lexer.Token, refs.len);
        for (refs, toks) |r, *out| out.* = self.b.tok(r);
        const label = try self.p.freshNamed("taut");
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(formula), .by, try internStrRt(self.p, rule), &.{}, toks));
        return label;
    }

    /// A block under construction: its label + its step list. Close with `finishBlock`.
    const OpenBlock = struct { label: StrId, body: std.ArrayList(ast.Step) = .empty };

    pub fn openBlock(self: *TautAst) CertError!OpenBlock {
        return .{ .label = try self.p.freshNamed("tautology") };
    }

    /// Wrap a filled OpenBlock as `assume formula { body } @label` in `parent`.
    pub fn finishBlock(self: *TautAst, parent: *std.ArrayList(ast.Step), blk: *OpenBlock, formula: TermId) CertError!void {
        try parent.append(self.p.ctx.arena, try self.b.assumeStep(blk.label, try self.b.termExpr(formula), blk.body.items));
    }

    /// Restate an assume block's hypothesis `formula` as `[by hypothesis <blk>]`.
    pub fn hyp(self: *TautAst, blk: *OpenBlock, formula: TermId) CertError!StrId {
        return self.emit(&blk.body, formula, "hypothesis", &.{blk.label});
    }

    /// Prove `goal` in `block`. The entry point: a refuted premise closes by `ex_falso`; a
    /// true goal derives structurally; otherwise split on the first unassigned atom via an
    /// excluded-middle lemma + `common_conclusion` over the two assumption branches.
    ///
    /// An iterative DFS over the decision tree (was self-recursion in the two split arms;
    /// depth is the ≤16-atom cap, but Zig will disallow recursion regardless). `expand`
    /// handles one node (premise-refute / true-derive / split); a split pushes `finish`
    /// (below) then the right-arm setup then the left-arm setup+expand, so the LEFT subtree
    /// fully drains before the RIGHT arm's `assignment[idx]` is set, and the `finish` frame
    /// (finishBlocks + common_conclusion + restore) runs after BOTH arms — identical to the recursive
    /// set/recurse/restore discipline. Scratch stacks on the pool's GPA. The goal-proving
    /// step is the block's last; callers read it from there (no label to return).
    pub fn deriveGoal(self: *TautAst, block: *std.ArrayList(ast.Step)) CertError!void {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        const Frame = union(enum) {
            expand: *std.ArrayList(ast.Step),
            // set the right arm's assignment, then expand it into `right.body`.
            arm_right: struct { idx: usize, right: *OpenBlock },
            // both arms drained: finish them into `block` + common_conclusion + restore assignment.
            finish: struct { block: *std.ArrayList(ast.Step), idx: usize, atom: TermId, not_atom: TermId, lem: StrId, left: *OpenBlock, right: *OpenBlock },
        };
        var work: std.ArrayList(Frame) = .empty;
        try work.append(sa, .{ .expand = block });

        while (work.pop()) |frame| switch (frame) {
            .expand => |blk| {
                const refuted_premise: ?Prem = for (self.premises) |pr| {
                    if (self.eval(pr.formula) == false) break pr;
                } else null;
                if (refuted_premise) |pr| {
                    const refuted = try self.deriveFalse(blk, pr.formula);
                    _ = try self.emit(blk, self.goal, "ex_falso", &.{ pr.label, refuted });
                    continue;
                }
                if (self.eval(self.goal) == true) {
                    _ = try self.deriveTrue(blk, self.goal);
                    continue;
                }
                // some atom is still unassigned; split on it (see the recursive-version note).
                std.debug.assert(std.mem.indexOfScalar(?bool, self.assignment, null) != null);
                const idx = for (self.assignment, 0..) |v, i| {
                    if (v == null) break i;
                } else unreachable;
                const atom = self.atoms[idx];
                const not_atom = try self.pool().add(.{ .not = atom });
                const disj = try self.pool().add(.{ .bin = .{ .op = .or_op, .lhs = atom, .rhs = not_atom } });
                const lem = try self.emitLem(blk, atom, not_atom, disj);

                const left = try sa.create(OpenBlock);
                left.* = try self.openBlock();
                const right = try sa.create(OpenBlock);
                right.* = try self.openBlock();

                // stack order (LIFO): left-expand runs first (drains fully), then arm_right sets
                // the right assignment + expands it, then finish closes both arms.
                try work.append(sa, .{ .finish = .{ .block = blk, .idx = idx, .atom = atom, .not_atom = not_atom, .lem = lem, .left = left, .right = right } });
                try work.append(sa, .{ .arm_right = .{ .idx = idx, .right = right } });
                // left arm: assume atom; the arm block IS its literal source.
                self.assignment[idx] = true;
                self.lit_blocks[idx] = left.label;
                try work.append(sa, .{ .expand = &left.body });
            },
            .arm_right => |a| {
                self.assignment[a.idx] = false;
                self.lit_blocks[a.idx] = a.right.label;
                try work.append(sa, .{ .expand = &a.right.body });
            },
            .finish => |c| {
                try self.finishBlock(c.block, c.left, c.atom);
                try self.finishBlock(c.block, c.right, c.not_atom);
                self.assignment[c.idx] = null;
                self.lit_blocks[c.idx] = null;
                _ = try self.emit(c.block, self.goal, "common_conclusion", &.{ c.lem, c.left.label, c.right.label });
            },
        };
    }

    /// `atom or not atom` the classical way: contradiction on the negated disjunction, then
    /// double_negation. A fixed AST gadget (the port of `TautCert.emitLem`).
    pub fn emitLem(self: *TautAst, block: *std.ArrayList(ast.Step), atom: TermId, not_atom: TermId, disj: TermId) CertError!StrId {
        const not_disj = try self.pool().add(.{ .not = disj });
        const not_not = try self.pool().add(.{ .not = not_disj });

        var outer = try self.openBlock();
        const hyp_outer = try self.hyp(&outer, not_disj);
        // inner: assume atom, derive the disjunction by either_lhs.
        var inner = try self.openBlock();
        const hyp_inner = try self.hyp(&inner, atom);
        const or_left = try self.emit(&inner.body, disj, "either_lhs", &.{hyp_inner});
        try self.finishBlock(&outer.body, &inner, atom);
        const derived_not = try self.emit(&outer.body, not_atom, "contradiction", &.{ inner.label, or_left, hyp_outer });
        const or_right = try self.emit(&outer.body, disj, "either_rhs", &.{derived_not});
        try self.finishBlock(block, &outer, not_disj);

        const nn = try self.emit(block, not_not, "contradiction", &.{ outer.label, or_right, hyp_outer });
        return self.emit(block, disj, "double_negation", &.{nn});
    }

    /// Emit a step proving `f` (which evaluates true) in `block`; return its label.
    pub fn deriveTrue(self: *TautAst, block: *std.ArrayList(ast.Step), f: TermId) CertError!StrId {
        return self.deriveStructural(.true, block, f);
    }

    /// Emit a step proving `not f` (f evaluates false) in `block`; return its label.
    pub fn deriveFalse(self: *TautAst, block: *std.ArrayList(ast.Step), f: TermId) CertError!StrId {
        return self.deriveStructural(.false, block, f);
    }

    const Mode = enum { true, false };

    /// The shared iterative engine behind `deriveTrue`/`deriveFalse` (was mutual native
    /// recursion over formula structure — a deep goal could blow the C stack). A post-order
    /// worklist: an `expand` frame decomposes `(mode, f)`, pushing child `expand`s that emit
    /// into the SAME `block` (except `deriveTrue.implies`, whose child emits into a fresh
    /// sub-block) followed by a `combine` frame; a `combine` pops the child result labels off
    /// `results` and emits the parent step, pushing ITS label. The step vocabulary + emission
    /// order are byte-identical to the recursive version. Scratch stacks on the pool's GPA.
    pub fn deriveStructural(self: *TautAst, root_mode: Mode, root_block: *std.ArrayList(ast.Step), root_f: TermId) CertError!StrId {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        // A fresh sub-block heap-allocated on the scratch arena so `&ob.body` pointers stay
        // stable across the worklist loop (the recursive version used a stack local).
        const Frame = union(enum) {
            expand: struct { mode: Mode, block: *std.ArrayList(ast.Step), f: TermId },
            // combiners — each pops N labels from `results`, emits, pushes one label.
            combine_and: struct { block: *std.ArrayList(ast.Step), f: TermId }, // pops left,right
            combine_or_left: struct { block: *std.ArrayList(ast.Step), f: TermId }, // pops l
            combine_or_right: struct { block: *std.ArrayList(ast.Step), f: TermId }, // pops r
            // true.implies (true consequent): child already emitted into blk.body; finish + discharge.
            combine_true_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId },
            // true.implies (false antecedent): refutation on `results`; emit ex_falso inside blk.body, then finish + discharge.
            combine_true_implies_absurd: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId, conseq: TermId, hyp: StrId },
            // false.and: child (refuted `side`) already on `results`.
            combine_false_and: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, side: TermId, left_false: bool },
            // false.or: pops not_left,not_right (order: not_left pushed first → deeper on stack).
            combine_false_or: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, lhs: TermId, rhs: TermId },
            // false.implies: pops ante(true),not_conseq(false).
            combine_false_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, rhs: TermId },
            // false.not (not not inner): pops deriveTrue(inner).
            combine_false_not: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId },
        };
        var work: std.ArrayList(Frame) = .empty;
        var results: std.ArrayList(StrId) = .empty;
        try work.append(sa, .{ .expand = .{ .mode = root_mode, .block = root_block, .f = root_f } });

        while (work.pop()) |frame| switch (frame) {
            .expand => |e| switch (e.mode) {
                .true => switch (self.pool().get(e.f)) {
                    .bin => |bn| switch (bn.op) {
                        .and_op => {
                            // children into same block; combine emits both/make_equivalence.
                            try work.append(sa, .{ .combine_and = .{ .block = e.block, .f = e.f } });
                            try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bn.rhs } });
                            try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bn.lhs } });
                        },
                        .or_op => {
                            if (self.eval(bn.lhs) == true) {
                                try work.append(sa, .{ .combine_or_left = .{ .block = e.block, .f = e.f } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bn.lhs } });
                            } else {
                                try work.append(sa, .{ .combine_or_right = .{ .block = e.block, .f = e.f } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bn.rhs } });
                            }
                        },
                        .implies => {
                            const blk = try sa.create(OpenBlock);
                            blk.* = try self.openBlock();
                            if (self.eval(bn.rhs) == true) {
                                try work.append(sa, .{ .combine_true_implies = .{ .block = e.block, .f = e.f, .blk = blk, .ante = bn.lhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = &blk.body, .f = bn.rhs } });
                            } else {
                                // antecedent false: assume it, refute it, explode into consequent.
                                const h = try self.hyp(blk, bn.lhs);
                                // ex_falso(h, refuted) emitted after the refutation resolves — but the
                                // recursive version emits it INSIDE blk.body before finishBlock. A
                                // dedicated combine emits ex_falso then finishes + discharge.
                                try work.append(sa, .{ .combine_true_implies_absurd = .{ .block = e.block, .f = e.f, .blk = blk, .ante = bn.lhs, .conseq = bn.rhs, .hyp = h } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = &blk.body, .f = bn.lhs } });
                            }
                        },
                    },
                    .not => |inner| {
                        // deriveTrue(not inner) == deriveFalse(inner), same block, same result.
                        try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = inner } });
                    },
                    else => try results.append(sa, try self.emit(e.block, e.f, "hypothesis", &.{self.litBlock(e.f)})),
                },
                .false => switch (self.pool().get(e.f)) {
                    .bin => |bn| switch (bn.op) {
                        .and_op => {
                            const left_false = self.eval(bn.lhs) == false;
                            const side = if (left_false) bn.lhs else bn.rhs;
                            const nf = try self.pool().add(.{ .not = e.f });
                            try work.append(sa, .{ .combine_false_and = .{ .block = e.block, .f = e.f, .nf = nf, .side = side, .left_false = left_false } });
                            try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = side } });
                        },
                        .or_op => {
                            const nf = try self.pool().add(.{ .not = e.f });
                            try work.append(sa, .{ .combine_false_or = .{ .block = e.block, .f = e.f, .nf = nf, .lhs = bn.lhs, .rhs = bn.rhs } });
                            // not_left resolves first, not_right second (recursive order).
                            try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bn.rhs } });
                            try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bn.lhs } });
                        },
                        .implies => {
                            const nf = try self.pool().add(.{ .not = e.f });
                            try work.append(sa, .{ .combine_false_implies = .{ .block = e.block, .f = e.f, .nf = nf, .rhs = bn.rhs } });
                            // ante(true) resolves first, not_conseq(false) second.
                            try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bn.rhs } });
                            try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bn.lhs } });
                        },
                    },
                    .not => |inner| {
                        const nf = try self.pool().add(.{ .not = e.f });
                        try work.append(sa, .{ .combine_false_not = .{ .block = e.block, .f = e.f, .nf = nf } });
                        try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = inner } });
                    },
                    else => {
                        const nf = try self.pool().add(.{ .not = e.f });
                        try results.append(sa, try self.emit(e.block, nf, "hypothesis", &.{self.litBlock(e.f)}));
                    },
                },
            },
            .combine_and => |c| {
                const right = results.pop().?;
                const left = results.pop().?;
                const rule: []const u8 = if (self.p.isBiconditionalShape(c.f)) "make_equivalence" else "both";
                try results.append(sa, try self.emit(c.block, c.f, rule, &.{ left, right }));
            },
            .combine_or_left => |c| {
                const l = results.pop().?;
                try results.append(sa, try self.emit(c.block, c.f, "either_lhs", &.{l}));
            },
            .combine_or_right => |c| {
                const r = results.pop().?;
                try results.append(sa, try self.emit(c.block, c.f, "either_rhs", &.{r}));
            },
            .combine_true_implies => |c| {
                // true-consequent branch: child already emitted into blk.body; discard its label.
                _ = results.pop().?;
                try self.finishBlock(c.block, c.blk, c.ante);
                try results.append(sa, try self.emit(c.block, c.f, "discharge", &.{c.blk.label}));
            },
            .combine_true_implies_absurd => |c| {
                const refuted = results.pop().?;
                _ = try self.emit(&c.blk.body, c.conseq, "ex_falso", &.{ c.hyp, refuted });
                try self.finishBlock(c.block, c.blk, c.ante);
                try results.append(sa, try self.emit(c.block, c.f, "discharge", &.{c.blk.label}));
            },
            .combine_false_and => |c| {
                const refuted = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                const elim = try self.emit(&blk.body, c.side, if (c.left_false) "and_lhs" else "and_rhs", &.{h});
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, elim, refuted }));
            },
            .combine_false_or => |c| {
                const not_right = results.pop().?;
                const not_left = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                var left = try self.openBlock();
                _ = try self.hyp(&left, c.lhs);
                try self.finishBlock(&blk.body, &left, c.lhs);
                var right = try self.openBlock();
                const rh = try self.hyp(&right, c.rhs);
                _ = try self.emit(&right.body, c.lhs, "ex_falso", &.{ rh, not_right });
                try self.finishBlock(&blk.body, &right, c.rhs);
                const conc = try self.emit(&blk.body, c.lhs, "common_conclusion", &.{ h, left.label, right.label });
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, conc, not_left }));
            },
            .combine_false_implies => |c| {
                const not_conseq = results.pop().?;
                const ante = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                const conseq = try self.emit(&blk.body, c.rhs, "modus_ponens", &.{ h, ante });
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, conseq, not_conseq }));
            },
            .combine_false_not => |c| {
                const truth = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, truth, h }));
            },
        };
        return results.items[0];
    }
};

/// The fresh-label trampoline EqCert calls (type-erased `*Prove`).
pub fn eqCertFresh(ctx: *anyopaque, prefix: []const u8) anyerror!StrId {
    const self: *Prove = @ptrCast(@alignCast(ctx));
    return self.freshNamed(prefix);
}

/// The FORMULA of a cited global fact, by the route the current mode allows.
///
/// Strict resolves the fact itself (`resolveFactRef`, which requires `.proven`). ADMIT mode
/// cannot: the trusted read pass deliberately racks no ProveTask for a cited rule, since that
/// is the proof cascade `--fast` exists to avoid. But an accelerant's DECISION needs only the
/// STATEMENT — and `elaborateFactStatement` reads one without racking a ProveTask, which is
/// exactly the right weight. A `.suspended` records `producer_blocker` so the caller treats the
/// `Recover` as a PARK (re-run) rather than a diagnosed rejection; rejecting would drop the
/// step's LABEL from the walk and surface as "unknown reference" at whatever cited it next.
///
/// Returns the formula and whether the fact is an AXIOM (admit mode cannot tell, and does not
/// need to — the kind only decorates an emitted cert's `[by axiom|theorem]` word).
pub fn citedFactFormula(prove: *Prove, ref: lexer.Token) Error!struct { formula: TermId, is_axiom: bool } {
    if (!prove.admit_mode) {
        const fact = try prove.resolveFactRef(ref);
        const key = prove.ctx.interner.keyOf(fact).fact;
        return .{
            .formula = try prove.pool.copyIn(prove.ctx.interner, key.formula),
            .is_axiom = key.kind == .axiom,
        };
    }
    return .{ .formula = try factStatement(prove, ref), .is_axiom = false };
}

/// A cited fact's STATEMENT, read without demanding its proof — what a trusted decision reads.
/// Parks (`producer_blocker`) if it is not yet resolvable, which means phase 1 missed it.
pub fn factStatement(prove: *Prove, ref: lexer.Token) Error!TermId {
    const sfile = if (ref.qualifier == InternPool.Index.none) prove.file else blk: {
        const ns = try prove.resolveQualifier(ref);
        break :blk prove.ctx.interner.keyOf(ns).namespace.file;
    };
    switch (try Prove.elaborateFactStatement(prove.ctx, prove.h, sfile, Prove.tokName(ref), prove.model, prove.pool)) {
        .ready => |stmt| return stmt,
        .suspended => {
            prove.producer_blocker = prove.h.blocked_on;
            return error.Recover;
        },
        .failed => return error.Recover,
    }
}

/// Prepare one rewrite rule from a cited ref: resolve its formula (LOCAL step or GLOBAL
/// axiom/theorem), orient the (possibly ∀-prefixed) equation left→right opening each binder
/// at a fresh `#`-mangled pattern fvar, and record how the cert cites it. A rule's binders
/// must all occur on the lhs (else it is not a usable rewrite rule).
pub const PreparedRule = struct { rule: rewrite.Rule, cite: EqCert.RuleCite, local: bool, formula: TermId };

pub fn prepareRule(prove: *Prove, w: *const Walk, ref: lexer.Token) Error!PreparedRule {
    var formula: TermId = undefined;
    var cite: EqCert.RuleCite = undefined;
    const is_local = ref.qualifier == InternPool.Index.none and w.findStep(Prove.tokName(ref)) != null;
    if (is_local) {
        // a LOCAL equation step: it becomes a schema antecedent, restated by hypothesis.
        const sref = try prove.resolveStepRef(w, ref);
        formula = prove.producerPremiseFormula(sref);
        cite = .{ .local = .{ .hyp = try premiseHypLabel(prove, ref) } };
    } else {
        const got = try citedFactFormula(prove, ref);
        formula = got.formula;
        cite = .{ .global = .{ .head = ref, .is_axiom = got.is_axiom } };
    }
    // orient: peel `forall` binders as fresh pattern fvars, require an equation body. Under a
    // model TRANSFER the cited lemma is RELATIVIZED — `∀a; inH(a) -> ∀b; … -> lhs=rhs` — with
    // guard `->`s interleaved with the binders; SKIP them here to reach the equation (they are
    // discharged where the lemma is applied: emitInstance cites + forall_elims the lemma, and the
    // instance ProveTask runs under the model so the apply_at discharge machinery strips them).
    var binders: std.ArrayList(rewrite.Binder) = .empty;
    var body = formula;
    while (true) {
        const node = prove.pool.get(body);
        if (node == .quant and node.quant.q == .forall) {
            const fresh = try prove.freshNamed("p#");
            const fv = try prove.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            body = try prove.pool.open(node.quant.body, fv);
            try binders.append(prove.ctx.arena, .{ .fvar = fresh, .sort = node.quant.sort });
            continue;
        }
        // a relativization guard `inH(v) -> …` (transfer only): skip to the consequent.
        if (node == .bin and node.bin.op == .implies and prove.model != InternPool.Index.none and prove.model != .universe) {
            body = node.bin.rhs;
            continue;
        }
        break;
    }
    const bn = prove.pool.get(body);
    if (bn != .eq) return prove.fail(ref.start, "'{s}' is not an equation", .{prove.text(ref)});
    for (binders.items) |bd| {
        if (!prove.pool.occursFree(bn.eq.lhs, bd.fvar)) {
            return prove.fail(ref.start, "'{s}': not every bound variable occurs on the left-hand side", .{prove.text(ref)});
        }
    }
    return .{
        .rule = .{ .binders = binders.items, .lhs = bn.eq.lhs, .rhs = bn.eq.rhs, .formula = formula },
        .cite = cite,
        .local = is_local,
        .formula = formula,
    };
}

/// The deterministic hypothesis-restatement label for a LOCAL rule premise `ref` (stable
/// across re-entry: derived from the ref's stamped name, so the wrapper and the cert name
/// the same step).
pub fn premiseHypLabel(prove: *Prove, ref: lexer.Token) Error!StrId {
    return prove.ctx.interner.internString(std.fmt.allocPrint(prove.ctx.arena, "prem-{d}", .{@intFromEnum(Prove.tokName(ref))}) catch return error.OutOfMemory) catch return error.OutOfMemory;
}

/// Shared core for both simplify variants: prepare rules, normalize both sides of the body
/// equation `eq_goal`, join (or fail on differing NFs / a cap overflow), then build the
/// synthetic schema. `eigen` (empty for plain simplify) are the peeled ∀ eigenvariables the
/// quantified variant re-generalizes over via `fix` blocks (they are NOT abstracted into
/// params — the schema proof re-binds them; only genuinely-free caller-locals become params).
pub fn buildSimplify(prove: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    // `--fast` declines to EMIT the certificate; the NORMALIZE DECISION still runs. (Admitting
    // here let `--fast` accept `add(ZERO, succ(ZERO)) = succ(succ(ZERO))`, which strict rejects
    // — a both-ways divergence the `--fast` contract forbids.) The decision needs the cited
    // rules' STATEMENTS, which `prepareRule` reads via `elaborateFactStatement` in admit mode —
    // no ProveTask, so no proof cascade. Admit lands after the normal-form comparison below,
    // before `EqCert` emission. See design/acceleration.md.
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // prepare the rewrite rules (in citation order) + how the cert cites each.
    const prepared = try prove.ctx.arena.alloc(PreparedRule, c.refs.len);
    for (c.refs, prepared) |r, *out| out.* = try prepareRule(prove, w, r);
    const rules = try prove.ctx.arena.alloc(rewrite.Rule, prepared.len);
    const cites = try prove.ctx.arena.alloc(EqCert.RuleCite, prepared.len);
    for (prepared, rules, cites) |p, *ru, *ci| {
        ru.* = p.rule;
        ci.* = p.cite;
    }

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix` at the call site) into
    // value params UP FRONT — before normalizing — so `s`/`t`, the cert steps (built over the
    // trace), and the schema body ALL speak the param names `p1, p2, …`. Eigenvariables (the
    // quantified variant's peeled ∀ vars) are EXCLUDED: they stay free here and are re-bound
    // by the `fix` wrapper. A local rule premise's formula may share such an fvar, so include
    // each in the abstraction domain too.
    var local_pf: std.ArrayList(TermId) = .empty;
    for (prepared) |p| if (p.local) try local_pf.append(prove.ctx.arena, p.formula);
    const ag = try abstractGoal(prove, &b, eq_goal_raw, local_pf.items, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;

    // A LOCAL rule's lhs/rhs are in the CALLER's eigenvar space (`k,b,c`); the goal was just
    // abstracted into param space (`p1,p2,…`). Re-substitute each local rule through `abs` so it
    // matches the param-space goal subterms — else a local IH rewrite never fires (its pattern
    // names `k` while the goal names `p1`). Global rules are closed, unaffected.
    for (prepared, rules) |p, *ru| if (p.local) {
        ru.lhs = try substFvarsToParams(prove, ru.lhs, abs);
        ru.rhs = try substFvarsToParams(prove, ru.rhs, abs);
    };

    const gn = prove.pool.get(eq_goal).eq;
    const s = gn.lhs;
    const t = gn.rhs;

    // normalize both sides; a looping rule set trips the cap (1000, as the eager core).
    const rs = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules, s, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "simplify: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules, t, 1000) catch |e| switch (e) {
        error.Limit => return prove.fail(c.rule.start, "simplify: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!prove.pool.alphaEq(rs.nf, rt.nf)) {
        // render over the ORIGINAL caller names: undo the param abstraction (pK -> display
        // fvar) so the diagnostic shows `add(n, ZERO)`, not the synthetic `add(p1, ZERO)`.
        return prove.fail(c.rule.start, "simplify: normal forms differ: '{s}' vs '{s}'", .{
            try prove.renderTerm(try unabstract(prove, rs.nf, abs)),
            try prove.renderTerm(try unabstract(prove, rt.nf, abs)),
        });
    }

    // ADMIT: both sides reached the SAME normal form under the cited rules, so a certificate
    // demonstrably exists — only emitting it is pruned. `producer_premise_refs` is cleared:
    // it records the LOCAL refs a produced synthetic kept as antecedents, and the admitted
    // path reads it to decide which cited refs are steps to resolve; an admitted step builds
    // no instance and has none. (It was null here before only because `simplify` admitted
    // before producing at all.)
    if (prove.admit_mode) {
        prove.producer_premise_refs = null;
        prove.admit_ok = true;
        return null;
    }

    // Build the equation-cert AST proving `s = t` into a fresh step list.
    var cert: EqCert = .{
        .b = &b,
        .pool = prove.pool,
        .rules = rules,
        .cites = cites,
        .fresh_ctx = prove,
        .freshFn = eqCertFresh,
    };
    var body_steps: std.ArrayList(ast.Step) = .empty;
    _ = try cert.emitJoin(&body_steps, s, t, rs, rt);
    var steps: []const ast.Step = body_steps.items;

    // LOCAL rules are schema antecedents (restated by hypothesis + discharged at the call
    // site) in ref order; collect their (cite, param-substituted formula) for the wrappers.
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (prepared) |p| if (p.local) {
        try local_cites.append(prove.ctx.arena, p.cite);
        try local_formulae.append(prove.ctx.arena, try substFvarsToParams(prove, p.formula, abs));
    };

    // the inner proposition the cert proves under its assumptions: `prem0 -> … -> (s = t)`.
    const eq_prop = try prove.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    // the antecedents are the premises the cert CITES (an uncited rule is dropped — see
    // wrapSimplifyPremises), so compute them from the emitted cert before wrapping.
    const kept = try keptPremises(prove, local_cites.items, local_formulae.items, steps);
    const kept_refs = try keptRefTokens(prove, w, c.refs, local_cites.items, steps);
    const inner_prop = try impliesChain(prove, eq_prop, kept);

    // wrap the cert in nested `assume <local-prem>` blocks (the `->` antecedents), then in
    // `fix` blocks for the ∀ eigenvariables (the quantified variant's re-generalization).
    steps = try wrapSimplifyPremises(prove, &b, local_cites.items, local_formulae.items, eq_prop, steps);
    steps = try wrapSimplifyForall(prove, &b, eigen, inner_prop, steps);

    // PARAM GUARDS, exactly as `finishReorder` does for the reorder path. A rewrite rule
    // quantified over a sort the MODEL refines relativizes to `∀a; good(a) -> …`; opening it
    // at the abstracted param `p1` leaks `good(p1)`, which is dischargeable NOWHERE inside
    // the synthetic — a param sits in no `fix`'s scope, and closure recursion dead-ends on a
    // bare fvar. So the guard becomes an OUTERMOST antecedent of the synthetic's statement
    // and `withGuardPremises` discharges it at the call site, where the original binder's
    // guard really is in scope. Empty outside a guarded model, so the universe is unaffected.
    var e_guard = prove.elab(w);
    const guards = try paramGuards(prove, w, &e_guard, abs);
    const eigen_prop = try closeOverEigen(prove, inner_prop, eigen);
    steps = try wrapParamGuards(prove, &b, guards, eigen_prop, steps);

    // the schema body proposition = the guard-prefixed ∀-generalized `inner_prop`.
    const full_prop = try impliesChain(prove, eigen_prop, guards);
    const body_expr = try b.termExpr(full_prop);

    // params from the abstracted free fvars (value params of the fvars' sorts).
    const params = try prove.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        pp.* = .{ .name = b.tok(name), .kind = .{ .value = b.sortTok(sort) } };
    }

    // deterministic hash-name from the (pre-substitution) full proposition (re-entry stable).
    const hash = Schema.termHash(prove.ctx.interner, prove.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "simplify{{{x}}}", .{hash}));

    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = kept_refs, // the cited premises, discharged at the call site
        .seen = b.seen.items,
        .fvar_binds = try fvarBinds(prove, w, abs),
    };
}

/// The LOCAL rule ref TOKENS (for the `Synthetic.premises` slot — the demand plumbing rides
/// these as the instance claim's `refs`; `accelerantPremises` re-resolves them to steps).
pub fn localRefTokens(prove: *Prove, w: *const Walk, refs: []const lexer.Token) Error![]const lexer.Token {
    var out: std.ArrayList(lexer.Token) = .empty;
    for (refs) |r| {
        if (r.qualifier == InternPool.Index.none and w.findStep(Prove.tokName(r)) != null) {
            try out.append(prove.ctx.arena, r);
        }
    }
    return out.items;
}

/// The LOCAL refs whose premises the cert CITES — the call-site discharge list, in lockstep
/// with the antecedents `keptPremises`/`wrapSimplifyPremises` keep. A ref whose rewrite never
/// fired is neither an antecedent nor discharged (see `wrapSimplifyPremises`).
pub fn keptRefTokens(prove: *Prove, w: *const Walk, refs: []const lexer.Token, cites: []const EqCert.RuleCite, inner: []const ast.Step) Error![]const lexer.Token {
    const locals = try localRefTokens(prove, w, refs);
    const used = try usedPremiseCites(prove, cites, inner);
    if (locals.len != used.len) return locals; // shapes disagree — keep every local (no filter)
    var out: std.ArrayList(lexer.Token) = .empty;
    for (locals, used) |r, u| if (u) try out.append(prove.ctx.arena, r);
    return out.items;
}

/// `ants[0] -> … -> ants[n] -> consequent` (right-assoc) as a kernel term.
pub fn impliesChain(prove: *Prove, consequent: TermId, ants: []const TermId) Error!TermId {
    var acc = consequent;
    var i: usize = ants.len;
    while (i > 0) {
        i -= 1;
        acc = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = ants[i], .rhs = acc } });
    }
    return acc;
}

/// Which LOCAL premises the emitted certificate ACTUALLY cites: a premise becomes a rewrite
/// RULE offered to the normalizer, but a rule whose lhs never matches never fires, and
/// `EqCert` emits a citation only for rules the trace used. `cites[i]` names premise `i`'s
/// restated-hypothesis label; scan `steps` for a citation of it. (Scanning the emitted proof
/// — rather than threading each producer's trace here — keeps the one seam every producer
/// already shares, and is exactly the question being asked: does the cert cite this step?)
fn usedPremiseCites(prove: *Prove, cites: []const EqCert.RuleCite, steps: []const ast.Step) Error![]bool {
    const used = try prove.ctx.arena.alloc(bool, cites.len);
    @memset(used, false);
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();
    var stack: std.ArrayList([]const ast.Step) = .empty;
    try stack.append(a, steps);
    while (stack.pop()) |lvl| for (lvl) |st| switch (st.body) {
        .claim => |c| for (c.refs) |r| {
            for (cites, used) |cite, *u| {
                if (cite == .local and cite.local.hyp == r.name) u.* = true;
            }
        },
        .assume => |blk| try stack.append(a, blk.steps),
        .fix => |blk| try stack.append(a, blk.steps),
        .unpack => |blk| {
            for (cites, used) |cite, *u| {
                if (cite == .local and cite.local.hyp == blk.from.name) u.* = true;
            }
            try stack.append(a, blk.steps);
        },
        .case => |cb| {
            for (cites, used) |cite, *u| {
                if (cite == .local and cite.local.hyp == cb.disj.name) u.* = true;
            }
            for (cb.arms) |arm| try stack.append(a, arm.steps);
        },
    };
    return used;
}

/// The LOCAL premises the cert cites, in order — what `wrapSimplifyPremises` will wrap, so a
/// caller's `impliesChain` antecedents match the wrapper's blocks exactly. (An uncited premise
/// is dropped from both: see `wrapSimplifyPremises`.)
pub fn keptPremises(prove: *Prove, cites: []const EqCert.RuleCite, formulae: []const TermId, inner: []const ast.Step) Error![]const TermId {
    const used = try usedPremiseCites(prove, cites, inner);
    var out: std.ArrayList(TermId) = .empty;
    for (formulae, used) |f, u| if (u) try out.append(prove.ctx.arena, f);
    return out.items;
}

/// Wrap the cert `inner` (proving the equation `eq_prop`) in nested `assume <local-prem>`
/// blocks — one per LOCAL rule premise the cert CITES, restating its hypothesis (under the
/// deterministic `prem-…` label the cert cites) and exporting `prem_i -> …` with
/// `discharge` out through each level. With no such premises the cert steps pass through
/// verbatim. (Same shape as tautology's `wrapTautologyPremises`.)
///
/// A premise the cert never cites is DROPPED — not wrapped: it was offered to the normalizer
/// as a rewrite rule and never fired, so restating it would leave an uncited step that trips
/// the generated schema's own use-all-facts pass. `keptPremises` computes the surviving
/// formulae so the caller's `impliesChain` antecedents match this wrapper's blocks exactly.
pub fn wrapSimplifyPremises(prove: *Prove, b: *Accelerant.Builder, cites_in: []const EqCert.RuleCite, formulae_in: []const TermId, eq_prop: TermId, inner: []const ast.Step) Error![]const ast.Step {
    const used = try usedPremiseCites(prove, cites_in, inner);
    var cites_kept: std.ArrayList(EqCert.RuleCite) = .empty;
    var formulae_kept: std.ArrayList(TermId) = .empty;
    for (cites_in, formulae_in, used) |c, f, u| if (u) {
        try cites_kept.append(prove.ctx.arena, c);
        try formulae_kept.append(prove.ctx.arena, f);
    };
    const cites = cites_kept.items;
    const formulae = formulae_kept.items;

    var body_steps = inner;
    var i: usize = formulae.len;
    while (i > 0) {
        i -= 1;
        const blk_label = try prove.freshNamed("assume-prem");
        var blk_body = try std.ArrayList(ast.Step).initCapacity(prove.ctx.arena, body_steps.len + 1);
        const hyp_label = cites[i].local.hyp;
        blk_body.appendAssumeCapacity(try b.claimStep(hyp_label, try b.termExpr(formulae[i]), .by, try prove.internStr("hypothesis"), &.{}, try oneRef(prove, b, blk_label)));
        blk_body.appendSliceAssumeCapacity(body_steps);
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, try b.assumeStep(blk_label, try b.termExpr(formulae[i]), blk_body.items));
        // export: `prem_i -> … -> (s = t)`.
        const exported = try impliesChain(prove, eq_prop, formulae[i..]);
        try lvl.append(prove.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try prove.freshNamed("export"),
            try b.termExpr(exported),
            .by,
            try prove.internStr("discharge"),
            &.{},
            try oneRef(prove, b, blk_label),
        ));
        body_steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }
    return body_steps;
}

/// Wrap `body_steps` (proving `inner`) in `assume good(p_i) { … }` + `discharge` per param
/// guard, outermost = guards[0], so the synthetic's statement becomes
/// `good(p_0) -> … -> inner`. Unlike `wrapSimplifyPremises` a guard has no local cite to
/// restate — nothing inside the body needs to NAME it; it only has to be assumed so the
/// relativized lemma's leaked guard is discharged from the assumption (source 2c). See
/// `paramGuards` for why the synthetic owes these at all.
fn wrapParamGuards(prove: *Prove, b: *Accelerant.Builder, guards: []const TermId, inner: TermId, body_steps: []const ast.Step) Error![]const ast.Step {
    if (guards.len == 0) return body_steps;
    var steps = body_steps;
    var prop = inner;
    var i: usize = guards.len;
    while (i > 0) {
        i -= 1;
        const blk_label = try prove.freshNamed("assume-guard");
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, try b.assumeStep(blk_label, try b.termExpr(guards[i]), steps));
        prop = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = guards[i], .rhs = prop } });
        try lvl.append(prove.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try prove.freshNamed("export-guard"),
            try b.termExpr(prop),
            .by,
            try prove.internStr("discharge"),
            &.{},
            try oneRef(prove, b, blk_label),
        ));
        steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }
    return steps;
}

/// Wrap the premise-wrapped `body_steps` (proving `inner_prop = prem0 -> … -> (s = t)`) in
/// nested `fix` blocks for the ∀ eigenvariables (outermost = eigen[0]), concluding each level
/// with `generalize`. With no eigenvariables the steps pass through unchanged (plain
/// simplify). The `fix` binder re-uses each eigenvariable's DISPLAY name — the same name the
/// cert body's delaborated fvars carry, so they re-resolve to the binder.
pub fn wrapSimplifyForall(prove: *Prove, b: *Accelerant.Builder, eigen: []const term.Node.Fvar, inner_prop: TermId, body_steps: []const ast.Step) Error![]const ast.Step {
    if (eigen.len == 0) return body_steps;
    var steps = body_steps;
    var prop = inner_prop; // the proposition inside the current fix (before this ∀ closes)
    var i: usize = eigen.len;
    while (i > 0) {
        i -= 1;
        const fv = eigen[i];
        // GUARD level (13e, a transferred `_quantified` goal): wrap the current steps in
        // `assume guard(v) { … }` + an discharge export INSIDE this fix — generalize
        // then derives the guarded `∀v; guard(v) -> …` (matching the relativized body), and
        // the discharge machinery finds `guard(v)` via the assume-source (2c).
        if (i < prove.quant_guards.len) if (prove.quant_guards[i]) |g| {
            const blk_label = try prove.freshNamed("assume-guard");
            var gsteps: std.ArrayList(ast.Step) = .empty;
            try gsteps.append(prove.ctx.arena, try b.assumeStep(blk_label, try b.termExpr(g), steps));
            prop = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = g, .rhs = prop } });
            try gsteps.append(prove.ctx.arena, try b.claimStep(try prove.freshNamed("export-guard"), try b.termExpr(prop), .by, try prove.internStr("discharge"), &.{}, try oneRef(prove, b, blk_label)));
            steps = try gsteps.toOwnedSlice(prove.ctx.arena);
        };
        const fix_label = try prove.freshNamed("fix");
        const bname = b.tok(try displayName(prove, fv.name));
        const fix_step: ast.Step = .{ .label = b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = b.sortTok(fv.sort), .steps = steps } } };
        // plain ∀-close: the guard (if any) is already folded into `prop` above.
        const closed = try prove.pool.close(prop, fv.name);
        prop = try prove.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, fix_step);
        try lvl.append(prove.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try prove.freshNamed("gen"),
            try b.termExpr(prop),
            .by,
            try prove.internStr("generalize"),
            &.{},
            try oneRef(prove, b, fix_label),
        ));
        steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }
    return steps;
}

/// Re-close `prop` over the peeled ∀ eigenvariables (outermost = eigen[0]), re-adding each
/// level's peeled relativization guard (`∀v; inH(v) -> …`) — the schema-body counterpart of
/// the kernel's guarded generalize (the fix binder re-resolves to the refined sort under the
/// model, so its generalize derives the guarded form; the stated body must match).
pub fn closeOverEigen(prove: *Prove, prop_in: TermId, eigen: []const term.Node.Fvar) Error!TermId {
    var prop = prop_in;
    var ei: usize = eigen.len;
    while (ei > 0) {
        ei -= 1;
        prop = try guardedQuant(prove, prop, eigen[ei], ei);
    }
    return prop;
}

/// One level of `closeOverEigen`: `∀v; [guard(v) ->] prop`.
fn guardedQuant(prove: *Prove, prop_in: TermId, fv: term.Node.Fvar, level: usize) Error!TermId {
    var prop = prop_in;
    if (level < prove.quant_guards.len) if (prove.quant_guards[level]) |g| {
        prop = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = g, .rhs = prop } });
    };
    const closed = try prove.pool.close(prop, fv.name);
    return prove.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
}

/// Abstract each distinct FREE fvar in `id` into a synthetic value param — the goal's
/// genuinely-free caller-local fvars (an enclosing `fix` at the call site). Returns the param
/// names/sorts (for the schema `params`), the original fvar names (for substitution), and the
/// caller-site arg exprs (each naming the fvar by its EXACT hygienic name, re-resolving through
/// the bind `fvarBinds` installs — never by display spelling, which two distinct eigenvariables
/// can share). A closed `id` yields no params (like a plain tautology).
pub const FvarAbstraction = struct {
    names: []const StrId,
    sorts: []const SortId,
    origs: []const StrId,
    args: []const *const ast.Expr,
};

/// The CALLER-SCOPE bindings for an abstraction's free fvars (`Synthetic.fvar_binds`): each
/// call-site arg names its fvar by the EXACT hygienic name (`n#6`), and this binds that name to
/// the very fvar. Keyed exactly, the binds shadow nothing an author can write (`#` never lexes),
/// so a caller `fix`-bound eigenvar keeps its binder (and a refined-sort binder its guard), and
/// one INHERITED from a schema-instance monomorphization (a lambda capturing the instantiating
/// proof's variable — no binder of its own here) resolves too — even when it DISPLAYS like a
/// local one (the schema's own `fix n` vs a captured `n`: the bug this replaces).
/// The GUARD ANTECEDENTS a painted synthetic owes for its abstracted params.
///
/// `abstractGoal` turns the goal's free caller-locals into schema params. Outside a guarded
/// model that loses nothing. Under one, the caller-local was a `fix a: H` whose guard
/// `good(a)` is available in the citing proof via `[by predicate]` — but the PARAM `p1` has
/// no enclosing guarded `fix`, so a leaked `good(recip(p1))` from a relativized lemma has no
/// way to be discharged inside the synthetic (`emitDischargeStep` source 2 cannot fire, and
/// source 3's closure recursion dead-ends on `good(p1)`).
///
/// So each param abstracted from a REFINED-sort binder contributes `good(p_i)` as an
/// antecedent of the synthetic's statement. `withGuardPremises` then discharges it at the
/// CALL SITE — where the original binder's guard really is in scope — because it treats
/// antecedents in excess of the supplied premise refs as guards to discharge.
///
/// Returns the guard atoms in param order, already phrased over the param fvars.
fn paramGuards(prove: *Prove, w: *const Walk, e: *Elab, abs: FvarAbstraction) Error![]const TermId {
    var out: std.ArrayList(TermId) = .empty;
    for (abs.origs, abs.names, abs.sorts) |orig, pname, psort| {
        const ident = w.findIdentByFvar(orig) orelse continue;
        const refined = refinedImageOf(prove, ident, psort);
        if (refined == InternPool.Index.none) continue;
        const quals = prove.ctx.interner.qualifiersOf(prove.ctx.arena, refined) catch return error.OutOfMemory;
        for (quals) |qual| {
            const pf = try prove.pool.add(.{ .fvar = .{ .name = pname, .sort = psort } });
            try out.append(prove.ctx.arena, try e.qualifierApp(qual, pf));
        }
    }
    return out.items;
}

/// The REFINED sort a param carries, if any — as seen from the space the synthetic will be
/// CHECKED in, not the space it is written in.
///
/// A binder whose own sort is refined (`fix h: Perm`) reports it directly. But when the
/// refinement is introduced by the MODEL (`Src: GoodTgt` with `GoodTgt = Tgt where good`),
/// the source binder is `fix n: Src` — unrefined — while the transferred proof's `apply_at`
/// steps nonetheless leak `good(p1)`. Reading only `ident.info.refined` missed exactly that
/// case and left the guard undischargeable (a param is in no `fix`'s scope, and closure
/// recursion dead-ends on a bare fvar), so a `simplify` whose rewrite set mentions a lemma
/// quantified over the mapped sort could not transfer at all.
///
/// Same test as `freeFvarParams` makes for its own abstraction: map the sort through the
/// active model and ask whether the IMAGE is refined.
fn refinedImageOf(prove: *Prove, ident: Walk.LocalIdent, psort: SortId) InternPool.Index {
    if (ident.info.refined != InternPool.Index.none) return ident.info.refined;
    if (prove.model == InternPool.Index.none or prove.model == .universe) return .none;
    const src_sort: InternPool.Index = @enumFromInt(@intFromEnum(psort));
    const image = prove.ctx.interner.applyModel(prove.model, src_sort);
    return if (prove.ctx.interner.isRefined(image)) image else .none;
}

pub fn fvarBinds(prove: *Prove, w: *const Walk, abs: FvarAbstraction) Error![]const Accelerant.Synthetic.FvarBind {
    _ = w;
    var binds: std.ArrayList(Accelerant.Synthetic.FvarBind) = .empty;
    for (abs.origs, abs.sorts) |orig, sort| {
        try binds.append(prove.ctx.arena, .{ .name = orig, .fvar = orig, .sort = sort });
    }
    return binds.items;
}

fn abstractFreeFvars(prove: *Prove, b: *Accelerant.Builder, terms: []const TermId, exclude: []const term.Node.Fvar) Error!FvarAbstraction {
    var seen: std.ArrayList(term.Node.Fvar) = .empty;
    for (terms) |t| try prove.collectFreeFvars(t, &seen);
    // drop excluded eigenvariables (they are `fix`-bound, not param-abstracted).
    var kept: std.ArrayList(term.Node.Fvar) = .empty;
    outer: for (seen.items) |fv| {
        for (exclude) |e| if (e.name == fv.name) continue :outer;
        try kept.append(prove.ctx.arena, fv);
    }
    seen = kept;
    const names = try prove.ctx.arena.alloc(StrId, seen.items.len);
    const sorts = try prove.ctx.arena.alloc(SortId, seen.items.len);
    const origs = try prove.ctx.arena.alloc(StrId, seen.items.len);
    const args = try prove.ctx.arena.alloc(*const ast.Expr, seen.items.len);
    for (seen.items, 0..) |fv, i| {
        names[i] = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "p{d}", .{i + 1}));
        sorts[i] = fv.sort;
        origs[i] = fv.name;
        args[i] = try b.nameExpr(fv.name); // the EXACT name → the bind `fvarBinds` installs
    }
    return .{ .names = names, .sorts = sorts, .origs = origs, .args = args };
}

/// The shared accelerant preamble: abstract the goal's free caller-local fvars (an enclosing
/// `fix` at the call site) into value params `p1, p2, …`, INCLUDING those shared with a local
/// premise's formula (so premise + goal + cert steps all speak the param names), while EXCLUDING
/// `eigen` (a quantified-variant's peeled ∀ vars, re-bound by the `fix` wrapper). Returns the
/// abstraction + the param-substituted goal. Every producer opens with this; callers then
/// `substFvarsToParams` their own (typed) premise formulae with the returned `abs`.
const AbstractedGoal = struct { abs: FvarAbstraction, goal_p: TermId };

pub fn abstractGoal(prove: *Prove, b: *Accelerant.Builder, goal: TermId, local_prem_formulae: []const TermId, eigen: []const term.Node.Fvar) Error!AbstractedGoal {
    var abs_terms: std.ArrayList(TermId) = .empty;
    try abs_terms.append(prove.ctx.arena, goal);
    try abs_terms.appendSlice(prove.ctx.arena, local_prem_formulae);
    const abs = try abstractFreeFvars(prove, b, abs_terms.items, eigen);
    return .{ .abs = abs, .goal_p = try substFvarsToParams(prove, goal, abs) };
}

/// Substitute each `origs[i]` fvar with a fresh param fvar named `names[i]` (same sort)
/// throughout `id`; the param fvar delaborates to the bare param name the schema Elab binds.
pub fn substFvarsToParams(prove: *Prove, id: TermId, abs: FvarAbstraction) Error!TermId {
    var out = id;
    for (abs.origs, abs.names, abs.sorts) |orig, name, sort| {
        const pf = try prove.pool.add(.{ .fvar = .{ .name = name, .sort = sort } });
        out = try prove.pool.substFvar(out, orig, pf);
    }
    return out;
}

/// The inverse of `substFvarsToParams` for DISPLAY: replace each param fvar `pK` with a
/// fresh fvar named after the original caller-local (display-trimmed), so a diagnostic shows
/// the name the author wrote instead of the synthetic `pK`.
pub fn unabstract(prove: *Prove, id: TermId, abs: FvarAbstraction) Error!TermId {
    var out = id;
    for (abs.names, abs.origs, abs.sorts) |name, orig, sort| {
        const disp = try prove.pool.add(.{ .fvar = .{ .name = try displayName(prove, orig), .sort = sort } });
        out = try prove.pool.substFvar(out, name, disp);
    }
    return out;
}

/// An fvar's display name (trimmed at the hygiene `#`), re-interned — the bare name the `fix`
/// binder + the cert's fvar references share, and what re-elaboration re-binds.
pub fn displayName(prove: *Prove, name: StrId) Error!StrId {
    const s = prove.ctx.interner.stringBytes(name);
    if (std.mem.indexOfScalar(u8, s, '#')) |k| {
        return prove.ctx.interner.internString(s[0..k]) catch error.OutOfMemory;
    }
    return name;
}

/// Resolve an accelerant ARGUMENT (a bare-name expr naming an equation lemma) into a prepared
/// rewrite rule + its cert cite — the arg-expr analogue of `prepareRule` (which takes a ref
/// token). A GLOBAL lemma is cited `[by axiom|theorem …]` inside the cert; a LOCAL step is
/// restated by hypothesis. (assoc/assoc_commut lemmas are demanded as `.fact` in the read
/// pass when they are bare names — see RefScan's accelerant arm.)
pub fn argRule(prove: *Prove, w: *const Walk, arg: *const ast.Expr) Error!PreparedRule {
    if (arg.* != .name) return prove.fail(Elab.exprLoc(arg), "argument must name an equation lemma", .{});
    return prepareRule(prove, w, arg.name);
}

/// The well-known AC triple + operator for a bare `assoc_commut`, chosen by the goal LHS's
/// head symbol NAME (`add` or `mul`). Null when the head is neither.
const WellKnownOp = struct { sym: term.SymId, assoc: []const u8, comm: []const u8, swap: []const u8 };

pub fn pickWellKnownOp(prove: *Prove, head: ?term.SymId) ?WellKnownOp {
    const h = head orelse return null;
    const name = prove.ctx.interner.stringBytes(prove.ctx.interner.nameOf(@enumFromInt(@intFromEnum(h))));
    if (std.mem.eql(u8, name, "add")) {
        return .{ .sym = h, .assoc = "addIsAssociative", .comm = "addIsCommutative", .swap = "addLeftSwap" };
    }
    if (std.mem.eql(u8, name, "mul")) {
        return .{ .sym = h, .assoc = "mulIsAssociative", .comm = "mulIsCommutative", .swap = "mulLeftSwap" };
    }
    return null;
}

/// Orient a (possibly ∀-prefixed) equation `formula` into an L→R rewrite rule, opening each
/// binder at a fresh pattern fvar. Null when the body is not an equation or a binder is
/// unused on the LHS (not a usable rewrite rule) — the extracted core of `prepareRule`.
pub fn orientRule(prove: *Prove, formula: TermId) Error!?rewrite.Rule {
    var binders: std.ArrayList(rewrite.Binder) = .empty;
    var body = formula;
    while (true) {
        const node = prove.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const fresh = try prove.freshNamed("p#");
        const fv = try prove.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
        body = try prove.pool.open(node.quant.body, fv);
        try binders.append(prove.ctx.arena, .{ .fvar = fresh, .sort = node.quant.sort });
    }
    const bn = prove.pool.get(body);
    if (bn != .eq) return null;
    for (binders.items) |bd| {
        if (!prove.pool.occursFree(bn.eq.lhs, bd.fvar)) return null;
    }
    return .{ .binders = binders.items, .lhs = bn.eq.lhs, .rhs = bn.eq.rhs, .formula = formula };
}

/// Peel a `forall …; s = t` goal's ∀ prefix into fresh eigenvariables (returned outermost
/// first) and return the body equation. Diagnoses a non-∀ / non-equation goal per `who`.
/// Is `f` a relativization guard over `fv` — a unary pred applied to exactly that fvar, or
/// an and-tree of such (the canonical multi-qualifier conjunction)?
fn isGuardOver(prove: *Prove, f: TermId, fv: StrId) bool {
    // a conjunction of `pred(fv)` guards, ALL over the same fvar — iterative AND-walk.
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), prove.ctx.gpa);
    const al = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(al);
    stack.append(al, f) catch return false;
    while (stack.pop()) |cur| {
        const n = prove.pool.get(cur);
        if (n == .bin and n.bin.op == .and_op) {
            stack.append(al, n.bin.lhs) catch return false;
            stack.append(al, n.bin.rhs) catch return false;
            continue;
        }
        if (n != .pred) return false;
        const args = prove.pool.args(n.pred);
        if (args.len != 1) return false;
        const a = prove.pool.get(args[0]);
        if (!(a == .fvar and a.fvar.name == fv)) return false;
    }
    return true;
}

const PeeledEq = struct { body: TermId, eigen: []const term.Node.Fvar };

pub fn peelForallEq(prove: *Prove, goal: TermId, c: ast.Step.Claim, comptime who: []const u8) Error!?PeeledEq {
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var guards: std.ArrayList(?TermId) = .empty;
    prove.quant_guards = &.{};
    var body = goal;
    while (true) {
        const node = prove.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = prove.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{ .name = try prove.freshNamed(if (hint.len > 0) hint else "q"), .sort = node.quant.sort };
        const fvt = try prove.pool.add(.{ .fvar = fv });
        body = try prove.pool.open(node.quant.body, fvt);
        try eigen.append(prove.ctx.arena, fv);
        // TRANSFER: the goal is RELATIVIZED — peel this binder's injected guard (`inH(v) ->`,
        // a unary pred over exactly the just-opened fvar), recording it for the re-closers.
        var guard: ?TermId = null;
        if (prove.model != InternPool.Index.none and prove.model != .universe) {
            const bn = prove.pool.get(body);
            if (bn == .bin and bn.bin.op == .implies and isGuardOver(prove, bn.bin.lhs, fv.name)) {
                guard = bn.bin.lhs;
                body = bn.bin.rhs;
            }
        }
        try guards.append(prove.ctx.arena, guard);
    }
    prove.quant_guards = guards.items;
    if (eigen.items.len == 0) {
        return prove.fail(c.rule.start, who ++ " expects a quantified goal; drop the '_quantified' suffix for a bare equation", .{});
    }
    if (prove.pool.get(body) != .eq) {
        return prove.fail(c.rule.start, who ++ ": the quantified body is not an equation", .{});
    }
    return .{ .body = body, .eigen = eigen.items };
}

/// The shared TAIL for both reordering accelerants (identical to `buildSimplify`'s tail): the
/// rules/cites + the two normalized `Result`s are already built (in PARAM space); emit the
/// EqCert join, wrap in the LOCAL-premise `assume`/`discharge` and ∀-eigenvariable
/// `fix`/`generalize` shells, and package the synthetic schema. `local_prems` are the
/// PreparedRules whose origin is a LOCAL step (restated by hypothesis + discharged at the call
/// site); the AC triple / assoc lemma when global is cited INSIDE the cert. `name_prefix` seeds
/// the schema hash name.
pub fn finishReorder(
    prove: *Prove,
    w: *const Walk,
    b: *Accelerant.Builder,
    c: ast.Step.Claim,
    comptime name_prefix: []const u8,
    s: TermId,
    t: TermId,
    rules: []const rewrite.Rule,
    cites: []const EqCert.RuleCite,
    rs: rewrite.Result,
    rt: rewrite.Result,
    abs: FvarAbstraction,
    eigen: []const term.Node.Fvar,
    local_prems: []const PreparedRule,
) Error!?Accelerant.Synthetic {
    // build the equation-cert AST proving `s = t`.
    var cert: EqCert = .{ .b = b, .pool = prove.pool, .rules = rules, .cites = cites, .fresh_ctx = prove, .freshFn = eqCertFresh };
    var body_steps: std.ArrayList(ast.Step) = .empty;
    _ = try cert.emitJoin(&body_steps, s, t, rs, rt);
    var steps: []const ast.Step = body_steps.items;

    // LOCAL premises → schema antecedents (restated by hypothesis, discharged at the call
    // site) in ref order; collect their (cite, param-substituted formula) for the wrappers.
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (local_prems) |p| {
        try local_cites.append(prove.ctx.arena, p.cite);
        try local_formulae.append(prove.ctx.arena, try substFvarsToParams(prove, p.formula, abs));
    }

    const eq_prop = try prove.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    const kept = try keptPremises(prove, local_cites.items, local_formulae.items, steps);
    const kept_refs = try keptRefTokens(prove, w, c.refs, local_cites.items, steps);
    const inner_prop = try impliesChain(prove, eq_prop, kept);
    steps = try wrapSimplifyPremises(prove, b, local_cites.items, local_formulae.items, eq_prop, steps);
    steps = try wrapSimplifyForall(prove, b, eigen, inner_prop, steps);

    // PARAM GUARDS (painted production under a guarded model): the params abstracted from
    // refined-sort caller binders owe their guards as the OUTERMOST antecedents — outside the
    // eigen `fix`es, since a param is not in any `fix`'s scope. Empty in the universe.
    var e_guard = prove.elab(w);
    const guards = try paramGuards(prove, w, &e_guard, abs);
    const eigen_prop = try closeOverEigen(prove, inner_prop, eigen);
    steps = try wrapParamGuards(prove, b, guards, eigen_prop, steps);

    // the schema body proposition = the guard-prefixed ∀-generalized `inner_prop`.
    const full_prop = try impliesChain(prove, eigen_prop, guards);
    const body_expr = try b.termExpr(full_prop);

    const params = try prove.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        pp.* = .{ .name = b.tok(name), .kind = .{ .value = b.sortTok(sort) } };
    }

    const hash = Schema.termHash(prove.ctx.interner, prove.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, name_prefix ++ "{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = kept_refs, // the cited premises, discharged at the call site
        .seen = b.seen.items,
        .fvar_binds = try fvarBinds(prove, w, abs),
    };
}

/// Concatenate two rewrite traces (short-circuiting an empty side).
pub fn concatTrace(prove: *Prove, a: []const rewrite.Rewrite, bb: []const rewrite.Rewrite) Error![]const rewrite.Rewrite {
    if (a.len == 0) return bb;
    if (bb.len == 0) return a;
    var out: std.ArrayList(rewrite.Rewrite) = .empty;
    try out.appendSlice(prove.ctx.arena, a);
    try out.appendSlice(prove.ctx.arena, bb);
    return out.items;
}

test "usedPremiseCites: a premise whose hypothesis the cert CITES is kept; an uncited one is dropped" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;
    var b: Accelerant.Builder = .{ .arena = arena, .interner = rig.ctx.interner, .pool = p.pool, .loc = 0 };
    const used_lbl = try internStrRt(p, "prem-used");
    const unused_lbl = try internStrRt(p, "prem-unused");
    const cites = [_]EqCert.RuleCite{
        .{ .local = .{ .hyp = used_lbl } },
        .{ .local = .{ .hyp = unused_lbl } },
    };
    // a cert body that cites ONLY the first premise's hypothesis label.
    const a = try rig.v("a");
    const refs = try arena.alloc(lexer.Token, 1);
    refs[0] = b.tok(used_lbl);
    const steps = [_]ast.Step{
        try b.claimStep(try internStrRt(p, "s1"), try b.termExpr(a), .by, try internStrRt(p, "rewrite"), &.{}, refs),
    };
    const mask = try usedPremiseCites(p, &cites, &steps);
    try testing.expect(mask[0]);
    try testing.expect(!mask[1]);
}

test "usedPremiseCites: a citation NESTED in an assume/fix block still counts" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;
    var b: Accelerant.Builder = .{ .arena = arena, .interner = rig.ctx.interner, .pool = p.pool, .loc = 0 };
    const hyp = try internStrRt(p, "prem-deep");
    const cites = [_]EqCert.RuleCite{.{ .local = .{ .hyp = hyp } }};
    const a = try rig.v("a");
    const refs = try arena.alloc(lexer.Token, 1);
    refs[0] = b.tok(hyp);
    const inner = [_]ast.Step{
        try b.claimStep(try internStrRt(p, "deep"), try b.termExpr(a), .by, try internStrRt(p, "rewrite"), &.{}, refs),
    };
    const outer = [_]ast.Step{
        try b.assumeStep(try internStrRt(p, "blk"), try b.termExpr(a), &inner),
    };
    const mask = try usedPremiseCites(p, &cites, &outer);
    try testing.expect(mask[0]);
}

test "usedPremiseCites: a GLOBAL cite is never a local antecedent; an empty cert cites nothing" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;
    const cites = [_]EqCert.RuleCite{
        .{ .local = .{ .hyp = try internStrRt(p, "prem-0") } },
        .{ .global = .{ .head = .{ .tag = .identifier, .start = 0, .end = 0 }, .is_axiom = false } },
    };
    const mask = try usedPremiseCites(p, &cites, &.{});
    try testing.expect(!mask[0]);
    try testing.expect(!mask[1]); // a global is never a local antecedent
}

test "fvarBinds: an abstraction's origs become caller-scope bindings keyed by their EXACT hygienic name (fvar, sort)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;
    // an abstraction over two inherited fvars: a hygienic `b#7` and a plain `x`.
    const mangled = try internStrRt(p, "b#7");
    const plain = try internStrRt(p, "x");
    const abs: FvarAbstraction = .{
        .names = &.{ try internStrRt(p, "p1"), try internStrRt(p, "p2") },
        .sorts = &.{ rig.int, rig.int },
        .origs = &.{ mangled, plain },
        .args = &.{},
    };
    var wk = Walk.init(arena, rig.ctx.interner, testrig.Rig.source, rig.ctx.sink);
    const binds = try fvarBinds(p, &wk, abs);
    try testing.expectEqual(@as(usize, 2), binds.len);
    // the DISPLAY name drops the hygiene mangle (so the call-site arg re-resolves by spelling)
    // while `fvar` keeps the identity.
    try testing.expectEqual(mangled, binds[0].name); // NOT the display `b`: two eigenvariables can display alike
    try testing.expectEqual(mangled, binds[0].fvar);
    try testing.expectEqual(rig.int, binds[0].sort);
    try testing.expectEqual(plain, binds[1].name);
    try testing.expectEqual(plain, binds[1].fvar);
}

test "fvarBinds: an abstraction with no free fvars yields no bindings" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const abs: FvarAbstraction = .{ .names = &.{}, .sorts = &.{}, .origs = &.{}, .args = &.{} };
    var wk = Walk.init(arena, rig.ctx.interner, testrig.Rig.source, rig.ctx.sink);
    const binds = try fvarBinds(rig.prove, &wk, abs);
    try testing.expectEqual(@as(usize, 0), binds.len);
}

/// A phase-2 `decide` for a tactic whose decision is still FUSED with its certificate
/// emission: run `certify` in ADMIT MODE, where the producer stops at its own accept/reject
/// point and sets `admit_ok` instead of building. The three-phase contract is honoured — the
/// scaffolding sees a decide/certify pair — while unfusing the producer is its own work. A
/// producer that reaches its decision accepts; one that fails has diagnosed its rejection; one
/// that returns without deciding is not admit-aware, which is a reject.
pub fn decideFused(tactic: anytype, prove: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    _ = e;
    const prev_mode = prove.admit_mode;
    const prev_ok = prove.admit_ok;
    prove.admit_mode = true;
    prove.admit_ok = false;
    defer {
        prove.admit_mode = prev_mode;
        prove.admit_ok = prev_ok;
    }
    _ = try tactic.certify(prove, w, goal, c);
    if (!prove.admit_ok) return prove.fail(c.rule.start, "'{s}' cannot admit this step under `--fast` (no fast acceptance)", .{prove.text(c.rule)});
}
