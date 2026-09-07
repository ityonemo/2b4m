//! EqCert — a SHARED equation-cert emitter: given a goal `s = t` plus the left/right
//! rewrite `Result`s from `simplify.normalize`, it emits `ast.Step`s that prove `s = t`
//! via a reflexivity + rewrite + symmetry chain the kernel re-checks. This is the AST port
//! of the eager `emitJoin`/`emitSideChain`/`emitInstance` (which emitted kernel steps).
//!
//! REUSABLE: every equational accelerant (simplify now; assoc / chain / polynomial next)
//! proves an equality by rewriting to a common normal form, so they all reduce to "here are
//! the two rewrite traces, emit the join". They differ only in how they PRODUCE the rules +
//! traces; this file owns the certificate shape. See memory `accelerants-emit-ast`.
//!
//! CITING A RULE INSTANCE (`emitInstance`): a rewrite by rule R at bindings β needs the
//! specific equation `R@β` as a proven step. The rule's ORIGIN is cited once (a GLOBAL
//! axiom/theorem by its fact word + token, or a LOCAL premise restated as a hypothesis in
//! the enclosing assume block), then a `forall_elim` per binder specializes it at β. The
//! result is the instance equation the `rewrite` step consumes.
//!
//! SCOPE: the emitted steps assume nothing about their surrounding block beyond the cited
//! rule origins being in scope (globals always are; a local rule's `RuleCite.local` names
//! the hypothesis-restatement label the producer placed in the wrapping assume block). All
//! fresh labels come from the caller's `Prove.freshNamed` via the `label` callback shape.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const Token = lexer.Token;
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const Accelerant = @import("Accelerant.zig");
const simplify = @import("simplify.zig");

/// How a rule's ORIGIN is cited inside the certificate.
pub const RuleCite = union(enum) {
    /// a GLOBAL fact: cite it with `[by axiom|theorem <token>]`. `axiom` selects the word.
    global: struct { head: Token, is_axiom: bool },
    /// a LOCAL premise: its formula is a schema antecedent restated by hypothesis under the
    /// label `hyp` in the wrapping assume block — cite that step directly (no fresh cite).
    local: struct { hyp: StrId },
};

/// The emitter state: the shared builder + pool, the rules (parallel to `cites`), and a
/// fresh-label source (the producer's `Prove.freshNamed`, type-erased through a closure).
b: *Accelerant.Builder,
pool: *term.Pool,
rules: []const simplify.Rule,
cites: []const RuleCite,
/// fresh-label callback: `ctx` is the producer (`*Prove`); returns an interned unique label.
fresh_ctx: *anyopaque,
freshFn: *const fn (ctx: *anyopaque, prefix: []const u8) anyerror!StrId,

const EqCert = @This();
pub const Error = error{OutOfMemory};

fn fresh(self: *EqCert, prefix: []const u8) Error!StrId {
    return self.freshFn(self.fresh_ctx, prefix) catch return error.OutOfMemory;
}

/// A single-label ref token slice on the builder arena.
fn oneRef(self: *EqCert, name: StrId) Error![]const Token {
    const r = try self.b.arena.alloc(Token, 1);
    r[0] = self.b.tok(name);
    return r;
}

/// Emit the citation + `forall_elim` chain specializing rule #`ri` at `bindings`; append the
/// steps to `block` and return the label of the step proving the instance equation. Mirrors
/// the eager `emitInstance`: cite the origin, then one `forall_elim` per binder.
fn emitInstance(self: *EqCert, block: *std.ArrayList(ast.Step), ri: usize, bindings: []const TermId) Error!StrId {
    const rule = self.rules[ri];
    // step 0: the rule's quantified formula, cited from its origin.
    var cur_label: StrId = undefined;
    switch (self.cites[ri]) {
        .global => |g| {
            cur_label = try self.fresh("simplify");
            // KIND-AGNOSTIC cite: the generated ProveTask resolves the fact + the kernel
            // picks its arm by the resolved kind — the cert never guesses axiom-vs-theorem.
            const wid = self.b.interner.internString("cite") catch return error.OutOfMemory;
            const refs = try self.b.arena.alloc(Token, 1);
            refs[0] = g.head; // the head token carries the stamped fact name
            try block.append(self.b.arena, try self.b.claimStep(cur_label, try self.b.termExpr(rule.formula), .by, wid, &.{}, refs));
        },
        .local => |l| cur_label = l.hyp, // already a proven step (restated hypothesis)
    }
    // one forall_elim per binder, opening the formula at the matched binding. Under a model
    // TRANSFER the cited lemma is RELATIVIZED — `∀a; inH(a) -> ∀b; …` — so a guard `->` sits
    // between binders; SKIP it (advance past the antecedent) so the next `∀` is found. The
    // forall_elim step is emitted claiming the guard-STRIPPED opened form; the instance ProveTask
    // (which runs under the model) discharges the leaked guard via its forall_elim machinery.
    var cur_formula = rule.formula;
    const forall_elim = self.b.interner.internString("forall_elim") catch return error.OutOfMemory;
    for (rule.binders, bindings) |_, val| {
        while (true) {
            const n = self.pool.get(cur_formula);
            if (n == .bin and n.bin.op == .implies) {
                cur_formula = n.bin.rhs;
                continue;
            }
            break;
        }
        const q = self.pool.get(cur_formula).quant;
        var opened = try self.pool.open(q.body, val);
        // strip any guard(s) leaked immediately after opening (before the equation / next binder).
        while (true) {
            const n = self.pool.get(opened);
            if (n == .bin and n.bin.op == .implies) {
                opened = n.bin.rhs;
                continue;
            }
            break;
        }
        const lbl = try self.fresh("simplify");
        const arg1 = try self.b.arena.alloc(*const ast.Expr, 1);
        arg1[0] = try self.b.termExpr(val);
        try block.append(self.b.arena, try self.b.claimStep(lbl, try self.b.termExpr(opened), .by, forall_elim, arg1, try self.oneRef(cur_label)));
        cur_formula = opened;
        cur_label = lbl;
    }
    return cur_label;
}

/// Emit `eq(start, start)` by reflexivity, then one `rewrite` step per trace entry; append to
/// `block` and return the label proving `eq(start, <after last entry>)`. `trace` non-empty.
fn emitSideChain(self: *EqCert, block: *std.ArrayList(ast.Step), start: TermId, trace: []const simplify.Rewrite) Error!StrId {
    const refl_formula = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = start } });
    const reflexivity = self.b.interner.internString("reflexivity") catch return error.OutOfMemory;
    const rewrite = self.b.interner.internString("rewrite") catch return error.OutOfMemory;
    var prev = try self.fresh("simplify");
    try block.append(self.b.arena, try self.b.claimStep(prev, try self.b.termExpr(refl_formula), .by, reflexivity, &.{}, &.{}));
    for (trace) |rw| {
        const inst = try self.emitInstance(block, rw.rule_idx, rw.bindings);
        const next_formula = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = rw.after } });
        const lbl = try self.fresh("simplify");
        // `[by rewrite <inst-eq> <target>]` — kernel rewrites all occurrences of the eq's lhs.
        const refs = try self.b.arena.alloc(Token, 2);
        refs[0] = self.b.tok(inst);
        refs[1] = self.b.tok(prev);
        try block.append(self.b.arena, try self.b.claimStep(lbl, try self.b.termExpr(next_formula), .by, rewrite, &.{}, refs));
        prev = lbl;
    }
    return prev;
}

/// A reflexivity step proving `t = t`; append it, return its label. (Used when a side has an
/// empty trace — it is already the shared normal form.)
fn emitRefl(self: *EqCert, block: *std.ArrayList(ast.Step), t: TermId) Error!StrId {
    const refl_formula = try self.pool.add(.{ .eq = .{ .lhs = t, .rhs = t } });
    const reflexivity = self.b.interner.internString("reflexivity") catch return error.OutOfMemory;
    const lbl = try self.fresh("simplify");
    try block.append(self.b.arena, try self.b.claimStep(lbl, try self.b.termExpr(refl_formula), .by, reflexivity, &.{}, &.{}));
    return lbl;
}

/// Emit the full join proving `s = t` into `block` and return the label of the final step
/// (whose formula is exactly `s = t`). Ported from the eager `emitJoin`:
///   - both sides normalize to a shared NF; the s-chain proves `s = NF`;
///   - the t-chain proves `t = NF`, flipped by `symmetry` to `NF = t`;
///   - a final `rewrite` composes `s = NF` with `NF = t` into `s = t`.
/// The degenerate cases (t already the NF, or s already the NF) collapse the flip/compose.
pub fn emitJoin(self: *EqCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, rs: simplify.Result, rt: simplify.Result) Error!StrId {
    const symmetry = self.b.interner.internString("symmetry") catch return error.OutOfMemory;
    const rewrite = self.b.interner.internString("rewrite") catch return error.OutOfMemory;

    // `s = NF` (reflexivity if s is already the NF).
    const s_end = if (rs.trace.len > 0)
        try self.emitSideChain(block, s, rs.trace)
    else
        try self.emitRefl(block, s);

    if (rt.trace.len == 0) {
        // t IS the shared NF: `s = NF` already equals `s = t`. Rename by an identity rewrite
        // is unnecessary — the s-chain's final formula is literally `s = t`.
        return s_end;
    }

    // t moves: prove `t = NF`, flip to `NF = t`, then rewrite `s = NF` by `NF = t` → `s = t`.
    const t_end = try self.emitSideChain(block, t, rt.trace);
    const flipped = try self.pool.add(.{ .eq = .{ .lhs = rt.nf, .rhs = t } });
    const sym_lbl = try self.fresh("simplify");
    try block.append(self.b.arena, try self.b.claimStep(sym_lbl, try self.b.termExpr(flipped), .by, symmetry, &.{}, try self.oneRef(t_end)));

    const goal_eq = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    const join_lbl = try self.fresh("simplify");
    const refs = try self.b.arena.alloc(Token, 2);
    refs[0] = self.b.tok(sym_lbl); // the equation `NF = t`
    refs[1] = self.b.tok(s_end); // the target `s = NF`
    try block.append(self.b.arena, try self.b.claimStep(join_lbl, try self.b.termExpr(goal_eq), .by, rewrite, &.{}, refs));
    return join_lbl;
}
