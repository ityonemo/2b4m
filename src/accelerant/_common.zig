//! Shared closure plumbing for the certificate-emitting accelerants.
//!
//! In strict mode an accelerant wraps its kernel-step certificate into a
//! CONTEXT-FREE synthetic theorem — one that cites nothing from the environment.
//! `generate` builds that theorem and the citation that specializes it back:
//!
//!     <tactic>$n :  ∀ <eigenvars> ;  P₁ -> … -> Pₖ -> <goal>
//!
//! The premises `Pᵢ` are the refs the accelerant chooses to close (each ref it
//! was handed — a global axiom/theorem OR a caller-local hypothesis — becomes a
//! premise; pass `&.{}` to close nothing but eigenvariables). The `∀`-prefix is
//! the in-scope eigenvariables the goal or any premise mentions. The proof is
//! `fix <eigenvars> { assume P₁ { … assume Pₖ { <certificate> } } }`, closed by
//! an implies_intro chain then a forall_intro chain; each premise is surfaced as
//! a labeled `hypothesis` step (under the ref's own name) so the certificate
//! resolves it as a local rule. The citation reverses the closure: `theorem_ref`
//! + `forall_elim(<caller eigenvars>)` + one `modus_ponens` per premise,
//! discharged with the SAME ref the accelerant was handed. The whole synthetic
//! theorem is kernel-checked in `wrapAsTheorem` (the soundness anchor).
//!
//! The accelerant supplies its policy: the `tactic` name (used for the mangled
//! `<tactic>$n` theorem name), the `refs` to close, and a `body` context whose
//! `emit(self, low, block, body_goal) !Justification` proves the fresh-eigenvar
//! `body_goal` (a bare goal, or a still-quantified one it peels itself). Naming
//! and which-refs-to-close stay with the accelerant; only this plumbing is
//! shared. `model` does NOT use this (it transfers a closed statement, a
//! different shape).

const std = @import("std");
const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;
const StatementId = elaborate.StatementId;
const StrId = @import("../InternPool.zig").StrId;

const kernel = @import("../kernel.zig");
const lexer = @import("../lexer.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

/// One cited fact, classified for closure: its formula (with the CALLER's
/// eigenvars), how to discharge it at the cite (global → axiom/theorem ref;
/// local → the caller's step), and its ref token (whose name labels the
/// surfaced hypothesis step inside the proof so the certificate resolves it).
const Premise = struct {
    name: StrId,
    formula: TermId,
    target: Elaborator.RefTarget,
};

/// Build + cite the context-free synthetic theorem. `body` is any value with a
/// `pub fn emit(*@This(), *Elaborator, *Lowering, kernel.BlockId, TermId)
/// ElabError!?kernel.Justification` proving the fresh-eigenvar body goal.
///
/// Returns null when the body-emit DECLINES (returns null) — e.g. tautology's
/// certificate replay runs out of budget. On decline nothing is registered and
/// the caller's `low` is untouched; the accelerant should fall back to the
/// accelerated verdict. A body-emit that always succeeds never yields null.
pub fn generate(
    self: *Elaborator,
    low: *Lowering,
    block_id: kernel.BlockId,
    loc: u32,
    tactic: []const u8,
    goal: TermId,
    refs: []const lexer.Token,
    body: anytype,
) ElabError!?kernel.Justification {
    // classify every ref (in cite order) — each becomes a premise.
    var premises: std.ArrayList(Premise) = .empty;
    for (refs) |ref| {
        const t = try self.refTarget(low, block_id, ref);
        try premises.append(self.arena, .{
            .name = try self.internTok(ref),
            .formula = switch (t) {
                .local_step => |s| s.formula,
                .global => |g| g.formula,
            },
            .target = t,
        });
    }

    // eigenvariables the goal OR any premise mentions (scope order,
    // outermost-first). `.name` is the kernel fvar identity (keys close/
    // occursFree); `hint` keeps the user-facing name for display.
    var vars: std.ArrayList(term.Node.Fvar) = .empty;
    var hints: std.ArrayList(StrId) = .empty;
    for (self.scope.items) |entry| {
        var mentioned = self.pool.occursFree(goal, entry.fvar);
        if (!mentioned) for (premises.items) |p| {
            if (self.pool.occursFree(p.formula, entry.fvar)) {
                mentioned = true;
                break;
            }
        };
        if (mentioned) {
            try vars.append(self.arena, .{ .name = entry.fvar, .sort = entry.sort });
            try hints.append(self.arena, entry.name);
        }
    }

    // chain `P₁ -> … -> Pₖ -> goal` (fold from the right so cite order reads
    // outermost premise first), then ∀-close over the eigenvariables.
    var chain = goal;
    {
        var i = premises.items.len;
        while (i > 0) {
            i -= 1;
            chain = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = premises.items[i].formula, .rhs = chain } });
        }
    }
    var closed = chain;
    {
        var i = vars.items.len;
        while (i > 0) {
            i -= 1;
            const b = try self.pool.close(closed, vars.items[i].name);
            closed = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = vars.items[i].sort, .hint = hints.items[i], .body = b } });
        }
    }

    // ---- build the synthetic theorem's proof in a FRESH Lowering ----
    var plow: Lowering = .{};
    try plow.blocks.append(self.arena, .{
        .parent = null,
        .label = try self.interner.internString("proof"),
        .kind = .root,
        .first_step = 0,
        .last_step = 0,
    });
    const root: kernel.BlockId = @enumFromInt(0);

    // peel EXACTLY the closure-added eigenvariable prefix (`vars.len` binders),
    // one fix block each — the goal's OWN leading binders stay in the body for
    // the body-emit to handle. `u.body` is the fresh-eigenvar implication chain.
    const u = try self.peelUniversalN(closed, tactic, vars.items.len);
    const opened = try self.openUniversal(&plow, root, u);

    // one assume block per premise, surfacing each as a labeled hypothesis step
    // (under the ref's own name) so the certificate resolves it as a local rule.
    var parent = opened.innermost;
    var assume_blocks: std.ArrayList(kernel.BlockId) = .empty;
    var body_goal = u.body;
    for (premises.items) |p| {
        const node = self.pool.get(body_goal);
        std.debug.assert(node == .bin and node.bin.op == .implies);
        const ante = node.bin.lhs;
        const ab = try self.newBlock(&plow, try self.freshNamed("assume"), parent, .{ .assume = ante });
        _ = try registerLabeledHypothesis(self, &plow, ab, p.name, ante, loc);
        try assume_blocks.append(self.arena, ab);
        parent = ab;
        body_goal = node.bin.rhs;
    }

    // Build the certificate for `body_goal` (citing each premise via the local
    // labels surfaced above). When there ARE premises we emit the concluding
    // step into the innermost assume block so the implies_intro chain can
    // reference it; when there are none, closeUniversal emits the body itself
    // (from `body_just`) — emitting here too would duplicate.
    var body_mut = body;
    const cert_just = (try body_mut.emit(self, &plow, parent, body_goal)) orelse
        // the body-emit declined (e.g. tautology's replay ran out of budget) —
        // nothing was registered, `plow` is discarded, the caller falls back.
        return null;

    // DECIDE vs GENERATE. The body-emit above did the validity work in `plow`
    // (a false goal already failed inside it — with a located error). In --fast
    // (`!certify_arithmetic`) we stop here: DISCARD the constructed certificate,
    // record the accelerated taint, and return the verdict the kernel accepts on
    // trust. No synthetic theorem is registered, nothing is kernel-checked, and
    // the caller's `low` is untouched (everything went into the throwaway `plow`).
    // In strict mode we continue: wrap the certificate into a kernel-checked
    // synthetic theorem and cite it.
    if (!self.verify.certify_arithmetic) {
        const taint = try self.interner.internString(tactic);
        try self.recordAccelerated(taint, loc);
        return .{ .accelerated = taint };
    }

    if (assume_blocks.items.len > 0) {
        _ = try self.emitStep(&plow, parent, loc, body_goal, cert_just);
    }

    // close the assume blocks with an implies_intro chain, innermost-first: each
    // implies_intro is emitted into its PARENT block and proves `Pᵢ -> <rest>`.
    // The OUTERMOST implies_intro (proving `u.body = P₁ -> … -> goal`) is not
    // emitted here — it is handed to closeUniversal as the fix-body justification
    // so it lands in the innermost fix block. `body_just` proves `u.body`.
    var body_just = cert_just;
    if (assume_blocks.items.len > 0) {
        var conclusion = body_goal;
        var bi = assume_blocks.items.len;
        while (bi > 0) {
            bi -= 1;
            const ab = assume_blocks.items[bi];
            self.closeBlock(&plow, ab);
            const assume_formula = plow.blocks.items[@intFromEnum(ab)].kind.assume;
            conclusion = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = assume_formula, .rhs = conclusion } });
            const ii: kernel.Justification = .{ .implies_intro = .{ .id = ab, .loc = loc } };
            if (bi == 0) {
                body_just = ii; // outermost — hand to closeUniversal
            } else {
                _ = try self.emitStep(&plow, assume_blocks.items[bi - 1], loc, conclusion, ii);
            }
        }
    }

    // close the fix blocks with forall_intro (closeUniversal emits the u.body
    // step into the innermost fix block and the forall_intro chain), then emit
    // the concluding root step proving `closed`.
    const proof_just = try self.closeUniversal(&plow, loc, u, opened.blocks, body_just);
    _ = try self.emitStep(&plow, root, loc, closed, proof_just);
    plow.blocks.items[0].last_step = @intCast(plow.steps.items.len);

    // wrap + kernel-check as a suppressed synthetic theorem.
    const name = try mangledName(self, tactic);
    const accel = try self.arena.dupe(StrId, self.accelerated_used.items);
    const holes = try self.arena.dupe(StrId, self.holes_used.items);
    const on_fail = try std.fmt.allocPrint(self.arena, "{s} certificate does not kernel-check", .{tactic});
    const thm = try self.wrapAsTheorem(name, closed, plow.steps.items, plow.blocks.items, accel, holes, loc, on_fail);

    // ---- cite it back in the caller: forall_elim(eigenvars) then a
    // modus_ponens per premise (discharge with the original refs) ----
    return try emitCitation(self, low, block_id, loc, thm, closed, vars.items, premises.items);
}

/// Surface `formula` as a `hypothesis` step in `block` (an assume block) and
/// register it under `name` so the certificate's ref lookups resolve it.
fn registerLabeledHypothesis(self: *Elaborator, low: *Lowering, block: kernel.BlockId, name: StrId, formula: TermId, loc: u32) ElabError!kernel.SRef {
    const id: kernel.StepId = @enumFromInt(low.steps.items.len);
    try low.steps.append(self.arena, .{
        .formula = formula,
        .just = .{ .hypothesis = .{ .id = block, .loc = loc } },
        .block = block,
        .label = name,
        .loc = loc,
    });
    try low.labels.put(self.arena, name, .{ .step = id });
    return .{ .id = id, .loc = loc };
}

/// Cite the synthetic theorem in the caller: `theorem_ref`, `forall_elim` per
/// eigenvariable (caller's real fvars), then `modus_ponens` per premise
/// (discharged by re-resolving each ref exactly as the dispatch would). Each
/// operation but the LAST is emitted as its own step; the last is RETURNED as
/// this step's justification (the caller wraps it into the goal step).
fn emitCitation(
    self: *Elaborator,
    low: *Lowering,
    block_id: kernel.BlockId,
    loc: u32,
    thm: StatementId,
    closed: TermId,
    vars: []const term.Node.Fvar,
    premises: []const Premise,
) ElabError!kernel.Justification {
    var pending: kernel.Justification = .{ .theorem_ref = .{ .stmt = thm, .loc = loc } };
    var pending_formula = closed;
    for (vars) |v| {
        const prev = try self.emitStep(low, block_id, loc, pending_formula, pending);
        const q = self.pool.get(pending_formula).quant;
        const val = try self.pool.add(.{ .fvar = v });
        pending_formula = try self.pool.open(q.body, val);
        pending = .{ .forall_elim = .{ .step = prev, .with = val, .with_loc = loc } };
    }
    for (premises) |p| {
        const prev = try self.emitStep(low, block_id, loc, pending_formula, pending);
        const node = self.pool.get(pending_formula);
        std.debug.assert(node == .bin and node.bin.op == .implies);
        const ante_ref = try dischargeRef(self, low, block_id, loc, p);
        pending_formula = node.bin.rhs;
        pending = .{ .modus_ponens = .{ .implication = prev, .antecedent = ante_ref } };
    }
    return pending;
}

/// Produce the step reference discharging a premise: a caller-local step is
/// cited directly; a global is materialized as an axiom_ref/theorem_ref step.
fn dischargeRef(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, loc: u32, p: Premise) ElabError!kernel.SRef {
    return switch (p.target) {
        .local_step => |s| s.sref,
        .global => |g| blk: {
            const just: kernel.Justification = if (g.is_theorem)
                .{ .theorem_ref = .{ .stmt = g.stmt, .loc = loc } }
            else
                .{ .axiom_ref = .{ .stmt = g.stmt, .loc = loc } };
            break :blk try self.emitStep(low, block_id, loc, g.formula, just);
        },
    };
}

/// `<tactic>$<n>` — a collision-free mangled name (`$` is unlexable, `n` a
/// per-file counter). Accelerants that mangle differently (e.g. `model`) do not
/// use this.
fn mangledName(self: *Elaborator, tactic: []const u8) ElabError!StrId {
    self.fresh_counter += 1;
    const text_ = std.fmt.allocPrint(self.arena, "{s}${d}", .{ tactic, self.fresh_counter }) catch return error.OutOfMemory;
    return self.interner.internString(text_) catch return error.OutOfMemory;
}
