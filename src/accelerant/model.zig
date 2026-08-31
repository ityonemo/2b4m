//! The `model` accelerant (structure-reuse "X is-a Y"): transfers a source
//! theorem to the goal through a declared model's interpretation. Two modes
//! (MODEL-DESIGN.md): `--fast` trusts the transfer and taints `accelerated:
//! model`; the default (strict) MATERIALIZES the remapped source proof as a
//! synthetic kernel-checked theorem `Model$thm` (recursively for its cited
//! children), then cites it via `theorem_ref` — kernel-checked, untainted.
//! Split out of the elaborate monolith. The `models` field and the `model`
//! DECLARATION handler (`elaborateModel`) stay in elaborate.zig (decl-side);
//! the `Model`/`StmtPair` types stay there too (the field names them) and this
//! module references them as `Elaborator.Model`. The shared synthetic-theorem
//! primitives (begin/finish/wrapAsTheorem) stay as `pub` methods on Elaborator.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const Model = Elaborator.Model;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const StatementId = @import("../env.zig").StatementId;

/// Two modes (MODEL-DESIGN.md):
///  - `--fast` (`!certify_arithmetic`): trust the transfer — taint
///    `accelerated: model`, check nothing about the source proof.
///  - default (strict): MATERIALIZE the source proof remapped as a synthetic
///    checked theorem `Model$thm` (recursively for its cited children), then
///    cite it via `theorem_ref` — kernel-checked, untainted.
/// Uniform accelerant signature (the registry calls every accelerant the same
/// way); `model` ignores `low`/`block_id` — it cites its materialized synthetic
/// theorem, splicing no steps into the caller's block.
pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    _ = low;
    _ = block_id;
    const loc = c.rule.start;
    const inst_tok = c.schema orelse
        return self.fail(loc, "model requires an instance: model(<Instance>) <source.theorem>", .{});
    if (c.refs.len != 1) {
        return self.fail(loc, "model(<Instance>) cites exactly one source theorem; got {d}", .{c.refs.len});
    }
    const inst_name = try self.internTok(inst_tok);
    const model = self.models.getPtr(inst_name) orelse
        return self.fail(inst_tok.start, "unknown model '{s}'", .{self.text(inst_tok)});

    const stmt_id = try self.resolveStatementRef(c.refs[0]);

    // A SCHEMA source (e.g. `peano.induction`) is transferred like a mapped
    // AXIOM: it has no ground formula to remap-and-α-check here (its body carries
    // an unbound predicate param), so it MUST be discharged by an explicit model
    // mapping (`source.induction: localSchema`) whose target was α-checked against
    // the guard-relativized remap at the model DECL site. Resolve straight through
    // stmt_map to that discharge — in both strict and --fast mode. The kernel then
    // checks the discharge's schema statement α-matches the goal.
    if (self.env.statements.items[@intFromEnum(stmt_id)] == .schema) {
        const discharge = blk: {
            for (model.stmt_map) |p| {
                if (p.from == stmt_id) break :blk p.to;
            }
            return self.fail(c.refs[0].start, "model does not discharge the schema '{s}'; add a mapping `{s}: <local schema>` to the model", .{ self.text(c.refs[0]), self.text(c.refs[0]) });
        };
        return schemaDischarge(self, discharge, goal, loc);
    }

    const src_formula = switch (self.env.statements.items[@intFromEnum(stmt_id)]) {
        .axiom => |f| f.formula,
        .theorem => |f| f.formula,
        .schema => unreachable, // handled above
    };
    const transferred = self.pool.remapFormula(src_formula, model.remap) catch return error.OutOfMemory;
    if (!self.pool.alphaEq(transferred, goal)) {
        return self.fail(loc, "model transfer of '{s}' does not match the goal:\n  transferred: {s}\n  goal:        {s}", .{
            self.text(c.refs[0]),
            try self.renderTerm(transferred),
            try self.renderTerm(goal),
        });
    }

    if (!self.verify.certify_arithmetic) {
        // --fast: trust the transfer wholesale.
        const name = self.interner.internString("model") catch return error.OutOfMemory;
        try self.recordAccelerated(name, loc);
        return .{ .accelerated = name };
    }

    // DIRECT-MAPPED source: if the cited fact is itself in the model's mapping
    // (`group.opAssoc: <discharge>`), its discharge IS the mapped target — cite it
    // directly, exactly as remapCitation does when the fact is reached transitively
    // inside a proof. This is the ONLY way to transfer a mapped AXIOM (which has no
    // proof to materialize) — e.g. `[by model(HGroup) group.opAssoc]` in the K<H<G
    // stack. The kernel then checks the discharge's formula α-matches the goal.
    for (model.stmt_map) |p| {
        if (p.from == stmt_id) return citeStatement(self, p.to, loc);
    }

    // strict: materialize the remapped source proof and cite it. Inherit the
    // materialized theorem's provenance (if the source proof leaned on an
    // accelerated tactic or a hole, the transfer discloses it transitively),
    // exactly like `fallback`.
    const mat_id = try materializeModelTheorem(self, model, stmt_id, c.refs[0].start);
    const mat = self.env.statements.items[@intFromEnum(mat_id)].theorem;
    try self.inheritAccelerated(mat.accelerated);
    try self.inheritHoles(mat.holes);
    return .{ .theorem_ref = .{ .stmt = mat_id, .loc = loc } };
}

/// Public entry for a `<model>@<projected>` MAPPING VALUE (Level 1): materialize
/// `source` (a theorem in `model`'s source theory) transferred through `model`, and
/// return the synthetic statement — the obligation's discharge. Thin wrapper over
/// materializeModelTheorem so the elaborator (decl-side) can reach it.
pub fn materializeThrough(self: *Elaborator, model: *Model, source: StatementId, loc: u32) ElabError!StatementId {
    return materializeModelTheorem(self, model, source, loc);
}

/// Materialize a source theorem's proof, remapped through `model`, as a
/// synthetic kernel-checked theorem `Model$thm` in the current file — then
/// return its StatementId. Recursively materializes any source theorem the
/// proof cites (memoized per model, so a diamond emits once). Source axioms
/// cited by the proof are repointed through the model's `stmt_map` to their
/// discharging local facts; an unmapped axiom is an undischarged obligation.
fn materializeModelTheorem(self: *Elaborator, model: *Model, source: StatementId, loc: u32) ElabError!StatementId {
    if (model.materialized.get(source)) |existing| return existing;

    // DIRECT-MAPPED source: the model explicitly maps this fact to a discharge —
    // its `stmt_map` target IS the materialization. This is the ONLY route for a
    // mapped AXIOM (no proof to remap), and it is what lets a `@`-projection value
    // `subgroup.grpAssoc: HGroup@group.opAssoc` resolve `group.opAssoc` (an axiom)
    // through HGroup to its H-relativized discharge. Reached transitively inside a
    // proof, remapCitation already does this; here we honor it at the entry too.
    for (model.stmt_map) |p| {
        if (p.from == source) return p.to;
    }

    // An ACCELERANT SYNTHETIC (`simplify$n`, `chain$n`, …) whose proof is
    // CONTEXT-FREE w.r.t. the interpretation — it discharges every premise from an
    // ASSUME hypothesis and cites no model-AFFECTED environment fact — is a bare
    // equational lemma `∀ eigenvars; premises -> s = t` proved purely by rewriting.
    // It quantifies over carrier ELEMENTS, never over membership, so under a GUARDED
    // model it must be transferred UNGUARDED (a plain 1:1 remap over the target base
    // carrier), NOT relativized: relativizing would inject `guard(k) ->` obligations
    // its citation (a bare forall_elim + modus_ponens, emitted in source space) does
    // not discharge — the eigenvariable-escape that made a `simplify`-under-`fix`
    // proof untransferable. Sound because the model's mapped premises hold on the
    // whole target carrier (a discharge for `∀b; plus(Z,b)=b` is unconditional).
    //
    // A synthetic that CITES a model-affected axiom/theorem directly (e.g. `assoc`
    // cites `opAssoc`, which a subgroup model relativizes to `∀x; inK(x) -> …`) is
    // NOT context-free: guard-stripping it would mismatch that relativized citation.
    // Such a synthetic stays on the ordinary GUARDED path (which weakens the cited
    // axiom and discharges each forall_elim), exactly like a non-synthetic theorem.
    const strip_guard = model.remap.guard != null and isContextFreeSynthetic(self, model, source);
    if (model.remap.guard != null and !strip_guard) return materializeGuardedModelTheorem(self, model, source, loc);
    const saved_guard = model.remap.guard;
    if (strip_guard) model.remap.guard = null;
    defer model.remap.guard = saved_guard;

    const stmt = self.env.statements.items[@intFromEnum(source)];
    const fact = switch (stmt) {
        .theorem => |t| t,
        .axiom => return self.fail(loc, "model materialization reached an axiom without a mapping; add it to the model", .{}),
        .schema => return self.fail(loc, "model cannot materialize a schema", .{}),
    };
    const proof = fact.proof orelse
        return self.fail(loc, "model cannot materialize '{s}': its proof was not retained (trusted import?)", .{self.interner.stringBytes(fact.name)});

    // mangled name `Model$sourcename`, bound in the current file. `$` is not
    // a lexable identifier char, so it cannot collide with a user name.
    const mangled = try mangledModelName(self, model.name, fact.name);
    const remapped_formula = self.pool.remapFormula(fact.formula, model.remap) catch return error.OutOfMemory;

    // register (unproven) FIRST so a self/mutual citation resolves; memoize
    // before recursing so a cycle terminates.
    const mat_id = try self.beginSyntheticTheorem(mangled, remapped_formula, loc);
    try model.materialized.put(self.arena, source, mat_id);

    // remap each step's formula + justification ids.
    const new_steps = try self.arena.alloc(kernel.Step, proof.steps.len);
    for (proof.steps, new_steps) |s, *out| {
        out.* = .{
            .formula = self.pool.remapFormula(s.formula, model.remap) catch return error.OutOfMemory,
            .just = try remapJustification(self, model, s.just, loc),
            .block = s.block,
            .label = s.label,
            .loc = loc,
        };
    }

    // remap each block's sort-bearing data: a `fix` eigenvariable's sort, an
    // `assume` formula, an `unpack` witness sort. (SRef/BRef indices and the
    // step ranges are structural — unchanged.)
    const new_blocks = try self.arena.alloc(kernel.Block, proof.blocks.len);
    for (proof.blocks, new_blocks) |b, *out| {
        out.* = b;
        out.kind = switch (b.kind) {
            .root => .root,
            .assume => |f| .{ .assume = self.pool.remapFormula(f, model.remap) catch return error.OutOfMemory },
            .fix => |f| .{ .fix = .{
                .v = .{ .name = f.v.name, .sort = model.remap.sort(f.v.sort) },
                .guard = if (f.guard) |g| self.pool.remapFormula(g, model.remap) catch return error.OutOfMemory else null,
            } },
            .unpack => |u| .{ .unpack = .{
                .v = .{ .name = u.v.name, .sort = model.remap.sort(u.v.sort) },
                .source = u.source,
            } },
        };
    }

    // kernel-check the remapped proof, mark proven, retain it, and inherit the
    // source proof's provenance (accelerated/holes) — retention lets an OUTER
    // model re-materialize through this synthetic theorem (the multi-level
    // chain ℤ models ring models group).
    const on_fail = try std.fmt.allocPrint(self.arena, "model transfer of '{s}' does not kernel-check under the interpretation (an obligation is undischarged?)", .{self.interner.stringBytes(fact.name)});
    try self.finishSyntheticTheorem(mat_id, new_steps, new_blocks, fact.accelerated, fact.holes, loc, on_fail);
    return mat_id;
}

/// True if `source` is an accelerant SYNTHETIC whose proof is CONTEXT-FREE w.r.t.
/// this model's interpretation: it is `.synthetic`, and no step in its proof cites
/// an axiom/theorem whose formula the model's remap AFFECTS. Such a synthetic (e.g.
/// `simplify$n`, which discharges its premises from ASSUME hypotheses) transfers
/// UNGUARDED. A synthetic that cites a model-affected fact directly (e.g. `assoc$n`
/// citing `opAssoc`, relativized by a subgroup model) is NOT context-free and stays
/// on the guarded path — stripping its guard would mismatch that relativized cite.
fn isContextFreeSynthetic(self: *Elaborator, model: *Model, source: StatementId) bool {
    const fact = switch (self.env.statements.items[@intFromEnum(source)]) {
        .theorem => |t| t,
        else => return false,
    };
    if (!fact.synthetic) return false;
    const proof = fact.proof orelse return false;
    for (proof.steps) |s| {
        const cited: StatementId = switch (s.just) {
            .axiom_ref => |r| r.stmt,
            .theorem_ref => |r| r.stmt,
            else => continue,
        };
        const cf = switch (self.env.statements.items[@intFromEnum(cited)]) {
            .axiom => |f| f.formula,
            .theorem => |f| f.formula,
            .schema => return false,
        };
        // a directly-MAPPED fact resolves (via remapCitation) to its target as-is.
        // Guard-stripping is safe iff the GUARDLESS remap of the source formula
        // α-matches that target — i.e. the author mapped it to an UNCONDITIONAL
        // (unguarded) discharge (`addZeroLeft` → `∀b; tadd(TZERO,b)=b`). If the map
        // target is a genuinely RELATIVIZED form (`opAssoc` → `∀x; inK(x) -> …`), the
        // guardless citation would mismatch it → not context-free.
        var mapped_target: ?StatementId = null;
        for (model.stmt_map) |p| {
            if (p.from == cited) mapped_target = p.to;
        }
        if (mapped_target) |tgt| {
            var guardless = model.remap;
            guardless.guard = null;
            const want = self.pool.remapFormula(cf, guardless) catch return false;
            const tgt_f = switch (self.env.statements.items[@intFromEnum(tgt)]) {
                .axiom => |f| f.formula,
                .theorem => |f| f.formula,
                .schema => return false,
            };
            if (!self.pool.alphaEq(want, tgt_f)) return false;
            continue;
        }
        if (!model.remap.affects(self.pool, cf)) continue; // unaffected: cites as-is, fine.
        // affected + unmapped: a NESTED context-free synthetic (e.g. `arithmetic`
        // cites `simplify#n`) is itself guard-stripped by recursion — fine. Any
        // other affected+unmapped fact would need a relativized materialization the
        // guardless synthetic cannot consume → not context-free.
        if (!isContextFreeSynthetic(self, model, cited)) return false;
    }
    return true;
}

/// Materialize a source theorem's proof through a GUARDED model. Unlike the
/// unguarded 1:1 remap, guard relativization is not structure-preserving: it
/// re-emits the proof into a fresh Lowering, inserting `assume guard(a)` blocks
/// under each carrier `fix` and a `guard(t)` discharge at each `forall_elim` over
/// a guarded universal. SRefs are captured as steps are emitted (no index
/// arithmetic). (Built rung by rung: L1 = flat proofs, constant discharge.)
fn materializeGuardedModelTheorem(self: *Elaborator, model: *Model, source: StatementId, loc: u32) ElabError!StatementId {
    const stmt = self.env.statements.items[@intFromEnum(source)];
    const fact = switch (stmt) {
        .theorem => |t| t,
        .axiom => return self.fail(loc, "model materialization reached an axiom without a mapping; add it to the model", .{}),
        .schema => return self.fail(loc, "model cannot materialize a schema", .{}),
    };
    const proof = fact.proof orelse
        return self.fail(loc, "model cannot materialize '{s}': its proof was not retained (trusted import?)", .{self.interner.stringBytes(fact.name)});

    const mangled = try mangledModelName(self, model.name, fact.name);
    const remapped_formula = self.pool.remapFormula(fact.formula, model.remap) catch return error.OutOfMemory;
    const mat_id = try self.beginSyntheticTheorem(mangled, remapped_formula, loc);
    try model.materialized.put(self.arena, source, mat_id);

    // re-emit into a fresh Lowering, capturing each source step's new ref.
    var plow: Lowering = .{};
    try plow.blocks.append(self.arena, .{
        .parent = null,
        .label = try self.interner.internString("proof"),
        .kind = .root,
        .first_step = 0,
        .last_step = 0,
    });
    const root: kernel.BlockId = @enumFromInt(0);

    var guardless = model.remap;
    guardless.guard = null;
    var ctx: GuardedCtx = .{
        .model = model,
        .proof = proof,
        .step_map = .empty,
        .guard_hyp = .empty,
        .block_map = .empty,
        .synthetic_blind = .empty,
        .guardless = guardless,
        .loc = loc,
    };
    try markSyntheticClusters(self, &ctx);

    // walk the source block tree from the root, re-emitting each block's directly
    // owned steps and recursing into children (a carrier `fix` becomes
    // `fix a { assume guard(a) { … } }`). Captures every ref by emission.
    try reemitBlock(self, &plow, root, &ctx, @enumFromInt(0));

    // TOP-LEVEL WEAKENING: when the whole proof is a guard-blind synthetic cluster
    // (e.g. `reassociate`'s single `[by assoc(op)]` step), the re-emitted body
    // concludes the UNGUARDED carrier universal `∀x…; P`, but the theorem's declared
    // statement is the relativized `∀x; guard(x) -> …; P`. Wrap the unguarded result
    // in `fix xᵢ; assume guard(xᵢ)` layers with a forall_elim(x₁…xₙ) at the core —
    // the same weakening `emitWeakenedAxiom` performs for an unconditional axiom, but
    // citing the cluster's final STEP instead of a mapped statement.
    if (plow.steps.items.len > 0) {
        const last = plow.steps.items[plow.steps.items.len - 1];
        if (!self.pool.alphaEq(last.formula, remapped_formula)) {
            const last_ref: kernel.SRef = .{ .id = @enumFromInt(plow.steps.items.len - 1), .loc = loc };
            _ = try emitTopLevelWeakening(self, &plow, root, &ctx, last_ref, last.formula, remapped_formula);
        }
    }
    plow.blocks.items[0].last_step = @intCast(plow.steps.items.len);

    const on_fail = try std.fmt.allocPrint(self.arena, "guarded model transfer of '{s}' does not kernel-check under the interpretation", .{self.interner.stringBytes(fact.name)});
    try self.finishSyntheticTheorem(mat_id, plow.steps.items, plow.blocks.items, fact.accelerated, fact.holes, loc, on_fail);
    return mat_id;
}

/// State threaded through the guarded re-emitter.
const GuardedCtx = struct {
    model: *Model,
    proof: @import("../env.zig").Statement.LoweredProof,
    /// source StepId -> the captured ref of its (final) re-emitted step
    step_map: std.AutoHashMapUnmanaged(kernel.StepId, kernel.SRef),
    /// carrier eigenvariable name -> the SRef of its `assume guard(a)` hypothesis
    /// step (the base case of `emitGuardProof` for a fixed variable).
    guard_hyp: std.AutoHashMapUnmanaged(StrId, kernel.SRef),
    /// source BlockId -> the new BlockId it re-emitted to (for BRef-carrying
    /// justifications: hypothesis, or_elim arms).
    block_map: std.AutoHashMapUnmanaged(kernel.BlockId, kernel.BlockId),
    /// source StepId set: steps belonging to an ACCELERANT-SYNTHETIC citation
    /// cluster (theorem_ref of a `.synthetic` theorem, its chained forall_elims /
    /// modus_ponens, and the premise-discharge global refs those modus_ponens
    /// consume). These are re-emitted GUARD-BLIND (see emitGuardBlindStep).
    synthetic_blind: std.AutoHashMapUnmanaged(kernel.StepId, void),
    /// the model's interpretation with the carrier guard STRIPPED — used to remap
    /// synthetic-cluster formulas so they match the unguarded synthetic theorem.
    guardless: term.Pool.Remap,
    loc: u32,
};

/// Precompute the set of source steps that form ACCELERANT-SYNTHETIC citation
/// clusters. A synthetic is a CONTEXT-FREE equational lemma transferred UNGUARDED
/// (materializeModelTheorem's `.synthetic` branch), so its citation cluster in the
/// guarded proof must be re-emitted guard-blind — otherwise the relativizing remap
/// injects `guard(...) ->` obligations the (unguarded) synthetic never carries.
/// The cluster is contiguous: a `theorem_ref` to a `.synthetic` theorem, then one
/// `forall_elim` per eigenvariable each citing the previous (`.step`), then one
/// `modus_ponens` per premise each citing the previous (`.implication`). A
/// modus_ponens also consumes a premise-discharge step via `.antecedent`; when the
/// premise is a GLOBAL axiom/theorem it is a separate `axiom_ref`/`theorem_ref`
/// step that likewise must be transferred unguarded (the synthetic's mapped premise
/// is unconditional), so we mark it too. Steps are processed in emission order, so a
/// single forward pass propagates the marking.
fn markSyntheticClusters(self: *Elaborator, ctx: *GuardedCtx) ElabError!void {
    for (ctx.proof.steps, 0..) |s, i| {
        const sid: kernel.StepId = @enumFromInt(i);
        switch (s.just) {
            .theorem_ref => |r| {
                // only a CONTEXT-FREE synthetic is transferred guard-blind (see
                // isContextFreeSynthetic + the `.synthetic` branch of
                // materializeModelTheorem). A synthetic that cites a model-affected
                // fact (e.g. `assoc` → `opAssoc`) rides the ordinary guarded path,
                // so its cluster must NOT be marked blind.
                if (isContextFreeSynthetic(self, ctx.model, r.stmt))
                    try ctx.synthetic_blind.put(self.arena, sid, {});
            },
            .forall_elim => |r| {
                if (ctx.synthetic_blind.contains(r.step.id)) try ctx.synthetic_blind.put(self.arena, sid, {});
            },
            .modus_ponens => |r| {
                if (ctx.synthetic_blind.contains(r.implication.id)) {
                    try ctx.synthetic_blind.put(self.arena, sid, {});
                    // the premise-discharge step feeding this modus_ponens must match
                    // the UNGUARDED synthetic premise. When it is a BARE GLOBAL
                    // axiom/theorem ref (an unconditional mapped fact — `dischargeRef`'s
                    // global branch), it must be transferred guard-blind too; else the
                    // guarded re-emit would auto-weaken it (`∀x; guard(x) -> …`) and
                    // mismatch. A LOCAL derived discharge (e.g. a `forall_elim` of an
                    // in-scope universal, or a hypothesis) is left to the ordinary
                    // guarded re-emit — its guarded form already matches the premise
                    // (relativization only wraps `∀` binders, which a ground premise or
                    // an already-specialized step does not reintroduce).
                    const ante = ctx.proof.steps[@intFromEnum(r.antecedent.id)];
                    if (ante.just == .axiom_ref or ante.just == .theorem_ref) {
                        try ctx.synthetic_blind.put(self.arena, r.antecedent.id, {});
                    }
                }
            },
            else => {},
        }
    }
}

/// Re-emit a source block's directly-owned steps into a corresponding target
/// block, recursing into child blocks. A `fix a` over the carrier sort is
/// materialized as `fix a { assume guard(a) { <body> } }` — the assume block
/// surfaces `guard(a)` for eigenvariable discharge, and closes with implies_intro
/// then the fix closes with forall_intro (reconstructing the relativized ∀).
fn reemitBlock(self: *Elaborator, plow: *Lowering, target: kernel.BlockId, ctx: *GuardedCtx, src_block: kernel.BlockId) ElabError!void {
    const sb = ctx.proof.blocks[@intFromEnum(src_block)];
    var i: u32 = sb.first_step;
    while (i < sb.last_step) : (i += 1) {
        const step = ctx.proof.steps[@intFromEnum(@as(kernel.StepId, @enumFromInt(i)))];
        if (@intFromEnum(step.block) != @intFromEnum(src_block)) continue; // owned by a nested child; emitted there
        if (step.just == .or_elim) {
            // case split: re-emit both arm subproofs, then the or_elim step
            // citing them + the (already-emitted) disjunction step.
            const r = step.just.or_elim;
            try reemitArm(self, plow, target, ctx, r.left.id);
            try reemitArm(self, plow, target, ctx, r.right.id);
            const new_formula = try remapStepFormula(self, ctx, step.formula);
            const ref = try self.emitStep(plow, target, ctx.loc, new_formula, .{ .or_elim = .{
                .disj = ctx.step_map.get(r.disj.id).?,
                .left = .{ .id = ctx.block_map.get(r.left.id).?, .loc = ctx.loc },
                .right = .{ .id = ctx.block_map.get(r.right.id).?, .loc = ctx.loc },
            } });
            try ctx.step_map.put(self.arena, @enumFromInt(i), ref);
        } else if (step.just == .not_intro) {
            // proof-by-contradiction: re-emit the assume arm (deriving the
            // contradiction), then the not_intro step citing the mapped block and
            // the two contradicting steps (resolved from step_map, now populated by
            // the arm re-emission). Like or_elim, the arm has no closing step of
            // its own — not_intro closes it.
            const r = step.just.not_intro;
            try reemitArm(self, plow, target, ctx, r.block.id);
            const new_formula = try remapStepFormula(self, ctx, step.formula);
            const ref = try self.emitStep(plow, target, ctx.loc, new_formula, .{ .not_intro = .{
                .block = .{ .id = ctx.block_map.get(r.block.id).?, .loc = ctx.loc },
                .s1 = ctx.step_map.get(r.s1.id).?,
                .s2 = ctx.step_map.get(r.s2.id).?,
            } });
            try ctx.step_map.put(self.arena, @enumFromInt(i), ref);
        } else if (childBlockOf(step.just)) |child| {
            try reemitChild(self, plow, target, ctx, child, @enumFromInt(i));
        } else if (ctx.synthetic_blind.contains(@enumFromInt(i))) {
            // an accelerant-synthetic citation-cluster step: re-emit guard-blind
            // (formula remapped WITHOUT the guard, justification a plain 1:1 remap)
            // so it matches the unguarded materialized synthetic.
            const new_ref = try emitGuardBlindStep(self, plow, target, ctx, step);
            try ctx.step_map.put(self.arena, @enumFromInt(i), new_ref);
        } else {
            const new_ref = try emitGuardedStep(self, plow, target, ctx, step);
            try ctx.step_map.put(self.arena, @enumFromInt(i), new_ref);
        }
    }
}

/// The child block a block-closing justification refers to (fix→forall_intro,
/// assume→implies_intro, etc.), else null.
fn childBlockOf(j: kernel.Justification) ?kernel.BlockId {
    return switch (j) {
        .forall_intro, .implies_intro, .exists_elim => |b| b.id,
        else => null,
    };
}

/// Re-emit a child subproof block and its closing step. `closing_src` is the
/// source step whose justification closes `child` (forall_intro / implies_intro).
fn reemitChild(self: *Elaborator, plow: *Lowering, parent: kernel.BlockId, ctx: *GuardedCtx, child: kernel.BlockId, closing_src: kernel.StepId) ElabError!void {
    const cb = ctx.proof.blocks[@intFromEnum(child)];
    const loc = ctx.loc;
    const guard = ctx.model.remap.guard.?;

    switch (cb.kind) {
        .fix => |fb| {
            const fv = fb.v;
            const new_sort = ctx.model.remap.sort(fv.sort);
            const fix_b = try self.newBlock(plow, try self.freshNamed("gm-fix"), parent, .{ .fix = .{ .v = .{ .name = fv.name, .sort = new_sort } } });
            if (fv.sort == guard.carrier) {
                // carrier fix → insert `assume guard(a)`, surface the hypothesis.
                const bound = try self.pool.add(.{ .fvar = .{ .name = fv.name, .sort = new_sort } });
                const guard_a = try self.pool.addApp(.pred, guard.pred, &.{bound});
                const asm_b = try self.newBlock(plow, try self.freshNamed("gm-guard"), fix_b, .{ .assume = guard_a });
                const hyp = try self.emitStep(plow, asm_b, loc, guard_a, .{ .hypothesis = .{ .id = asm_b, .loc = loc } });
                try ctx.guard_hyp.put(self.arena, fv.name, hyp);
                // re-emit the fix body inside the assume block.
                try reemitBlock(self, plow, asm_b, ctx, child);
                // close the assume with implies_intro (→ guard(a) -> <body last>),
                // emitted in the fix block; then close the fix with forall_intro.
                const body_last = try remapStepFormula(self, ctx, lastStepFormula(ctx, child));
                const impl = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = guard_a, .rhs = body_last } });
                self.closeBlock(plow, asm_b);
                _ = try self.emitStep(plow, fix_b, loc, impl, .{ .implies_intro = .{ .id = asm_b, .loc = loc } });
                _ = ctx.guard_hyp.remove(fv.name);
            } else {
                try reemitBlock(self, plow, fix_b, ctx, child);
            }
            self.closeBlock(plow, fix_b);
            const closed = try remapStepFormula(self, ctx, ctx.proof.steps[@intFromEnum(closing_src)].formula);
            const ref = try self.emitStep(plow, parent, loc, closed, .{ .forall_intro = .{ .id = fix_b, .loc = loc } });
            try ctx.step_map.put(self.arena, closing_src, ref);
        },
        .assume => |f| {
            const asm_f = try remapStepFormula(self, ctx, f);
            const asm_b = try self.newBlock(plow, try self.freshNamed("gm-assume"), parent, .{ .assume = asm_f });
            try ctx.block_map.put(self.arena, child, asm_b);
            try reemitBlock(self, plow, asm_b, ctx, child);
            self.closeBlock(plow, asm_b);
            const closed = try remapStepFormula(self, ctx, ctx.proof.steps[@intFromEnum(closing_src)].formula);
            const ref = try self.emitStep(plow, parent, loc, closed, .{ .implies_intro = .{ .id = asm_b, .loc = loc } });
            try ctx.step_map.put(self.arena, closing_src, ref);
        },
        .unpack => |u| {
            // the source existential `∃x; body` relativizes to `∃x; guard(x) and
            // body` (∃ takes `and`), so unpacking the witness w surfaces
            // `guard(w) and body[w]`. Extract guard(w) (register it for the body's
            // eigenvariable discharges) and body[w] (map the source's own
            // hypothesis-of-the-witness to it).
            const new_sort = ctx.model.remap.sort(u.v.sort);
            const src_ref = ctx.step_map.get(u.source.id).?;
            const unp_b = try self.newBlock(plow, try self.freshNamed("gm-unpack"), parent, .{ .unpack = .{
                .v = .{ .name = u.v.name, .sort = new_sort },
                .source = src_ref,
            } });
            try ctx.block_map.put(self.arena, child, unp_b);
            const guarded_witness = u.v.sort == guard.carrier;
            if (guarded_witness) {
                // surface `guard(w) and body[w]`, split it. The unpack surfaces
                // the RELATIVIZED existential's opened body — remapFormula (not the
                // step-level remap) injects the guard as a leading `and` conjunct,
                // so we read the body off the fully-remapped source formula.
                const w = try self.pool.add(.{ .fvar = .{ .name = u.v.name, .sort = new_sort } });
                const src_ex = ctx.proof.steps[@intFromEnum(u.source.id)].formula;
                const remapped_ex = self.pool.remapFormula(src_ex, ctx.model.remap) catch return error.OutOfMemory; // ∃x; guard(x) and P(x)
                const ex_node = self.pool.get(remapped_ex);
                const hyp_formula = try self.pool.open(ex_node.quant.body, w); // guard(w) and P(w)
                const hyp = try self.emitStep(plow, unp_b, loc, hyp_formula, .{ .hypothesis = .{ .id = unp_b, .loc = loc } });
                const guard_ref = try self.emitStep(plow, unp_b, loc, try self.pool.addApp(.pred, guard.pred, &.{w}), .{ .and_elim_left = hyp });
                try ctx.guard_hyp.put(self.arena, u.v.name, guard_ref);
            }
            try reemitBlock(self, plow, unp_b, ctx, child);
            self.closeBlock(plow, unp_b);
            if (guarded_witness) _ = ctx.guard_hyp.remove(u.v.name);
            const closed = try remapStepFormula(self, ctx, ctx.proof.steps[@intFromEnum(closing_src)].formula);
            const ref = try self.emitStep(plow, parent, loc, closed, .{ .exists_elim = .{ .id = unp_b, .loc = loc } });
            try ctx.step_map.put(self.arena, closing_src, ref);
        },
        .root => unreachable,
    }
}

/// Re-emit an `assume`-arm block of a case split (the `or_elim` step, emitted by
/// the caller, references it). Records the block in `block_map` so its inner
/// `hypothesis` steps resolve. No closing step (the arm is closed by or_elim).
fn reemitArm(self: *Elaborator, plow: *Lowering, parent: kernel.BlockId, ctx: *GuardedCtx, arm: kernel.BlockId) ElabError!void {
    const ab = ctx.proof.blocks[@intFromEnum(arm)];
    std.debug.assert(ab.kind == .assume);
    const asm_f = try remapStepFormula(self, ctx, ab.kind.assume);
    const new_b = try self.newBlock(plow, try self.freshNamed("gm-arm"), parent, .{ .assume = asm_f });
    try ctx.block_map.put(self.arena, arm, new_b);
    try reemitBlock(self, plow, new_b, ctx, arm);
    self.closeBlock(plow, new_b);
}

fn remapStepFormula(self: *Elaborator, ctx: *GuardedCtx, f: TermId) ElabError!TermId {
    return self.pool.remapFormula(f, ctx.model.remap) catch return error.OutOfMemory;
}

/// The (source) formula of the last step directly owned by `block`.
fn lastStepFormula(ctx: *GuardedCtx, block: kernel.BlockId) TermId {
    const b = ctx.proof.blocks[@intFromEnum(block)];
    var i = b.last_step;
    while (i > b.first_step) {
        i -= 1;
        const s = ctx.proof.steps[@intFromEnum(@as(kernel.StepId, @enumFromInt(i)))];
        if (@intFromEnum(s.block) == @intFromEnum(block)) return s.formula;
    }
    return ctx.proof.steps[@intFromEnum(@as(kernel.StepId, @enumFromInt(b.first_step)))].formula;
}

/// Re-emit one source step into `plow`; return the ref of its (final) emitted
/// step. A `forall_elim` over a guarded (carrier-sorted) universal expands to
/// three steps — the elim (`guard(t) -> C`), a `guard(t)` discharge, and a
/// modus_ponens yielding the bare `C` (whose ref is returned).
fn emitGuardedStep(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, s: kernel.Step) ElabError!kernel.SRef {
    const model = ctx.model;
    const loc = ctx.loc;
    const new_formula = self.pool.remapFormula(s.formula, model.remap) catch return error.OutOfMemory;

    switch (s.just) {
        .axiom_ref, .theorem_ref => {
            // AUTO-WEAKENING: a mapped axiom that holds UNCONDITIONALLY on the
            // carrier (its target is the unguarded universal `∀x; P`) has a
            // relativized obligation `∀x; guard(x) -> P` — a free weakening. When
            // the target's formula is that unguarded universal, synthesize the
            // weakening rather than citing the target directly (which would
            // mismatch the relativized claim). Real (guard-restricted) axioms whose
            // author-supplied target is ALREADY relativized fall through unchanged.
            if (s.just == .axiom_ref) {
                if (try emitWeakenedAxiom(self, plow, block, ctx, s.just.axiom_ref.stmt, new_formula)) |ref| return ref;
            }
            const j = try remapJustification(self, model, s.just, loc);
            return self.emitStep(plow, block, loc, new_formula, j);
        },
        .forall_elim => |r| {
            // the cited universal, in the SOURCE proof, before remap.
            const cited_src = ctx.proof.steps[@intFromEnum(r.step.id)].formula;
            const cited_node = self.pool.get(cited_src);
            const guarded = cited_node == .quant and cited_node.quant.q == .forall and
                cited_node.quant.sort == model.remap.guard.?.carrier;
            const with = self.pool.remapFormula(r.with, model.remap) catch return error.OutOfMemory;
            const cited_ref = ctx.step_map.get(r.step.id).?;
            if (!guarded) {
                return self.emitStep(plow, block, loc, new_formula, .{ .forall_elim = .{ .step = cited_ref, .with = with, .with_loc = loc } });
            }
            // guarded: the elim derives `guard(with) -> new_formula`.
            const guard = model.remap.guard.?;
            const guard_app = try self.pool.addApp(.pred, guard.pred, &.{with});
            const implied = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = guard_app, .rhs = new_formula } });
            const elim_ref = try self.emitStep(plow, block, loc, implied, .{ .forall_elim = .{ .step = cited_ref, .with = with, .with_loc = loc } });
            const guard_ref = try emitGuardProof(self, plow, block, ctx, with);
            return self.emitStep(plow, block, loc, new_formula, .{ .modus_ponens = .{ .implication = elim_ref, .antecedent = guard_ref } });
        },
        // a `hypothesis` step surfaces its (assume) block's formula; re-point at
        // the mapped block.
        .hypothesis => |b| return self.emitStep(plow, block, loc, new_formula, .{ .hypothesis = .{ .id = ctx.block_map.get(b.id).?, .loc = loc } }),
        // steps that reference other steps by SRef (no guard-discharge needed):
        // translate each ref through step_map and re-emit 1:1.
        .reflexivity => return self.emitStep(plow, block, loc, new_formula, .reflexivity),
        .modus_ponens => |r| return self.emitStep(plow, block, loc, new_formula, .{ .modus_ponens = .{ .implication = ctx.step_map.get(r.implication.id).?, .antecedent = ctx.step_map.get(r.antecedent.id).? } }),
        .rewrite => |r| return self.emitStep(plow, block, loc, new_formula, .{ .rewrite = .{ .equation = ctx.step_map.get(r.equation.id).?, .target = ctx.step_map.get(r.target.id).? } }),
        .iff_rewrite => |r| return self.emitStep(plow, block, loc, new_formula, .{ .iff_rewrite = .{ .biconditional = ctx.step_map.get(r.biconditional.id).?, .target = ctx.step_map.get(r.target.id).? } }),
        .symmetry => |sr| return self.emitStep(plow, block, loc, new_formula, .{ .symmetry = ctx.step_map.get(sr.id).? }),
        .double_negation => |sr| return self.emitStep(plow, block, loc, new_formula, .{ .double_negation = ctx.step_map.get(sr.id).? }),
        .and_intro => |r| return self.emitStep(plow, block, loc, new_formula, .{ .and_intro = .{ .left = ctx.step_map.get(r.left.id).?, .right = ctx.step_map.get(r.right.id).? } }),
        .and_elim_left => |sr| return self.emitStep(plow, block, loc, new_formula, .{ .and_elim_left = ctx.step_map.get(sr.id).? }),
        .and_elim_right => |sr| return self.emitStep(plow, block, loc, new_formula, .{ .and_elim_right = ctx.step_map.get(sr.id).? }),
        .or_intro_left => |sr| return self.emitStep(plow, block, loc, new_formula, .{ .or_intro_left = ctx.step_map.get(sr.id).? }),
        .or_intro_right => |sr| return self.emitStep(plow, block, loc, new_formula, .{ .or_intro_right = ctx.step_map.get(sr.id).? }),
        .absurd => |r| return self.emitStep(plow, block, loc, new_formula, .{ .absurd = .{ .s1 = ctx.step_map.get(r.s1.id).?, .s2 = ctx.step_map.get(r.s2.id).? } }),
        .exists_intro => |r| {
            const witness = self.pool.remapFormula(r.witness, model.remap) catch return error.OutOfMemory;
            const src_node = self.pool.get(s.formula); // source ∃ (pre-remap)
            const guarded = src_node == .quant and src_node.quant.q == .exists and
                src_node.quant.sort == model.remap.guard.?.carrier;
            var body_ref = ctx.step_map.get(r.step.id).?;
            if (guarded) {
                // target is `∃x; guard(x) and P(x)`, so exists_intro needs a proof
                // of `guard(w) and P(w)` — the source only established `P(w)`.
                // Synthesize `guard(w)` and conjoin.
                const guard = model.remap.guard.?;
                const guard_app = try self.pool.addApp(.pred, guard.pred, &.{witness});
                const p_ref = body_ref;
                const p_formula = try remapStepFormula(self, ctx, ctx.proof.steps[@intFromEnum(r.step.id)].formula);
                const guard_ref = try emitGuardProof(self, plow, block, ctx, witness);
                const conj = try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = guard_app, .rhs = p_formula } });
                body_ref = try self.emitStep(plow, block, loc, conj, .{ .and_intro = .{ .left = guard_ref, .right = p_ref } });
            }
            return self.emitStep(plow, block, loc, new_formula, .{ .exists_intro = .{ .step = body_ref, .witness = witness, .witness_loc = loc } });
        },
        // schema instantiation (e.g. `instantiate induction(P) base step`): the
        // instance formula is remapped through the model (relativizing its
        // conclusion), and each premise SRef is translated through step_map — the
        // premises were already re-emitted as guarded steps. This is what lets an
        // induction-based proof transfer through a guarded model (e.g. peano ℕ onto
        // the nonnegative integers).
        .schema_instance => |r| {
            const instance = self.pool.remapFormula(r.instance, model.remap) catch return error.OutOfMemory;
            const new_premises = try self.arena.alloc(kernel.SRef, r.premises.len);
            for (r.premises, new_premises) |pr, *out| out.* = ctx.step_map.get(pr.id).?;
            return self.emitStep(plow, block, loc, new_formula, .{ .schema_instance = .{ .instance = instance, .premises = new_premises } });
        },
        // BRef-carrying / case-split forms not yet needed; reject cleanly if one
        // appears (accelerated-tactic steps like `simplify` also land here — a
        // separate boundary).
        else => return self.fail(loc, "guarded model materialization does not yet handle this proof shape", .{}),
    }
}

/// Re-emit one source step of an ACCELERANT-SYNTHETIC citation cluster GUARD-BLIND:
/// the formula is remapped with the guard STRIPPED (`ctx.guardless`), and the
/// justification is re-emitted as the plain 1:1 unguarded shape — NO guarded
/// forall_elim (`guard(with) ->`) special-casing and NO auto-weakening. This is
/// exactly what a synthetic (context-free equational lemma) needs: it holds on the
/// whole target carrier, so its remapped citation carries no membership obligation.
///  - `theorem_ref`/`axiom_ref`: route through `remapCitation` — the synthetic's
///    theorem_ref resolves to its UNGUARDED materialization (the `.synthetic` branch
///    in materializeModelTheorem); a mapped global premise axiom resolves to its
///    stmt_map target; an unaffected fact cites as-is.
///  - `forall_elim`/`modus_ponens`: plain re-emit, SRefs through `ctx.step_map`,
///    the `with` term through the guardless remap.
fn emitGuardBlindStep(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, s: kernel.Step) ElabError!kernel.SRef {
    const model = ctx.model;
    const loc = ctx.loc;
    const new_formula = self.pool.remapFormula(s.formula, ctx.guardless) catch return error.OutOfMemory;
    switch (s.just) {
        .axiom_ref => |r| {
            const j = try remapCitation(self, model, r.stmt, false, loc);
            return self.emitStep(plow, block, loc, new_formula, j);
        },
        .theorem_ref => |r| {
            const j = try remapCitation(self, model, r.stmt, true, loc);
            return self.emitStep(plow, block, loc, new_formula, j);
        },
        .forall_elim => |r| {
            const with = self.pool.remapFormula(r.with, ctx.guardless) catch return error.OutOfMemory;
            return self.emitStep(plow, block, loc, new_formula, .{ .forall_elim = .{ .step = ctx.step_map.get(r.step.id).?, .with = with, .with_loc = loc } });
        },
        .modus_ponens => |r| return self.emitStep(plow, block, loc, new_formula, .{ .modus_ponens = .{ .implication = ctx.step_map.get(r.implication.id).?, .antecedent = ctx.step_map.get(r.antecedent.id).? } }),
        // a synthetic cluster is built only from the shapes above; anything else
        // was mis-marked — fall back to the guarded re-emit rather than mis-handle.
        else => return emitGuardedStep(self, plow, block, ctx, s),
    }
}

/// TOP-LEVEL WEAKENING of a guard-blind synthetic conclusion. The re-emitted proof
/// body proved the UNGUARDED carrier universal `unguarded` (formula of `src_ref`),
/// but the theorem's declared statement is the relativized `target`
/// `∀x₁; guard(x₁) -> … -> ∀xₙ; guard(xₙ) -> P`. Emit the `fix xᵢ; assume guard(xᵢ)`
/// weakening layers with a `forall_elim(x₁…xₙ)` of `src_ref` at the core, returning
/// the ref of the relativized conclusion. Errors if `target` is not the guarded
/// weakening of `unguarded` (a shape the transfer does not produce).
fn emitTopLevelWeakening(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, src_ref: kernel.SRef, unguarded: TermId, target: TermId) ElabError!kernel.SRef {
    const guard = ctx.model.remap.guard.?;
    const lowered_carrier = ctx.model.remap.sort(guard.carrier);

    // peel the target's alternating `∀xᵢ:carrier; guard(xᵢ) -> …` layers.
    var hints: std.ArrayList(StrId) = .empty;
    var residual = target;
    while (true) {
        const q = self.pool.get(residual);
        if (q != .quant or q.quant.q != .forall or q.quant.sort != lowered_carrier) break;
        const b = self.pool.get(q.quant.body);
        if (b != .bin or b.bin.op != .implies) break;
        const ante = self.pool.get(b.bin.lhs);
        if (ante != .pred or ante.pred.sym != guard.pred or ante.pred.args_len != 1) break;
        const arg = self.pool.args(ante.pred)[0];
        if (self.pool.get(arg) != .bvar or self.pool.get(arg).bvar != 0) break;
        try hints.append(self.arena, q.quant.hint);
        residual = b.bin.rhs;
    }
    if (hints.items.len == 0)
        return self.fail(ctx.loc, "guarded model: transferred synthetic conclusion is not a relativized universal", .{});

    // the unguarded result must be `∀x₁…xₙ:carrier; residual`.
    var rebuilt = residual;
    var i: usize = hints.items.len;
    while (i > 0) {
        i -= 1;
        rebuilt = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = lowered_carrier, .hint = hints.items[i], .body = rebuilt } });
    }
    if (!self.pool.alphaEq(unguarded, rebuilt))
        return self.fail(ctx.loc, "guarded model: transferred synthetic conclusion does not weaken to the theorem statement", .{});

    return emitTopWeakenLayer(self, plow, block, ctx, src_ref, unguarded, target, hints.items, &.{});
}

/// One `fix xᵢ; assume guard(xᵢ)` layer of the top-level weakening (mirrors
/// emitWeakenLayer, but the base case cites the ALREADY-EMITTED unguarded step
/// `src_ref` via a forall_elim chain rather than a statement).
fn emitTopWeakenLayer(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, src_ref: kernel.SRef, unguarded: TermId, claim: TermId, hints: []const StrId, fixed: []const TermId) ElabError!kernel.SRef {
    const loc = ctx.loc;
    const guard = ctx.model.remap.guard.?;

    if (hints.len == 0) {
        // base: specialize the unguarded universal at every fixed var.
        var step_ref = src_ref;
        var current = unguarded;
        for (fixed) |fv| {
            const q = self.pool.get(current);
            const opened = try self.pool.open(q.quant.body, fv);
            step_ref = try self.emitStep(plow, block, loc, opened, .{ .forall_elim = .{ .step = step_ref, .with = fv, .with_loc = loc } });
            current = opened;
        }
        return step_ref;
    }

    const lowered_carrier = ctx.model.remap.sort(guard.carrier);
    const hint = hints[0];
    const fix_b = try self.newBlock(plow, try self.freshNamed("gm-topweaken-fix"), block, .{ .fix = .{ .v = .{ .name = hint, .sort = lowered_carrier } } });
    const x = try self.pool.add(.{ .fvar = .{ .name = hint, .sort = lowered_carrier } });
    const guard_x = try self.pool.addApp(.pred, guard.pred, &.{x});
    const asm_b = try self.newBlock(plow, try self.freshNamed("gm-topweaken-guard"), fix_b, .{ .assume = guard_x });
    _ = try self.emitStep(plow, asm_b, loc, guard_x, .{ .hypothesis = .{ .id = asm_b, .loc = loc } });

    const claim_node = self.pool.get(claim);
    const opened = try self.pool.open(claim_node.quant.body, x); // guard(x) -> rest[x]
    const inner_claim = self.pool.get(opened).bin.rhs; // rest[x]

    const new_fixed = try self.arena.alloc(TermId, fixed.len + 1);
    @memcpy(new_fixed[0..fixed.len], fixed);
    new_fixed[fixed.len] = x;
    _ = try emitTopWeakenLayer(self, plow, asm_b, ctx, src_ref, unguarded, inner_claim, hints[1..], new_fixed);

    self.closeBlock(plow, asm_b);
    _ = try self.emitStep(plow, fix_b, loc, opened, .{ .implies_intro = .{ .id = asm_b, .loc = loc } });
    self.closeBlock(plow, fix_b);
    return self.emitStep(plow, block, loc, claim, .{ .forall_intro = .{ .id = fix_b, .loc = loc } });
}

/// AUTO-WEAKENING of an unconditional mapped axiom. If `source_axiom` maps to a
/// target whose formula is an UNGUARDED universal over N carrier binders,
/// `∀x₁…xₙ:carrier; P`, while the relativized claim `new_formula` is the guarded
/// `∀x₁; guard(x₁) -> … -> ∀xₙ; guard(xₙ) -> P`, synthesize the weakening — nested
/// `fix xᵢ; assume guard(xᵢ)` blocks with one multi-arg `forall_elim(x₁…xₙ)` of
/// the target at the core — and return its ref. Returns null (fall through to a
/// direct citation) when the target is NOT the matching unguarded universal (the
/// author supplied an already-relativized, genuinely guard-restricted target).
fn emitWeakenedAxiom(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, source_axiom: StatementId, new_formula: TermId) ElabError!?kernel.SRef {
    const model = ctx.model;
    const guard = model.remap.guard.?;

    // find the mapped target for this source axiom.
    var target: ?StatementId = null;
    for (model.stmt_map) |p| {
        if (p.from == source_axiom) target = p.to;
    }
    const tgt = target orelse return null;
    const tgt_formula = switch (self.env.statements.items[@intFromEnum(tgt)]) {
        .axiom => |f| f.formula,
        .theorem => |f| f.formula,
        .schema => return null,
    };

    // the guard keys on the SOURCE carrier sort, but `new_formula` (the relativized
    // claim) and the mapped target are over the LOWERED target sort — e.g. mapping
    // `group.Grp` to `Fn where invertible` gives carrier `Fn`, not `Grp`. Compare
    // binder sorts against the remapped carrier so the cross-sort case (source sort ≠
    // target base sort) is recognized, not just the same-sort subgroup case.
    const lowered_carrier = model.remap.sort(guard.carrier);

    // peel the claim's alternating `∀xᵢ:carrier; guard(xᵢ) -> …` layers, collecting
    // the binder hints; the residual (after n layers) is the guard-free body P.
    var hints: std.ArrayList(StrId) = .empty;
    var residual = new_formula;
    while (true) {
        const q = self.pool.get(residual);
        if (q != .quant or q.quant.q != .forall or q.quant.sort != lowered_carrier) break;
        const b = self.pool.get(q.quant.body);
        if (b != .bin or b.bin.op != .implies) break;
        // the antecedent must be exactly `guard(bvar0)` for this to be a weakening layer.
        const ante = self.pool.get(b.bin.lhs);
        if (ante != .pred or ante.pred.sym != guard.pred or ante.pred.args_len != 1) break;
        const arg = self.pool.args(ante.pred)[0];
        if (self.pool.get(arg) != .bvar or self.pool.get(arg).bvar != 0) break;
        try hints.append(self.arena, q.quant.hint);
        residual = b.bin.rhs;
    }
    if (hints.items.len == 0) return null;

    // the target must be the UNGUARDED universal `∀x₁…xₙ:carrier; <residual>` —
    // rebuild it and α-compare. (If the target already carries guards, no match.)
    var unguarded = residual;
    var i: usize = hints.items.len;
    while (i > 0) {
        i -= 1;
        unguarded = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = lowered_carrier, .hint = hints.items[i], .body = unguarded } });
    }
    if (!self.pool.alphaEq(tgt_formula, unguarded)) return null;

    return try emitWeakenLayer(self, plow, block, ctx, tgt, tgt_formula, new_formula, hints.items, &.{});
}

/// Emit one `fix xᵢ; assume guard(xᵢ) { … }` layer of a multi-binder weakening,
/// recursing on the remaining binders. `fixed` are the eigenvariables fixed by the
/// enclosing layers (in order); at the base (no binders left) it cites the target
/// and specializes it at all fixed vars in one `forall_elim`. `claim` is the still-
/// guarded formula this layer proves (`∀xᵢ; guard(xᵢ) -> <rest>`).
fn emitWeakenLayer(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, tgt: StatementId, tgt_formula: TermId, claim: TermId, hints: []const StrId, fixed: []const TermId) ElabError!kernel.SRef {
    const loc = ctx.loc;
    const guard = ctx.model.remap.guard.?;

    if (hints.len == 0) {
        // base: cite the unconditional target, specialize at every fixed var by a
        // CHAIN of single-arg forall_elims (the kernel elim takes one `with`).
        var step_ref = try self.emitStep(plow, block, loc, tgt_formula, citeStatement(self, tgt, loc));
        var current = tgt_formula;
        for (fixed) |fv| {
            const q = self.pool.get(current);
            const opened = try self.pool.open(q.quant.body, fv);
            step_ref = try self.emitStep(plow, block, loc, opened, .{ .forall_elim = .{ .step = step_ref, .with = fv, .with_loc = loc } });
            current = opened;
        }
        return step_ref;
    }

    // the materialized `fix`/fvar are over the LOWERED carrier (the target base
    // sort), not the source `guard.carrier` — see emitWeakenedAxiom.
    const lowered_carrier = ctx.model.remap.sort(guard.carrier);
    const hint = hints[0];
    const fix_b = try self.newBlock(plow, try self.freshNamed("gm-weaken-fix"), block, .{ .fix = .{ .v = .{ .name = hint, .sort = lowered_carrier } } });
    const x = try self.pool.add(.{ .fvar = .{ .name = hint, .sort = lowered_carrier } });
    const guard_x = try self.pool.addApp(.pred, guard.pred, &.{x});
    const asm_b = try self.newBlock(plow, try self.freshNamed("gm-weaken-guard"), fix_b, .{ .assume = guard_x });
    _ = try self.emitStep(plow, asm_b, loc, guard_x, .{ .hypothesis = .{ .id = asm_b, .loc = loc } });

    // `claim` = `∀xᵢ:carrier; guard(xᵢ) -> rest`; the inner formula, opened at x, is
    // `guard(x) -> rest[x]`, whose consequent `rest[x]` is what the recursion proves.
    const claim_node = self.pool.get(claim);
    const opened = try self.pool.open(claim_node.quant.body, x); // guard(x) -> rest[x]
    const inner_claim = self.pool.get(opened).bin.rhs; // rest[x]

    const new_fixed = try self.arena.alloc(TermId, fixed.len + 1);
    @memcpy(new_fixed[0..fixed.len], fixed);
    new_fixed[fixed.len] = x;
    _ = try emitWeakenLayer(self, plow, asm_b, ctx, tgt, tgt_formula, inner_claim, hints[1..], new_fixed);

    self.closeBlock(plow, asm_b);
    _ = try self.emitStep(plow, fix_b, loc, opened, .{ .implies_intro = .{ .id = asm_b, .loc = loc } });
    self.closeBlock(plow, fix_b);
    return self.emitStep(plow, block, loc, claim, .{ .forall_intro = .{ .id = fix_b, .loc = loc } });
}

/// Emit a proof of `guard(t)` and return its ref, by recursion on `t`:
///  - a carrier eigenvariable → its in-scope `assume guard(a)` hypothesis (L2);
///  - a mapped constant → the base closure fact `guard(c)` in scope (L1);
///  - anything else → a closure fact matched by shape, else a clean error (L3).
fn emitGuardProof(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, t: TermId) ElabError!kernel.SRef {
    const guard = ctx.model.remap.guard.?;
    // eigenvariable: cite the guard hypothesis surfaced by its `fix a { assume
    // guard(a) }` block.
    if (self.pool.get(t) == .fvar) {
        if (ctx.guard_hyp.get(self.pool.get(t).fvar.name)) |hyp| return hyp;
    }
    const want = try self.pool.addApp(.pred, guard.pred, &.{t});
    // a proven local fact whose formula is exactly `guard(t)` (base closure).
    if (findFactByFormula(self, want)) |id| {
        return self.emitStep(plow, block, ctx.loc, want, citeStatement(self, id, ctx.loc));
    }
    // composite: a closure fact `∀v…; guard(p₁) -> … -> guard(pₖ) -> guard(C)`
    // whose conclusion C unifies with t — instantiate it, recurse on each
    // antecedent, and chain forall_elim + modus_ponens.
    if (try emitCompositeGuard(self, plow, block, ctx, t, want)) |ref| return ref;
    return self.fail(ctx.loc, "guarded model '{s}' cannot discharge the closure obligation '{s}' — supply an axiom or theorem establishing it, in scope where model '{s}' is declared", .{ self.interner.stringBytes(ctx.model.name), try self.renderTerm(want), self.interner.stringBytes(ctx.model.name) });
}

/// Discharge `guard(t)` for a composite `t` via a closure fact. Searches for a
/// proven fact `∀v…; guard(p₁) -> … -> guard(pₖ) -> guard(C)` whose conclusion
/// `C` matches `t` (solving the binders), recurses to prove each instantiated
/// antecedent, and emits the forall_elim + modus_ponens chain. Returns null if no
/// closure fact matches (the caller then errors cleanly).
fn emitCompositeGuard(self: *Elaborator, plow: *Lowering, block: kernel.BlockId, ctx: *GuardedCtx, t: TermId, want: TermId) ElabError!?kernel.SRef {
    const guard = ctx.model.remap.guard.?;
    candidates: for (self.env.statements.items, 0..) |st, si| {
        const fact_formula: TermId, const is_axiom: bool = switch (st) {
            .axiom => |a| .{ a.formula, true },
            .theorem => |th| if (th.proven) .{ th.formula, false } else continue,
            .schema => continue,
        };
        // peel leading ∀ binders (collect their sorts).
        var binder_sorts: std.ArrayList(term.SortId) = .empty;
        var body = fact_formula;
        while (true) {
            const n = self.pool.get(body);
            if (n != .quant or n.quant.q != .forall) break;
            try binder_sorts.append(self.arena, n.quant.sort);
            body = n.quant.body; // keep bvars loose; we solve for them
        }
        // peel `->` antecedents; the conclusion must be `guard(C)`.
        var antecedents: std.ArrayList(TermId) = .empty;
        var concl = body;
        while (true) {
            const n = self.pool.get(concl);
            if (n != .bin or n.bin.op != .implies) break;
            try antecedents.append(self.arena, n.bin.lhs);
            concl = n.bin.rhs;
        }
        const cn = self.pool.get(concl);
        if (cn != .pred or cn.pred.sym != guard.pred or cn.pred.args_len != 1) continue;
        const concl_arg = self.pool.args(cn.pred)[0];
        // solve binders by matching the conclusion arg (a bvar-pattern) against t.
        const binding = try self.arena.alloc(?TermId, binder_sorts.items.len);
        @memset(binding, null);
        if (!matchBvarPattern(self.pool, concl_arg, t, binding)) continue;
        // every binder must be solved (no unused-binder guessing); else this fact
        // is not a usable closure for `t` — try the next candidate.
        for (binding) |b| if (b == null) continue :candidates;
        // `binding[i]` is the solution for the bvar of de Bruijn INDEX i (0 =
        // innermost). `open`/`forall_elim` strips the OUTERMOST binder first (highest
        // index), so the elim chain below must instantiate in outer→inner order:
        // fill `args` reversed so args[0] is the outermost binder's solution.
        const args = try self.arena.alloc(TermId, binding.len);
        for (binding, 0..) |b, i| args[binding.len - 1 - i] = b.?;

        // cite the closure fact, forall_elim at the solved args, then MP each
        // (recursively-proved) antecedent.
        var cur = try self.emitStep(plow, block, ctx.loc, fact_formula, if (is_axiom)
            .{ .axiom_ref = .{ .stmt = @as(StatementId, @enumFromInt(si)), .loc = ctx.loc } }
        else
            .{ .theorem_ref = .{ .stmt = @as(StatementId, @enumFromInt(si)), .loc = ctx.loc } });
        var cur_formula = fact_formula;
        for (args) |arg| {
            const q = self.pool.get(cur_formula).quant;
            const opened = try self.pool.open(q.body, arg);
            cur = try self.emitStep(plow, block, ctx.loc, opened, .{ .forall_elim = .{ .step = cur, .with = arg, .with_loc = ctx.loc } });
            cur_formula = opened;
        }
        // cur_formula is now `guard(p₁[args]) -> … -> guard(C[args]=t)`.
        for (antecedents.items) |_| {
            const node = self.pool.get(cur_formula);
            const ante = node.bin.lhs; // guard(pᵢ[args])
            const ante_arg = self.pool.args(self.pool.get(ante).pred)[0];
            const ante_ref = try emitGuardProof(self, plow, block, ctx, ante_arg);
            cur_formula = node.bin.rhs;
            cur = try self.emitStep(plow, block, ctx.loc, cur_formula, .{ .modus_ponens = .{ .implication = cur, .antecedent = ante_ref } });
        }
        _ = want;
        return cur;
    }
    return null;
}

/// First-order match of a pattern (loose bvars are variables) against a ground
/// term `t`, filling `binding[deBruijn] = subterm`. Bvar index is depth-from-here
/// (no binders inside our patterns), so `bvar i` binds `binding[i]`.
fn matchBvarPattern(pool: *term.Pool, pattern: TermId, t: TermId, binding: []?TermId) bool {
    switch (pool.get(pattern)) {
        .bvar => |i| {
            if (i >= binding.len) return false;
            if (binding[i]) |prev| return pool.alphaEq(prev, t);
            binding[i] = t;
            return true;
        },
        .app => |pa| {
            const tn = pool.get(t);
            if (tn != .app or tn.app.sym != pa.sym or tn.app.args_len != pa.args_len) return false;
            const pargs = pool.args(pa);
            const targs = pool.args(tn.app);
            for (pargs, targs) |p, tt| if (!matchBvarPattern(pool, p, tt, binding)) return false;
            return true;
        },
        else => return pool.alphaEq(pattern, t),
    }
}

/// The StatementId of a proven axiom/theorem in the current file whose formula is
/// alpha-equal to `formula` (used to find guard-closure facts by shape).
fn findFactByFormula(self: *Elaborator, formula: TermId) ?StatementId {
    for (self.env.statements.items, 0..) |st, i| {
        const f: TermId = switch (st) {
            .axiom => |a| a.formula,
            .theorem => |t| if (t.proven) t.formula else continue,
            .schema => continue,
        };
        if (self.pool.alphaEq(f, formula)) return @enumFromInt(i);
    }
    return null;
}

/// Remap a justification's embedded ids through the model: TermId fields via
/// remapFormula, StatementId fields (axiom/theorem refs) through the model's
/// mappings (axioms via `stmt_map`; theorems recursively materialized).
/// Intra-proof SRef/BRef indices are structural — unchanged.
fn remapJustification(self: *Elaborator, model: *Model, j: kernel.Justification, loc: u32) ElabError!kernel.Justification {
    return switch (j) {
        // a cited statement (axiom or theorem) in a materialized proof. The
        // citation rule (MODEL-DESIGN.md): it may cite the mapped target (in
        // the substitution list); an existing fact NOT affected by the
        // substitution (as-is, walk ends); or, for a source theorem affected
        // but unmapped, its recursive materialization. It may NOT cite a fact
        // that IS affected by the substitution but is absent from the mapping.
        .axiom_ref => |r| try remapCitation(self, model, r.stmt, false, loc),
        .theorem_ref => |r| try remapCitation(self, model, r.stmt, true, loc),
        .forall_elim => |r| .{ .forall_elim = .{
            .step = r.step,
            .with = self.pool.remapFormula(r.with, model.remap) catch return error.OutOfMemory,
            .with_loc = loc,
        } },
        .exists_intro => |r| .{ .exists_intro = .{
            .step = r.step,
            .witness = self.pool.remapFormula(r.witness, model.remap) catch return error.OutOfMemory,
            .witness_loc = loc,
        } },
        .schema_instance => |r| .{ .schema_instance = .{
            .instance = self.pool.remapFormula(r.instance, model.remap) catch return error.OutOfMemory,
            .premises = r.premises,
        } },
        // all other justifications carry only intra-proof SRef/BRef indices
        // (unchanged by the remap) or nothing.
        else => j,
    };
}

/// Repoint a cited statement (`source`, `is_theorem` = it was a theorem_ref)
/// through the model, per the materialization citation rule (MODEL-DESIGN.md):
///  - in the mapping  → cite the mapped target, kind-matched;
///  - not affected by the substitution → cite as-is, walk ends (its meaning
///    is unchanged by the interpretation);
///  - affected + a theorem → recursively materialize it;
///  - affected + an axiom, unmapped → FORBIDDEN (its meaning shifts under the
///    interpretation with nothing accounting for it) → error.
fn remapCitation(self: *Elaborator, model: *Model, source: StatementId, is_theorem: bool, loc: u32) ElabError!kernel.Justification {
    _ = is_theorem;
    // in the substitution list → cite the mapped target.
    for (model.stmt_map) |p| {
        if (p.from == source) return citeStatement(self, p.to, loc);
    }
    // not in the list: decide by whether the remap affects the fact.
    const stmt = self.env.statements.items[@intFromEnum(source)];
    const formula = switch (stmt) {
        .axiom => |f| f.formula,
        .theorem => |f| f.formula,
        .schema => return self.fail(loc, "model cannot transfer a proof citing a schema", .{}),
    };
    if (!model.remap.affects(self.pool, formula)) {
        // substitution-invariant: cite as-is, walk ends.
        return citeStatement(self, source, loc);
    }
    // affected but unmapped: a theorem is materialized; an axiom is forbidden.
    switch (stmt) {
        .theorem => {
            const mat = try materializeModelTheorem(self, model, source, loc);
            return .{ .theorem_ref = .{ .stmt = mat, .loc = loc } };
        },
        .axiom => |f| return self.fail(loc, "model materialization cites axiom '{s}', which the substitution affects but the model does not map; add a mapping for it", .{self.interner.stringBytes(f.name)}),
        .schema => unreachable,
    }
}

fn mangledModelName(self: *Elaborator, model_name: StrId, source_name: StrId) ElabError!StrId {
    const text_ = std.fmt.allocPrint(self.arena, "{s}${s}", .{
        self.interner.stringBytes(model_name), self.interner.stringBytes(source_name),
    }) catch return error.OutOfMemory;
    return self.interner.internString(text_) catch return error.OutOfMemory;
}

fn statementNameOf(self: *Elaborator, id: StatementId) StrId {
    return switch (self.env.statements.items[@intFromEnum(id)]) {
        .axiom => |f| f.name,
        .theorem => |f| f.name,
        .schema => |s| s.name,
    };
}

/// A citation of a statement by the justification matching its kind — so a
/// model obligation (an abstract axiom) discharged by a proven local theorem
/// cites it as `theorem_ref`, and one discharged by a local axiom as
/// `axiom_ref`. (A schema can't discharge an obligation — rejected earlier.)
fn citeStatement(self: *Elaborator, id: StatementId, loc: u32) kernel.Justification {
    return switch (self.env.statements.items[@intFromEnum(id)]) {
        .axiom => .{ .axiom_ref = .{ .stmt = id, .loc = loc } },
        .theorem => .{ .theorem_ref = .{ .stmt = id, .loc = loc } },
        .schema => .{ .axiom_ref = .{ .stmt = id, .loc = loc } }, // unreachable in practice
    };
}

/// Discharge a transferred SCHEMA source: the model maps `source.<schema>` to a
/// local `discharge` schema whose statement is the guarded remap of the source
/// (α-verified at the model DECL site). The transfer cite occurs while the OUTER
/// schema is being instantiated (self.schema_args binds its opaque predicate
/// param), so instantiating `discharge` at those SAME args yields exactly the
/// goal formula — emit it as a zero-premise `schema_instance` the kernel checks.
/// `discharge` may be a posited axiom-schema or a proven theorem-schema; either
/// way its body is what instantiates.
fn schemaDischarge(self: *Elaborator, discharge: StatementId, goal: TermId, loc: u32) ElabError!kernel.Justification {
    const stmt = &self.env.statements.items[@intFromEnum(discharge)];
    if (stmt.* != .schema) {
        return self.fail(loc, "model schema mapping target is not a schema", .{});
    }
    const sch = &stmt.schema;
    const args = self.schema_args orelse
        return self.fail(loc, "a transferred schema can only be cited inside a schema body (there is no predicate parameter to instantiate at)", .{});
    const schema_ctx: Elaborator.Ctx = .{ .source = sch.source, .file = sch.file, .diag = @intFromEnum(sch.file) };
    const inst = (try self.instantiateSchemaCore(discharge, sch, schema_ctx, args)) orelse
        return self.fail(loc, "model transfer failed to instantiate the discharge schema", .{});
    if (!self.pool.alphaEq(inst, goal)) {
        return self.fail(loc, "model schema transfer does not match the goal:\n  transferred: {s}\n  goal:        {s}", .{
            try self.renderTerm(inst),
            try self.renderTerm(goal),
        });
    }
    return .{ .schema_instance = .{ .instance = inst, .premises = &.{} } };
}
