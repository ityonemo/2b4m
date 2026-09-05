//! Prove — the DEMAND WALK DRIVER (Step 8, W5): the semantic half of a ProveTask's
//! step-walk. It plugs into `Walk`'s driver seam (readPass / process / caseConclude /
//! exitBlock) and accumulates the kernel-checkable lowering (steps + blocks) as the walk
//! advances; `finish` runs the kernel over the whole proof and the use-all-facts pass.
//!
//! It is the demand-resolution port of the eager pure-kernel lowering (the late
//! Prover.zig / elaborate.zig subset): every kernel justification arm survives; every
//! name resolves LOCAL (Walk's LocalStepKV/LocalIdentKV) then GLOBAL (IdentKV/FactKV,
//! populated by the read pass) — never through an eager environment. Schema
//! `instantiate`, `model`, and every accelerant are UNSUPPORTED: an unrecognized rule
//! name hard-errors "unsupported by the demand prover" (red until the Phase-5 rebuilds).
//!
//! ORDINAL ALIGNMENT: Walk assigns StepOrdinals/BlockOrdinals in walk order; this driver
//! appends exactly ONE main kernel step per walked leaf step (synthetics — multi-arg
//! forall_elim intermediates — carry no ordinal) and one kernel block per entered block,
//! so `ordinal_step`/`ordinal_block` map Walk ordinals -> kernel ids by index (asserted).
//!
//! FAILED CITATIONS WEDGE: a cited theorem whose ProveTask failed leaves its FactKV entry
//! in_flight-forever; the citing task re-suspends on the (completed) owner and parks for
//! good. The root-cause diagnostic is already in the sink; wedge REPORTING is deferred.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const Diagnostics = @import("../../diagnostics.zig");
const kernel = @import("../../kernel.zig");
const Engine = @import("../../Engine.zig");
const Context = @import("../../Context.zig");
const Walk = @import("Walk.zig");
const RefScan = @import("RefScan.zig");
const Elab = @import("Elab.zig");
const Schema = @import("Schema.zig");
const Accelerant = @import("Accelerant.zig");
const EqCert = @import("EqCert.zig");
const simplify_mod = @import("simplify.zig");
const smt = @import("smt.zig");
const IdentKV = @import("../../IdentKV.zig");
const FactKV = @import("../../FactKV.zig");
const FetchTask = @import("../../Engine/FetchTask.zig");
const ModelTask = @import("../../Engine/ModelTask.zig");
const ProveTask = @import("../ProveTask.zig");

const Prove = @This();

pub const Error = error{ Recover, OutOfMemory };

ctx: *Context,
/// the engine handle of the CURRENT run — refreshed by the ProveTask on every (re)entry
/// (a resume gets a fresh handle; racking/suspension go through it).
h: *Engine.Handle,
/// this proof's OWN term scratchpad (Step 10): the substitution calculus is per-proof
/// construction workspace, so each ProveTask builds its terms here, not in one shared
/// pool. Cited durable terms `copyIn` from `extra`; the goal `reify`s back at publish.
/// Arena-resident (survives suspends); discarded with the task arena at conclusion.
pool: *term.Pool,
/// the proving file's source (step tokens index into it)
source: []const u8,
/// the proving file's pool `.file` Index and universe namespace
file: InternPool.Index,
ns: InternPool.Index,

// -- the accumulated kernel lowering (survives suspends; arena-resident) ---------------
low_steps: std.ArrayList(kernel.Step) = .empty,
low_blocks: std.ArrayList(kernel.Block) = .empty,
/// Walk StepOrdinal -> kernel StepId (main steps only; synthetics skip)
ordinal_step: std.ArrayList(kernel.StepId) = .empty,
/// Walk BlockOrdinal -> kernel BlockId (index 0 = root)
ordinal_block: std.ArrayList(kernel.BlockId) = .empty,
/// open `case` contexts, innermost last (pushed at case-process, popped at conclude)
case_stack: std.ArrayList(CaseCtx) = .empty,
/// hygienic fresh-name counter (shared with Elab via pointer)
fresh_counter: u32 = 0,
/// use-all-facts extra reachability roots (TCC dischargers — none yet; kept for shape)
extra_reachable_steps: std.ArrayList(u32) = .empty,
/// REFINED-SORT proof obligations (Step 3c): a guarded-function application over a refined
/// param appends `inH(arg)` here (via the Elab); `dischargeTccs` after each formula proves
/// them against the LOCAL context (result_facts + block guards/assumes + prior steps) — no
/// global scan (the plan's fetch-only mandate; global-fact discharge is deferred).
pending_tccs: std.ArrayList(Elab.Tcc) = .empty,
/// closure facts surfaced by refined-RESULT funcs/consts (an available discharger).
result_facts: std.ArrayList(TermId) = .empty,
/// SCHEMA CONTEXT (set only when this Prove drives a schema INSTANCE): the bound args
/// (installed on every Elab it builds) + the param names (skipped by the read pass). Null/
/// empty for an ordinary proof. See [[schema-reification-blocker]] rebuild (Step 12).
schema_args: ?*const Schema.SchemaArgs = null,
schema_params: []const StrId = &.{},
/// MODEL this proof runs THROUGH (Step 13): when non-`.universe`, this Prove is
/// re-proving a source theorem in a model namespace — every global (sym via Elab, fact
/// via resolveFactRef) is filtered `applyModel(model, source)`, so source names remap to
/// their targets. `.universe` = an ordinary (identity) proof.
model: InternPool.Index = .universe,

const CaseCtx = struct { goal: TermId, disj: kernel.SRef, loc: u32 };

pub fn init(ctx: *Context, h: *Engine.Handle, source: []const u8, file: InternPool.Index, ns: InternPool.Index) Allocator.Error!*Prove {
    const p = try ctx.arena.create(Prove);
    const pool = try ctx.arena.create(term.Pool);
    pool.* = .init(ctx.arena);
    p.* = .{ .ctx = ctx, .h = h, .pool = pool, .source = source, .file = file, .ns = ns };
    // kernel block 0 = the root proof body; sealed in finish().
    try p.low_blocks.append(ctx.arena, .{
        .parent = null,
        .label = try ctx.interner.internString("proof"),
        .kind = .root,
        .first_step = 0,
        .last_step = 0,
    });
    try p.ordinal_block.append(ctx.arena, @enumFromInt(0));
    return p;
}

fn elab(self: *Prove, w: *const Walk) Elab {
    var e = Elab.init(self.ctx.arena, self.ctx.io, self.ctx.interner, &self.ctx.idents, self.pool, self.ctx.sink, self.source, w, self.ns, &self.fresh_counter);
    e.schema_args = self.schema_args; // null in an ordinary proof; set for a schema instance
    e.model = self.model; // .universe (identity) in an ordinary proof; M for a model transfer
    e.tccs = &self.pending_tccs; // refined-sort obligation sink (Step 3c)
    e.result_facts = &self.result_facts;
    return e;
}

// -- small utilities -------------------------------------------------------------------

fn text(self: *const Prove, tok: lexer.Token) []const u8 {
    return self.source[tok.start..tok.end];
}

/// A stamped token's interned name — the parser stamped every engine-parsed token, so past
/// parsing names are integers, never re-derived from source text.
fn tokName(tok: lexer.Token) StrId {
    std.debug.assert(tok.name != InternPool.Index.none);
    return tok.name;
}

/// A stamped name in a LOCAL-only position (step label, step/block ref, proof binder):
/// a `ns.`-qualified token is rejected — matching only its base name would let `x.y`
/// falsely resolve to a local `y`.
fn localName(self: *Prove, tok: lexer.Token) Error!StrId {
    if (tok.qualifier != InternPool.Index.none) {
        return self.fail(tok.start, "'{s}' cannot be namespace-qualified here", .{self.text(tok)});
    }
    return tokName(tok);
}

fn fail(self: *Prove, offset: u32, comptime fmt: []const u8, args: anytype) Error {
    self.ctx.sink.add(offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
}

fn freshNamed(self: *Prove, prefix: []const u8) Error!StrId {
    self.fresh_counter += 1;
    const s = std.fmt.allocPrint(self.ctx.arena, "{s}#{d}", .{ prefix, self.fresh_counter }) catch return error.OutOfMemory;
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

fn renderTerm(self: *Prove, id: TermId) Error![]const u8 {
    return @import("../../print.zig").render(self.ctx.arena, self.pool, self.ctx.interner, id) catch error.OutOfMemory;
}

fn sortName(self: *const Prove, sort: SortId) []const u8 {
    if (sort == Elab.prop_sort) return "Prop";
    return self.ctx.interner.sortName(@enumFromInt(@intFromEnum(sort)));
}

// -- global demand resolution (shared with ProveTask's formula pass) -------------------

/// Resolve one read-pass candidate set against the KV tables, racking Fetch/Prove tasks
/// for absent names. Returns a blocker to suspend on, or null when the whole closure is
/// resolved "enough" to process (proven/done, or in_flight-SELF — the latter is left for
/// process to diagnose as a self-citation). IDEMPOTENT — re-runs on every resume.
pub fn resolveRefs(ctx: *Context, h: *Engine.Handle, file: InternPool.Index, ns: InternPool.Index, refs: []const RefScan.Ref) Allocator.Error!?Engine.TaskIndex {
    var blocker: ?Engine.TaskIndex = null;
    for (refs) |r| {
        // a QUALIFIED candidate resolves its import first; until the import is done we
        // cannot even name the target namespace — block on it (the base resolves on a
        // later resume).
        var target_file = file;
        var target_ns = ns;
        if (r.ns) |ns_name| {
            const state = ctx.idents.lookup(ctx.io, .{ .namespace = ns, .name = ns_name }) orelse {
                blocker = try h.rackIndexed(try FetchTask.new(ctx.arena, .{ .file = file, .name = ns_name, .loc = r.loc, .loc_file = file }));
                continue;
            };
            switch (state) {
                .in_flight => |owner| {
                    if (owner != h.self_index) blocker = owner;
                    continue;
                },
                .done => |ix| switch (ctx.interner.keyOf(ix)) {
                    .import => |m| {
                        target_ns = m.namespace;
                        target_file = ctx.interner.keyOf(m.namespace).namespace.file;
                    },
                    else => continue, // not a namespace — elaboration diagnoses
                },
            }
        }
        switch (r.domain) {
            // a schema resolves via IdentKV like an identifier (a FetchTask mints its
            // locator); the instantiate handler then demands the instance FACT separately.
            .ident, .schema => {
                const state = ctx.idents.lookup(ctx.io, .{ .namespace = target_ns, .name = r.name }) orelse {
                    // loc is in the DEMANDING file (`file`); the fetch targets `target_file`.
                    blocker = try h.rackIndexed(try FetchTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file }));
                    continue;
                };
                switch (state) {
                    .in_flight => |owner| {
                        if (owner != h.self_index) blocker = owner;
                    },
                    .done => {},
                }
            },
            // a model name resolves via IdentKV too, but its producer is a ModelTask (which
            // builds the overlay), not a FetchTask.
            .model => {
                const state = ctx.idents.lookup(ctx.io, .{ .namespace = target_ns, .name = r.name }) orelse {
                    blocker = try h.rackIndexed(try ModelTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file }));
                    continue;
                };
                switch (state) {
                    .in_flight => |owner| {
                        if (owner != h.self_index) blocker = owner;
                    },
                    .done => {},
                }
            },
            .fact => {
                const state = ctx.facts.lookup(ctx.io, .{ .namespace = target_ns, .name = r.name }) orelse {
                    blocker = try h.rackIndexed(try ProveTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file }));
                    continue;
                };
                switch (state) {
                    .in_flight => |owner| {
                        if (owner != h.self_index) blocker = owner;
                    },
                    .proven => {},
                }
            },
        }
    }
    return blocker;
}

// -- the Walk driver seam --------------------------------------------------------------

pub fn readPass(self: *Prove, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!?Engine.TaskIndex {
    _ = block;
    var scanner = RefScan.init(self.ctx.arena, self.ctx.interner, self.source, w);
    scanner.schema_params = self.schema_params; // skip param names when driving a schema instance
    const refs = try scanner.scanStep(step);
    if (try resolveRefs(self.ctx, self.h, self.file, self.ns, refs)) |blocker| return blocker;

    // an `instantiate` step additionally DEMANDS the monomorphized instance FACT (its own
    // ProveTask) — the schema name + args are now resolved, so build the instance and
    // suspend until it's proved. `process`/`lowerInstantiate` then just looks it up.
    if (step.body == .claim) {
        const c = step.body.claim;
        if (c.rule.name == InternPool.RuleStr.instantiation.id()) {
            var e = self.elab(w);
            switch (try self.demandInstance(&e, c)) {
                .proven => return null, // ready — process can run lowerInstantiate
                .blocked => |t| return t,
                .failed => return null, // diagnosed; process will re-hit .failed and reject
            }
        }
        // a `[by model(M) src.thm]` step DEMANDS the transferred fact (its own ProveTask in
        // (M, src_file)); the model name resolved above, so demand the transfer + suspend.
        if (c.rule.name == InternPool.RuleStr.model.id()) {
            switch (try self.demandTransfer(c)) {
                .proven => return null,
                .blocked => |t| return t,
                .failed => return null,
            }
        }
        // an ACCELERANT step (`using <accel> …`) DEMANDS its generated synthetic-schema
        // instance; the shared `demandUsing` builds+registers the schema (idempotent) and
        // racks the instance ProveTask. RE-ENTRANT: first pass racks + suspends.
        if (c.kind == .using and isAccelerant(c.rule.name)) {
            var e = self.elab(w);
            const goal_typed = elaborateGoal(&e, c.formula) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => return null, // diagnosed; process re-hits + rejects
            };
            switch (try self.demandUsing(w, &e, goal_typed, c)) {
                .proven => return null,
                .blocked => |t| return t,
                .failed => return null,
            }
        }
    }
    return null;
}

pub fn process(self: *Prove, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!bool {
    self.processInner(w, step, block) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return false,
    };
    return true;
}

fn processInner(self: *Prove, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Error!void {
    const kb = self.kernelBlock(block);
    const label = try self.localName(step.label);
    switch (step.body) {
        .claim => |c| {
            const tcc_start = self.pending_tccs.items.len;
            var e = self.elab(w);
            const f = try e.requireProp(try e.elaborateExpr(c.formula), c.formula);
            const just = try self.lowerJustification(w, &e, kb, f.id, c);
            try self.dischargeTccs(kb, tcc_start);
            try self.appendMainStep(w, .{
                .formula = f.id,
                .just = just,
                .block = kb,
                .label = label,
                .loc = step.label.start,
            });
        },
        .assume => |blk| {
            const tcc_start = self.pending_tccs.items.len;
            var e = self.elab(w);
            const f = try e.requireProp(try e.elaborateExpr(blk.formula), blk.formula);
            try self.dischargeTccs(kb, tcc_start);
            try self.newBlock(w, label, kb, .{ .assume = f.id });
        },
        .fix => |blk| {
            const b = try self.bindProofVar(w, .{ .name = blk.name, .sort = blk.sort });
            try self.newBlock(w, label, kb, .{ .fix = .{ .v = b.v, .guard = b.guard } });
        },
        .unpack => |blk| {
            const source_ref = try self.resolveStepRef(w, blk.from);
            const b = try self.bindProofVar(w, .{ .name = blk.name, .sort = blk.sort });
            try self.newBlock(w, label, kb, .{ .unpack = .{ .v = b.v, .source = source_ref } });
        },
        .case => |c| {
            var e = self.elab(w);
            const goal = try e.requireProp(try e.elaborateExpr(c.goal), c.goal);
            const disj = try self.resolveStepRef(w, c.disj);
            const disj_formula = self.low_steps.items[@intFromEnum(disj.id)].formula;
            const node = self.pool.get(disj_formula);
            if (node != .bin or node.bin.op != .or_op) {
                return self.fail(step.label.start, "case: 'on' step is '{s}', not a disjunction", .{try self.renderTerm(disj_formula)});
            }
            if (c.arms.len < 2) {
                return self.fail(step.label.start, "case over a disjunction needs at least two arms", .{});
            }
            // the arm blocks walk as siblings (assume-shaped); caseConclude assembles the
            // (possibly nested, for N>2) or_elim tree over the disjunction structure.
            try self.case_stack.append(self.ctx.arena, .{ .goal = goal.id, .disj = disj, .loc = step.label.start });
        },
    }
}

/// The `case` step's conclusion, after both arm blocks walked: emit the or_elim step.
pub fn caseConclude(self: *Prove, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!bool {
    self.caseConcludeInner(w, step, block) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return false,
    };
    return true;
}

fn caseConcludeInner(self: *Prove, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Error!void {
    const c = step.body.case;
    const cc = self.case_stack.pop().?;
    const kb = self.kernelBlock(block);
    // resolve each arm's walked assume-block (each assumes its disjunct + concludes goal).
    const arm_blocks = try self.ctx.arena.alloc(kernel.BRef, c.arms.len);
    for (c.arms, arm_blocks) |arm, *out| out.* = try self.resolveBlockRef(w, arm.label);

    const disj_formula = self.low_steps.items[@intFromEnum(cc.disj.id)].formula;
    const just = try self.emitCaseTree(kb, cc.loc, cc.disj, disj_formula, arm_blocks, cc.goal);
    try self.appendMainStep(w, .{
        .formula = cc.goal,
        .just = just,
        .block = kb,
        .label = try self.localName(step.label),
        .loc = cc.loc,
    });
}

/// Build the (possibly nested) or_elim justification for a `case` over a LEFT-NESTED
/// disjunction. `disj_ref`/`disj_formula` are the disjunction step + its term; `arms` are
/// the walked arm assume-blocks, one per disjunct, in left-to-right disjunct order.
///   - 2 arms: one `or_elim{disj, arms[0], arms[1]}`.
///   - N>2: the disjunction is `LHS or arms[N-1]` where LHS is the (N-1)-way nested
///     disjunction; build a SYNTHETIC block that assumes LHS, re-derives it as a
///     hypothesis, recurses over `arms[0..N-1]` inside it, concludes the goal, and the
///     top or_elim uses that synthetic block as its left, `arms[N-1]` as its right.
/// (Ported from the eager Prover's emitCaseTree, retargeted to synthetic blocks.)
fn emitCaseTree(self: *Prove, parent: kernel.BlockId, loc: u32, disj_ref: kernel.SRef, disj_formula: TermId, arms: []const kernel.BRef, goal: TermId) Error!kernel.Justification {
    const node = self.pool.get(disj_formula);
    if (node != .bin or node.bin.op != .or_op) {
        return self.fail(loc, "case: 'on' step is '{s}', not a disjunction", .{try self.renderTerm(disj_formula)});
    }
    std.debug.assert(arms.len >= 2);
    if (arms.len == 2) {
        return .{ .or_elim = .{ .disj = disj_ref, .left = arms[0], .right = arms[1] } };
    }
    // N>2: left = a synthetic block over the nested LHS disjunction.
    const lhs = node.bin.lhs; // the (N-1)-way disjunction
    const lb = try self.newSyntheticBlock(try self.freshNamed("case"), parent, .{ .assume = lhs });
    // step 1: the assumed LHS disjunction, as this block's hypothesis.
    const hyp = try self.emitSynthetic(lb, loc, lhs, .{ .hypothesis = .{ .id = lb, .loc = loc } });
    // step 2: recurse — an or_elim over `hyp` splitting the first N-1 arms into the goal.
    const inner = try self.emitCaseTree(lb, loc, hyp, lhs, arms[0 .. arms.len - 1], goal);
    _ = try self.emitSynthetic(lb, loc, goal, inner);
    self.closeSyntheticBlock(lb);
    return .{ .or_elim = .{
        .disj = disj_ref,
        .left = .{ .id = lb, .loc = loc },
        .right = arms[arms.len - 1],
    } };
}

/// A block descoped: seal its kernel step range (same closing the eager path did).
pub fn exitBlock(self: *Prove, w: *Walk, block: Walk.BlockOrdinal) Allocator.Error!void {
    _ = w;
    const kb = self.kernelBlock(block);
    const blk = &self.low_blocks.items[@intFromEnum(kb)];
    blk.last_step = @intCast(self.low_steps.items.len);
    if (std.debug.runtime_safety) {
        // every step in the range must belong to this block's subtree
        const self_idx = @intFromEnum(kb);
        var i: usize = blk.first_step;
        while (i < blk.last_step) : (i += 1) {
            var bi = @intFromEnum(self.low_steps.items[i].block);
            while (bi > self_idx) {
                bi = @intFromEnum(self.low_blocks.items[bi].parent.?);
            }
            std.debug.assert(bi == self_idx);
        }
    }
}

// -- lowering pieces -------------------------------------------------------------------

fn kernelBlock(self: *const Prove, ord: Walk.BlockOrdinal) kernel.BlockId {
    return self.ordinal_block.items[@intFromEnum(ord)];
}

/// Append the walked step's MAIN kernel step and record its ordinal (Walk assigns the
/// matching StepOrdinal in bindStepLabel right after process returns — asserted aligned).
fn appendMainStep(self: *Prove, w: *const Walk, step: kernel.Step) Error!void {
    std.debug.assert(w.next_step == self.ordinal_step.items.len);
    const id: kernel.StepId = @enumFromInt(self.low_steps.items.len);
    try self.low_steps.append(self.ctx.arena, step);
    try self.ordinal_step.append(self.ctx.arena, id);
}

/// Append a SYNTHETIC kernel step (multi-arg forall_elim intermediate) — no ordinal.
fn emitSynthetic(self: *Prove, kb: kernel.BlockId, loc: u32, formula: TermId, just: kernel.Justification) Error!kernel.SRef {
    const id: kernel.StepId = @enumFromInt(self.low_steps.items.len);
    try self.low_steps.append(self.ctx.arena, .{
        .formula = formula,
        .just = just,
        .block = kb,
        .label = try self.freshNamed("simplify"),
        .loc = loc,
    });
    return .{ .id = id, .loc = loc };
}

/// Create the kernel block for a walked block step and record its ordinal (Walk assigns
/// the matching BlockOrdinal in enterBlock right after process returns — asserted).
fn newBlock(self: *Prove, w: *const Walk, label: StrId, parent: kernel.BlockId, kind: kernel.Block.Kind) Error!void {
    std.debug.assert(w.next_block == self.ordinal_block.items.len);
    const id: kernel.BlockId = @enumFromInt(self.low_blocks.items.len);
    try self.low_blocks.append(self.ctx.arena, .{
        .parent = parent,
        .label = label,
        .kind = kind,
        .first_step = @intCast(self.low_steps.items.len),
        .last_step = 0,
    });
    try self.ordinal_block.append(self.ctx.arena, id);
}

/// Create a SYNTHETIC kernel block (no Walk counterpart, so no ordinal record) and return
/// its id — for the nested or_elim spine of an N-arm `case`. `first_step` opens at the
/// current step count; seal with `closeSyntheticBlock`.
fn newSyntheticBlock(self: *Prove, label: StrId, parent: kernel.BlockId, kind: kernel.Block.Kind) Error!kernel.BlockId {
    const id: kernel.BlockId = @enumFromInt(self.low_blocks.items.len);
    try self.low_blocks.append(self.ctx.arena, .{
        .parent = parent,
        .label = label,
        .kind = kind,
        .first_step = @intCast(self.low_steps.items.len),
        .last_step = 0,
    });
    return id;
}

/// Seal a synthetic block's step range (its `last_step`). Call after emitting its steps.
fn closeSyntheticBlock(self: *Prove, id: kernel.BlockId) void {
    self.low_blocks.items[@intFromEnum(id)].last_step = @intCast(self.low_steps.items.len);
}

const BoundVar = struct { v: term.Node.Fvar, guard: ?TermId };

/// A fix/unpack binder: resolve its (possibly refined/inline-`where`) sort, mint the
/// hygienic fvar at the CARRIER, and — for a refined sort — build its guard `inH(v)`
/// (conjoined over multiple qualifiers). The fvar (carrier sort) goes to the Walk via
/// pending_binder; the guard is returned for the block's `fix.guard` slot ([by predicate]
/// surfaces it; forall_intro makes it the antecedent).
fn bindProofVar(self: *Prove, w: *Walk, b: ast.Binder) Error!BoundVar {
    const name = try self.localName(b.name);
    if (w.findIdent(name) != null) {
        return self.fail(b.name.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(b.name)});
    }
    var e = self.elab(w);
    const refined = try e.resolveBinderSort(b); // handles inline `S where inH`
    const sort: SortId = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(refined)))));
    const quals = self.ctx.interner.qualifiersOf(self.ctx.arena, @enumFromInt(@intFromEnum(refined))) catch return error.OutOfMemory;
    const fvar = try self.freshNamed(self.text(b.name));
    w.pending_binder = .{ .sort = sort, .fvar = fvar };
    // build the guard over the fresh fvar (conjunction if multiple qualifiers).
    var guard: ?TermId = null;
    for (quals) |qpred| {
        const fv = try self.pool.add(.{ .fvar = .{ .name = fvar, .sort = sort } });
        const app = try self.pool.addApp(.pred, @enumFromInt(@intFromEnum(qpred)), &.{fv});
        guard = if (guard) |prev| try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = prev, .rhs = app } }) else app;
    }
    return .{ .v = .{ .name = fvar, .sort = sort }, .guard = guard };
}

// -- refined-sort obligation discharge (Step 3c) ---------------------------------------

/// Discharge the obligations accrued since `start` (a guarded application over a refined
/// param demands `inH(arg)`), proving each against the LOCAL proof context. On any failure
/// records "unproved obligation" and rejects. Obligations discharged here also mark their
/// discharging step reachable (so the use-all-facts pass doesn't flag it dead).
fn dischargeTccs(self: *Prove, kb: kernel.BlockId, start: usize) Error!void {
    var any_failed = false;
    for (self.pending_tccs.items[start..]) |t| {
        if (!self.tccDischarged(kb, t.formula)) {
            self.ctx.sink.add(t.loc, "unproved obligation: '{s}'", .{try self.renderTerm(t.formula)}) catch return error.OutOfMemory;
            any_failed = true;
        }
    }
    self.pending_tccs.shrinkRetainingCapacity(start);
    if (start == 0) self.result_facts.clearRetainingCapacity();
    if (any_failed) return error.Recover;
}

/// True if obligation `f` follows from the LOCAL context. Peels `->`/`and`/`forall` (adding
/// antecedents as local hypotheses, monomorphizing `forall` at a fresh fvar) and matches
/// each atom against: result_facts (surfaced closures), enclosing block guards/assumes, and
/// prior in-scope steps. NO global-statement scan — the demand model has no "all facts" set
/// (the plan's fetch-only mandate); an obligation needing a global fact goes red for now.
fn tccDischarged(self: *Prove, kb: kernel.BlockId, formula: TermId) bool {
    var hyps: std.ArrayList(TermId) = .empty;
    return self.tccDischargedHyps(kb, formula, &hyps);
}

fn tccDischargedHyps(self: *Prove, kb: kernel.BlockId, formula: TermId, hyps: *std.ArrayList(TermId)) bool {
    var f = formula;
    while (true) {
        for (hyps.items) |h| if (self.pool.alphaEq(h, f)) return true;
        if (self.tccMatches(kb, f)) return true;
        const node = self.pool.get(f);
        if (node == .bin and node.bin.op == .implies) {
            hyps.append(self.ctx.arena, node.bin.lhs) catch return false;
            f = node.bin.rhs;
            continue;
        }
        if (node == .bin and node.bin.op == .and_op) {
            return self.tccDischargedHyps(kb, node.bin.lhs, hyps) and self.tccDischargedHyps(kb, node.bin.rhs, hyps);
        }
        if (node == .quant and node.quant.q == .forall) {
            const fresh = self.freshNamed("obl") catch return false;
            const fv = self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } }) catch return false;
            f = self.pool.open(node.quant.body, fv) catch return false;
            continue;
        }
        return false;
    }
}

/// Produce a PROVEN step whose formula is the guard `g`, and return its SRef — for
/// auto-discharging a refined-sort `forall_elim`'s guard (`good(t)`). Sources, in order:
///   (1) a prior in-scope step already asserting `g` → cite it directly (no new step);
///   (2) an enclosing fix-block whose guard is `g` → emit a `[by predicate]` (hypothesis)
///       step over that block;
/// Returns null if `g` isn't dischargeable this way (the caller falls back to the plain,
/// guard-leaking elim). (Composite-closure discharge — applying a closure axiom, recursing
/// — is a later extension.)
fn emitDischargeStep(self: *Prove, kb: kernel.BlockId, loc: u32, g: TermId) Error!?kernel.SRef {
    // (1) an accessible prior step already proves g.
    for (self.low_steps.items, 0..) |s, i| {
        if (!lowAncestorOrSelf(self.low_blocks.items, s.block, kb)) continue;
        if (self.pool.alphaEq(s.formula, g)) return .{ .id = @enumFromInt(i), .loc = loc };
    }
    // (2) an enclosing fix-block's guard is g → restate it via [by predicate] (hypothesis).
    var cur: ?kernel.BlockId = kb;
    while (cur) |c| {
        const b = self.low_blocks.items[@intFromEnum(c)];
        if (b.kind == .fix) if (b.kind.fix.guard) |bg| {
            if (self.pool.alphaEq(bg, g)) {
                return try self.emitSynthetic(kb, loc, g, .{ .hypothesis = .{ .id = c, .loc = loc } });
            }
        };
        cur = b.parent;
    }
    return null;
}

fn tccMatches(self: *Prove, kb: kernel.BlockId, f: TermId) bool {
    for (self.result_facts.items) |fact| if (self.pool.alphaEq(fact, f)) return true;
    // enclosing block guards (fix) + assumptions, walking to the root.
    var cur: ?kernel.BlockId = kb;
    while (cur) |c| {
        const b = self.low_blocks.items[@intFromEnum(c)];
        switch (b.kind) {
            .assume => |a| if (self.pool.alphaEq(a, f)) return true,
            .fix => |fx| if (fx.guard) |g| {
                if (self.pool.alphaEq(g, f)) return true;
            },
            else => {},
        }
        cur = b.parent;
    }
    // prior in-scope proof steps.
    for (self.low_steps.items, 0..) |s, i| {
        if (!lowAncestorOrSelf(self.low_blocks.items, s.block, kb)) continue;
        if (self.pool.alphaEq(s.formula, f)) {
            self.extra_reachable_steps.append(self.ctx.arena, @intCast(i)) catch {};
            return true;
        }
    }
    return false;
}

fn lowAncestorOrSelf(blocks: []const kernel.Block, a: kernel.BlockId, b: kernel.BlockId) bool {
    var cur: ?kernel.BlockId = b;
    while (cur) |c| {
        if (c == a) return true;
        cur = blocks[@intFromEnum(c)].parent;
    }
    return false;
}

// -- reference resolution --------------------------------------------------------------

/// A kernel-rule step reference: LOCAL-only (a live label in the walk's scope).
fn resolveStepRef(self: *Prove, w: *const Walk, tok: lexer.Token) Error!kernel.SRef {
    const name = try self.localName(tok);
    const target = w.resolveStep(name) orelse {
        // nicety: a global fact cited where a step label belongs
        if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = self.ns, .name = name }) != null) {
            return self.fail(tok.start, "'{s}' is a fact, not a proof step; introduce it as a step first with `[by axiom {s}]` or `[by theorem {s}]`, then reference that step", .{
                self.text(tok), self.text(tok), self.text(tok),
            });
        }
        return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
    };
    return switch (target) {
        .step => |ord| .{ .id = self.ordinal_step.items[@intFromEnum(ord)], .loc = tok.start },
        .block => self.fail(tok.start, "'{s}' names a subproof; a step reference is required", .{self.text(tok)}),
    };
}

fn resolveBlockRef(self: *Prove, w: *const Walk, tok: lexer.Token) Error!kernel.BRef {
    const name = try self.localName(tok);
    const target = w.resolveStep(name) orelse {
        return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
    };
    return switch (target) {
        .block => |ord| .{ .id = self.kernelBlock(ord), .loc = tok.start },
        .step => self.fail(tok.start, "'{s}' names a step; a subproof reference is required", .{self.text(tok)}),
    };
}

/// An axiom/theorem citation: GLOBAL fact via FactKV (the read pass made it proven, or
/// left an in_flight-self / failed entry — diagnosed here).
fn resolveFactRef(self: *Prove, tok: lexer.Token) Error!InternPool.Index {
    const ns = try self.resolveQualifier(tok);
    const state = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = tokName(tok) }) orelse {
        return self.fail(tok.start, "unknown statement '{s}'", .{self.text(tok)});
    };
    return switch (state) {
        // in a model transfer, a source-axiom citation remaps (via the overlay) to its
        // discharging LOCAL fact — an obligation. `.universe` = identity (ordinary proof).
        .proven => |ix| self.ctx.interner.applyModel(self.model, ix),
        .in_flight => self.fail(tok.start, "cites '{s}', whose proof has not completed (self-citation or a failed/cyclic dependency)", .{self.text(tok)}),
    };
}

/// The namespace a (possibly `ns.`-qualified) stamped token resolves in: unqualified =
/// this proof's ns; qualified = the import named by `tok.qualifier`. (Multi-level
/// qualification was diagnosed at parse — the stamped qualifier is at most one level.)
fn resolveQualifier(self: *Prove, tok: lexer.Token) Error!InternPool.Index {
    if (tok.qualifier == InternPool.Index.none) return self.ns;
    const qtext = self.ctx.interner.stringBytes(tok.qualifier);
    const state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tok.qualifier }) orelse {
        return self.fail(tok.start, "unknown namespace '{s}'", .{qtext});
    };
    return switch (state) {
        .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
            .import => |m| m.namespace,
            else => self.fail(tok.start, "'{s}' is not a namespace", .{qtext}),
        },
        .in_flight => self.fail(tok.start, "unknown namespace '{s}'", .{qtext}),
    };
}

// -- schema instantiation --------------------------------------------------------------

/// A resolved schema reference: the schema's file/namespace + its AST decl. Reachable only
/// after the read pass resolved the `.schema` locator to `done`.
const ResolvedSchema = struct {
    file: InternPool.Index,
    ns: InternPool.Index,
    name: StrId, // the schema's name (keys the AST registry + the instance payload)
    decl: ast.Decl, // the `.schema` decl (from the by-name registry)
    source: []const u8,
};

/// Resolve a schema name token (optionally `ns.`-qualified) to its file/ns + AST decl.
/// The `.schema` locator must be `done` in IdentKV (the read pass guarantees it); the decl
/// itself comes from the by-name AST registry (so a synthetic schema resolves too).
fn resolveSchemaRef(self: *Prove, tok: lexer.Token) Error!ResolvedSchema {
    const ns = try self.resolveQualifier(tok);
    const st = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = ns, .name = tokName(tok) }) orelse
        return self.fail(tok.start, "unknown schema '{s}'", .{self.text(tok)});
    const ix = switch (st) {
        .done => |x| x,
        .in_flight => return self.fail(tok.start, "unknown schema '{s}'", .{self.text(tok)}),
    };
    const loc = switch (self.ctx.interner.keyOf(ix)) {
        .schema => |s| s,
        else => return self.fail(tok.start, "'{s}' is not a schema", .{self.text(tok)}),
    };
    const fid = self.ctx.pool_file.get(loc.file).?;
    const decl = self.ctx.declOf(fid, loc.name) orelse
        return self.fail(tok.start, "internal: schema '{s}' locator has no decl", .{self.text(tok)});
    return .{
        .file = loc.file,
        .ns = ns,
        .name = loc.name,
        .decl = decl.*,
        .source = self.ctx.files.items[@intFromEnum(fid)].source,
    };
}

/// Elaborate the instantiation args in the CALLER's Elab `e` (caller scope + ns, so args
/// may reference caller-local binders), binding each schema param to a `Schema.SchemaArg`.
/// A value param → the elaborated arg term; an N-ary param → a lambda arg (or a bare
/// symbol eta-expanded). Sort tokens resolve in the SCHEMA's ns via a schema-scoped Elab.
fn bindSchemaArgs(self: *Prove, e: *Elab, rs: ResolvedSchema, c: ast.Step.Claim) Error!*Schema.SchemaArgs {
    const params = rs.decl.schema.params;
    if (c.args.len != params.len) {
        return self.fail(c.schema.?.start, "schema '{s}' expects {d} argument(s), got {d}", .{
            self.text(c.schema.?), params.len, c.args.len,
        });
    }
    // a schema-scoped Elab to resolve param SORT tokens in the schema's ns. Under a model
    // TRANSFER it is model-aware, so a param sort `Elem` remaps to its target (`Num`) —
    // matching the caller's already-remapped lambda args.
    var empty_walk = Walk.init(self.ctx.arena, self.ctx.interner, rs.source, self.ctx.sink);
    var se = Elab.init(self.ctx.arena, self.ctx.io, self.ctx.interner, &self.ctx.idents, self.pool, self.ctx.sink, rs.source, &empty_walk, rs.ns, &self.fresh_counter);
    se.model = self.model;

    const args = try self.ctx.arena.create(Schema.SchemaArgs);
    args.* = .empty;
    for (params, c.args) |p, arg_expr| {
        const pname = tokName(p.name);
        if (p.arg_sorts.len == 0) {
            // VALUE param: elaborate the arg at the use site; sort-check vs the param sort.
            const want = try se.resolveSortTok(p.result);
            const typed = try e.elaborateExpr(arg_expr);
            const want_carrier = self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(want)));
            const got_carrier = if (typed.sort == Elab.prop_sort) @intFromEnum(typed.sort) else @intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort))));
            if (@intFromEnum(want_carrier) != got_carrier) {
                return self.fail(Elab.exprLoc(arg_expr), "expected sort '{s}', got '{s}'", .{
                    self.ctx.interner.sortName(@enumFromInt(@intFromEnum(want))), self.sortName(typed.sort),
                });
            }
            try args.put(self.ctx.arena, pname, .{ .value = .{ .id = typed.id, .sort = want } });
        } else {
            // N-ary GENERATOR param: a lambda arg (or a bare symbol → eta-expand).
            const arg_sorts = try self.ctx.arena.alloc(SortId, p.arg_sorts.len);
            for (p.arg_sorts, arg_sorts) |st, *out| out.* = try se.resolveSortTok(st);
            const result_sort = try se.resolveSortTok(p.result);
            const lam = try self.bindLambdaArg(e, arg_expr, arg_sorts, result_sort);
            try args.put(self.ctx.arena, pname, lam);
        }
    }
    return args;
}

/// Bind an N-ary generator param's argument: a `fun x.. => body` lambda (binders bound as
/// fresh KEPT-FREE fvars, body elaborated with them in `e.scope`), or a bare symbol of the
/// signature (eta-expanded to `fun x.. => sym(x..)`). Terms build in `self.pool`.
fn bindLambdaArg(self: *Prove, e: *Elab, arg_expr: *const ast.Expr, arg_sorts: []const SortId, result_sort: SortId) Error!Schema.SchemaArg {
    switch (arg_expr.*) {
        .lambda => |l| {
            if (l.binders.len != arg_sorts.len) {
                return self.fail(l.tok.start, "schema parameter expects a {d}-argument lambda, got {d}", .{ arg_sorts.len, l.binders.len });
            }
            const fresh = try self.ctx.arena.alloc(StrId, l.binders.len);
            const scope_mark = e.scopeMark();
            for (l.binders, arg_sorts, fresh) |b, asort, *fr| {
                const bsort = try e.resolveSortTok(b.sort);
                if (@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(bsort)))) != @intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(asort))))) {
                    return self.fail(b.sort.start, "expected sort '{s}', got '{s}'", .{ self.sortName(asort), self.sortName(bsort) });
                }
                fr.* = try self.freshNamed(self.ctx.interner.stringBytes(tokName(b.name)));
                try e.pushBinder(tokName(b.name), asort, fr.*);
            }
            const body = try e.elaborateExpr(l.body);
            e.scopeTruncate(scope_mark);
            if (@intFromEnum(body.sort) != @intFromEnum(result_sort)) {
                return self.fail(Elab.exprLoc(l.body), "expected sort '{s}', got '{s}'", .{ self.sortName(result_sort), self.sortName(body.sort) });
            }
            return .{ .lambda = .{ .body = body.id, .params = fresh, .arg_sorts = arg_sorts, .result_sort = result_sort } };
        },
        .name => |tok| {
            // eta-sugar: a bare symbol `p` of the signature → `fun x.. => p(x..)`.
            const fresh = try self.ctx.arena.alloc(StrId, arg_sorts.len);
            const fvars = try self.ctx.arena.alloc(TermId, arg_sorts.len);
            for (arg_sorts, fresh, fvars) |asort, *fr, *fv| {
                fr.* = try self.freshNamed("eta");
                fv.* = try self.pool.add(.{ .fvar = .{ .name = fr.*, .sort = asort } });
            }
            const applied = try self.etaApply(e, tok, fvars, result_sort);
            return .{ .lambda = .{ .body = applied, .params = fresh, .arg_sorts = arg_sorts, .result_sort = result_sort } };
        },
        else => return self.fail(Elab.exprLoc(arg_expr), "schema parameter requires a lambda or a bare symbol", .{}),
    }
}

/// Build `sym(fvars…)` for eta-expansion, resolving `sym` in the caller ns and checking it
/// is a func/pred of the right result sort.
fn etaApply(self: *Prove, e: *Elab, tok: lexer.Token, fvars: []const TermId, result_sort: SortId) Error!TermId {
    _ = result_sort;
    // reuse the caller Elab's call machinery by synthesizing a call expr is awkward; apply
    // directly via IdentKV lookup. (A qualified bare symbol was never supported here —
    // matching only its base name could falsely hit a local, so reject.)
    const name = try self.localName(tok);
    const sym = e.lookupIdentPub(self.ns, name) orelse
        return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
    const kind: term.AppKind = switch (self.ctx.interner.keyOf(sym)) {
        .pred => .pred,
        .func, .constant => .app,
        else => return self.fail(tok.start, "'{s}' is not a symbol", .{self.text(tok)}),
    };
    return self.pool.addApp(kind, @enumFromInt(@intFromEnum(sym)), fvars);
}

/// Demand the monomorphized instance FACT for `[by instantiate schema(args)]`. Returns:
///   - `.proven`  → the instance fact Index (its formula copyIn's into the citing proof).
///   - `.blocked` → a TaskIndex to suspend on (the instance's ProveTask, just racked or
///                  already in flight). Called from the READ PASS.
/// Builds the payload idempotently (re-run on each wake); the hash keys FactKV dedup.
const InstanceOutcome = union(enum) { proven: InternPool.Index, blocked: Engine.TaskIndex, failed };

fn demandInstance(self: *Prove, e: *Elab, c: ast.Step.Claim) Allocator.Error!InstanceOutcome {
    const rs = self.resolveSchemaRef(c.schema.?) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    const args = self.bindSchemaArgs(e, rs, c) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    const params = rs.decl.schema.params;
    const schema_name = tokName(c.schema.?);
    // stable ordered param-name list for the hash + payload.
    const pnames = try self.ctx.arena.alloc(StrId, params.len);
    for (params, pnames) |p, *out| out.* = tokName(p.name);

    const hash = Schema.instanceHash(self.pool, schema_name, pnames, args);
    const inst_name_bytes = std.fmt.allocPrint(self.ctx.arena, "{s}{{{x}}}", .{ self.ctx.interner.stringBytes(schema_name), hash }) catch return error.OutOfMemory;
    const inst_name = self.ctx.interner.internString(inst_name_bytes) catch return error.OutOfMemory;
    // the instance is minted in the CURRENT model's namespace over the schema's file: an
    // instantiate inside a model TRANSFER monomorphizes UNDER that model (so the schema
    // body's source syms overlay-remap, matching the caller's remapped args). `.universe`
    // (an ordinary proof) → the plain (universe, src_file) instance.
    const inst_ns = self.ctx.interner.namespace(self.model, rs.file) catch return error.OutOfMemory;
    const key = FactKV.Key{ .namespace = inst_ns, .name = inst_name };

    if (self.ctx.facts.lookup(self.ctx.io, key)) |state| switch (state) {
        .proven => |ix| return .{ .proven = ix },
        .in_flight => |owner| {
            if (owner == self.h.self_index) {
                // demanding the very instance THIS task is proving — a self-cycle.
                self.ctx.sink.add(c.schema.?.start, "cyclic schema instantiation of '{s}'", .{self.text(c.schema.?)}) catch return error.OutOfMemory;
                return .failed;
            }
            return .{ .blocked = owner };
        },
    };
    // ABSENT: reify the args durably + rack the instance ProveTask.
    const durable = try self.ctx.arena.alloc(ProveTask.DurableArg, params.len);
    for (pnames, durable) |pname, *out| {
        const arg = args.get(pname).?;
        out.* = switch (arg) {
            .value => |v| .{ .value = .{ .off = try self.pool.reify(v.id, self.ctx.interner), .sort = v.sort } },
            .lambda => |l| .{ .lambda = .{ .off = try self.pool.reify(l.body, self.ctx.interner), .params = l.params, .arg_sorts = l.arg_sorts, .result_sort = l.result_sort } },
        };
    }
    const blocker = try self.h.rackIndexed(try ProveTask.new(self.ctx.arena, .{
        .file = rs.file,
        .name = inst_name,
        .loc = c.schema.?.start,
        .loc_file = self.file,
        .model = self.model, // monomorphize the schema body UNDER the transfer's model
        .instance = .{ .schema_name = rs.name, .params = pnames, .args = durable },
    }));
    return .{ .blocked = blocker };
}

/// The `instantiate` justification (in `process`, after the read pass demanded + proved the
/// instance fact): look it up, copyIn its formula, and emit `schema_instance` with the
/// caller's premise step-refs. The kernel peels the instance's `->` antecedents against the
/// premises and requires the final consequent == the citing claim.
fn lowerInstantiate(self: *Prove, w: *const Walk, e: *Elab, c: ast.Step.Claim) Error!kernel.Justification {
    if (c.schema == null) return self.fail(c.rule.start, "instantiate requires a schema name", .{});
    const outcome = try self.demandInstance(e, c);
    const fact = switch (outcome) {
        .proven => |ix| ix,
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: instantiate not resolved before process (read-pass bug)", .{}),
    };
    const formula_off = self.ctx.interner.keyOf(fact).fact.formula;
    const instance = try self.pool.copyIn(self.ctx.interner, formula_off);
    const premises = try self.ctx.arena.alloc(kernel.SRef, c.refs.len);
    for (c.refs, premises) |r, *out| out.* = try self.resolveStepRef(w, r);
    return .{ .schema_instance = .{ .instance = instance, .premises = premises } };
}

// -- model transfer --------------------------------------------------------------------

/// Demand the TRANSFERRED FACT for `[by model(M) src.thm]`: resolve M's `.model` Index
/// (read pass racked its ModelTask), split `src.thm` into (source file, name), and demand
/// that fact in namespace `(M, src_file)` — a ProveTask carrying `model = M` re-proves the
/// source theorem's proof with every global overlay-remapped. Returns the transferred fact
/// Index, or a blocker to suspend on. Called from the READ PASS (and re-checked in process).
fn demandTransfer(self: *Prove, c: ast.Step.Claim) Allocator.Error!InstanceOutcome {
    if (c.schema == null) {
        self.ctx.sink.add(c.rule.start, "model citation requires a model name: `[by model(M) src.thm]`", .{}) catch return error.OutOfMemory;
        return .failed;
    }
    if (c.refs.len != 1) {
        self.ctx.sink.add(c.rule.start, "`[by model(M) …]` cites exactly one transferred theorem", .{}) catch return error.OutOfMemory;
        return .failed;
    }
    // resolve M (a `.model` Index) in the CITING file's namespace. A model name is a
    // plain local identifier — a qualified one never resolved before and still doesn't
    // (the base-name lookup below would be wrong for it, so keep it a miss).
    const mtok = c.schema.?;
    if (mtok.qualifier != InternPool.Index.none) {
        self.ctx.sink.add(mtok.start, "unknown model '{s}'", .{self.text(mtok)}) catch return error.OutOfMemory;
        return .failed;
    }
    const mstate = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tokName(mtok) }) orelse {
        self.ctx.sink.add(mtok.start, "unknown model '{s}'", .{self.text(mtok)}) catch return error.OutOfMemory;
        return .failed;
    };
    const model_ix = switch (mstate) {
        .done => |ix| ix,
        .in_flight => |owner| return .{ .blocked = owner },
    };
    if (self.ctx.interner.keyOf(model_ix) != .model) {
        self.ctx.sink.add(mtok.start, "'{s}' is not a model", .{self.text(mtok)}) catch return error.OutOfMemory;
        return .failed;
    }
    // the qualifier of `src.thm` names the source file's import; the base is the theorem.
    const rtok = c.refs[0];
    if (rtok.qualifier == InternPool.Index.none) {
        self.ctx.sink.add(rtok.start, "`[by model(M) src.thm]` needs a qualified source theorem (e.g. `group.cancelLeft`)", .{}) catch return error.OutOfMemory;
        return .failed;
    }
    const base = tokName(rtok);
    const qtext = self.ctx.interner.stringBytes(rtok.qualifier);
    const imp_state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = rtok.qualifier }) orelse {
        self.ctx.sink.add(rtok.start, "unknown namespace '{s}'", .{qtext}) catch return error.OutOfMemory;
        return .failed;
    };
    const src_file = switch (imp_state) {
        .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
            .import => |imp| self.ctx.interner.keyOf(imp.namespace).namespace.file,
            else => {
                self.ctx.sink.add(rtok.start, "'{s}' is not a namespace", .{qtext}) catch return error.OutOfMemory;
                return .failed;
            },
        },
        .in_flight => |owner| return .{ .blocked = owner },
    };
    // demand the transferred fact in namespace (M, src_file).
    const tns = self.ctx.interner.namespace(model_ix, src_file) catch return error.OutOfMemory;
    if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = tns, .name = base })) |st| switch (st) {
        .proven => |ix| return .{ .proven = ix },
        .in_flight => |owner| {
            if (owner == self.h.self_index) {
                self.ctx.sink.add(rtok.start, "model transfer of '{s}' depends on itself", .{self.text(rtok)}) catch return error.OutOfMemory;
                return .failed;
            }
            return .{ .blocked = owner };
        },
    };
    const blocker = try self.h.rackIndexed(try ProveTask.new(self.ctx.arena, .{
        .file = src_file,
        .name = base,
        .loc = rtok.start,
        .loc_file = self.file,
        .model = model_ix,
    }));
    return .{ .blocked = blocker };
}

/// The `[by model(M) src.thm]` justification (in process, after the read pass proved the
/// transferred fact): copyIn its formula and cite it as a proven theorem. (The transferred
/// fact's formula is already in TARGET terms — proved under M's overlay.)
fn lowerModel(self: *Prove, w: *const Walk, c: ast.Step.Claim) Error!kernel.Justification {
    _ = w;
    const outcome = try self.demandTransfer(c);
    const fact = switch (outcome) {
        .proven => |ix| ix,
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: model transfer not resolved before process (read-pass bug)", .{}),
    };
    return .{ .theorem_ref = .{ .stmt = fact, .loc = c.refs[0].start } };
}

// -- the `using` accelerant framework --------------------------------------------------
// An accelerant (`using specialize …`, later `using tautology …`, …) is sugar for a
// GENERATED synthetic schema that the ordinary demand pipeline proves + the kernel
// re-checks. The re-entry-safe demand PLUMBING lives here ONCE (`demandUsing` / `lowerUsing`);
// each accelerant supplies only a PRODUCER (`produce*`) that builds the synthetic schema +
// the args/premises. See memory `accelerants-emit-ast`.

/// True for a `using` rule word that is an ACCELERANT (not the `instantiation`/`model`
/// engine words, which have their own handlers). Any non-RuleStr word reaching a `using`
/// step is an accelerant; `instantiation`/`model` are RuleStr but dispatched separately.
fn isAccelerant(rule: StrId) bool {
    return InternPool.RuleStr.of(rule) == null;
}

/// Elaborate an accelerant step's claim to its prop TermId (read-pass goal for the producer).
fn elaborateGoal(e: *Elab, formula: *const ast.Expr) Error!TermId {
    const f = try e.requireProp(try e.elaborateExpr(formula), formula);
    return f.id;
}

/// Demand the synthetic-schema INSTANCE fact for an accelerant step (read pass). Runs the
/// accelerant's producer, registers the synthetic schema (idempotently — falls through on
/// re-entry), and demands its instance via the schema path. Returns proven/blocked/failed
/// exactly like `demandInstance`. RE-ENTRANT: racks + suspends the first pass; on resume the
/// front gates (IdentKV for the schema, FactKV for the instance) skip the already-done work.
fn demandUsing(self: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Allocator.Error!InstanceOutcome {
    const syn = self.produceAccelerant(w, e, goal, c) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    } orelse return .failed; // producer diagnosed
    // register the synthetic decl + mint its `.schema` locator ONCE (both idempotent).
    const fid = self.ctx.pool_file.get(self.file).?;
    const decl_ptr = self.ctx.arena.create(ast.Decl) catch return error.OutOfMemory;
    decl_ptr.* = syn.decl;
    self.ctx.registerDecl(fid, decl_ptr) catch return error.OutOfMemory; // keep-first
    const schema_key = IdentKV.Key{ .namespace = self.ns, .name = syn.name };
    if (self.ctx.idents.lookup(self.ctx.io, schema_key) == null) {
        _ = self.ctx.idents.publish(self.ctx.io, schema_key, .{ .schema = .{
            .name = syn.name,
            .file = self.file,
            .loc = c.rule.start,
        } }) catch return error.OutOfMemory;
    }
    // demand the instance via the ordinary schema path, using a synthesized claim that names
    // the synthetic schema + carries the accelerant's args (premises ride c.refs separately).
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };
    const inst_c: ast.Step.Claim = .{
        .formula = c.formula,
        .kind = .using,
        .rule = c.rule,
        .schema = b.tok(syn.name),
        .args = syn.args,
        .refs = syn.premises,
    };
    return self.demandInstance(e, inst_c);
}

/// The `using <accelerant>` justification (process): the instance fact is proven (read pass);
/// emit `schema_instance` citing the accelerant's premise refs — the kernel peels the
/// instance's `->` antecedents against them and requires the final consequent == the claim.
fn lowerUsing(self: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!kernel.Justification {
    const outcome = try self.demandUsing(w, e, goal, c);
    const fact = switch (outcome) {
        .proven => |ix| ix,
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: accelerant instance not resolved before process (read-pass bug)", .{}),
    };
    const formula_off = self.ctx.interner.keyOf(fact).fact.formula;
    const instance = try self.pool.copyIn(self.ctx.interner, formula_off);
    // premises = the accelerant's own refs (the producer's premise order): the head-cite (if
    // the head is local) then the hyps, matching the synthetic body's antecedent order.
    const prems = try self.accelerantPremises(w, c);
    return .{ .schema_instance = .{ .instance = instance, .premises = prems } };
}

/// Dispatch to the accelerant's producer by rule name. Returns null if the producer
/// diagnosed (a Recover is mapped to null by the caller). Add new accelerants here.
fn produceAccelerant(self: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    _ = e;
    if (c.rule.name == try self.internStr("specialize")) return try self.produceSpecialize(w, goal, c);
    if (c.rule.name == try self.internStr("tautology")) return try self.produceTautology(w, goal, c);
    if (c.rule.name == try self.internStr("simplify")) return try self.produceSimplify(w, goal, c);
    if (c.rule.name == try self.internStr("simplify_quantified")) return try self.produceSimplifyQuantified(w, goal, c);
    if (c.rule.name == try self.internStr("chain")) return try self.produceChain(w, goal, c);
    return self.fail(c.rule.start, "unsupported by the demand prover: '{s}'", .{self.text(c.rule)});
}

/// The premise refs an accelerant's `schema_instance` discharges, in the synthetic body's
/// antecedent order. Each accelerant's body has a matching antecedent order:
///   - tautology: exactly the cited refs (the schema body's `prem0 -> … -> goal`), no head.
///   - simplify(_quantified): only the LOCAL cited rules (a global rule is cited INSIDE the
///     synthetic proof, not discharged here) — matching `produceSimplify`'s antecedents.
///   - specialize: the head-cite step (only when the head is LOCAL — a global head is cited
///     inside the synthetic proof, not discharged here) followed by the hyps.
fn accelerantPremises(self: *Prove, w: *const Walk, c: ast.Step.Claim) Error![]const kernel.SRef {
    // simplify's/chain's antecedents are only their LOCAL equation refs (globals cited in the cert).
    if (c.rule.name == try self.internStr("simplify") or c.rule.name == try self.internStr("simplify_quantified") or c.rule.name == try self.internStr("chain")) {
        return self.localRefsToSteps(w, c.refs);
    }
    // tautology has no head: its antecedents ARE the cited refs, in order.
    if (c.schema == null) {
        const out = try self.ctx.arena.alloc(kernel.SRef, c.refs.len);
        for (c.refs, out) |r, *o| o.* = try self.resolveStepRef(w, r);
        return out;
    }
    // specialize: head is c.schema; hyps are c.refs. A LOCAL head becomes the FIRST premise
    // (its formula is the synthetic schema's first antecedent); a GLOBAL head is not a premise.
    const head = c.schema.?;
    const head_local = w.findStep(tokName(head)) != null;
    const n = c.refs.len + @intFromBool(head_local);
    const out = try self.ctx.arena.alloc(kernel.SRef, n);
    var i: usize = 0;
    if (head_local) {
        out[i] = try self.resolveStepRef(w, head);
        i += 1;
    }
    for (c.refs) |r| {
        out[i] = try self.resolveStepRef(w, r);
        i += 1;
    }
    return out;
}

/// Intern a comptime literal once (cached on the Context's interner; cheap dedup).
fn internStr(self: *Prove, comptime s: []const u8) Error!StrId {
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

// -- specialize (the first accelerant producer) ----------------------------------------

/// Build the synthetic schema for `using specialize HEAD(args) hyps`. HEAD is a forall-
/// quantified fact (global theorem/axiom) or a LOCAL forall-shaped step. The schema:
///   params  = one value param per arg (sorts = the peeled ∀-binder sorts)
///   body    = [HEAD-formula ->]  <arg-instantiated HEAD tail>   (the `->`-tail after the
///             ∀ prefix is peeled at the params; a LOCAL head prepends its formula as the
///             first antecedent so the schema proof needn't cite it externally)
///   proof   = (global) cite HEAD; forall_elim(params)
///             (local)  assume HEAD-formula; forall_elim(params) on the assumption
/// The call site then instantiates at the args and discharges: (local head-step +) the hyps.
fn produceSpecialize(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    _ = goal;
    const head = c.schema orelse return self.fail(c.rule.start, "specialize requires a head theorem/axiom or local step", .{});
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // resolve HEAD → its formula term + how the schema proof cites it.
    const head_local = w.findStep(tokName(head)) != null;
    var head_formula: TermId = undefined;
    var head_kind_axiom = false; // global: is it an axiom (else theorem)?
    if (head_local) {
        const sref = try self.resolveStepRef(w, head);
        head_formula = self.low_steps.items[@intFromEnum(sref.id)].formula;
    } else {
        const fact = try self.resolveFactRef(head);
        head_formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
        head_kind_axiom = self.ctx.interner.keyOf(fact).fact.kind == .axiom;
    }

    // Instantiate one ∀ per arg at a fresh param fvar, INTERLEAVED with `->` antecedents:
    // a head `∀k; guard(k) -> ∀s; …` opens `k`, then must descend past `guard(k) ->` to
    // reach `∀s`. `openNextForall` walks the leading `->` chain (preserving it) to the next
    // forall, opens it at the param, and rebuilds the `->` prefix around the opened body.
    const nargs = c.args.len;
    const pnames = try self.ctx.arena.alloc(StrId, nargs);
    const params = try self.ctx.arena.alloc(ast.SchemaParam, nargs);
    var tail = head_formula;
    for (0..nargs) |i| {
        pnames[i] = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "p{d}", .{i + 1}));
        const opened = try self.openNextForall(tail, pnames[i]) orelse {
            return self.fail(c.rule.start, "specialize: head is not universally quantified enough for {d} argument(s)", .{nargs});
        };
        tail = opened.body;
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(opened.sort)));
        params[i] = .{ .name = b.tok(pnames[i]), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    // WALK the head formula (as `tail` was built) collecting, IN ORDER, the ∀-binders'
    // params and the kept `->` ANTECEDENTS — the schema body is `ant0 -> ant1 -> … -> C`
    // and its proof assumes each antecedent, threads forall_elim(param)/modus_ponens(ant)
    // to C, then implies_intro back. For a LOCAL head the head formula is antecedent #0.
    var ants: std.ArrayList(TermId) = .empty; // kept antecedents, in body order
    if (head_local) try ants.append(self.ctx.arena, head_formula);
    // re-walk head_formula interleaving to enumerate the `->` LHSs at the params.
    {
        var t2 = head_formula;
        var ai: usize = 0;
        while (true) {
            const node = self.pool.get(t2);
            if (node == .quant and node.quant.q == .forall and ai < nargs) {
                const pf = try self.pool.add(.{ .fvar = .{ .name = pnames[ai], .sort = node.quant.sort } });
                t2 = try self.pool.open(node.quant.body, pf);
                ai += 1;
            } else if (node == .bin and node.bin.op == .implies) {
                try ants.append(self.ctx.arena, node.bin.lhs);
                t2 = node.bin.rhs;
            } else break;
        }
    }
    const consequent = tail_consequent: {
        // C = tail with all leading `->` antecedents stripped (they're the kept ants after
        // the local-head one). Strip (ants.len - localOffset) implications off `tail`.
        var t3 = tail;
        var strip = ants.items.len - @intFromBool(head_local);
        while (strip > 0) : (strip -= 1) {
            t3 = self.pool.get(t3).bin.rhs;
        }
        break :tail_consequent t3;
    };

    var body_expr = try b.termExpr(tail);
    if (head_local) body_expr = try b.implies(try b.termExpr(head_formula), body_expr);

    const steps = try self.buildSpecializeProof(&b, head, head_local, head_kind_axiom, head_formula, pnames, ants.items, consequent);

    // deterministic hash-name from the head formula + arg count (re-entry stable).
    const hash = Schema.termHash(self.pool, head_formula) ^ (@as(u64, @intCast(nargs)) *% 0x9E3779B97F4A7C15);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "specialize{{{x}}}", .{hash}));

    return .{
        .name = name,
        .decl = .{ .schema = .{ .name = b.tok(name), .params = params, .formula = body_expr, .steps = steps } },
        .args = c.args,
        .premises = c.refs,
    };
}

/// Build the synthetic schema's PROOF for specialize: prove `ants[0] -> … -> consequent`
/// from the head. Structure: assume each antecedent (nested blocks), and in the innermost
/// context walk the head interleaving forall_elim(param) and modus_ponens(the matching
/// assumed antecedent) to reach `consequent`; then implies_intro back out through each block.
/// A GLOBAL head is cited (axiom/theorem); a LOCAL head is antecedent #0 (assumed, restated
/// by hypothesis). Handles the contiguous case (no interior `->`) as the ants-empty subset.
fn buildSpecializeProof(self: *Prove, b: *Accelerant.Builder, head: lexer.Token, head_local: bool, head_axiom: bool, head_formula: TermId, pnames: []const StrId, ants: []const TermId, consequent: TermId) Error![]const ast.Step {
    // labels for each assumed antecedent's block + its hypothesis restatement.
    const ablk = try self.ctx.arena.alloc(StrId, ants.len);
    const ahyp = try self.ctx.arena.alloc(StrId, ants.len);
    for (0..ants.len) |i| {
        ablk[i] = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "assume-ant{d}", .{i}));
        ahyp[i] = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "ant{d}", .{i}));
    }

    // the INNERMOST steps: cite/restate the head, then interleave elim/mp to `consequent`.
    var inner: std.ArrayList(ast.Step) = .empty;
    const law = try b.intern("the-head-law");
    if (head_local) {
        // head is antecedent #0 — restate it by hypothesis on its block.
        try inner.append(self.ctx.arena, try b.claimStep(law, try b.termExpr(head_formula), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(b, ablk[0])));
    } else {
        const rule: []const u8 = if (head_axiom) "axiom" else "theorem";
        try inner.append(self.ctx.arena, try b.claimStep(law, try b.termExpr(head_formula), .by, try self.internStrRt(rule), &.{}, try self.headRef(head)));
    }
    // walk the head, emitting a forall_elim step per binder and a modus_ponens step per `->`
    // (discharged by the matching assumed antecedent). `cur`/`cur_label` track the running
    // step; `ai` indexes params, `hi` indexes antecedents (offset past the local-head one).
    var cur = head_formula;
    var cur_label = law;
    var hi: usize = @intFromBool(head_local); // ant0 is the head itself for a local head
    var pi: usize = 0; // param index
    var stepn: u32 = 0;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .quant and node.quant.q == .forall and pi < pnames.len) {
            const pf = try self.pool.add(.{ .fvar = .{ .name = pnames[pi], .sort = node.quant.sort } });
            const opened = try self.pool.open(node.quant.body, pf);
            const lbl = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "elim{d}", .{stepn}));
            const arg1 = try self.ctx.arena.alloc(*const ast.Expr, 1);
            arg1[0] = try b.nameExpr(pnames[pi]);
            try inner.append(self.ctx.arena, try b.claimStep(lbl, try b.termExpr(opened), .by, try self.internStr("forall_elim"), arg1, try self.oneRef(b, cur_label)));
            cur = opened;
            cur_label = lbl;
            pi += 1;
            stepn += 1;
        } else if (node == .bin and node.bin.op == .implies and hi < ants.len) {
            const lbl = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "mp{d}", .{stepn}));
            const refs2 = try self.ctx.arena.alloc(lexer.Token, 2);
            refs2[0] = b.tok(cur_label);
            refs2[1] = b.tok(ahyp[hi]);
            try inner.append(self.ctx.arena, try b.claimStep(lbl, try b.termExpr(node.bin.rhs), .by, try self.internStr("modus_ponens"), &.{}, refs2));
            cur = node.bin.rhs;
            cur_label = lbl;
            hi += 1;
            stepn += 1;
        } else break;
    }
    // the innermost block's LAST step (cur_label) IS `consequent`; wrap up below.
    // now wrap `inner` in nested assume blocks (innermost = ants[last]) + implies_intro out.
    // build from the innermost outward.
    var body_steps = try inner.toOwnedSlice(self.ctx.arena);
    var i: usize = ants.len;
    while (i > 0) {
        i -= 1;
        // the block's body: restate THIS level's hypothesis (unless it's the local head's
        // ant0, already restated as `law` in the innermost steps), then the inner body.
        const needs_restate = !(head_local and i == 0);
        var blk_body: []const ast.Step = body_steps;
        if (needs_restate) {
            var bb = try std.ArrayList(ast.Step).initCapacity(self.ctx.arena, body_steps.len + 1);
            bb.appendAssumeCapacity(try b.claimStep(ahyp[i], try b.termExpr(ants[i]), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(b, ablk[i])));
            bb.appendSliceAssumeCapacity(body_steps);
            blk_body = bb.items;
        }
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, try b.assumeStep(ablk[i], try b.termExpr(ants[i]), blk_body));
        // export this level: `ants[i] -> <what the block concluded>`.
        const exported = try impliesFrom(b, ants[i..ants.len], consequent);
        try lvl.append(self.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try b.intern(try std.fmt.allocPrint(self.ctx.arena, "export{d}", .{i})),
            exported,
            .by,
            try self.internStr("implies_intro"),
            &.{},
            try self.oneRef(b, ablk[i]),
        ));
        body_steps = try lvl.toOwnedSlice(self.ctx.arena);
    }
    return body_steps;
}

/// `ants[0] -> ants[1] -> … -> consequent` as an AST expr (right-assoc `->`).
fn impliesFrom(b: *Accelerant.Builder, ants: []const TermId, consequent: TermId) Error!*const ast.Expr {
    var acc = try b.termExpr(consequent);
    var i: usize = ants.len;
    while (i > 0) {
        i -= 1;
        acc = try b.implies(try b.termExpr(ants[i]), acc);
    }
    return acc;
}

/// Instantiate the NEXT `forall` reachable through a leading `->` chain, at a fresh fvar
/// named `pname`. Descends the RHS of `->` nodes (preserving them), opens the forall's body
/// at the fvar, and rebuilds the `->` prefix around it. Returns the rebuilt term + the
/// binder's sort, or null if no forall is reachable (only `->`s / a non-quant leaf).
const OpenedForall = struct { body: TermId, sort: SortId };
fn openNextForall(self: *Prove, id: TermId, pname: StrId) Error!?OpenedForall {
    const node = self.pool.get(id);
    switch (node) {
        .quant => |q| {
            if (q.q != .forall) return null;
            const pf = try self.pool.add(.{ .fvar = .{ .name = pname, .sort = q.sort } });
            return .{ .body = try self.pool.open(q.body, pf), .sort = q.sort };
        },
        .bin => |bn| {
            if (bn.op != .implies) return null;
            const rhs = (try self.openNextForall(bn.rhs, pname)) orelse return null;
            // rebuild `lhs -> rhs'` with the opened rhs.
            const rebuilt = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = bn.lhs, .rhs = rhs.body } });
            return .{ .body = rebuilt, .sort = rhs.sort };
        },
        else => return null,
    }
}

/// A single-token ref slice (arena) for a synthetic step's `refs`.
fn oneRef(self: *Prove, b: *Accelerant.Builder, name: StrId) Error![]const lexer.Token {
    const r = try self.ctx.arena.alloc(lexer.Token, 1);
    r[0] = b.tok(name);
    return r;
}

/// The head's own ref token (for a global head-cite step): reuse the head token verbatim.
fn headRef(self: *Prove, head: lexer.Token) Error![]const lexer.Token {
    const r = try self.ctx.arena.alloc(lexer.Token, 1);
    r[0] = head;
    return r;
}

/// Intern a runtime rule string (axiom/theorem chosen at runtime).
fn internStrRt(self: *Prove, s: []const u8) Error!StrId {
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

// -- tautology (the second accelerant producer) ----------------------------------------

/// Build the synthetic schema for `using tautology refs…`, closing a goal that is a
/// PROPOSITIONAL CONSEQUENCE of the cited premises. `smt.tautology` DECIDES validity (an
/// honest oracle — rejects a non-consequence with a countermodel / over-cap with the atom
/// count); on `valid` the truth search REPLAYS as a natural-deduction certificate emitted
/// as AST (`TautAst`) — every step re-checked by the kernel.
///
/// The synthetic schema (same shape as specialize): body = `prem0 -> … -> premN -> goal`;
/// proof = nest one `assume prem_i` per premise (restating each hypothesis), then in the
/// innermost context emit the cert. The call site discharges the antecedents with `c.refs`.
///
/// PARAMS: the fixtures (+ every propositional consequence at a closed site) have no caller-
/// local free fvars, so no params are abstracted (unlike specialize's value params). A
/// tautology inside a `fix` would surface a free fvar in a premise/goal; that abstraction is
/// left for a follow-up; a goal/premise carrying a free fvar is rejected gracefully below.
fn produceTautology(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "tautology takes no arguments", .{});
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // premises = the cited LOCAL steps' formulae (in ref order — the body's antecedent order).
    const prems = try self.ctx.arena.alloc(TautAst.Prem, c.refs.len);
    for (c.refs, prems) |r, *out| {
        const sref = try self.resolveStepRef(w, r);
        out.* = .{
            .formula = self.low_steps.items[@intFromEnum(sref.id)].formula,
            .label = try self.freshNamed("prem"), // the restated-hypothesis step (in the block)
            .blk_label = try self.freshNamed("assume-prem"), // the assume block itself
        };
    }

    // DECIDE. A non-consequence / over-cap is a HARD failure (strict-only — no --fast escape).
    const prem_formulae = try self.ctx.arena.alloc(TermId, prems.len);
    for (prems, prem_formulae) |p, *out| out.* = p.formula;
    const verdict = smt.tautology(self.ctx.arena, self.pool, prem_formulae, goal) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {},
        .too_many_atoms => |n| return self.fail(c.rule.start, "tautology: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
        .countermodel => |lits| {
            var msg: std.Io.Writer.Allocating = .init(self.ctx.arena);
            for (lits, 0..) |lit, i| {
                msg.writer.print("{s}{s} := {s}", .{
                    if (i > 0) ", " else "",
                    try self.renderTerm(lit.atom),
                    if (lit.value) "true" else "false",
                }) catch return error.OutOfMemory;
            }
            return self.fail(c.rule.start, "tautology: not a propositional consequence; countermodel: {s}", .{msg.written()});
        },
    }

    // GENERATE the certificate. Collect the atoms once (the cert's split order), then replay.
    var atom_list: std.ArrayList(TermId) = .empty;
    for (prem_formulae) |f| smt.collectAtoms(self.ctx.arena, self.pool, &atom_list, f) catch return error.OutOfMemory;
    smt.collectAtoms(self.ctx.arena, self.pool, &atom_list, goal) catch return error.OutOfMemory;

    // A free caller-local fvar (a `fix` eigenvariable in the goal/premises — tautology inside
    // a fix block) would delaborate to a name unresolvable in the empty-scope schema body.
    // Abstracting such fvars into schema value params (as specialize does with its args) is a
    // shared-framework follow-up; until then this is a clean FAILURE, never a crash.
    if (self.hasFreeFvar(goal)) return self.fail(c.rule.start, "tautology over a proof-local variable is not yet supported (free variable in the goal)", .{});
    for (prem_formulae) |f| {
        if (self.hasFreeFvar(f)) return self.fail(c.rule.start, "tautology over a proof-local variable is not yet supported (free variable in a premise)", .{});
    }

    const assignment = try self.ctx.arena.alloc(?bool, atom_list.items.len);
    @memset(assignment, null);
    const lit_blocks = try self.ctx.arena.alloc(?StrId, atom_list.items.len);
    @memset(lit_blocks, null);
    var cert: TautAst = .{
        .p = self,
        .b = &b,
        .goal = goal,
        .premises = prems,
        .atoms = atom_list.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
    };

    // the innermost block's steps: the whole cert, concluding `goal`.
    var inner: std.ArrayList(ast.Step) = .empty;
    _ = try cert.deriveGoal(&inner);

    // wrap in nested `assume prem_i { restate hyp; … }` blocks, exporting each `->` back out.
    const steps = try self.wrapTautologyPremises(&b, prems, goal, inner.items);

    // schema body = `prem0 -> … -> goal` (an ordinary proof with no premises just = goal).
    var body_expr = try b.termExpr(goal);
    var i: usize = prems.len;
    while (i > 0) {
        i -= 1;
        body_expr = try b.implies(try b.termExpr(prems[i].formula), body_expr);
    }

    // deterministic hash-name from the goal + all premise formulae (re-entry stable).
    var hash = Schema.termHash(self.pool, goal);
    for (prem_formulae) |f| hash ^= Schema.termHash(self.pool, f) *% 0x9E3779B97F4A7C15;
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "tautology{{{x}}}", .{hash}));

    return .{
        .name = name,
        .decl = .{ .schema = .{ .name = b.tok(name), .params = &.{}, .formula = body_expr, .steps = steps } },
        .args = &.{},
        .premises = c.refs,
    };
}

/// True if `id` contains any FREE fvar — a caller-local variable the delaborated schema body
/// could not re-resolve in its empty scope. The tautology producer rejects such a goal/premise
/// gracefully (the abstraction of free locals into params is deferred; see `produceTautology`).
fn hasFreeFvar(self: *Prove, id: TermId) bool {
    return switch (self.pool.get(id)) {
        .fvar => true,
        .bvar => false,
        .app, .pred => |a| {
            for (self.pool.args(a)) |arg| if (self.hasFreeFvar(arg)) return true;
            return false;
        },
        .eq => |p| self.hasFreeFvar(p.lhs) or self.hasFreeFvar(p.rhs),
        .not => |t| self.hasFreeFvar(t),
        .bin => |bn| self.hasFreeFvar(bn.lhs) or self.hasFreeFvar(bn.rhs),
        .quant => |q| self.hasFreeFvar(q.body),
    };
}

/// Wrap the innermost cert `inner` (which concludes `goal`) in nested `assume prem_i { … }`
/// blocks (innermost = the last premise), restating each hypothesis and exporting `prem_i ->
/// …` with `implies_intro` out through each level — the shape `buildSpecializeProof` uses.
/// With no premises the cert steps are the proof body verbatim.
fn wrapTautologyPremises(self: *Prove, b: *Accelerant.Builder, prems: []const TautAst.Prem, goal: TermId, inner: []const ast.Step) Error![]const ast.Step {
    var body_steps = inner;
    var i: usize = prems.len;
    while (i > 0) {
        i -= 1;
        // this level's block: restate its hypothesis, then the inner body.
        var blk_body = try std.ArrayList(ast.Step).initCapacity(self.ctx.arena, body_steps.len + 1);
        blk_body.appendAssumeCapacity(try b.claimStep(prems[i].label, try b.termExpr(prems[i].formula), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(b, prems[i].blk_label)));
        blk_body.appendSliceAssumeCapacity(body_steps);
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, try b.assumeStep(prems[i].blk_label, try b.termExpr(prems[i].formula), blk_body.items));
        // export: `prem_i -> prem_{i+1} -> … -> goal`.
        var exported = try b.termExpr(goal);
        var j: usize = prems.len;
        while (j > i) {
            j -= 1;
            exported = try b.implies(try b.termExpr(prems[j].formula), exported);
        }
        try lvl.append(self.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try self.freshNamed("export"),
            exported,
            .by,
            try self.internStr("implies_intro"),
            &.{},
            try self.oneRef(b, prems[i].blk_label),
        ));
        body_steps = try lvl.toOwnedSlice(self.ctx.arena);
    }
    return body_steps;
}

/// The truth-search certificate, emitted as AST steps. A faithful port of the eager
/// `TautCert` (which emitted kernel steps into a shared `Lowering`): every recursive site
/// that opened a kernel block instead builds a fresh `assume { … }` AST block here. The
/// step vocabulary is identical (excluded-middle split per atom → `or_elim`; leaves derive
/// the goal structurally or `absurd` a refuted premise). No step budget (strict-only: the
/// cert MUST build for a `valid` verdict — an unbuildable one is an internal bug, not a
/// fallback). `theoryLeaf` (arithmetic) is DROPPED — pure propositional never needs it.
const TautAst = struct {
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
        /// the assume block's own label (referenced by the hypothesis / implies_intro steps)
        blk_label: StrId,
    };

    const CertError = Error;

    fn pool(self: *const TautAst) *term.Pool {
        return self.p.pool;
    }

    fn eval(self: *const TautAst, f: TermId) ?bool {
        return smt.eval(self.pool(), self.atoms, self.assignment, f);
    }

    /// The assume-block label whose hypothesis is the literal for atom `f` (assigned, else
    /// eval could not have decided the branch that calls this).
    fn litBlock(self: *const TautAst, f: TermId) StrId {
        for (self.atoms, self.lit_blocks) |a, blk| {
            if (self.pool().alphaEq(a, f)) return blk.?;
        }
        unreachable; // every leaf is a collected atom
    }

    /// Append a claim step proving `formula` by `rule` citing `refs` (given as labels); return
    /// its fresh label. The variadic `refs` are label StrIds, wrapped as tokens here.
    fn emit(self: *TautAst, block: *std.ArrayList(ast.Step), formula: TermId, rule: []const u8, refs: []const StrId) CertError!StrId {
        const toks = try self.p.ctx.arena.alloc(lexer.Token, refs.len);
        for (refs, toks) |r, *out| out.* = self.b.tok(r);
        const label = try self.p.freshNamed("taut");
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(formula), .by, try self.p.internStrRt(rule), &.{}, toks));
        return label;
    }

    /// A block under construction: its label + its step list. Close with `finishBlock`.
    const OpenBlock = struct { label: StrId, body: std.ArrayList(ast.Step) = .empty };

    fn openBlock(self: *TautAst) CertError!OpenBlock {
        return .{ .label = try self.p.freshNamed("tautology") };
    }

    /// Wrap a filled OpenBlock as `assume formula { body } @label` in `parent`.
    fn finishBlock(self: *TautAst, parent: *std.ArrayList(ast.Step), blk: *OpenBlock, formula: TermId) CertError!void {
        try parent.append(self.p.ctx.arena, try self.b.assumeStep(blk.label, try self.b.termExpr(formula), blk.body.items));
    }

    /// Restate an assume block's hypothesis `formula` as `[by hypothesis <blk>]`.
    fn hyp(self: *TautAst, blk: *OpenBlock, formula: TermId) CertError!StrId {
        return self.emit(&blk.body, formula, "hypothesis", &.{blk.label});
    }

    /// Prove `goal` in `block`. The entry point: a refuted premise closes by `absurd`; a
    /// true goal derives structurally; otherwise split on the first unassigned atom via an
    /// excluded-middle lemma + `or_elim` over the two assumption branches.
    fn deriveGoal(self: *TautAst, block: *std.ArrayList(ast.Step)) CertError!StrId {
        for (self.premises) |pr| {
            if (self.eval(pr.formula) == false) {
                // the premise's hypothesis step is `pr.label`; refute its formula and explode.
                const refuted = try self.deriveFalse(block, pr.formula);
                return self.emit(block, self.goal, "absurd", &.{ pr.label, refuted });
            }
        }
        if (self.eval(self.goal) == true) {
            return self.deriveTrue(block, self.goal);
        }
        // eval(goal) == false on a FULLY decided branch would be an unclosable boolean dead
        // end — impossible for a `valid` verdict over pure-propositional atoms (no theory
        // leaf). Some atom is still unassigned; split on it.
        std.debug.assert(std.mem.indexOfScalar(?bool, self.assignment, null) != null);
        const idx = for (self.assignment, 0..) |v, i| {
            if (v == null) break i;
        } else unreachable;
        const atom = self.atoms[idx];
        const not_atom = try self.pool().add(.{ .not = atom });
        const disj = try self.pool().add(.{ .bin = .{ .op = .or_op, .lhs = atom, .rhs = not_atom } });
        const lem = try self.emitLem(block, atom, not_atom, disj);

        // left arm: assume atom; recurse with idx := true, the arm block IS its literal source.
        var left = try self.openBlock();
        self.assignment[idx] = true;
        self.lit_blocks[idx] = left.label;
        _ = try self.deriveGoal(&left.body);
        try self.finishBlock(block, &left, atom);

        var right = try self.openBlock();
        self.assignment[idx] = false;
        self.lit_blocks[idx] = right.label;
        _ = try self.deriveGoal(&right.body);
        try self.finishBlock(block, &right, not_atom);

        self.assignment[idx] = null;
        self.lit_blocks[idx] = null;
        return self.emit(block, self.goal, "or_elim", &.{ lem, left.label, right.label });
    }

    /// `atom or not atom` the classical way: not_intro on the negated disjunction, then
    /// double_negation. A fixed AST gadget (the port of `TautCert.emitLem`).
    fn emitLem(self: *TautAst, block: *std.ArrayList(ast.Step), atom: TermId, not_atom: TermId, disj: TermId) CertError!StrId {
        const not_disj = try self.pool().add(.{ .not = disj });
        const not_not = try self.pool().add(.{ .not = not_disj });

        var outer = try self.openBlock();
        const hyp_outer = try self.hyp(&outer, not_disj);
        // inner: assume atom, derive the disjunction by or_intro_left.
        var inner = try self.openBlock();
        const hyp_inner = try self.hyp(&inner, atom);
        const or_left = try self.emit(&inner.body, disj, "or_intro_left", &.{hyp_inner});
        try self.finishBlock(&outer.body, &inner, atom);
        const derived_not = try self.emit(&outer.body, not_atom, "not_intro", &.{ inner.label, or_left, hyp_outer });
        const or_right = try self.emit(&outer.body, disj, "or_intro_right", &.{derived_not});
        try self.finishBlock(block, &outer, not_disj);

        const nn = try self.emit(block, not_not, "not_intro", &.{ outer.label, or_right, hyp_outer });
        return self.emit(block, disj, "double_negation", &.{nn});
    }

    /// Emit a step proving `f` (which evaluates true) in `block`; return its label.
    fn deriveTrue(self: *TautAst, block: *std.ArrayList(ast.Step), f: TermId) CertError!StrId {
        switch (self.pool().get(f)) {
            .bin => |bn| switch (bn.op) {
                .and_op => {
                    const left = try self.deriveTrue(block, bn.lhs);
                    const right = try self.deriveTrue(block, bn.rhs);
                    // a biconditional `(X->Y) and (Y->X)` is canonically an iff — the kernel
                    // forbids `and_intro` from producing it (must be `iff_intro`, the same rule
                    // named for what it proves). A tautology goal / hypothesis is routinely an
                    // iff (the membership-axiom pattern), so pick the rule by the shape.
                    const rule: []const u8 = if (self.p.isBiconditionalShape(f)) "iff_intro" else "and_intro";
                    return self.emit(block, f, rule, &.{ left, right });
                },
                .or_op => {
                    if (self.eval(bn.lhs) == true) {
                        const l = try self.deriveTrue(block, bn.lhs);
                        return self.emit(block, f, "or_intro_left", &.{l});
                    }
                    const r = try self.deriveTrue(block, bn.rhs);
                    return self.emit(block, f, "or_intro_right", &.{r});
                },
                .implies => {
                    var blk = try self.openBlock();
                    if (self.eval(bn.rhs) == true) {
                        _ = try self.deriveTrue(&blk.body, bn.rhs);
                    } else {
                        // the antecedent is false here: assume it and explode into the consequent.
                        const h = try self.hyp(&blk, bn.lhs);
                        const refuted = try self.deriveFalse(&blk.body, bn.lhs);
                        _ = try self.emit(&blk.body, bn.rhs, "absurd", &.{ h, refuted });
                    }
                    try self.finishBlock(block, &blk, bn.lhs);
                    return self.emit(block, f, "implies_intro", &.{blk.label});
                },
            },
            // f = not inner, true: exactly a proof that inner is false.
            .not => |inner| return self.deriveFalse(block, inner),
            // an atom assigned true: restate its assumption's hypothesis.
            else => return self.emit(block, f, "hypothesis", &.{self.litBlock(f)}),
        }
    }

    /// Emit a step proving `not f` (f evaluates false) in `block`; return its label.
    fn deriveFalse(self: *TautAst, block: *std.ArrayList(ast.Step), f: TermId) CertError!StrId {
        const nf = try self.pool().add(.{ .not = f });
        switch (self.pool().get(f)) {
            .bin => |bn| switch (bn.op) {
                .and_op => {
                    // a false conjunct refutes the conjunction.
                    const left_false = self.eval(bn.lhs) == false;
                    const side = if (left_false) bn.lhs else bn.rhs;
                    const refuted = try self.deriveFalse(block, side);
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, f);
                    const elim = try self.emit(&blk.body, side, if (left_false) "and_elim_left" else "and_elim_right", &.{h});
                    try self.finishBlock(block, &blk, f);
                    return self.emit(block, nf, "not_intro", &.{ blk.label, elim, refuted });
                },
                .or_op => {
                    // both disjuncts false; case-split to reproduce the left one, contradicting it.
                    const not_left = try self.deriveFalse(block, bn.lhs);
                    const not_right = try self.deriveFalse(block, bn.rhs);
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, f);
                    var left = try self.openBlock();
                    _ = try self.hyp(&left, bn.lhs);
                    try self.finishBlock(&blk.body, &left, bn.lhs);
                    var right = try self.openBlock();
                    const rh = try self.hyp(&right, bn.rhs);
                    _ = try self.emit(&right.body, bn.lhs, "absurd", &.{ rh, not_right });
                    try self.finishBlock(&blk.body, &right, bn.rhs);
                    const conc = try self.emit(&blk.body, bn.lhs, "or_elim", &.{ h, left.label, right.label });
                    try self.finishBlock(block, &blk, f);
                    return self.emit(block, nf, "not_intro", &.{ blk.label, conc, not_left });
                },
                .implies => {
                    // true antecedent, false consequent.
                    const ante = try self.deriveTrue(block, bn.lhs);
                    const not_conseq = try self.deriveFalse(block, bn.rhs);
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, f);
                    const conseq = try self.emit(&blk.body, bn.rhs, "modus_ponens", &.{ h, ante });
                    try self.finishBlock(block, &blk, f);
                    return self.emit(block, nf, "not_intro", &.{ blk.label, conseq, not_conseq });
                },
            },
            .not => |inner| {
                // not f = not not inner, with inner true.
                const truth = try self.deriveTrue(block, inner);
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, f);
                try self.finishBlock(block, &blk, f);
                return self.emit(block, nf, "not_intro", &.{ blk.label, truth, h });
            },
            // an atom assigned false: its assumption IS the negation.
            else => return self.emit(block, nf, "hypothesis", &.{self.litBlock(f)}),
        }
    }
};

// -- simplify / simplify_quantified (the equational accelerants) -----------------------

/// The subset of `refs` that name LOCAL proof steps (in walk scope), resolved to step refs —
/// the simplify accelerant's schema antecedents (a global rule is cited inside the cert).
fn localRefsToSteps(self: *Prove, w: *const Walk, refs: []const lexer.Token) Error![]const kernel.SRef {
    var out: std.ArrayList(kernel.SRef) = .empty;
    for (refs) |r| {
        if (r.qualifier == InternPool.Index.none and w.findStep(tokName(r)) != null) {
            try out.append(self.ctx.arena, try self.resolveStepRef(w, r));
        }
    }
    return out.items;
}

/// The fresh-label trampoline EqCert calls (type-erased `*Prove`).
fn eqCertFresh(ctx: *anyopaque, prefix: []const u8) anyerror!StrId {
    const self: *Prove = @ptrCast(@alignCast(ctx));
    return self.freshNamed(prefix);
}

/// Prepare one rewrite rule from a cited ref: resolve its formula (LOCAL step or GLOBAL
/// axiom/theorem), orient the (possibly ∀-prefixed) equation left→right opening each binder
/// at a fresh `#`-mangled pattern fvar, and record how the cert cites it. A rule's binders
/// must all occur on the lhs (else it is not a usable rewrite rule).
const PreparedRule = struct { rule: simplify_mod.Rule, cite: EqCert.RuleCite, local: bool, formula: TermId };
fn prepareRule(self: *Prove, w: *const Walk, ref: lexer.Token) Error!PreparedRule {
    var formula: TermId = undefined;
    var cite: EqCert.RuleCite = undefined;
    const is_local = ref.qualifier == InternPool.Index.none and w.findStep(tokName(ref)) != null;
    if (is_local) {
        // a LOCAL equation step: it becomes a schema antecedent, restated by hypothesis.
        const sref = try self.resolveStepRef(w, ref);
        formula = self.low_steps.items[@intFromEnum(sref.id)].formula;
        cite = .{ .local = .{ .hyp = try self.premiseHypLabel(ref) } };
    } else {
        const fact = try self.resolveFactRef(ref);
        formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
        cite = .{ .global = .{ .head = ref, .is_axiom = self.ctx.interner.keyOf(fact).fact.kind == .axiom } };
    }
    // orient: peel `forall` binders as fresh pattern fvars, require an equation body.
    var binders: std.ArrayList(simplify_mod.Binder) = .empty;
    var body = formula;
    while (true) {
        const node = self.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const fresh = try self.freshNamed("p#");
        const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
        body = try self.pool.open(node.quant.body, fv);
        try binders.append(self.ctx.arena, .{ .fvar = fresh, .sort = node.quant.sort });
    }
    const bn = self.pool.get(body);
    if (bn != .eq) return self.fail(ref.start, "'{s}' is not an equation", .{self.text(ref)});
    for (binders.items) |bd| {
        if (!self.pool.occursFree(bn.eq.lhs, bd.fvar)) {
            return self.fail(ref.start, "'{s}': not every bound variable occurs on the left-hand side", .{self.text(ref)});
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
fn premiseHypLabel(self: *Prove, ref: lexer.Token) Error!StrId {
    return self.ctx.interner.internString(std.fmt.allocPrint(self.ctx.arena, "prem-{d}", .{@intFromEnum(tokName(ref))}) catch return error.OutOfMemory) catch return error.OutOfMemory;
}

/// `[using simplify refs…]` — prove an equation goal `s = t` by rewriting BOTH sides to a
/// common normal form using each cited fact as a left→right rewrite rule. Certificate-total:
/// on a shared NF the reflexivity/rewrite/symmetry chain is emitted (via the shared EqCert)
/// as the synthetic schema's proof; on differing NFs or a rewrite-cap overflow it FAILS with
/// the diagnostic. Synthetic schema (specialize-shaped): value params abstract the goal's
/// free (fix-eigenvariable) fvars; LOCAL rule refs become premise antecedents restated by
/// hypothesis; GLOBAL rules are cited inside the cert.
fn produceSimplify(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "simplify takes no arguments", .{});
    const gn = self.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return self.fail(c.rule.start, "simplify proves equations; did you mean simplify_quantified?", .{});
        }
        return self.fail(c.rule.start, "simplify: goal is not an equation", .{});
    }
    return self.buildSimplify(w, c, goal, &.{});
}

/// `[using simplify_quantified refs…]` — like simplify but the goal is `forall …; s = t`.
/// Peel the ∀ prefix into fresh eigenvariable fvars, run the simplify core on the body
/// equation, and re-generalize: the synthetic schema's proof `fix`es each eigenvariable,
/// proves the body via the EqCert, and `forall_intro`s back out.
fn produceSimplifyQuantified(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "simplify_quantified takes no arguments", .{});
    // peel the ∀ prefix into fresh eigenvariables; the body must be an equation.
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var body = goal;
    while (true) {
        const node = self.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = self.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{ .name = try self.freshNamed(if (hint.len > 0) hint else "q"), .sort = node.quant.sort };
        body = try self.pool.open(node.quant.body, try self.pool.add(.{ .fvar = fv }));
        try eigen.append(self.ctx.arena, fv);
    }
    if (eigen.items.len == 0) {
        return self.fail(c.rule.start, "simplify_quantified expects a quantified goal; did you mean simplify?", .{});
    }
    if (self.pool.get(body) != .eq) {
        return self.fail(c.rule.start, "simplify_quantified: the quantified body is not an equation", .{});
    }
    return self.buildSimplify(w, c, body, eigen.items);
}

/// Shared core for both simplify variants: prepare rules, normalize both sides of the body
/// equation `eq_goal`, join (or fail on differing NFs / a cap overflow), then build the
/// synthetic schema. `eigen` (empty for plain simplify) are the peeled ∀ eigenvariables the
/// quantified variant re-generalizes over via `fix` blocks (they are NOT abstracted into
/// params — the schema proof re-binds them; only genuinely-free caller-locals become params).
fn buildSimplify(self: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // prepare the rewrite rules (in citation order) + how the cert cites each.
    const prepared = try self.ctx.arena.alloc(PreparedRule, c.refs.len);
    for (c.refs, prepared) |r, *out| out.* = try self.prepareRule(w, r);
    const rules = try self.ctx.arena.alloc(simplify_mod.Rule, prepared.len);
    const cites = try self.ctx.arena.alloc(EqCert.RuleCite, prepared.len);
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
    var abs_terms: std.ArrayList(TermId) = .empty;
    try abs_terms.append(self.ctx.arena, eq_goal_raw);
    for (prepared) |p| if (p.local) try abs_terms.append(self.ctx.arena, p.formula);
    const abs = try self.abstractFreeFvars(&b, abs_terms.items, eigen);
    const eq_goal = try self.substFvarsToParams(eq_goal_raw, abs);

    const gn = self.pool.get(eq_goal).eq;
    const s = gn.lhs;
    const t = gn.rhs;

    // normalize both sides; a looping rule set trips the cap (1000, as the eager core).
    const rs = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules, s, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "simplify: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules, t, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "simplify: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        // render over the ORIGINAL caller names: undo the param abstraction (pK -> display
        // fvar) so the diagnostic shows `add(n, ZERO)`, not the synthetic `add(p1, ZERO)`.
        return self.fail(c.rule.start, "simplify: normal forms differ: '{s}' vs '{s}'", .{
            try self.renderTerm(try self.unabstract(rs.nf, abs)),
            try self.renderTerm(try self.unabstract(rt.nf, abs)),
        });
    }

    // Build the equation-cert AST proving `s = t` into a fresh step list.
    var cert: EqCert = .{
        .b = &b,
        .pool = self.pool,
        .rules = rules,
        .cites = cites,
        .fresh_ctx = self,
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
        try local_cites.append(self.ctx.arena, p.cite);
        try local_formulae.append(self.ctx.arena, try self.substFvarsToParams(p.formula, abs));
    };

    // the inner proposition the cert proves under its assumptions: `prem0 -> … -> (s = t)`.
    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    const inner_prop = try self.impliesChain(eq_prop, local_formulae.items);

    // wrap the cert in nested `assume <local-prem>` blocks (the `->` antecedents), then in
    // `fix` blocks for the ∀ eigenvariables (the quantified variant's re-generalization).
    steps = try self.wrapSimplifyPremises(&b, local_cites.items, local_formulae.items, eq_prop, steps);
    steps = try self.wrapSimplifyForall(&b, eigen, inner_prop, steps);

    // the schema body proposition = the ∀-generalized `inner_prop` (params already in place).
    var full_prop = inner_prop;
    var ei: usize = eigen.len;
    while (ei > 0) {
        ei -= 1;
        const closed = try self.pool.close(full_prop, eigen[ei].name);
        full_prop = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = eigen[ei].sort, .hint = eigen[ei].name, .body = closed } });
    }
    const body_expr = try b.termExpr(full_prop);

    // params from the abstracted free fvars (value params of the fvars' sorts).
    const params = try self.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        pp.* = .{ .name = b.tok(name), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    // deterministic hash-name from the (pre-substitution) full proposition (re-entry stable).
    const hash = Schema.termHash(self.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "simplify{{{x}}}", .{hash}));

    return .{
        .name = name,
        .decl = .{ .schema = .{ .name = b.tok(name), .params = params, .formula = body_expr, .steps = steps } },
        .args = abs.args,
        .premises = try self.localRefTokens(w, c.refs), // discharged at the call site
    };
}

/// The LOCAL rule ref TOKENS (for the `Synthetic.premises` slot — the demand plumbing rides
/// these as the instance claim's `refs`; `accelerantPremises` re-resolves them to steps).
fn localRefTokens(self: *Prove, w: *const Walk, refs: []const lexer.Token) Error![]const lexer.Token {
    var out: std.ArrayList(lexer.Token) = .empty;
    for (refs) |r| {
        if (r.qualifier == InternPool.Index.none and w.findStep(tokName(r)) != null) {
            try out.append(self.ctx.arena, r);
        }
    }
    return out.items;
}

/// `ants[0] -> … -> ants[n] -> consequent` (right-assoc) as a kernel term.
fn impliesChain(self: *Prove, consequent: TermId, ants: []const TermId) Error!TermId {
    var acc = consequent;
    var i: usize = ants.len;
    while (i > 0) {
        i -= 1;
        acc = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = ants[i], .rhs = acc } });
    }
    return acc;
}

/// Wrap the cert `inner` (proving the equation `eq_prop`) in nested `assume <local-prem>`
/// blocks — one per LOCAL rule premise, restating its hypothesis (under the deterministic
/// `prem-…` label the cert cites) and exporting `prem_i -> …` with `implies_intro` out
/// through each level. With no local premises the cert steps pass through verbatim. (Same
/// shape as tautology's `wrapTautologyPremises`.)
fn wrapSimplifyPremises(self: *Prove, b: *Accelerant.Builder, cites: []const EqCert.RuleCite, formulae: []const TermId, eq_prop: TermId, inner: []const ast.Step) Error![]const ast.Step {
    var body_steps = inner;
    var i: usize = formulae.len;
    while (i > 0) {
        i -= 1;
        const hyp_label = cites[i].local.hyp;
        const blk_label = try self.freshNamed("assume-prem");
        var blk_body = try std.ArrayList(ast.Step).initCapacity(self.ctx.arena, body_steps.len + 1);
        blk_body.appendAssumeCapacity(try b.claimStep(hyp_label, try b.termExpr(formulae[i]), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(b, blk_label)));
        blk_body.appendSliceAssumeCapacity(body_steps);
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, try b.assumeStep(blk_label, try b.termExpr(formulae[i]), blk_body.items));
        // export: `prem_i -> … -> (s = t)`.
        const exported = try self.impliesChain(eq_prop, formulae[i..]);
        try lvl.append(self.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try self.freshNamed("export"),
            try b.termExpr(exported),
            .by,
            try self.internStr("implies_intro"),
            &.{},
            try self.oneRef(b, blk_label),
        ));
        body_steps = try lvl.toOwnedSlice(self.ctx.arena);
    }
    return body_steps;
}

/// Wrap the premise-wrapped `body_steps` (proving `inner_prop = prem0 -> … -> (s = t)`) in
/// nested `fix` blocks for the ∀ eigenvariables (outermost = eigen[0]), concluding each level
/// with `forall_intro`. With no eigenvariables the steps pass through unchanged (plain
/// simplify). The `fix` binder re-uses each eigenvariable's DISPLAY name — the same name the
/// cert body's delaborated fvars carry, so they re-resolve to the binder.
fn wrapSimplifyForall(self: *Prove, b: *Accelerant.Builder, eigen: []const term.Node.Fvar, inner_prop: TermId, body_steps: []const ast.Step) Error![]const ast.Step {
    if (eigen.len == 0) return body_steps;
    var steps = body_steps;
    var prop = inner_prop; // the proposition inside the current fix (before this ∀ closes)
    var i: usize = eigen.len;
    while (i > 0) {
        i -= 1;
        const fv = eigen[i];
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(fv.sort)));
        const fix_label = try self.freshNamed("fix");
        const bname = b.tok(try self.displayName(fv.name));
        const fix_step: ast.Step = .{ .label = b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = b.tok(sort_name), .steps = steps } } };
        const closed = try self.pool.close(prop, fv.name);
        prop = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, fix_step);
        try lvl.append(self.ctx.arena, try b.claimStep(
            if (i == 0) try b.intern("conclusion") else try self.freshNamed("gen"),
            try b.termExpr(prop),
            .by,
            try self.internStr("forall_intro"),
            &.{},
            try self.oneRef(b, fix_label),
        ));
        steps = try lvl.toOwnedSlice(self.ctx.arena);
    }
    return steps;
}

/// Abstract each distinct FREE fvar in `id` into a synthetic value param — the goal's
/// genuinely-free caller-local fvars (an enclosing `fix` at the call site). Returns the param
/// names/sorts (for the schema `params`), the original fvar names (for substitution), and the
/// caller-site arg exprs (each the fvar's DISPLAY name, re-resolving to the caller binder).
/// A closed `id` yields no params (like a plain tautology).
const FvarAbstraction = struct {
    names: []const StrId,
    sorts: []const SortId,
    origs: []const StrId,
    args: []const *const ast.Expr,
};
fn abstractFreeFvars(self: *Prove, b: *Accelerant.Builder, terms: []const TermId, exclude: []const term.Node.Fvar) Error!FvarAbstraction {
    var seen: std.ArrayList(term.Node.Fvar) = .empty;
    for (terms) |t| try self.collectFreeFvars(t, &seen);
    // drop excluded eigenvariables (they are `fix`-bound, not param-abstracted).
    var kept: std.ArrayList(term.Node.Fvar) = .empty;
    outer: for (seen.items) |fv| {
        for (exclude) |e| if (e.name == fv.name) continue :outer;
        try kept.append(self.ctx.arena, fv);
    }
    seen = kept;
    const names = try self.ctx.arena.alloc(StrId, seen.items.len);
    const sorts = try self.ctx.arena.alloc(SortId, seen.items.len);
    const origs = try self.ctx.arena.alloc(StrId, seen.items.len);
    const args = try self.ctx.arena.alloc(*const ast.Expr, seen.items.len);
    for (seen.items, 0..) |fv, i| {
        names[i] = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "p{d}", .{i + 1}));
        sorts[i] = fv.sort;
        origs[i] = fv.name;
        args[i] = try b.termExpr(try self.pool.add(.{ .fvar = fv })); // display name → caller binder
    }
    return .{ .names = names, .sorts = sorts, .origs = origs, .args = args };
}

/// Collect distinct free fvars (by name) into `out`.
fn collectFreeFvars(self: *Prove, id: TermId, out: *std.ArrayList(term.Node.Fvar)) Error!void {
    switch (self.pool.get(id)) {
        .fvar => |v| {
            for (out.items) |e| if (e.name == v.name) return;
            try out.append(self.ctx.arena, v);
        },
        .bvar => {},
        .app, .pred => |a| for (self.pool.args(a)) |arg| try self.collectFreeFvars(arg, out),
        .eq => |p| {
            try self.collectFreeFvars(p.lhs, out);
            try self.collectFreeFvars(p.rhs, out);
        },
        .not => |t| try self.collectFreeFvars(t, out),
        .bin => |bn| {
            try self.collectFreeFvars(bn.lhs, out);
            try self.collectFreeFvars(bn.rhs, out);
        },
        .quant => |q| try self.collectFreeFvars(q.body, out),
    }
}

/// Substitute each `origs[i]` fvar with a fresh param fvar named `names[i]` (same sort)
/// throughout `id`; the param fvar delaborates to the bare param name the schema Elab binds.
fn substFvarsToParams(self: *Prove, id: TermId, abs: FvarAbstraction) Error!TermId {
    var out = id;
    for (abs.origs, abs.names, abs.sorts) |orig, name, sort| {
        const pf = try self.pool.add(.{ .fvar = .{ .name = name, .sort = sort } });
        out = try self.pool.substFvar(out, orig, pf);
    }
    return out;
}

/// The inverse of `substFvarsToParams` for DISPLAY: replace each param fvar `pK` with a
/// fresh fvar named after the original caller-local (display-trimmed), so a diagnostic shows
/// the name the author wrote instead of the synthetic `pK`.
fn unabstract(self: *Prove, id: TermId, abs: FvarAbstraction) Error!TermId {
    var out = id;
    for (abs.names, abs.origs, abs.sorts) |name, orig, sort| {
        const disp = try self.pool.add(.{ .fvar = .{ .name = try self.displayName(orig), .sort = sort } });
        out = try self.pool.substFvar(out, name, disp);
    }
    return out;
}

/// An fvar's display name (trimmed at the hygiene `#`), re-interned — the bare name the `fix`
/// binder + the cert's fvar references share, and what re-elaboration re-binds.
fn displayName(self: *Prove, name: StrId) Error!StrId {
    const s = self.ctx.interner.stringBytes(name);
    if (std.mem.indexOfScalar(u8, s, '#')) |k| {
        return self.ctx.interner.internString(s[0..k]) catch error.OutOfMemory;
    }
    return name;
}

// -- chain (the undirected-equation accelerant) ----------------------------------------

/// A cited equation, prepared for the chain search + cert. `lhs`/`rhs` are its two sides
/// (param-substituted); `body_label` is the step INSIDE the synthetic proof that proves this
/// equation in its cited (forward) orientation — a restated-hypothesis step for a LOCAL ref,
/// or an emitted `[by axiom|theorem …]` step for a GLOBAL one. `local` splits which.
const ChainEq = struct { lhs: TermId, rhs: TermId, body_label: StrId, local: bool, formula: TermId };

/// One edge of the found rewrite path: apply equation `eq_idx` in orientation `forward`
/// (`forward` = lhs→rhs) to reach `result` from its predecessor.
const ChainEdge = struct { eq_idx: usize, forward: bool, result: TermId };

/// `[using chain eq1 eq2 …]` — prove an equality goal `A = Z` from the cited equations used
/// as UNDIRECTED rewrite rules. Where `simplify` orients each equation left→right and reduces
/// to a normal form, `chain` BFS-searches for a rewrite path `A → … → Z`, applying each cited
/// `p = q` (or its `symmetry` flip) via the kernel `rewrite` (which rewrites all occurrences,
/// so congruence is free). Two phases: SEARCH the path purely, then EMIT it as reflexivity +
/// `symmetry`/`rewrite` steps the kernel re-checks — certificate-total, no --fast taint.
///
/// Synthetic schema (simplify-shaped): value params abstract the goal's free (fix-eigenvar)
/// fvars; LOCAL cited equations become premise antecedents restated by hypothesis; GLOBAL
/// equations are cited `[by axiom|theorem …]` INSIDE the synthetic proof.
fn produceChain(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "chain takes no arguments", .{});
    const gn0 = self.pool.get(goal);
    if (gn0 != .eq) return self.fail(c.rule.start, "chain proves an equation 'A = Z'; the goal is not an equation", .{});
    if (c.refs.len == 0) return self.fail(c.rule.start, "chain needs at least one cited equation", .{});
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // RESOLVE each cited equation to its formula + how the synthetic proof cites it (LOCAL =
    // restated hypothesis, GLOBAL = a `[by axiom|theorem]` head step). Kept as raw formulae
    // for the fvar-abstraction pass; the sides are (re)read after substitution below.
    const Prepared = struct { formula: TermId, body_label: StrId, local: bool, head: lexer.Token, is_axiom: bool };
    const prepared = try self.ctx.arena.alloc(Prepared, c.refs.len);
    for (c.refs, prepared) |ref, *out| {
        const is_local = ref.qualifier == InternPool.Index.none and w.findStep(tokName(ref)) != null;
        var formula: TermId = undefined;
        var body_label: StrId = undefined;
        var is_axiom = false;
        if (is_local) {
            const sref = try self.resolveStepRef(w, ref);
            formula = self.low_steps.items[@intFromEnum(sref.id)].formula;
            body_label = try self.premiseHypLabel(ref); // the restated-hypothesis step's label
        } else {
            const fact = try self.resolveFactRef(ref);
            formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
            body_label = try self.freshNamed("chain-cite"); // the `[by axiom|theorem]` head step
            is_axiom = self.ctx.interner.keyOf(fact).fact.kind == .axiom;
        }
        if (self.pool.get(formula) != .eq) return self.fail(ref.start, "'{s}' is not an equation", .{self.text(ref)});
        out.* = .{ .formula = formula, .body_label = body_label, .local = is_local, .head = ref, .is_axiom = is_axiom };
    }

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix`) into value params — the
    // goal plus each LOCAL equation formula (a global's formula is closed) speak the param
    // names `p1, p2, …` after substitution. (chain has no ∀-eigenvariables to exclude.)
    var abs_terms: std.ArrayList(TermId) = .empty;
    try abs_terms.append(self.ctx.arena, goal);
    for (prepared) |p| if (p.local) try abs_terms.append(self.ctx.arena, p.formula);
    const abs = try self.abstractFreeFvars(&b, abs_terms.items, &.{});

    const gn = self.pool.get(try self.substFvarsToParams(goal, abs)).eq;
    const start = gn.lhs;
    const target = gn.rhs;
    const eqs = try self.ctx.arena.alloc(ChainEq, prepared.len);
    for (prepared, eqs) |p, *out| {
        const f = try self.substFvarsToParams(p.formula, abs);
        const fn2 = self.pool.get(f).eq;
        out.* = .{ .lhs = fn2.lhs, .rhs = fn2.rhs, .body_label = p.body_label, .local = p.local, .formula = f };
    }

    // PHASE 1 — BFS `start` → `target` over the equations as undirected rewrites. The pool is
    // NOT hash-consed (structurally-equal terms carry distinct TermIds), so a by-id `seen` set
    // would miss reconvergence; canonicalize each rewrite result to an already-seen id when
    // alpha-equal (target first — the common case — then the rest of the frontier).
    var came_from: std.AutoHashMapUnmanaged(TermId, ChainEdge) = .empty;
    var seen: std.AutoHashMapUnmanaged(TermId, void) = .empty;
    var queue: std.ArrayList(TermId) = .empty;
    try queue.append(self.ctx.arena, start);
    try seen.put(self.ctx.arena, start, {});
    var head_i: usize = 0;
    const cap = 4096; // node budget — congruence-free equational chains are tiny
    var found = self.pool.alphaEq(start, target);
    while (head_i < queue.items.len and !found and seen.count() < cap) {
        const curterm = queue.items[head_i];
        head_i += 1;
        for (eqs, 0..) |e, ei| {
            for ([_]bool{ true, false }) |forward| {
                const from = if (forward) e.lhs else e.rhs;
                const to = if (forward) e.rhs else e.lhs;
                const raw = try self.pool.rewriteAll(curterm, from, to);
                if (self.pool.alphaEq(raw, curterm)) continue; // no change
                var nxt = raw;
                if (self.pool.alphaEq(raw, target)) {
                    nxt = target;
                } else {
                    var it = seen.keyIterator();
                    while (it.next()) |k| {
                        if (self.pool.alphaEq(raw, k.*)) {
                            nxt = k.*;
                            break;
                        }
                    }
                }
                if (seen.get(nxt) != null) continue; // already reached
                try seen.put(self.ctx.arena, nxt, {});
                try came_from.put(self.ctx.arena, nxt, .{ .eq_idx = ei, .forward = forward, .result = curterm });
                try queue.append(self.ctx.arena, nxt);
                if (self.pool.alphaEq(nxt, target)) {
                    found = true;
                    break;
                }
            }
            if (found) break;
        }
    }
    if (!found) {
        // render over ORIGINAL caller names (undo the param abstraction) for the diagnostic.
        return self.fail(c.rule.start, "chain: cannot connect '{s}' to '{s}' from the cited equations", .{
            try self.renderTerm(try self.unabstract(start, abs)),
            try self.renderTerm(try self.unabstract(target, abs)),
        });
    }

    // reconstruct the path start → … → target (list of intermediate terms, target last).
    var path: std.ArrayList(TermId) = .empty;
    {
        var t = target;
        while (!self.pool.alphaEq(t, start)) {
            try path.append(self.ctx.arena, t);
            const edge = came_from.get(t) orelse return self.fail(c.rule.start, "chain: internal path reconstruction failed", .{});
            t = edge.result;
        }
    }
    std.mem.reverse(TermId, path.items); // target-first → start-order

    // PHASE 2 — emit the cert body. GLOBAL equations are cited up front (each once, in ref
    // order) as a `[by axiom|theorem head]` step under the label the search recorded; LOCAL
    // ones are the wrapper's restated hypotheses (their `body_label` = the `prem-…` step).
    var body_steps: std.ArrayList(ast.Step) = .empty;
    for (prepared) |p| if (!p.local) {
        const word = if (p.is_axiom) try self.internStr("axiom") else try self.internStr("theorem");
        try body_steps.append(self.ctx.arena, try b.claimStep(p.body_label, try b.termExpr(p.formula), .by, word, &.{}, try self.headRef(p.head)));
    };
    // reflexivity `start = start`, then one rewrite per path edge (symmetry-flip a backward edge).
    const refl = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = start } });
    var cur_label = try self.freshNamed("chain");
    try body_steps.append(self.ctx.arena, try b.claimStep(cur_label, try b.termExpr(refl), .by, try self.internStr("reflexivity"), &.{}, &.{}));
    for (path.items) |next_term| {
        const edge = came_from.get(next_term).?;
        const e = eqs[edge.eq_idx];
        // the equation to cite as the rewrite's rule: forward = as proved; backward = its flip.
        var eq_label = e.body_label;
        if (!edge.forward) {
            const flipped = try self.pool.add(.{ .eq = .{ .lhs = e.rhs, .rhs = e.lhs } });
            eq_label = try self.freshNamed("chain");
            try body_steps.append(self.ctx.arena, try b.claimStep(eq_label, try b.termExpr(flipped), .by, try self.internStr("symmetry"), &.{}, try self.oneRef(&b, e.body_label)));
        }
        const new_goal = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = next_term } });
        const lbl = try self.freshNamed("chain");
        const refs = try self.ctx.arena.alloc(lexer.Token, 2);
        refs[0] = b.tok(eq_label); // the equation (kernel `rewrite` rewrites all occurrences)
        refs[1] = b.tok(cur_label); // the running `start = …` target
        try body_steps.append(self.ctx.arena, try b.claimStep(lbl, try b.termExpr(new_goal), .by, try self.internStr("rewrite"), &.{}, refs));
        cur_label = lbl;
    }

    // LOCAL equations are the schema's `->` antecedents (restated + discharged at the call
    // site), in ref order; collect their (cite, param-substituted formula) for the wrapper.
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (eqs) |e| if (e.local) {
        try local_cites.append(self.ctx.arena, .{ .local = .{ .hyp = e.body_label } });
        try local_formulae.append(self.ctx.arena, e.formula);
    };

    // wrap the cert in nested `assume <local-eq>` blocks (the `->` antecedents), each restating
    // its hypothesis under `body_label` and exporting `prem_i -> … -> (start = target)` out.
    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = target } });
    const steps = try self.wrapSimplifyPremises(&b, local_cites.items, local_formulae.items, eq_prop, body_steps.items);

    // schema body proposition = `local-prem0 -> … -> (start = target)`; params already in place.
    const full_prop = try self.impliesChain(eq_prop, local_formulae.items);
    const body_expr = try b.termExpr(full_prop);

    // params from the abstracted free fvars (value params of the fvars' sorts).
    const params = try self.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        pp.* = .{ .name = b.tok(name), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    // deterministic hash-name from the full proposition (re-entry stable).
    const hash = Schema.termHash(self.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "chain{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .schema = .{ .name = b.tok(name), .params = params, .formula = body_expr, .steps = steps } },
        .args = abs.args,
        .premises = try self.localRefTokens(w, c.refs), // discharged at the call site
    };
}

// -- justification lowering ------------------------------------------------------------

fn isBiconditionalShape(self: *const Prove, id: TermId) bool {
    const pool = self.pool;
    const n = pool.get(id);
    if (n != .bin or n.bin.op != .and_op) return false;
    const l = pool.get(n.bin.lhs);
    const r = pool.get(n.bin.rhs);
    if (l != .bin or l.bin.op != .implies) return false;
    if (r != .bin or r.bin.op != .implies) return false;
    return pool.alphaEq(l.bin.lhs, r.bin.rhs) and pool.alphaEq(l.bin.rhs, r.bin.lhs);
}

fn wantRefs(self: *Prove, c: ast.Step.Claim, n: usize) Error!void {
    if (c.refs.len != n) {
        return self.fail(c.rule.start, "'{s}' expects {d} reference(s), got {d}", .{
            self.text(c.rule), n, c.refs.len,
        });
    }
}

fn lowerJustification(self: *Prove, w: *const Walk, e: *Elab, kb: kernel.BlockId, goal: TermId, c: ast.Step.Claim) Error!kernel.Justification {
    // An ACCELERANT (`using <accel> …`) lowers to a schema_instance over its generated
    // synthetic schema (the instance was demanded + proven in the read pass).
    if (c.kind == .using and isAccelerant(c.rule.name)) return self.lowerUsing(w, e, goal, c);
    // Otherwise the rule word dispatches by its RESERVED StrId (integer comparison — no
    // strcmp past parsing); a non-rule word here is a typo.
    const kind = InternPool.RuleStr.of(c.rule.name) orelse {
        return self.fail(c.rule.start, "unsupported by the demand prover: '{s}'", .{self.text(c.rule)});
    };
    switch (kind) {
        // `instantiation` resolves a SCHEMA (not a kernel rule) — the instance fact was
        // demanded (racked + proven) in the read pass; look it up, copyIn its formula, and
        // emit the kernel schema_instance justification (peels premises against `c.refs`).
        .instantiation => return self.lowerInstantiate(w, e, c),
        // `using model(M) src.thm` transfers a source theorem: the transferred fact was
        // demanded (proved in namespace (M, src_file)) in the read pass; cite it.
        .model => return self.lowerModel(w, c),
        else => {},
    }
    const wants_args: usize = switch (kind) {
        .forall_elim => if (c.args.len == 0) 1 else c.args.len,
        .exists_intro => 1,
        else => 0,
    };
    if (c.args.len != wants_args) {
        return self.fail(c.rule.start, "'{s}' expects {d} argument(s), got {d}", .{
            self.text(c.rule), wants_args, c.args.len,
        });
    }
    switch (kind) {
        .instantiation, .model => unreachable, // dispatched above
        .axiom, .theorem => {
            try self.wantRefs(c, 1);
            const stmt = try self.resolveFactRef(c.refs[0]);
            // Emit the justification matching the RESOLVED fact's kind, not the rule word.
            // Identity in an ordinary proof (a `by axiom` cites an axiom). In a MODEL
            // transfer a source-axiom citation may remap (via the obligation overlay) to a
            // discharging THEOREM — so `by axiom srcAx` legitimately lands on a theorem;
            // pick the kernel arm by the fact's actual kind (the kernel re-matches the
            // formula regardless — the kind gate is the only thing that'd wrongly reject).
            const loc = c.refs[0].start;
            return switch (self.ctx.interner.keyOf(stmt).fact.kind) {
                .axiom => .{ .axiom_ref = .{ .stmt = stmt, .loc = loc } },
                .theorem => .{ .theorem_ref = .{ .stmt = stmt, .loc = loc } },
            };
        },
        .hypothesis, .predicate => {
            try self.wantRefs(c, 1);
            return .{ .hypothesis = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .modus_ponens => {
            try self.wantRefs(c, 2);
            return .{ .modus_ponens = .{
                .implication = try self.resolveStepRef(w, c.refs[0]),
                .antecedent = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .implies_intro => {
            try self.wantRefs(c, 1);
            return .{ .implies_intro = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .forall_intro => {
            try self.wantRefs(c, 1);
            return .{ .forall_intro = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .forall_elim => {
            try self.wantRefs(c, 1);
            var cur = try self.resolveStepRef(w, c.refs[0]);
            var cur_formula = self.low_steps.items[@intFromEnum(cur.id)].formula;
            for (c.args[0 .. c.args.len - 1]) |arg_expr| {
                const node = self.pool.get(cur_formula);
                if (node != .quant or node.quant.q != .forall) {
                    return self.fail(Elab.exprLoc(arg_expr), "forall_elim: '{s}' is not universally quantified here", .{try self.renderTerm(cur_formula)});
                }
                const arg = try e.elaborateExpr(arg_expr);
                const opened = try self.pool.open(node.quant.body, arg.id);
                cur = try self.emitSynthetic(kb, Elab.exprLoc(arg_expr), opened, .{
                    .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = Elab.exprLoc(arg_expr) },
                });
                cur_formula = opened;
            }
            const last = c.args[c.args.len - 1];
            const arg = try e.elaborateExpr(last);
            const last_loc = Elab.exprLoc(last);
            // REFINED-SORT elim: `∀h:H; P` is stored `∀h; good(h) -> P`, so opening at t
            // yields `good(t) -> P(t)` while the step claims bare `P(t)` (the "for h IN H"
            // abstraction). If the opened form peels its leading antecedent to the claim,
            // auto-DISCHARGE that guard: emit the elim, prove the guard, modus_ponens.
            const qn = self.pool.get(cur_formula);
            if (qn == .quant and qn.quant.q == .forall) {
                const opened = try self.pool.open(qn.quant.body, arg.id);
                const on = self.pool.get(opened);
                if (!self.pool.alphaEq(opened, goal) and on == .bin and on.bin.op == .implies and self.pool.alphaEq(on.bin.rhs, goal)) {
                    if (try self.emitDischargeStep(kb, last_loc, on.bin.lhs)) |g_step| {
                        const elim = try self.emitSynthetic(kb, last_loc, opened, .{ .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = last_loc } });
                        return .{ .modus_ponens = .{ .implication = elim, .antecedent = g_step } };
                    }
                }
            }
            return .{ .forall_elim = .{
                .step = cur,
                .with = arg.id,
                .with_loc = last_loc,
            } };
        },
        .exists_intro => {
            try self.wantRefs(c, 1);
            const arg = try e.elaborateExpr(c.args[0]);
            return .{ .exists_intro = .{
                .step = try self.resolveStepRef(w, c.refs[0]),
                .witness = arg.id,
                .witness_loc = Elab.exprLoc(c.args[0]),
            } };
        },
        .exists_elim => {
            try self.wantRefs(c, 1);
            return .{ .exists_elim = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .and_intro => {
            try self.wantRefs(c, 2);
            if (self.isBiconditionalShape(goal)) {
                return self.fail(c.rule.start, "this goal is a biconditional '(X -> Y) and (Y -> X)' — use `iff_intro` (which is the same rule, named for what it proves)", .{});
            }
            return .{ .and_intro = .{
                .left = try self.resolveStepRef(w, c.refs[0]),
                .right = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .and_elim_left => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_left = try self.resolveStepRef(w, c.refs[0]) };
        },
        .and_elim_right => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_right = try self.resolveStepRef(w, c.refs[0]) };
        },
        .iff_intro => {
            try self.wantRefs(c, 2);
            if (!self.isBiconditionalShape(goal)) {
                return self.fail(c.rule.start, "iff_intro's goal must be a biconditional (from `P iff Q`); this goal is not of the form '(X -> Y) and (Y -> X)' — did you mean `and_intro`?", .{});
            }
            return .{ .and_intro = .{
                .left = try self.resolveStepRef(w, c.refs[0]),
                .right = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .iff_elim_forward => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_left = try self.resolveStepRef(w, c.refs[0]) };
        },
        .iff_elim_backward => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_right = try self.resolveStepRef(w, c.refs[0]) };
        },
        .or_intro_left => {
            try self.wantRefs(c, 1);
            return .{ .or_intro_left = try self.resolveStepRef(w, c.refs[0]) };
        },
        .or_intro_right => {
            try self.wantRefs(c, 1);
            return .{ .or_intro_right = try self.resolveStepRef(w, c.refs[0]) };
        },
        .or_elim => {
            try self.wantRefs(c, 3);
            return .{ .or_elim = .{
                .disj = try self.resolveStepRef(w, c.refs[0]),
                .left = try self.resolveBlockRef(w, c.refs[1]),
                .right = try self.resolveBlockRef(w, c.refs[2]),
            } };
        },
        .not_intro => {
            try self.wantRefs(c, 3);
            return .{ .not_intro = .{
                .block = try self.resolveBlockRef(w, c.refs[0]),
                .s1 = try self.resolveStepRef(w, c.refs[1]),
                .s2 = try self.resolveStepRef(w, c.refs[2]),
            } };
        },
        .absurd => {
            try self.wantRefs(c, 2);
            return .{ .absurd = .{
                .s1 = try self.resolveStepRef(w, c.refs[0]),
                .s2 = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .double_negation => {
            try self.wantRefs(c, 1);
            return .{ .double_negation = try self.resolveStepRef(w, c.refs[0]) };
        },
        .reflexivity => {
            try self.wantRefs(c, 0);
            return .reflexivity;
        },
        .symmetry => {
            try self.wantRefs(c, 1);
            return .{ .symmetry = try self.resolveStepRef(w, c.refs[0]) };
        },
        .rewrite => {
            try self.wantRefs(c, 2);
            return .{ .rewrite = .{
                .equation = try self.resolveStepRef(w, c.refs[0]),
                .target = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .iff_rewrite => {
            try self.wantRefs(c, 2);
            return .{ .iff_rewrite = .{
                .biconditional = try self.resolveStepRef(w, c.refs[0]),
                .target = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
    }
}

// -- conclusion ------------------------------------------------------------------------

/// Walk done: seal the root, kernel-check the whole lowering against `goal`, then the
/// use-all-facts pass (unless --draft). True iff the theorem is established.
pub fn finish(self: *Prove, goal: TermId, goal_loc: u32) Allocator.Error!bool {
    self.low_blocks.items[0].last_step = @intCast(self.low_steps.items.len);
    var k: kernel.Kernel = .{
        .arena = self.ctx.arena,
        .pool = self.pool,
        .interner = self.ctx.interner,
        .sink = self.ctx.sink,
    };
    const proven = try k.check(.{ .steps = self.low_steps.items, .blocks = self.low_blocks.items }, goal, goal_loc);
    if (!proven) return false;
    if (!self.ctx.verify.draft) {
        if (!try self.checkAllStepsUsed()) return false;
    }
    return true;
}

// -- use-all-facts reachability (ported from the eager pass) ---------------------------

fn checkAllStepsUsed(self: *Prove) Allocator.Error!bool {
    const steps = self.low_steps.items;
    const blocks = self.low_blocks.items;
    if (steps.len == 0) return true;
    const arena = self.ctx.arena;
    const reached = try arena.alloc(bool, steps.len);
    @memset(reached, false);
    const lastStepOf = struct {
        fn f(bs: []const kernel.Block, b: kernel.BlockId) ?u32 {
            const blk = bs[@intFromEnum(b)];
            if (blk.last_step > blk.first_step) return blk.last_step - 1;
            return null;
        }
    }.f;
    var seed: ?u32 = null;
    {
        var it: usize = steps.len;
        while (it > 0) {
            it -= 1;
            if (@intFromEnum(steps[it].block) == 0) {
                seed = @intCast(it);
                break;
            }
        }
    }
    const start = seed orelse return true;
    var work: std.ArrayList(u32) = .empty;
    try work.append(arena, start);
    reached[start] = true;
    for (self.extra_reachable_steps.items) |di| try mark(reached, &work, arena, di);
    while (work.pop()) |si| {
        {
            var b: ?kernel.BlockId = steps[si].block;
            while (b) |bid| {
                const blk = blocks[@intFromEnum(bid)];
                if (blk.kind == .unpack) try mark(reached, &work, arena, @intFromEnum(blk.kind.unpack.source.id));
                b = blk.parent;
            }
        }
        switch (steps[si].just) {
            .modus_ponens => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.implication.id));
                try mark(reached, &work, arena, @intFromEnum(r.antecedent.id));
            },
            .forall_elim => |r| try mark(reached, &work, arena, @intFromEnum(r.step.id)),
            .exists_intro => |r| try mark(reached, &work, arena, @intFromEnum(r.step.id)),
            .and_intro => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.left.id));
                try mark(reached, &work, arena, @intFromEnum(r.right.id));
            },
            .and_elim_left, .and_elim_right, .or_intro_left, .or_intro_right, .double_negation, .symmetry => |sr| try mark(reached, &work, arena, @intFromEnum(sr.id)),
            .rewrite => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.equation.id));
                try mark(reached, &work, arena, @intFromEnum(r.target.id));
            },
            .iff_rewrite => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.biconditional.id));
                try mark(reached, &work, arena, @intFromEnum(r.target.id));
            },
            .absurd => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.s1.id));
                try mark(reached, &work, arena, @intFromEnum(r.s2.id));
            },
            .not_intro => |r| {
                if (lastStepOf(blocks, r.block.id)) |ls| try mark(reached, &work, arena, ls);
                try mark(reached, &work, arena, @intFromEnum(r.s1.id));
                try mark(reached, &work, arena, @intFromEnum(r.s2.id));
            },
            .or_elim => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.disj.id));
                if (lastStepOf(blocks, r.left.id)) |ls| try mark(reached, &work, arena, ls);
                if (lastStepOf(blocks, r.right.id)) |ls| try mark(reached, &work, arena, ls);
            },
            .implies_intro, .forall_intro, .exists_elim => |b| {
                if (lastStepOf(blocks, b.id)) |ls| try mark(reached, &work, arena, ls);
            },
            .hypothesis => {},
            .schema_instance => |r| for (r.premises) |p| try mark(reached, &work, arena, @intFromEnum(p.id)),
            .axiom_ref, .theorem_ref, .reflexivity, .accelerated => {},
        }
    }
    var any_dead = false;
    for (steps, 0..) |s, i| {
        if (reached[i]) continue;
        const label = self.ctx.interner.stringBytes(s.label);
        if (std.mem.indexOfScalar(u8, label, '#') != null) continue; // synthetic
        self.ctx.sink.add(s.loc, "unused fact: step '{s}' is never used — no later step or the conclusion cites it (a proof must use every fact it introduces; use --draft while filling in a proof)", .{label}) catch return error.OutOfMemory;
        any_dead = true;
    }
    return !any_dead;
}

fn mark(reached: []bool, work: *std.ArrayList(u32), arena: Allocator, id: u32) Allocator.Error!void {
    if (id >= reached.len or reached[id]) return;
    reached[id] = true;
    try work.append(arena, id);
}
