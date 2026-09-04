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
    const target = w.findStep(name) orelse {
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
    const target = w.findStep(name) orelse {
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
    // The rule word dispatches by its RESERVED StrId (integer comparison — no strcmp past
    // parsing); a non-rule word is a typo or an accelerant, neither supported yet.
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
