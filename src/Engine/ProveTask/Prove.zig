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
const Polynomial = @import("Polynomial.zig");
const simplify_mod = @import("simplify.zig");
const presburger_mod = @import("presburger.zig");
const smt = @import("smt.zig");
const farkas = @import("farkas.zig");
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
/// currently-expanding define locators — the cycle guard for `define TWO = TWO` and mutual
/// define cycles. Reset per formula (an expansion always unwinds before the next one), so a
/// leftover entry can't leak across formulae. Installed on every Elab this Prove builds.
define_stack: std.ArrayList(InternPool.Index) = .empty,
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
    var e = Elab.init(self.ctx.arena, self.ctx.io, self.ctx, self.ctx.interner, &self.ctx.idents, self.pool, self.ctx.sink, self.source, w, self.ns, &self.fresh_counter);
    e.schema_args = self.schema_args; // null in an ordinary proof; set for a schema instance
    e.model = self.model; // .universe (identity) in an ordinary proof; M for a model transfer
    e.tccs = &self.pending_tccs; // refined-sort obligation sink (Step 3c)
    e.result_facts = &self.result_facts;
    e.define_stack = &self.define_stack; // define-expansion cycle guard
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

/// A term's sort: an fvar's own sort, an app's head result sort; `.prop` for non-term
/// structure. (The operand sort for polynomial's rule-pattern fvars comes from here.)
fn termSort(self: *const Prove, t: TermId) SortId {
    return switch (self.pool.get(t)) {
        .fvar => |v| v.sort,
        .app => |a| @enumFromInt(@intFromEnum(self.ctx.interner.symResult(@enumFromInt(@intFromEnum(a.sym))))),
        else => @enumFromInt(@intFromEnum(InternPool.Index.prop)),
    };
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

pub fn freshNamed(self: *Prove, prefix: []const u8) Error!StrId {
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
            // `arithmetic` needs its well-known operator symbols RESOLVED (add for the mul/order
            // certs, etc.) even when the goal itself doesn't mention them (a pure-succ order
            // goal, ground `mul`). Demand every well-known name DECLARED in this file so the
            // producer's ident lookups find them done; a name absent from the file is skipped
            // (no fetch, no error). No-op for the other accelerants.
            const arith_id = try self.ctx.interner.internString("arithmetic");
            const arith_q_id = try self.ctx.interner.internString("arithmetic_quantified");
            if (c.rule.name == arith_id or c.rule.name == arith_q_id) {
                if (try self.demandArithIdents(c.rule.start)) |blocker| return blocker;
            }
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

/// Demand (fetch + suspend) the well-known arithmetic operator idents DECLARED in this file,
/// so `readArithSymbols`' ident lookups find them `done` in the producer. Only declared names
/// are demanded (a missing one is skipped — no fetch, no "reference not found"). Returns a
/// blocker to suspend on, or null when all are resolved.
fn demandArithIdents(self: *Prove, loc: u32) Allocator.Error!?Engine.TaskIndex {
    const wk = [_][]const u8{ "add", "mul", "succ", "prev", "ZERO", "ONE", "neg", "sub", "less_than", "nonneg" };
    const fid = self.ctx.pool_file.get(self.file).?;
    var refs: std.ArrayList(RefScan.Ref) = .empty;
    for (wk) |name| {
        const nid = self.ctx.interner.internString(name) catch return error.OutOfMemory;
        if (self.ctx.declOf(fid, nid) == null) continue; // not declared here → skip
        try refs.append(self.ctx.arena, .{ .ns = null, .name = nid, .domain = .ident, .loc = loc });
    }
    return resolveRefs(self.ctx, self.h, self.file, self.ns, refs.items);
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
    /// the schema's Fact (params + formula) — a schema is an axiom/theorem/hole whose
    /// `Fact.params != null` (extracted via `ast.factOf`, decl-kind-agnostic).
    fact: ast.Fact,
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
    // a schema is an axiom/theorem/hole with params; extract its Fact decl-kind-agnostically.
    const fact = ast.factOf(decl) orelse
        return self.fail(tok.start, "'{s}' is not a schema", .{self.text(tok)});
    return .{
        .file = loc.file,
        .ns = ns,
        .name = loc.name,
        .fact = fact,
        .source = self.ctx.files.items[@intFromEnum(fid)].source,
    };
}

/// Elaborate the instantiation args in the CALLER's Elab `e` (caller scope + ns, so args
/// may reference caller-local binders), binding each schema param to a `Schema.SchemaArg`.
/// A value param → the elaborated arg term; an N-ary param → a lambda arg (or a bare
/// symbol eta-expanded). Sort tokens resolve in the SCHEMA's ns via a schema-scoped Elab.
fn bindSchemaArgs(self: *Prove, e: *Elab, rs: ResolvedSchema, c: ast.Step.Claim) Error!*Schema.SchemaArgs {
    const params = rs.fact.params.?;
    if (c.args.len != params.len) {
        return self.fail(c.schema.?.start, "schema '{s}' expects {d} argument(s), got {d}", .{
            self.text(c.schema.?), params.len, c.args.len,
        });
    }
    // a schema-scoped Elab to resolve param SORT tokens in the schema's ns. Under a model
    // TRANSFER it is model-aware, so a param sort `Elem` remaps to its target (`Num`) —
    // matching the caller's already-remapped lambda args.
    var empty_walk = Walk.init(self.ctx.arena, self.ctx.interner, rs.source, self.ctx.sink);
    var se = Elab.init(self.ctx.arena, self.ctx.io, self.ctx, self.ctx.interner, &self.ctx.idents, self.pool, self.ctx.sink, rs.source, &empty_walk, rs.ns, &self.fresh_counter);
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
    const params = rs.fact.params.?;
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
    if (c.rule.name == try self.internStr("assoc")) return try self.produceAssoc(w, goal, c);
    if (c.rule.name == try self.internStr("assoc_quantified")) return try self.produceAssocQuantified(w, goal, c);
    if (c.rule.name == try self.internStr("assoc_commut")) return try self.produceAssocCommut(w, goal, c);
    if (c.rule.name == try self.internStr("assoc_commut_quantified")) return try self.produceAssocCommutQuantified(w, goal, c);
    if (c.rule.name == try self.internStr("polynomial")) return try self.producePolynomial(w, goal, c);
    if (c.rule.name == try self.internStr("polynomial_quantified")) return try self.producePolynomialQuantified(w, goal, c);
    if (c.rule.name == try self.internStr("extensionality")) return try self.produceExtensionality(w, goal, c);
    if (c.rule.name == try self.internStr("extensionality_quantified")) return try self.produceExtensionalityQuantified(w, goal, c);
    if (c.rule.name == try self.internStr("arithmetic")) return try self.produceArithmetic(w, goal, c);
    if (c.rule.name == try self.internStr("arithmetic_quantified")) return try self.produceArithmetic(w, goal, c);
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
    // simplify's/chain's/assoc('s)/assoc_commut's antecedents are only their LOCAL equation
    // refs (globals — the assoc lemma arg, the AC triple, distribute pre-rules — cited in the
    // cert). assoc has no refs (its lemma rides `c.args`); assoc_commut's `c.refs` are its
    // optional distribute pre-rules, whose LOCAL members are antecedents.
    if (c.rule.name == try self.internStr("simplify") or c.rule.name == try self.internStr("simplify_quantified") or
        c.rule.name == try self.internStr("chain") or
        c.rule.name == try self.internStr("assoc") or c.rule.name == try self.internStr("assoc_quantified") or
        c.rule.name == try self.internStr("assoc_commut") or c.rule.name == try self.internStr("assoc_commut_quantified") or
        c.rule.name == try self.internStr("polynomial") or c.rule.name == try self.internStr("polynomial_quantified") or
        c.rule.name == try self.internStr("extensionality") or c.rule.name == try self.internStr("extensionality_quantified") or
        c.rule.name == try self.internStr("arithmetic") or c.rule.name == try self.internStr("arithmetic_quantified"))
    {
        // polynomial has NO refs (all rules are global well-known lemmas cited inside the cert);
        // localRefsToSteps returns empty for it. The others' LOCAL equation refs are antecedents.
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
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
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
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = &.{} }, .steps = steps } } },
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
    var local_pf: std.ArrayList(TermId) = .empty;
    for (prepared) |p| if (p.local) try local_pf.append(self.ctx.arena, p.formula);
    const ag = try self.abstractGoal(&b, eq_goal_raw, local_pf.items, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;

    // A LOCAL rule's lhs/rhs are in the CALLER's eigenvar space (`k,b,c`); the goal was just
    // abstracted into param space (`p1,p2,…`). Re-substitute each local rule through `abs` so it
    // matches the param-space goal subterms — else a local IH rewrite never fires (its pattern
    // names `k` while the goal names `p1`). Global rules are closed, unaffected.
    for (prepared, rules) |p, *ru| if (p.local) {
        ru.lhs = try self.substFvarsToParams(ru.lhs, abs);
        ru.rhs = try self.substFvarsToParams(ru.rhs, abs);
    };

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
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
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

/// The shared accelerant preamble: abstract the goal's free caller-local fvars (an enclosing
/// `fix` at the call site) into value params `p1, p2, …`, INCLUDING those shared with a local
/// premise's formula (so premise + goal + cert steps all speak the param names), while EXCLUDING
/// `eigen` (a quantified-variant's peeled ∀ vars, re-bound by the `fix` wrapper). Returns the
/// abstraction + the param-substituted goal. Every producer opens with this; callers then
/// `substFvarsToParams` their own (typed) premise formulae with the returned `abs`.
const AbstractedGoal = struct { abs: FvarAbstraction, goal_p: TermId };
fn abstractGoal(self: *Prove, b: *Accelerant.Builder, goal: TermId, local_prem_formulae: []const TermId, eigen: []const term.Node.Fvar) Error!AbstractedGoal {
    var abs_terms: std.ArrayList(TermId) = .empty;
    try abs_terms.append(self.ctx.arena, goal);
    try abs_terms.appendSlice(self.ctx.arena, local_prem_formulae);
    const abs = try self.abstractFreeFvars(b, abs_terms.items, eigen);
    return .{ .abs = abs, .goal_p = try self.substFvarsToParams(goal, abs) };
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
    var local_pf: std.ArrayList(TermId) = .empty;
    for (prepared) |p| if (p.local) try local_pf.append(self.ctx.arena, p.formula);
    const ag = try self.abstractGoal(&b, goal, local_pf.items, &.{});
    const abs = ag.abs;

    const gn = self.pool.get(ag.goal_p).eq;
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
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = try self.localRefTokens(w, c.refs), // discharged at the call site
    };
}

// -- assoc / assoc_commut (the reordering accelerants) ---------------------------------
//
// Both prove an equation `s = t` by NORMALIZING both sides with a fabricated rule set and
// joining via the shared EqCert — the same certificate shape as `simplify`, differing only
// in HOW the rules + traces are produced:
//   - `assoc(lemma)`  right-nests each side with a single associativity rule (from the arg
//     lemma), so the two right-nested combs coincide iff the sides differ by associativity
//     alone. No reordering, no commutativity.
//   - `assoc_commut`  additionally bubble-sorts the flattened summands into a canonical
//     order (one fabricated rewrite per transposition, via the commutativity/swap lemmas),
//     so the sides coincide iff they are the same multiset of atoms under A/C.
// The synthetic schema is specialize-shaped exactly as simplify's (value params abstract the
// goal's free fix-eigenvariable fvars; the `_quantified` variants re-generalize peeled ∀
// eigenvariables via `fix`/`forall_intro`); the shared `finishReorder` builds it.

/// Resolve an accelerant ARGUMENT (a bare-name expr naming an equation lemma) into a prepared
/// rewrite rule + its cert cite — the arg-expr analogue of `prepareRule` (which takes a ref
/// token). A GLOBAL lemma is cited `[by axiom|theorem …]` inside the cert; a LOCAL step is
/// restated by hypothesis. (assoc/assoc_commut lemmas are demanded as `.fact` in the read
/// pass when they are bare names — see RefScan's accelerant arm.)
fn argRule(self: *Prove, w: *const Walk, arg: *const ast.Expr) Error!PreparedRule {
    if (arg.* != .name) return self.fail(Elab.exprLoc(arg), "argument must name an equation lemma", .{});
    return self.prepareRule(w, arg.name);
}

/// `using assoc(assocLemma)` — prove `s = t` when the sides differ by ASSOCIATIVITY ALONE of
/// a single operator. The lemma (the sole arg) must have shape `f(f(a,b),c) = f(a,f(b,c))`;
/// the operator `f` is recovered from its LHS head. Right-nests both sides with the lemma as
/// a terminating rewrite and joins.
fn produceAssoc(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const gn = self.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return self.fail(c.rule.start, "assoc proves equations; use assoc_quantified for a 'forall …; s = t' goal", .{});
        }
        return self.fail(c.rule.start, "assoc proves equations; the goal is not an equation", .{});
    }
    return self.buildAssoc(w, c, goal, &.{});
}

/// `using assoc_quantified(assocLemma)` — like assoc but over a `forall …; s = t` goal: peel
/// the ∀ prefix into eigenvariables, reorder the body, re-generalize.
fn produceAssocQuantified(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const peeled = try self.peelForallEq(goal, c, "assoc_quantified") orelse return null;
    return self.buildAssoc(w, c, peeled.body, peeled.eigen);
}

/// Shared assoc core over the (possibly ∀-peeled) equation body `eq_goal_raw`. Abstracts the
/// goal's free caller-locals into params, builds the one-rule assoc set from the arg lemma,
/// right-nests both sides, and hands the join to `finishReorder`.
fn buildAssoc(self: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    if (c.args.len != 1) {
        return self.fail(c.rule.start, "assoc requires an associativity lemma: assoc(<assocLemma>); got {d} argument(s)", .{c.args.len});
    }
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    const prepared = try self.argRule(w, c.args[0]);
    // validate the shape `f(f(a,b),c) = f(a,f(b,c))`: the LHS must be a binary app whose head
    // `f` is shared by the RHS. (The rule's binders/lhs/rhs carry pattern fvars already.)
    const l = self.pool.get(prepared.rule.lhs);
    if (l != .app or l.app.args_len != 2) {
        return self.fail(Elab.exprLoc(c.args[0]), "assoc: the associativity lemma must have shape 'f(f(a, b), c) = f(a, f(b, c))'", .{});
    }
    const op_sym = l.app.sym;
    const r = self.pool.get(prepared.rule.rhs);
    if (r != .app or r.app.sym != op_sym) {
        return self.fail(Elab.exprLoc(c.args[0]), "assoc: the associativity lemma's two sides must share the operator", .{});
    }

    // abstract free caller-local fvars into params UP FRONT (before normalizing) so the goal,
    // the trace, and the schema body all speak `p1, p2, …`. Eigenvariables stay free (re-bound
    // by the `fix` wrapper). A LOCAL lemma's formula may share such an fvar — include it.
    const local_pf: []const TermId = if (prepared.local) &.{prepared.formula} else &.{};
    const ag = try self.abstractGoal(&b, eq_goal_raw, local_pf, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = self.pool.get(eq_goal).eq;
    const s = gn.lhs;
    const t = gn.rhs;

    const rules = [_]simplify_mod.Rule{prepared.rule};
    const cites = [_]EqCert.RuleCite{prepared.cite};

    // right-nest each side by the single associativity rule (terminating). The resulting
    // canonical forms agree iff the sides differ by associativity alone.
    const rs = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, &rules, s, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, &rules, t, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "assoc: rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        return self.fail(c.rule.start, "assoc: sides differ by more than associativity: '{s}' vs '{s}'", .{
            try self.renderTerm(try self.unabstract(rs.nf, abs)),
            try self.renderTerm(try self.unabstract(rt.nf, abs)),
        });
    }
    return self.finishReorder(w, &b, c, "assoc", s, t, &rules, &cites, rs, rt, abs, eigen, if (prepared.local) &.{prepared} else &.{});
}

/// `using assoc_commut` (bare = the well-known add/mul triple) or `assoc_commut(a, c, s)`
/// (an explicit assoc/comm/swap triple for a custom operator) — reorder an A/C sum: optional
/// distribute pre-pass (LOCAL cited refs → antecedents), then re-associate + flatten +
/// bubble-sort each side into canonical order, joining the concatenated traces.
fn produceAssocCommut(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const gn = self.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return self.fail(c.rule.start, "assoc_commut proves equations; use assoc_commut_quantified for a 'forall …; s = t' goal", .{});
        }
        return self.fail(c.rule.start, "assoc_commut proves equations; the goal is not an equation", .{});
    }
    return self.buildAssocCommut(w, c, goal, &.{});
}

fn produceAssocCommutQuantified(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const peeled = try self.peelForallEq(goal, c, "assoc_commut_quantified") orelse return null;
    return self.buildAssocCommut(w, c, peeled.body, peeled.eigen);
}

// -- polynomial / polynomial_quantified (the ring-identity accelerant) -----------------
//
// A theory-parameterized accelerant that proves a ring identity `s = t` by canonicalizing
// BOTH sides to the same sorted-sum-of-sorted-monomials normal form and emitting the
// distribute/fold/sort/cancel rewrite chain as a kernel-checked certificate. Per the design
// (memory accelerant-ast-mapping-no-checks): a DETERMINISTIC (goal AST, selector) -> proof AST
// function — the ring rewrite SHAPES are hardcoded (Polynomial.polyRules), the well-known
// lemma NAMES are emitted as cite tokens QUALIFIED by the theory selector (`c.schema`, or
// bare), and NOTHING is looked up here. The generated schema's ProveTask resolves the cited
// names + kernel-checks each rewrite; a missing/mismatched lemma fails THERE.

/// `[using polynomial(M) ]` — prove an equation goal `s = t` as a ring identity.
fn producePolynomial(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "polynomial takes no arguments (the theory is the parenthesized selector)", .{});
    const gn = self.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return self.fail(c.rule.start, "polynomial proves equations; did you mean polynomial_quantified?", .{});
        }
        return self.fail(c.rule.start, "polynomial: goal is not an equation", .{});
    }
    return self.buildPolynomial(w, c, goal, &.{});
}

/// `[using polynomial_quantified(M) ]` — like polynomial but the goal is `forall …; s = t`.
fn producePolynomialQuantified(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "polynomial_quantified takes no arguments (the theory is the parenthesized selector)", .{});
    const peeled = try self.peelForallEq(goal, c, "polynomial_quantified") orelse return null;
    return self.buildPolynomial(w, c, peeled.body, peeled.eigen);
}

/// Shared polynomial core over the (possibly ∀-peeled) equation body `eq_goal_raw`. Reads the
/// ring operator syms off the goal, builds the hardcoded rule set + selector-qualified cites,
/// abstracts free caller-locals into params, canonicalizes both sides IN PARAM SPACE, and hands
/// the traces to `finishReorder`. `polynomial` has no LOCAL premises (all its rules are global
/// well-known lemmas cited inside the cert), so `local_prems` is empty.
fn buildPolynomial(self: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // read the ring operators off the goal (by well-known head NAME — inspecting the goal, not
    // a scope lookup). `add`/`mul` are required; the rest are optional (present iff the goal
    // has them). The theory selector's qualifier is stamped into every emitted cite.
    const ops = (try self.readPolyOps(eq_goal_raw)) orelse
        return self.fail(c.rule.start, "polynomial: the goal has no add/mul structure", .{});
    const qualifier: StrId = if (c.schema) |s| s.name else .none;
    const pr = try Polynomial.polyRules(self, ops, qualifier, c.rule.start);

    // abstract free caller-local fvars (an enclosing `fix`) into value params, then canonicalize
    // in PARAM space so the trace + schema body speak `p1, p2, …`. Eigenvariables (the peeled ∀
    // vars) stay free and are re-bound by the `fix` wrapper in finishReorder.
    const ag = try self.abstractGoal(&b, eq_goal_raw, &.{}, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = self.pool.get(eq_goal).eq;
    const s0 = gn.lhs;
    const t0 = gn.rhs;

    const rs = (try Polynomial.polyCanon(self, pr, s0)) orelse
        return self.fail(c.rule.start, "polynomial: could not canonicalize the left side", .{});
    const rt = (try Polynomial.polyCanon(self, pr, t0)) orelse
        return self.fail(c.rule.start, "polynomial: could not canonicalize the right side", .{});
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        return self.fail(c.rule.start, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
            try self.renderTerm(try self.unabstract(rs.nf, abs)),
            try self.renderTerm(try self.unabstract(rt.nf, abs)),
        });
    }
    return self.finishReorder(w, &b, c, "polynomial", s0, t0, pr.rules, pr.cites, rs, rt, abs, eigen, &.{});
}

/// Read the ring operator SymIds off `eq_goal` (an equation) by scanning for apps whose head
/// NAME is a well-known ring operator. `add`/`mul` are required (null return if either is
/// absent). The operand sort (for freshly-built rule-pattern fvars) is the equation's lhs sort.
fn readPolyOps(self: *Prove, eq_goal: TermId) Error!?Polynomial.Ops {
    const eqn = self.pool.get(eq_goal);
    if (eqn != .eq) return null;
    var found: Polynomial.Ops = .{
        .add = undefined,
        .mul = undefined,
        .zero = null,
        .one = null,
        .neg = null,
        .sub = null,
        .succ = null,
        .prev = null,
        .sort = @enumFromInt(@intFromEnum(self.termSort(eqn.eq.lhs))),
    };
    var have_add = false;
    var have_mul = false;
    try self.collectPolyOps(eq_goal, &found, &have_add, &have_mul);
    if (!have_add or !have_mul) return null;
    return found;
}

/// Recursively match each app head's well-known NAME, filling `ops`. Pure goal inspection.
fn collectPolyOps(self: *Prove, id: TermId, ops: *Polynomial.Ops, have_add: *bool, have_mul: *bool) Error!void {
    const node = self.pool.get(id);
    switch (node) {
        .app => |a| {
            const name = self.ctx.interner.stringBytes(self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(a.sym))));
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
            // copy arg ids before recursing (pool.args aliases pool.extra).
            const args = try self.ctx.arena.dupe(TermId, self.pool.args(a));
            for (args) |arg| try self.collectPolyOps(arg, ops, have_add, have_mul);
        },
        .eq => |p| {
            try self.collectPolyOps(p.lhs, ops, have_add, have_mul);
            try self.collectPolyOps(p.rhs, ops, have_add, have_mul);
        },
        .bin => |bb| {
            try self.collectPolyOps(bb.lhs, ops, have_add, have_mul);
            try self.collectPolyOps(bb.rhs, ops, have_add, have_mul);
        },
        .not => |n| try self.collectPolyOps(n, ops, have_add, have_mul),
        .quant => |q| try self.collectPolyOps(q.body, ops, have_add, have_mul),
        else => {},
    }
}

/// Build the associativity / commutativity / swap triple for `op_sym` as HARDCODED rewrite
/// shapes (no facts.lookup), appending to `rules`/`cites` in the order assoc, comm, swap. The
/// cites name the well-known lemmas BARE (resolved in the proof's namespace by the generated
/// schema's ProveTask + kernel-checked). Shapes:
///   assoc: f(f(a,b),c) = f(a,f(b,c));  comm: f(a,b) = f(b,a);  swap: f(x,f(y,r)) = f(y,f(x,r))
fn pushACTriple(self: *Prove, rules: *std.ArrayList(simplify_mod.Rule), cites: *std.ArrayList(EqCert.RuleCite), op_sym: term.SymId, sort: term.SortId, assoc_name: []const u8, comm_name: []const u8, swap_name: []const u8, loc: u32) Error!void {
    // assoc: f(f(a,b),c) = f(a,f(b,c))
    {
        const a = try self.freshACFvar(sort);
        const b = try self.freshACFvar(sort);
        const cc = try self.freshACFvar(sort);
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = b.name, .sort = sort }, .{ .fvar = cc.name, .sort = sort } });
        const lhs = try self.pool.addApp(.app, op_sym, &.{ try self.pool.addApp(.app, op_sym, &.{ a.t, b.t }), cc.t });
        const rhs = try self.pool.addApp(.app, op_sym, &.{ a.t, try self.pool.addApp(.app, op_sym, &.{ b.t, cc.t }) });
        try self.pushHardcoded(rules, cites, binders, lhs, rhs, assoc_name, loc);
    }
    // comm: f(a,b) = f(b,a)
    {
        const a = try self.freshACFvar(sort);
        const b = try self.freshACFvar(sort);
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = b.name, .sort = sort } });
        const lhs = try self.pool.addApp(.app, op_sym, &.{ a.t, b.t });
        const rhs = try self.pool.addApp(.app, op_sym, &.{ b.t, a.t });
        try self.pushHardcoded(rules, cites, binders, lhs, rhs, comm_name, loc);
    }
    // swap: f(x,f(y,r)) = f(y,f(x,r))
    {
        const x = try self.freshACFvar(sort);
        const y = try self.freshACFvar(sort);
        const r = try self.freshACFvar(sort);
        const binders = try self.ctx.arena.dupe(simplify_mod.Binder, &.{ .{ .fvar = x.name, .sort = sort }, .{ .fvar = y.name, .sort = sort }, .{ .fvar = r.name, .sort = sort } });
        const lhs = try self.pool.addApp(.app, op_sym, &.{ x.t, try self.pool.addApp(.app, op_sym, &.{ y.t, r.t }) });
        const rhs = try self.pool.addApp(.app, op_sym, &.{ y.t, try self.pool.addApp(.app, op_sym, &.{ x.t, r.t }) });
        try self.pushHardcoded(rules, cites, binders, lhs, rhs, swap_name, loc);
    }
}

/// A fresh AC pattern fvar of `sort`.
fn freshACFvar(self: *Prove, sort: term.SortId) Error!struct { name: StrId, t: TermId } {
    const name = try self.freshNamed("p#");
    return .{ .name = name, .t = try self.pool.add(.{ .fvar = .{ .name = name, .sort = sort } }) };
}

/// Append one hardcoded rule (binders + lhs/rhs + its ∀-quantified formula) with a BARE cite
/// naming `name_text` (resolved by the generated ProveTask; is_axiom = placeholder).
fn pushHardcoded(self: *Prove, rules: *std.ArrayList(simplify_mod.Rule), cites: *std.ArrayList(EqCert.RuleCite), binders: []const simplify_mod.Binder, lhs: TermId, rhs: TermId, name_text: []const u8, loc: u32) Error!void {
    // ∀-quantify eq(lhs,rhs) over binders, outermost = binders[0] (matches emitInstance).
    var formula = try self.pool.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        const closed = try self.pool.close(formula, binders[i].fvar);
        formula = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = binders[i].sort, .hint = binders[i].fvar, .body = closed } });
    }
    const name = self.ctx.interner.internString(name_text) catch return error.OutOfMemory;
    try rules.append(self.ctx.arena, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = formula });
    try cites.append(self.ctx.arena, .{
        .global = .{
            // stamp the call-site loc so a "reference not found" on the emitted cite points at the
            // `assoc_commut` step, not 1:1.
            .head = .{ .tag = .identifier, .start = loc, .end = loc, .name = name, .qualifier = .none },
            .is_axiom = false,
        },
    });
}

/// Shared assoc_commut core over the (possibly ∀-peeled) equation body. Prepares the AC rule
/// set (distribute pre-rules from `c.refs` at the FRONT, then the AC triple), abstracts the
/// goal, distributes + AC-sorts both sides, and hands the concatenated traces to
/// `finishReorder`.
fn buildAssocCommut(self: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    // exactly two forms: bare (well-known add/mul) or three explicit lemmas. No partials.
    if (c.args.len != 0 and c.args.len != 3) {
        return self.fail(c.rule.start, "assoc_commut takes either no arguments (well-known add/mul) or exactly three (assoc, comm, swap); got {d}", .{c.args.len});
    }
    const explicit = c.args.len == 3;
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // optional distribute PRE-RULES from the cited refs (L→R before flattening); their rule
    // indices sit at the FRONT so the AC bubble-sort's indices shift after them.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var pre_prepared: std.ArrayList(PreparedRule) = .empty;
    for (c.refs) |ref| {
        const p = try self.prepareRule(w, ref);
        try rules.append(self.ctx.arena, p.rule);
        try cites.append(self.ctx.arena, p.cite);
        try pre_prepared.append(self.ctx.arena, p);
    }
    const pre_count = rules.items.len;

    // resolve the AC triple + its operator BEFORE abstracting (an explicit lemma may carry
    // pattern fvars — never caller-locals — so it is unaffected by abstraction). Bare form:
    // pick the operator from the goal's LHS head and resolve the well-known triple.
    var op_sym: term.SymId = undefined;
    if (explicit) {
        const a_rule = try self.argRule(w, c.args[0]);
        const c_rule = try self.argRule(w, c.args[1]);
        const w_rule = try self.argRule(w, c.args[2]);
        const c_lhs = self.pool.get(c_rule.rule.lhs);
        if (c_lhs != .app or c_lhs.app.args_len != 2) {
            return self.fail(Elab.exprLoc(c.args[1]), "assoc_commut: the commutativity lemma must have shape 'f(a, b) = f(b, a)'", .{});
        }
        op_sym = c_lhs.app.sym;
        try rules.append(self.ctx.arena, a_rule.rule);
        try cites.append(self.ctx.arena, a_rule.cite);
        try rules.append(self.ctx.arena, c_rule.rule);
        try cites.append(self.ctx.arena, c_rule.cite);
        try rules.append(self.ctx.arena, w_rule.rule);
        try cites.append(self.ctx.arena, w_rule.cite);
        // an explicit lemma cited by a LOCAL step is an antecedent too.
        if (a_rule.local) try pre_prepared.append(self.ctx.arena, a_rule);
        if (c_rule.local) try pre_prepared.append(self.ctx.arena, c_rule);
        if (w_rule.local) try pre_prepared.append(self.ctx.arena, w_rule);
    } else {
        const gn = self.pool.get(eq_goal_raw).eq;
        const s_head: ?term.SymId = if (self.pool.get(gn.lhs) == .app) self.pool.get(gn.lhs).app.sym else null;
        const op = self.pickWellKnownOp(s_head) orelse
            return self.fail(c.rule.start, "assoc_commut reorders an add- or mul-sum; the goal's left side is '{s}'", .{try self.renderTerm(gn.lhs)});
        op_sym = op.sym;
        // BUILD the AC triple as HARDCODED shapes (no facts.lookup, no existence check) — like
        // polynomial. Each rule's LHS/RHS is constructed from the goal's own operator sym; the
        // well-known lemma NAMES are emitted as bare cites, resolved + kernel-checked by the
        // generated schema's ProveTask (a missing lemma fails THERE). The operand sort is the
        // goal LHS's sort (the reordered operator's carrier).
        const sort: term.SortId = @enumFromInt(@intFromEnum(self.termSort(gn.lhs)));
        try self.pushACTriple(&rules, &cites, op_sym, sort, op.assoc, op.comm, op.swap, c.rule.start);
    }
    const assoc_idx = pre_count;
    const comm_idx = pre_count + 1;
    const swap_idx = pre_count + 2;

    // abstract free caller-locals into params (goal + any LOCAL premise formula), then rewrite
    // both sides IN PARAM SPACE so the trace + schema body speak `p1, p2, …`.
    var local_pf: std.ArrayList(TermId) = .empty;
    for (pre_prepared.items) |p| try local_pf.append(self.ctx.arena, p.formula);
    const ag = try self.abstractGoal(&b, eq_goal_raw, local_pf.items, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = self.pool.get(eq_goal).eq;
    const s0 = gn.lhs;
    const t0 = gn.rhs;

    const symbols: presburger_mod.Symbols = .{ .add = op_sym };
    const pre_rules = rules.items[0..pre_count];

    // distribute both sides (L→R with the pre-rules); traces feed the join unchanged.
    const s_pre = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, pre_rules, s0, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const t_pre = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, pre_rules, t0, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "assoc_commut: pre-normalization rewrite limit reached", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };

    // per side: re-associate to a right-nested comb, flatten, bubble-sort.
    const plan_s = (try self.acPlan(symbols, rules.items, assoc_idx, comm_idx, swap_idx, s_pre.nf)) orelse
        return self.fail(c.rule.start, "assoc_commut: could not re-associate the left side", .{});
    const plan_t = (try self.acPlan(symbols, rules.items, assoc_idx, comm_idx, swap_idx, t_pre.nf)) orelse
        return self.fail(c.rule.start, "assoc_commut: could not re-associate the right side", .{});
    if (!self.pool.alphaEq(plan_s.sorted, plan_t.sorted)) {
        return self.fail(c.rule.start, "assoc_commut: sides have different summands: '{s}' vs '{s}'", .{
            try self.renderTerm(try self.unabstract(plan_s.sorted, abs)),
            try self.renderTerm(try self.unabstract(plan_t.sorted, abs)),
        });
    }
    // prepend the distribution trace so the join replays s0 -> distributed -> sorted.
    const full_s = try self.concatTrace(s_pre.trace, plan_s.trace);
    const full_t = try self.concatTrace(t_pre.trace, plan_t.trace);
    const rs: simplify_mod.Result = .{ .nf = plan_s.sorted, .trace = full_s };
    const rt: simplify_mod.Result = .{ .nf = plan_t.sorted, .trace = full_t };
    return self.finishReorder(w, &b, c, "assoc_commut", s0, t0, rules.items, cites.items, rs, rt, abs, eigen, pre_prepared.items);
}

/// The well-known AC triple + operator for a bare `assoc_commut`, chosen by the goal LHS's
/// head symbol NAME (`add` or `mul`). Null when the head is neither.
const WellKnownOp = struct { sym: term.SymId, assoc: []const u8, comm: []const u8, swap: []const u8 };
fn pickWellKnownOp(self: *Prove, head: ?term.SymId) ?WellKnownOp {
    const h = head orelse return null;
    const name = self.ctx.interner.stringBytes(self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(h))));
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
fn orientRule(self: *Prove, formula: TermId) Error!?simplify_mod.Rule {
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
    if (bn != .eq) return null;
    for (binders.items) |bd| {
        if (!self.pool.occursFree(bn.eq.lhs, bd.fvar)) return null;
    }
    return .{ .binders = binders.items, .lhs = bn.eq.lhs, .rhs = bn.eq.rhs, .formula = formula };
}

/// Peel a `forall …; s = t` goal's ∀ prefix into fresh eigenvariables (returned outermost
/// first) and return the body equation. Diagnoses a non-∀ / non-equation goal per `who`.
const PeeledEq = struct { body: TermId, eigen: []const term.Node.Fvar };
fn peelForallEq(self: *Prove, goal: TermId, c: ast.Step.Claim, comptime who: []const u8) Error!?PeeledEq {
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
        return self.fail(c.rule.start, who ++ " expects a quantified goal; drop the '_quantified' suffix for a bare equation", .{});
    }
    if (self.pool.get(body) != .eq) {
        return self.fail(c.rule.start, who ++ ": the quantified body is not an equation", .{});
    }
    return .{ .body = body, .eigen = eigen.items };
}

/// The shared TAIL for both reordering accelerants (identical to `buildSimplify`'s tail): the
/// rules/cites + the two normalized `Result`s are already built (in PARAM space); emit the
/// EqCert join, wrap in the LOCAL-premise `assume`/`implies_intro` and ∀-eigenvariable
/// `fix`/`forall_intro` shells, and package the synthetic schema. `local_prems` are the
/// PreparedRules whose origin is a LOCAL step (restated by hypothesis + discharged at the call
/// site); the AC triple / assoc lemma when global is cited INSIDE the cert. `name_prefix` seeds
/// the schema hash name.
fn finishReorder(
    self: *Prove,
    w: *const Walk,
    b: *Accelerant.Builder,
    c: ast.Step.Claim,
    comptime name_prefix: []const u8,
    s: TermId,
    t: TermId,
    rules: []const simplify_mod.Rule,
    cites: []const EqCert.RuleCite,
    rs: simplify_mod.Result,
    rt: simplify_mod.Result,
    abs: FvarAbstraction,
    eigen: []const term.Node.Fvar,
    local_prems: []const PreparedRule,
) Error!?Accelerant.Synthetic {
    // build the equation-cert AST proving `s = t`.
    var cert: EqCert = .{ .b = b, .pool = self.pool, .rules = rules, .cites = cites, .fresh_ctx = self, .freshFn = eqCertFresh };
    var body_steps: std.ArrayList(ast.Step) = .empty;
    _ = try cert.emitJoin(&body_steps, s, t, rs, rt);
    var steps: []const ast.Step = body_steps.items;

    // LOCAL premises → schema antecedents (restated by hypothesis, discharged at the call
    // site) in ref order; collect their (cite, param-substituted formula) for the wrappers.
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (local_prems) |p| {
        try local_cites.append(self.ctx.arena, p.cite);
        try local_formulae.append(self.ctx.arena, try self.substFvarsToParams(p.formula, abs));
    }

    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    const inner_prop = try self.impliesChain(eq_prop, local_formulae.items);
    steps = try self.wrapSimplifyPremises(b, local_cites.items, local_formulae.items, eq_prop, steps);
    steps = try self.wrapSimplifyForall(b, eigen, inner_prop, steps);

    // the schema body proposition = the ∀-generalized `inner_prop`.
    var full_prop = inner_prop;
    var ei: usize = eigen.len;
    while (ei > 0) {
        ei -= 1;
        const closed = try self.pool.close(full_prop, eigen[ei].name);
        full_prop = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = eigen[ei].sort, .hint = eigen[ei].name, .body = closed } });
    }
    const body_expr = try b.termExpr(full_prop);

    const params = try self.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        pp.* = .{ .name = b.tok(name), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    const hash = Schema.termHash(self.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, name_prefix ++ "{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = try self.localRefTokens(w, c.refs), // discharged at the call site
    };
}

// -- extensionality / extensionality_quantified ---------------------------------------

/// `[using extensionality(extLemma) unfold1 unfold2 …]` — prove a bare `s = t` equation by
/// extensionality. See `produceExtensionalityQuantified` for the `forall …; s = t` form.
fn produceExtensionality(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.schema == null) return self.fail(c.rule.start, "extensionality requires an extensionality lemma: [using extensionality(<lemma>) <unfold lemmas>]", .{});
    if (self.pool.get(goal) != .eq) {
        if (self.pool.get(goal) == .quant and self.pool.get(goal).quant.q == .forall) {
            return self.fail(c.rule.start, "extensionality proves equations; did you mean extensionality_quantified?", .{});
        }
        return self.fail(c.rule.start, "extensionality proves an equation 's = t'; the goal is not an equation", .{});
    }
    return self.buildExtensionality(w, c, goal, &.{});
}

/// `[using extensionality_quantified(extLemma) unfold1 …]` — like extensionality but the goal
/// is `forall …; s = t`. Peel the ∀ prefix into fresh eigenvariables, run the core on the body
/// equation, and re-generalize via the `fix`/`forall_intro` shell.
fn produceExtensionalityQuantified(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.schema == null) return self.fail(c.rule.start, "extensionality_quantified requires an extensionality lemma: [using extensionality_quantified(<lemma>) <unfold lemmas>]", .{});
    const peeled = (try self.peelForallEq(goal, c, "extensionality_quantified")) orelse return null;
    return self.buildExtensionality(w, c, peeled.body, peeled.eigen);
}

/// A resolved extensionality lemma, read STRUCTURALLY off `c.schema`'s formula: its instantiated
/// obligations (one per pointwise inclusion) + how the cert cites the lemma.
const ExtLemma = struct {
    formula: TermId,
    is_axiom: bool,
    head: lexer.Token,
    /// each obligation `forall x: <elementSort>; body`, instantiated at (s, t) — outermost first.
    obligations: []const TermId,
    /// the element sort (the obligation binder's sort).
    universe: SortId,
};

/// Shared core for both extensionality variants. Instantiate the ext lemma at (s, t), prove each
/// pointwise obligation (`fix x` → unfold → close residue → forall_intro), then modus_ponens the
/// chain to `s = t`; wrap in the ∀-eigenvariable `fix` shell and package the synthetic schema.
fn buildExtensionality(self: *Prove, w: *const Walk, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerant.Synthetic {
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix` at the call site) into value
    // params — the fully-quantified fixtures have none (all free vars are peeled eigenvariables),
    // but a bare `[using extensionality(...)]` over fixed locals would surface them.
    const ag = try self.abstractGoal(&b, eq_goal_raw, &.{}, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const eq = self.pool.get(eq_goal).eq;
    const s = eq.lhs;
    const t = eq.rhs;

    // resolve the ext lemma (global fact) + instantiate at (s, t).
    const lemma = try self.resolveExtLemma(c.schema.?, s, t);

    // resolve each cited UNFOLD lemma to its formula (global facts). For the SET model these are
    // `member(x, op(...)) iff …`; for the FUNCTION model `apply(op(...), x) = …` rewrite rules.
    const unfolds = try self.ctx.arena.alloc(ExtUnfold, c.refs.len);
    for (c.refs, unfolds) |ref, *out| out.* = try self.resolveUnfold(ref);

    // build the cert steps proving `s = t`.
    var body_steps: std.ArrayList(ast.Step) = .empty;
    try self.emitExtEquation(&b, &body_steps, lemma, unfolds, s, t, c);

    // the inner proposition the cert proves: the equation `s = t` (no local premises — the ext +
    // unfold lemmas are all globals cited inside the cert; a LOCAL cite is unusual but supported
    // via the premises slot below).
    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });

    // wrap in `fix` blocks for the ∀ eigenvariables (the quantified variant's re-generalization).
    var steps: []const ast.Step = body_steps.items;
    steps = try self.wrapSimplifyForall(&b, eigen, eq_prop, steps);

    // schema body = the ∀-generalized equation.
    var full_prop = eq_prop;
    var ei: usize = eigen.len;
    while (ei > 0) {
        ei -= 1;
        const closed = try self.pool.close(full_prop, eigen[ei].name);
        full_prop = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = eigen[ei].sort, .hint = eigen[ei].name, .body = closed } });
    }
    const body_expr = try b.termExpr(full_prop);

    const params = try self.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        pp.* = .{ .name = b.tok(name), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    const hash = Schema.termHash(self.pool, full_prop);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "extensionality{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = try self.localRefTokens(w, c.refs), // a LOCAL unfold/ext cite, if any
    };
}

/// Resolve the extensionality lemma token to its formula and instantiate its `forall A, B;`
/// prefix at (s, t), reading off the leading `(forall x; …) ->` obligations. Requires a GLOBAL
/// axiom/theorem (the ext lemma is never a local step in the fixtures).
fn resolveExtLemma(self: *Prove, head: lexer.Token, s: TermId, t: TermId) Error!ExtLemma {
    const fact = try self.resolveFactRef(head);
    const formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
    const is_axiom = self.ctx.interner.keyOf(fact).fact.kind == .axiom;

    // peel the two structure binders at (s, t).
    var body = formula;
    for ([_]TermId{ s, t }) |arg| {
        const node = self.pool.get(body);
        if (node != .quant or node.quant.q != .forall) {
            return self.fail(head.start, "extensionality: '{s}' is not a two-argument universal (forall A, B; …)", .{self.text(head)});
        }
        body = try self.pool.open(node.quant.body, arg);
    }
    // count the leading `(forall x; body) ->` obligations before the `s = t` conclusion.
    var obligations: std.ArrayList(TermId) = .empty;
    var universe: ?SortId = null;
    var cur = body;
    while (true) {
        const node = self.pool.get(cur);
        if (node != .bin or node.bin.op != .implies) break;
        const premise = node.bin.lhs;
        if (self.pool.get(premise) == .quant and self.pool.get(premise).quant.q == .forall) {
            if (universe == null) universe = self.pool.get(premise).quant.sort;
        }
        try obligations.append(self.ctx.arena, premise);
        cur = node.bin.rhs;
    }
    if (obligations.items.len == 0 or universe == null) {
        return self.fail(head.start, "extensionality: '{s}' has no pointwise obligation (forall x: <element>; …)", .{self.text(head)});
    }
    // the residual conclusion must be `s = t`.
    if (self.pool.get(cur) != .eq or !self.pool.alphaEq(self.pool.get(cur).eq.lhs, s) or !self.pool.alphaEq(self.pool.get(cur).eq.rhs, t)) {
        return self.fail(head.start, "extensionality: '{s}' does not conclude the goal equation", .{self.text(head)});
    }
    return .{ .formula = formula, .is_axiom = is_axiom, .head = head, .obligations = obligations.items, .universe = universe.? };
}

/// A resolved unfold lemma: its formula + how the cert cites it. `set_op`/`fn_op` is the head
/// symbol of the characterized operator (for matching a `member(x, op(...))` / `apply(op(...), x)`
/// subterm to its lemma); null when the lemma has no such head (degenerate).
const ExtUnfold = struct {
    formula: TermId,
    is_axiom: bool,
    head: lexer.Token,
    local: bool,
    /// the operator head symbol this lemma characterizes (read off its stripped LHS).
    op: ?term.SymId,
    /// true = a FUNCTION model rewrite (`apply(op,x) = …`); false = a SET model `member iff`.
    is_eq: bool,
};

fn resolveUnfold(self: *Prove, ref: lexer.Token) Error!ExtUnfold {
    // ext unfold lemmas are always GLOBAL facts (membership / apply axioms) in practice.
    const fact = try self.resolveFactRef(ref);
    const formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
    const is_axiom = self.ctx.interner.keyOf(fact).fact.kind == .axiom;
    // strip the forall prefix; classify by the stripped body shape + read the characterized op.
    var body = formula;
    while (self.pool.get(body) == .quant and self.pool.get(body).quant.q == .forall) {
        const q = self.pool.get(body).quant;
        const fv = try self.pool.add(.{ .fvar = .{ .name = try self.freshNamed("u"), .sort = q.sort } });
        body = try self.pool.open(q.body, fv);
    }
    const bn = self.pool.get(body);
    var op: ?term.SymId = null;
    var is_eq = false;
    if (bn == .eq) {
        // FUNCTION model: `apply(op(...), x) = …` — the op is the head of the FIRST apply arg.
        is_eq = true;
        const lhs = self.pool.get(bn.eq.lhs);
        if (lhs == .app and self.pool.args(lhs.app).len >= 1) {
            const first = self.pool.get(self.pool.args(lhs.app)[0]);
            if (first == .app) op = first.app.sym;
        }
    } else {
        // SET model: `member(x, op(...)) iff …` — the op is the head of member's SECOND arg. The
        // iff desugars to a conjunction; the lhs of a conjunct's implication carries `member`.
        is_eq = false;
        op = self.setUnfoldOp(body);
    }
    return .{ .formula = formula, .is_axiom = is_axiom, .head = ref, .local = false, .op = op, .is_eq = is_eq };
}

/// Read the characterized operator head from a SET unfold lemma body. The `iff` desugars to
/// `(member(x, op(...)) -> R) and (R -> member(x, op(...)))`; find the `member(_, op(...))` atom
/// and return `op`'s head symbol (a const head has no args → still a valid sym).
fn setUnfoldOp(self: *Prove, body: TermId) ?term.SymId {
    return self.findMemberOp(body);
}

fn findMemberOp(self: *Prove, id: TermId) ?term.SymId {
    switch (self.pool.get(id)) {
        .pred => |p| {
            const args = self.pool.args(p);
            if (args.len == 2) {
                const set = self.pool.get(args[1]);
                if (set == .app) return set.app.sym;
            }
            return null;
        },
        .bin => |bn| return self.findMemberOp(bn.lhs) orelse self.findMemberOp(bn.rhs),
        .not => |inner| return self.findMemberOp(inner),
        else => return null,
    }
}

/// Emit the extensionality certificate proving `s = t` into `block`: cite the ext lemma,
/// forall_elim it at (s, t) to reach `Ob1 -> (Ob2 ->) s = t`, prove each obligation, and
/// modus_ponens the chain. The lemma cite + each obligation step live directly in `block`.
fn emitExtEquation(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), lemma: ExtLemma, unfolds: []const ExtUnfold, s: TermId, t: TermId, c: ast.Step.Claim) Error!void {
    // step 0: cite the ext lemma.
    const law = try self.freshNamed("extensionality");
    const word: []const u8 = if (lemma.is_axiom) "axiom" else "theorem";
    const law_refs = try self.ctx.arena.alloc(lexer.Token, 1);
    law_refs[0] = lemma.head;
    try block.append(self.ctx.arena, try b.claimStep(law, try b.termExpr(lemma.formula), .by, try self.internStrRt(word), &.{}, law_refs));

    // forall_elim at (s, t): one multi-arg elim peels both structure binders.
    var chain_formula = lemma.formula;
    for ([_]TermId{ s, t }) |arg| {
        chain_formula = try self.pool.open(self.pool.get(chain_formula).quant.body, arg);
    }
    const elim_lbl = try self.freshNamed("extensionality-at-sides");
    const elim_args = try self.ctx.arena.alloc(*const ast.Expr, 2);
    elim_args[0] = try b.termExpr(s);
    elim_args[1] = try b.termExpr(t);
    try block.append(self.ctx.arena, try b.claimStep(elim_lbl, try b.termExpr(chain_formula), .by, try self.internStr("forall_elim"), elim_args, try self.oneRef(b, law)));

    // prove each obligation + modus_ponens it into the chain; the last mp proves `s = t`.
    var chain_label = elim_lbl;
    for (lemma.obligations, 0..) |ob, i| {
        const ob_label = try self.emitExtObligation(b, block, ob, lemma.universe, unfolds, c);
        const imp = self.pool.get(chain_formula).bin;
        const mp_label = if (i + 1 == lemma.obligations.len) try self.freshNamed("extensionality-conclusion") else try self.freshNamed("extensionality-step");
        const mp_refs = try self.ctx.arena.alloc(lexer.Token, 2);
        mp_refs[0] = b.tok(chain_label);
        mp_refs[1] = b.tok(ob_label);
        try block.append(self.ctx.arena, try b.claimStep(mp_label, try b.termExpr(imp.rhs), .by, try self.internStr("modus_ponens"), &.{}, mp_refs));
        chain_formula = imp.rhs;
        chain_label = mp_label;
    }
}

/// Prove one obligation `forall x: <element>; body` — a `fix x { … }` block closing the pointwise
/// residue — then `forall_intro` it. Returns the label of the forall_intro step (in `block`).
fn emitExtObligation(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), ob: TermId, universe: SortId, unfolds: []const ExtUnfold, c: ast.Step.Claim) Error!StrId {
    const q = self.pool.get(ob).quant; // forall x: <element>; body
    const x: term.Node.Fvar = .{ .name = try self.freshNamed("x"), .sort = universe };
    const x_id = try self.pool.add(.{ .fvar = x });
    const body = try self.pool.open(q.body, x_id);

    var fix_steps: std.ArrayList(ast.Step) = .empty;
    if (self.pool.get(body) == .eq) {
        try self.emitExtFunctionResidue(b, &fix_steps, body, unfolds, c);
    } else {
        try self.emitExtSetResidue(b, &fix_steps, body, x_id, unfolds, c);
    }

    // wrap the fix block + forall_intro out.
    const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(universe)));
    const fix_label = try self.freshNamed("fix");
    const bname = b.tok(try self.displayName(x.name));
    const fix_step: ast.Step = .{ .label = b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = b.tok(sort_name), .steps = fix_steps.items } } };
    try block.append(self.ctx.arena, fix_step);

    // the ∀-closed obligation.
    const closed = try self.pool.close(body, x.name);
    const ob_closed = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = universe, .hint = x.name, .body = closed } });
    const gen_label = try self.freshNamed("pointwise-holds-for-all");
    try block.append(self.ctx.arena, try b.claimStep(gen_label, try b.termExpr(ob_closed), .by, try self.internStr("forall_intro"), &.{}, try self.oneRef(b, fix_label)));
    return gen_label;
}

/// FUNCTION model residue: close `apply(f, x) = apply(g, x)` by rewriting BOTH sides with the
/// cited `apply` unfold lemmas to a common normal form and emitting the EqCert join.
fn emitExtFunctionResidue(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), eq_goal: TermId, unfolds: []const ExtUnfold, c: ast.Step.Claim) Error!void {
    const eq = self.pool.get(eq_goal).eq;
    // build rewrite rules from the cited (equation) unfold lemmas, in citation order.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    for (unfolds) |u| {
        if (!u.is_eq) return self.fail(u.head.start, "extensionality: '{s}' is a membership lemma, but the obligation is an equation (function model)", .{self.text(u.head)});
        const rule = (try self.orientRule(u.formula)) orelse
            return self.fail(u.head.start, "extensionality: '{s}' is not a usable apply rewrite rule", .{self.text(u.head)});
        try rules.append(self.ctx.arena, rule);
        try cites.append(self.ctx.arena, .{ .global = .{ .head = u.head, .is_axiom = u.is_axiom } });
    }
    const rs = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules.items, eq.lhs, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "extensionality: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    const rt = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules.items, eq.rhs, 1000) catch |e| switch (e) {
        error.Limit => return self.fail(c.rule.start, "extensionality: rewrite limit reached (looping rule set?)", .{}),
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (!self.pool.alphaEq(rs.nf, rt.nf)) {
        return self.fail(c.rule.start, "extensionality: pointwise values differ: '{s}' vs '{s}' (is the identity true?)", .{
            try self.renderTerm(rs.nf), try self.renderTerm(rt.nf),
        });
    }
    var cert: EqCert = .{ .b = b, .pool = self.pool, .rules = rules.items, .cites = cites.items, .fresh_ctx = self, .freshFn = eqCertFresh };
    _ = try cert.emitJoin(block, eq.lhs, eq.rhs, rs, rt);
}

/// SET model residue: for each `member(x, op(...))` subterm of `body`, instantiate the matching
/// cited membership lemma at (op-args…, x) as a premise step, then close `body` (a `member -> …`
/// implication) propositionally by REUSING the tautology core with those premises.
fn emitExtSetResidue(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), body: TermId, x_id: TermId, unfolds: []const ExtUnfold, c: ast.Step.Claim) Error!void {
    var prems: std.ArrayList(TautAst.Prem) = .empty;
    try self.emitExtUnfoldMembership(b, block, body, x_id, unfolds, &prems);

    // DECIDE + close propositionally over the emitted unfold-instance premises.
    const prem_formulae = try self.ctx.arena.alloc(TermId, prems.items.len);
    for (prems.items, prem_formulae) |p, *out| out.* = p.formula;
    const verdict = smt.tautology(self.ctx.arena, self.pool, prem_formulae, body) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {},
        .too_many_atoms => |n| return self.fail(c.rule.start, "extensionality: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
        .countermodel => return self.fail(c.rule.start, "extensionality: could not close the pointwise obligation propositionally (is the identity true?)", .{}),
    }

    // GENERATE the cert: collect atoms (over premises + goal), replay the truth search.
    var atom_list: std.ArrayList(TermId) = .empty;
    for (prem_formulae) |f| smt.collectAtoms(self.ctx.arena, self.pool, &atom_list, f) catch return error.OutOfMemory;
    smt.collectAtoms(self.ctx.arena, self.pool, &atom_list, body) catch return error.OutOfMemory;

    const assignment = try self.ctx.arena.alloc(?bool, atom_list.items.len);
    @memset(assignment, null);
    const lit_blocks = try self.ctx.arena.alloc(?StrId, atom_list.items.len);
    @memset(lit_blocks, null);
    var cert: TautAst = .{
        .p = self,
        .b = b,
        .goal = body,
        .premises = prems.items,
        .atoms = atom_list.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
    };
    _ = try cert.deriveGoal(block);
}

/// Recurse over `body`, and for each `member(x, op(args…))` subterm instantiate the cited
/// membership lemma whose characterized op matches, at (args…, x). Each instance is emitted as a
/// step in `block` and recorded as a tautology premise. Dedups by formula.
fn emitExtUnfoldMembership(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), body: TermId, x_id: TermId, unfolds: []const ExtUnfold, out: *std.ArrayList(TautAst.Prem)) Error!void {
    const node = self.pool.get(body);
    switch (node) {
        .pred => |p| {
            const args = self.pool.args(p);
            if (args.len == 2) {
                const set = self.pool.get(args[1]);
                if (set == .app) {
                    try self.emitExtUnfoldOp(b, block, set.app, x_id, unfolds, out);
                }
            }
        },
        .bin => |bn| {
            try self.emitExtUnfoldMembership(b, block, bn.lhs, x_id, unfolds, out);
            try self.emitExtUnfoldMembership(b, block, bn.rhs, x_id, unfolds, out);
        },
        .not => |inner| try self.emitExtUnfoldMembership(b, block, inner, x_id, unfolds, out),
        else => {},
    }
}

/// Instantiate the membership lemma for `op(args…)` at (args…, x): cite the lemma globally, then
/// forall_elim once per op-arg + once for x. Append the instance step + record it as a premise.
/// Recurses into `op`'s set-typed arguments (nested operators unfold too).
fn emitExtUnfoldOp(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), app: term.Node.App, x_id: TermId, unfolds: []const ExtUnfold, out: *std.ArrayList(TautAst.Prem)) Error!void {
    // find the cited lemma characterizing this op head.
    var lemma: ?ExtUnfold = null;
    for (unfolds) |u| {
        if (u.op != null and u.op.? == app.sym) {
            lemma = u;
            break;
        }
    }
    // COPY the op-arg ids: pool.args aliases pool.extra, which the emitStep/open calls below grow.
    const op_args = try self.ctx.arena.dupe(TermId, self.pool.args(app));
    const u = lemma orelse {
        // no cited lemma for this op — leave the atom opaque, but recurse into set-typed args.
        for (op_args) |a| {
            const an = self.pool.get(a);
            if (an == .app) try self.emitExtUnfoldOp(b, block, an.app, x_id, unfolds, out);
        }
        return;
    };

    // cite the lemma; forall_elim at each op-arg, then at x.
    const cite_label = try self.freshNamed("membership-lemma");
    const word: []const u8 = if (u.is_axiom) "axiom" else "theorem";
    const cite_refs = try self.ctx.arena.alloc(lexer.Token, 1);
    cite_refs[0] = u.head;
    try block.append(self.ctx.arena, try b.claimStep(cite_label, try b.termExpr(u.formula), .by, try self.internStrRt(word), &.{}, cite_refs));

    var cur = u.formula;
    var cur_label = cite_label;
    var bindings: std.ArrayList(TermId) = .empty;
    for (op_args) |a| try bindings.append(self.ctx.arena, a);
    try bindings.append(self.ctx.arena, x_id);
    for (bindings.items) |val| {
        const qn = self.pool.get(cur);
        if (qn != .quant or qn.quant.q != .forall) {
            return self.fail(u.head.start, "extensionality: '{s}' is not universal enough to instantiate", .{self.text(u.head)});
        }
        cur = try self.pool.open(qn.quant.body, val);
        const lbl = try self.freshNamed("membership-at-element");
        const arg1 = try self.ctx.arena.alloc(*const ast.Expr, 1);
        arg1[0] = try b.termExpr(val);
        try block.append(self.ctx.arena, try b.claimStep(lbl, try b.termExpr(cur), .by, try self.internStr("forall_elim"), arg1, try self.oneRef(b, cur_label)));
        cur_label = lbl;
    }
    // dedup by formula, then record as a premise.
    for (out.items) |pr| if (self.pool.alphaEq(pr.formula, cur)) return;
    try out.append(self.ctx.arena, .{ .formula = cur, .label = cur_label, .blk_label = cur_label });

    // recurse into the operator's set-typed arguments (nested operators unfold too).
    for (op_args) |a| {
        const an = self.pool.get(a);
        if (an == .app) try self.emitExtUnfoldOp(b, block, an.app, x_id, unfolds, out);
    }
}

// -- arithmetic / arithmetic_quantified (the linear-arithmetic accelerant) --------------
//
// The heaviest accelerant. It DECIDES a linear-integer goal (via the ported presburger /
// smt / farkas modules) and EMITS a kernel-checked certificate as the synthetic schema's
// AST proof — the generated ProveTask re-checks every step. STRICT ONLY: no `.accelerated`
// trusted verdict. Well-known lemmas (addCancelLeft, lessThanElim, lessThanTransitive, the
// ring folds) are cited BY NAME (qualified by the theory selector `c.schema`), demand-
// resolved + kernel-checked by the generated ProveTask; the user-cited `c.refs` premises are
// resolved via the ordinary local-step / global-fact path.
//
// Ported from the deleted eager `arithmetic.zig`: `arithmeticJustification` (entry),
// `arithCertCore` (the equation/order/exists rewrite cert), `premiseCombinationCert`, the
// Farkas order-composition/infeasibility cert, the Cooper period-1 witness cert + the
// period-D induction cert, and `arithmeticFallback`. The old `emitStep(low,blk,f,just)` →
// `ArithCert.claim(block, label, formula, rule, args, refs)`; `newBlock(.fix/.unpack/.assume)`
// → `ArithCert.{fix,unpack,assume}Step`.

/// A well-known symbol's name text (for the head-name reads that build `Symbols`).
fn symName(self: *const Prove, sym: term.SymId) []const u8 {
    return self.ctx.interner.stringBytes(self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sym))));
}

/// Build the arithmetic `Symbols` by reading the goal's (and premises') operator head-NAMES
/// — like `readPolyOps`. An absent symbol stays null (shrinking the fragment), matching the
/// old `wellKnownSym` semantics. `c.schema` only qualifies the emitted lemma CITES; symbols
/// come off the terms.
fn readArithSymbols(self: *Prove, goal: TermId, premises: []const TermId) Error!presburger_mod.Symbols {
    var s: presburger_mod.Symbols = .{};
    try self.collectArithSyms(goal, &s);
    for (premises) |p| try self.collectArithSyms(p, &s);
    // Fill any core operator ABSENT from the goal by IDENT lookup (best-effort, no
    // fetch/suspend) — the old scope-based `wellKnownSym`. A pure-succ order goal like
    // `less_than(succ(ZERO), succ(succ(ZERO)))` has no `add`, but the order cert needs it for
    // `lessThanIntro`'s `add(a, succ(d)) = b`. Absent (not a top-level ident) → stays null.
    if (s.add == null) s.add = self.resolveArithSym("add", .func);
    if (s.mul == null) s.mul = self.resolveArithSym("mul", .func);
    if (s.succ == null) s.succ = self.resolveArithSym("succ", .func);
    if (s.prev == null) s.prev = self.resolveArithSym("prev", .func);
    if (s.zero == null) s.zero = self.resolveArithSym("ZERO", .constant);
    if (s.one == null) s.one = self.resolveArithSym("ONE", .constant);
    if (s.neg == null) s.neg = self.resolveArithSym("neg", .func);
    if (s.sub == null) s.sub = self.resolveArithSym("sub", .func);
    if (s.less_than == null) s.less_than = self.resolveArithSym("less_than", .pred);

    const anchor = s.succ orelse s.add orelse s.zero orelse s.one orelse s.mul orelse s.sub orelse s.neg;
    if (anchor) |sym| s.nat = @enumFromInt(@intFromEnum(self.ctx.interner.symResult(@enumFromInt(@intFromEnum(sym)))));
    // A well-known `nonneg` predicate: its PRESENCE in scope is the theory's request to
    // constrain its variables nonneg (ℕ binds it; ℤ/ℚ don't). Read as x ≥ 0 by the engine +
    // injected per free var below. Resolved by IDENT lookup (best-effort, no fetch/suspend) —
    // it's a top-level alias, resolved in the read pass; absent → pure ℤ.
    if (self.resolveArithNonneg()) |nn| s.nonneg = nn;
    return s;
}

/// Resolve the well-known `nonneg` predicate symbol in this proof's namespace, or null.
fn resolveArithNonneg(self: *Prove) ?term.SymId {
    return self.resolveArithSym("nonneg", .pred);
}

/// Resolve a well-known arithmetic symbol by NAME in this proof's namespace (a `done` IdentKV
/// entry of the given kind), or null. No fetch/suspend — a top-level alias/decl is resolved in
/// the read pass; an absent name reads as unresolved. This is the demand-framework equivalent
/// of the old scope-based `wellKnownSym`.
fn resolveArithSym(self: *Prove, name: []const u8, comptime kind: enum { func, pred, constant }) ?term.SymId {
    const nid = self.ctx.interner.internString(name) catch return null;
    const state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = nid }) orelse return null;
    const ix = switch (state) {
        .done => |x| self.ctx.interner.applyModel(self.model, x),
        .in_flight => return null,
    };
    return switch (self.ctx.interner.keyOf(ix)) {
        .func => if (kind == .func) @enumFromInt(@intFromEnum(ix)) else null,
        .pred => if (kind == .pred) @enumFromInt(@intFromEnum(ix)) else null,
        .constant => if (kind == .constant) @enumFromInt(@intFromEnum(ix)) else null,
        else => null,
    };
}

/// Collect a `nonneg(v)` guard for each distinct free var of the arithmetic sort in `id`
/// (dedup by name) into `out` — the ℕ theory's per-variable x ≥ 0 the pure-ℤ engine needs.
fn collectArithNonneg(self: *Prove, id: TermId, nat: term.SortId, nn: term.SymId, seen: *std.AutoHashMapUnmanaged(StrId, void), out: *std.ArrayList(TermId)) Error!void {
    switch (self.pool.get(id)) {
        .fvar => |v| {
            if (v.sort != nat) return;
            const gop = seen.getOrPut(self.ctx.arena, v.name) catch return error.OutOfMemory;
            if (gop.found_existing) return;
            try out.append(self.ctx.arena, try self.pool.addApp(.pred, nn, &.{id}));
        },
        .bvar => {},
        .app, .pred => |a| {
            const args = try self.ctx.arena.dupe(TermId, self.pool.args(a));
            for (args) |arg| try self.collectArithNonneg(arg, nat, nn, seen, out);
        },
        .eq => |p| {
            try self.collectArithNonneg(p.lhs, nat, nn, seen, out);
            try self.collectArithNonneg(p.rhs, nat, nn, seen, out);
        },
        .not => |t| try self.collectArithNonneg(t, nat, nn, seen, out),
        .bin => |bb| {
            try self.collectArithNonneg(bb.lhs, nat, nn, seen, out);
            try self.collectArithNonneg(bb.rhs, nat, nn, seen, out);
        },
        .quant => |q| try self.collectArithNonneg(q.body, nat, nn, seen, out),
    }
}

fn collectArithSyms(self: *Prove, id: TermId, s: *presburger_mod.Symbols) Error!void {
    switch (self.pool.get(id)) {
        .app, .pred => |a| {
            const name = self.symName(a.sym);
            if (std.mem.eql(u8, name, "ZERO")) s.zero = a.sym //
            else if (std.mem.eql(u8, name, "ONE")) s.one = a.sym //
            else if (std.mem.eql(u8, name, "succ")) s.succ = a.sym //
            else if (std.mem.eql(u8, name, "prev")) s.prev = a.sym //
            else if (std.mem.eql(u8, name, "add")) s.add = a.sym //
            else if (std.mem.eql(u8, name, "mul")) s.mul = a.sym //
            else if (std.mem.eql(u8, name, "neg")) s.neg = a.sym //
            else if (std.mem.eql(u8, name, "sub")) s.sub = a.sym //
            else if (std.mem.eql(u8, name, "less_than")) s.less_than = a.sym //
            else if (std.mem.eql(u8, name, "nonneg")) s.nonneg = a.sym;
            const args = try self.ctx.arena.dupe(TermId, self.pool.args(a));
            for (args) |arg| try self.collectArithSyms(arg, s);
        },
        .eq => |p| {
            try self.collectArithSyms(p.lhs, s);
            try self.collectArithSyms(p.rhs, s);
        },
        .not => |n| try self.collectArithSyms(n, s),
        .bin => |bb| {
            try self.collectArithSyms(bb.lhs, s);
            try self.collectArithSyms(bb.rhs, s);
        },
        .quant => |q| try self.collectArithSyms(q.body, s),
        else => {},
    }
}

/// Does `sym` (if present) name the given head?
fn symIs(self: *const Prove, sym: term.SymId, want: ?term.SymId) bool {
    _ = self;
    const w = want orelse return false;
    return sym == w;
}

/// Does the term `id` mention the symbol `want` anywhere?
fn usesSym(self: *Prove, want: term.SymId, id: TermId) bool {
    switch (self.pool.get(id)) {
        .bvar, .fvar => return false,
        .app, .pred => |a| {
            if (a.sym == want) return true;
            for (self.pool.args(a)) |arg| if (self.usesSym(want, arg)) return true;
            return false;
        },
        .eq => |p| return self.usesSym(want, p.lhs) or self.usesSym(want, p.rhs),
        .not => |t| return self.usesSym(want, t),
        .bin => |bb| return self.usesSym(want, bb.lhs) or self.usesSym(want, bb.rhs),
        .quant => |q| return self.usesSym(want, q.body),
    }
}

/// A cite token for a well-known lemma named `name`, qualified by the theory selector
/// `c.schema` (bare when absent) — the generated ProveTask resolves + kernel-checks it. No
/// facts.lookup here.
fn wkCite(self: *Prove, name: []const u8, c: ast.Step.Claim) Error!lexer.Token {
    const nid = self.ctx.interner.internString(name) catch return error.OutOfMemory;
    return .{
        .tag = .identifier,
        .start = c.rule.start,
        .end = c.rule.start,
        .name = nid,
        .qualifier = if (c.schema) |sel| sel.name else InternPool.Index.none,
    };
}

/// Resolve a cited premise `ref` (an equation or `less_than` atom) to its formula + how the
/// cert cites it (a LOCAL step restated by hypothesis, or a GLOBAL fact cited by name). Only
/// LOCAL refs are schema antecedents; a GLOBAL premise is cited inside the cert.
const ArithPremise = struct {
    formula: TermId,
    local: bool,
    /// LOCAL: the restated-hypothesis label (a schema antecedent). GLOBAL: unused.
    hyp: StrId,
    /// GLOBAL: the cite token + kind. LOCAL: unused.
    head: lexer.Token,
    is_axiom: bool,
};

fn resolveArithPremise(self: *Prove, w: *const Walk, ref: lexer.Token) Error!ArithPremise {
    const is_local = ref.qualifier == InternPool.Index.none and w.findStep(tokName(ref)) != null;
    if (is_local) {
        const sref = try self.resolveStepRef(w, ref);
        return .{
            .formula = self.low_steps.items[@intFromEnum(sref.id)].formula,
            .local = true,
            .hyp = try self.premiseHypLabel(ref),
            .head = ref,
            .is_axiom = false,
        };
    }
    const fact = try self.resolveFactRef(ref);
    const formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
    return .{
        .formula = formula,
        .local = false,
        .hyp = undefined,
        .head = ref,
        .is_axiom = self.ctx.interner.keyOf(fact).fact.kind == .axiom,
    };
}

/// The arithmetic certificate emitter: a growable step list plus the shared builder. Mirrors
/// the old `emitStep`/`newBlock` API onto `ast.Step`s the kernel re-checks.
const ArithCert = struct {
    p: *Prove,
    b: *Accelerant.Builder,
    c: ast.Step.Claim,

    /// A claim step `@label | <formula> [by <rule> args refs]`; refs are label StrIds.
    fn claim(self: *ArithCert, block: *std.ArrayList(ast.Step), formula: TermId, rule: []const u8, args: []const *const ast.Expr, refs: []const StrId) Error!StrId {
        const toks = try self.p.ctx.arena.alloc(lexer.Token, refs.len);
        for (refs, toks) |r, *o| o.* = self.b.tok(r);
        const label = try self.p.freshNamed("arith");
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(formula), .by, try self.p.internStrRt(rule), args, toks));
        return label;
    }

    /// Cite a well-known lemma by name (qualified by the theory selector); returns the cite
    /// step's label (its formula = the lemma's `forall …` statement). The word "axiom" is a
    /// placeholder — the kernel picks the arm by the RESOLVED fact's kind.
    fn citeLemma(self: *ArithCert, block: *std.ArrayList(ast.Step), name: []const u8, formula: TermId) Error!StrId {
        const head = try self.p.wkCite(name, self.c);
        const label = try self.p.freshNamed("arith-lemma");
        const refs = try self.p.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = head;
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(formula), .by, try self.p.internStr("axiom"), &.{}, refs));
        return label;
    }

    /// Cite a GLOBAL user premise (arith premise) by its own head token.
    fn citeGlobalPremise(self: *ArithCert, block: *std.ArrayList(ast.Step), prem: ArithPremise) Error!StrId {
        const label = try self.p.freshNamed("arith-prem");
        const refs = try self.p.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = prem.head;
        const word: []const u8 = if (prem.is_axiom) "axiom" else "theorem";
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(prem.formula), .by, try self.p.internStrRt(word), &.{}, refs));
        return label;
    }

    /// `forall_elim` the fact at `label` (formula `cur`) at each binding, appending steps;
    /// returns the final label + opened formula.
    fn elimChain(self: *ArithCert, block: *std.ArrayList(ast.Step), label: StrId, cur: TermId, bindings: []const TermId) Error!struct { label: StrId, formula: TermId } {
        var cur_label = label;
        var cur_formula = cur;
        for (bindings) |val| {
            const qn = self.p.pool.get(cur_formula);
            const opened = try self.p.pool.open(qn.quant.body, val);
            const arg1 = try self.p.ctx.arena.alloc(*const ast.Expr, 1);
            arg1[0] = try self.b.termExpr(val);
            cur_label = try self.claim(block, opened, "forall_elim", arg1, &.{cur_label});
            cur_formula = opened;
        }
        return .{ .label = cur_label, .formula = cur_formula };
    }

    /// A `fix name: sort { steps }` block step (returns the step + label).
    fn fixStep(self: *ArithCert, label_prefix: []const u8, name: StrId, sort: SortId, steps: []const ast.Step) Error!struct { step: ast.Step, label: StrId } {
        const sort_name = self.p.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        const fix_label = try self.p.freshNamed(label_prefix);
        const bname = self.b.tok(try self.p.displayName(name));
        return .{ .step = .{ .label = self.b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = self.b.tok(sort_name), .steps = steps } } }, .label = fix_label };
    }
};

/// `[using arithmetic (theory)? refs… (fallback(thm))?]` — the entry producer for both the
/// bare `arithmetic` and the `arithmetic_quantified` alias (same body; the goal shape drives
/// the ∀-peel). See `buildArithmetic`.
fn produceArithmetic(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "arithmetic takes no arguments", .{});
    return self.buildArithmetic(w, goal, c);
}

/// The arithmetic core: DECIDE the goal from its cited premises (+ injected nonneg guards),
/// then walk the certifier chain (equation/order/exists → premise-combination → Farkas →
/// Cooper), first that certifies wins, emitting its cert as the synthetic schema's proof.
/// A declined-but-valid goal with `fallback(thm)` emits the fallback path; else a terminal
/// error. STRICT ONLY — never a trusted verdict.
fn buildArithmetic(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // resolve cited premises (local steps / global facts).
    const prems = try self.ctx.arena.alloc(ArithPremise, c.refs.len);
    for (c.refs, prems) |r, *out| out.* = try self.resolveArithPremise(w, r);
    const prem_formulae = try self.ctx.arena.alloc(TermId, prems.len);
    for (prems, prem_formulae) |p, *out| out.* = p.formula;

    const symbols = try self.readArithSymbols(goal, prem_formulae);

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix`) into value params — so
    // the cert steps, premises and schema body all speak the param names. (The ∀-goal's own
    // binders are NOT free here; they are peeled into eigenvariables by each cert path.)
    var local_pf: std.ArrayList(TermId) = .empty;
    for (prems) |p| if (p.local) try local_pf.append(self.ctx.arena, p.formula);
    const ag = try self.abstractGoal(&b, goal, local_pf.items, &.{});
    const abs = ag.abs;
    const goal_p = ag.goal_p;
    for (prems, prem_formulae) |*p, *pf| {
        p.formula = try self.substFvarsToParams(p.formula, abs);
        pf.* = p.formula;
    }

    // build the cert into a fresh step list. Try each certifier in order — every path is
    // kernel-checked, so we CERTIFY FIRST and only run the decision procedure for a good error
    // when all decline. (The decision gate would otherwise need the theory's per-variable
    // `nonneg` guard for a ℕ order goal — resolvable only by an ident fetch — while the cert
    // itself, e.g. an order goal whose difference is a literal `succ`-tower, never needs it.)
    var cert: ArithCert = .{ .p = self, .b = &b, .c = c };
    var body_steps: std.ArrayList(ast.Step) = .empty;
    var proved_prop: TermId = goal_p; // the eigen-closed prop the wrapped cert concludes
    var certified = false;
    if (try self.arithEquationCert(&cert, &body_steps, goal_p, &proved_prop, prems, symbols)) {
        certified = true;
    } else if (try self.arithFarkasCert(&cert, &body_steps, goal_p, &proved_prop, symbols)) {
        certified = true;
    } else if (try self.arithCooperCert(&cert, &body_steps, goal_p, &proved_prop, symbols)) {
        certified = true;
    }

    if (!certified) {
        if (c.fallback) |fb| return self.buildArithFallback(w, &b, fb, goal_p, prems, abs, c);
        // DECIDE to produce a good error: a genuine non-consequence names the countermodel; a
        // valid-but-uncertifiable goal reports the fragment gap. Strip the ∀-Nat prefix +
        // inject the theory's per-variable `nonneg` guard (when it binds one) so a ℕ order
        // goal decides true.
        const decide_peel = try self.arithPeel(goal_p);
        var decide_prems: std.ArrayList(TermId) = .empty;
        try decide_prems.appendSlice(self.ctx.arena, prem_formulae);
        if (symbols.nonneg) |nn| if (symbols.nat) |nat| {
            var seen: std.AutoHashMapUnmanaged(StrId, void) = .empty;
            try self.collectArithNonneg(decide_peel.body, nat, nn, &seen, &decide_prems);
            for (prem_formulae) |pf| try self.collectArithNonneg(pf, nat, nn, &seen, &decide_prems);
        };
        const verdict = smt.decideMixed(self.ctx.arena, self.pool, symbols, decide_prems.items, decide_peel.body) catch return error.OutOfMemory;
        switch (verdict) {
            .valid => return self.fail(c.rule.start, "'arithmetic' is valid but no certifier could prove it here (equation/order/exists, farkas, cooper all declined); the goal is outside the certifiable fragment", .{}),
            .countermodel => return self.fail(c.rule.start, "arithmetic: not a consequence of the cited premises", .{}),
            .too_many_atoms => |n| return self.fail(c.rule.start, "arithmetic: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
            .too_large => return self.fail(c.rule.start, "arithmetic: decision exceeded the work limit", .{}),
            .overflow => return self.fail(c.rule.start, "arithmetic: coefficient overflow", .{}),
        }
    }
    // certified on our own: a `fallback(thm)` is redundant (strict; --draft suppresses).
    if (c.fallback) |fb| {
        if (!self.ctx.verify.draft) return self.fail(fb.start, "'arithmetic' certifies this goal on its own — the fallback '{s}' is unnecessary; drop `fallback({s})`", .{ self.text(fb), self.text(fb) });
    }

    // package with the cert's ACTUAL conclusion (`proved_prop`), not the raw `goal_p`: the
    // ∀-re-generalization shell (wrapArithForall) re-quantifies at the eigenvariables' fresh
    // names, so `proved_prop` is alpha-equal to `goal_p` but its binder hints match the proof's
    // final `forall_intro` steps. Declaring the schema body from `proved_prop` keeps the stated
    // schema and the emitted proof's conclusion byte-identical (a hint mismatch would surface as
    // "claims forall b1 but derives forall …", the cooper_witness bug).
    return try self.packageArith(w, &b, "arithmetic", proved_prop, prems, abs, body_steps.items, c);
}

/// Package the emitted cert `body_steps` (proving the param-substituted `goal_p`) as the
/// synthetic schema: body = `localPrem0 -> … -> goal_p` wrapped in `assume` blocks for the
/// LOCAL premises; params from the abstracted caller-locals; deterministic hash name.
fn packageArith(self: *Prove, w: *const Walk, b: *Accelerant.Builder, comptime prefix: []const u8, goal_p: TermId, prems: []const ArithPremise, abs: FvarAbstraction, body_steps: []const ast.Step, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    // LOCAL premises become schema antecedents (restated by hypothesis, discharged at the
    // call site) in ref order; GLOBAL premises are cited inside the cert (not antecedents).
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (prems) |p| if (p.local) {
        try local_cites.append(self.ctx.arena, .{ .local = .{ .hyp = p.hyp } });
        try local_formulae.append(self.ctx.arena, p.formula);
    };

    const inner_prop = try self.impliesChain(goal_p, local_formulae.items);
    const steps = try self.wrapSimplifyPremises(b, local_cites.items, local_formulae.items, goal_p, body_steps);

    const body_expr = try b.termExpr(inner_prop);
    const params = try self.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        pp.* = .{ .name = b.tok(name), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    const hash = Schema.termHash(self.pool, inner_prop);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, prefix ++ "{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = try self.localRefTokens(w, c.refs),
    };
}

/// `fallback(thm)` path: the certifier chain declined (or the goal isn't in the certifiable
/// fragment) but the goal is an INSTANCE of the manually-proven theorem `fb`. Emit the cert:
/// cite `fb`, forall_elim at the inferred witnesses, then modus_ponens each `->` antecedent
/// against the matching cited ref. Every step kernel-checked. Fast-path when `fb`'s statement
/// α-equals the goal (cite it directly). Packages the synthetic schema.
fn buildArithFallback(self: *Prove, w: *const Walk, b: *Accelerant.Builder, fb: lexer.Token, goal_p: TermId, prems: []const ArithPremise, abs: FvarAbstraction, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const fact = try self.resolveFactRef(fb);
    const key = self.ctx.interner.keyOf(fact).fact;
    const formula = try self.pool.copyIn(self.ctx.interner, key.formula);
    const is_axiom = key.kind == .axiom;
    var cert: ArithCert = .{ .p = self, .b = b, .c = c };
    var block: std.ArrayList(ast.Step) = .empty;

    // FAST PATH: fb IS the goal (α-equal) — cite it directly.
    if (self.pool.alphaEq(formula, goal_p)) {
        const word: []const u8 = if (is_axiom) "axiom" else "theorem";
        const label = try self.freshNamed("arith-fallback");
        const refs = try self.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = fb;
        try block.append(self.ctx.arena, try b.claimStep(label, try b.termExpr(goal_p), .by, try self.internStrRt(word), &.{}, refs));
        return try self.packageArith(w, b, "arithmetic", goal_p, prems, abs, block.items, c);
    }

    // SPECIALIZE PATH: peel fb's ∀ prefix into pattern fvars, split leading `->` antecedents.
    var pattern: std.ArrayList(term.Node.Fvar) = .empty;
    var f = formula;
    while (true) {
        const node = self.pool.get(f);
        if (node == .quant and node.quant.q == .forall) {
            const fv: term.Node.Fvar = .{ .name = try self.freshNamed("fallback-var"), .sort = node.quant.sort };
            try pattern.append(self.ctx.arena, fv);
            f = try self.pool.open(node.quant.body, try self.pool.add(.{ .fvar = fv }));
        } else break;
    }
    var antecedents: std.ArrayList(TermId) = .empty;
    while (true) {
        const node = self.pool.get(f);
        if (node == .bin and node.bin.op == .implies) {
            try antecedents.append(self.ctx.arena, node.bin.lhs);
            f = node.bin.rhs;
        } else break;
    }
    // infer each pattern var by matching the consequent against the goal.
    var binds: std.AutoHashMapUnmanaged(StrId, TermId) = .empty;
    if (!try self.arithMatchPattern(pattern.items, f, goal_p, &binds)) {
        return self.fail(fb.start, "fallback theorem '{s}' does not prove this goal (its conclusion does not match, even after specialization)", .{self.text(fb)});
    }
    const witnesses = try self.ctx.arena.alloc(TermId, pattern.items.len);
    for (pattern.items, witnesses) |pv, *out| {
        out.* = binds.get(pv.name) orelse
            return self.fail(fb.start, "fallback theorem '{s}' does not prove this goal (variable unconstrained by the conclusion)", .{self.text(fb)});
    }

    // resolve each antecedent (at the witnesses) to a matching cited ref.
    const ant_labels = try self.ctx.arena.alloc(StrId, antecedents.items.len);
    for (antecedents.items, ant_labels) |ant_raw, *out_label| {
        var ant = ant_raw;
        for (pattern.items, witnesses) |pv, wit| ant = try self.pool.substFvar(ant, pv.name, wit);
        var matched: ?StrId = null;
        for (prems) |p| {
            if (self.pool.alphaEq(p.formula, ant)) {
                matched = if (p.local) p.hyp else try cert.citeGlobalPremise(&block, p);
                break;
            }
        }
        out_label.* = matched orelse
            return self.fail(fb.start, "fallback theorem '{s}' needs a hypothesis '{s}' — supply it as a ref to the arithmetic step", .{ self.text(fb), try self.renderTerm(ant) });
    }

    // emit: cite fb, forall_elim at each witness, modus_ponens each antecedent.
    const word: []const u8 = if (is_axiom) "axiom" else "theorem";
    const cite_label = try self.freshNamed("arith-fallback");
    const cite_refs = try self.ctx.arena.alloc(lexer.Token, 1);
    cite_refs[0] = fb;
    try block.append(self.ctx.arena, try b.claimStep(cite_label, try b.termExpr(formula), .by, try self.internStrRt(word), &.{}, cite_refs));
    const elim = try cert.elimChain(&block, cite_label, formula, witnesses);
    var cur_label = elim.label;
    var cur_formula = elim.formula;
    for (ant_labels) |al| {
        const imp = self.pool.get(cur_formula).bin;
        cur_label = try cert.claim(&block, imp.rhs, "modus_ponens", &.{}, &.{ cur_label, al });
        cur_formula = imp.rhs;
    }
    return try self.packageArith(w, b, "arithmetic", goal_p, prems, abs, block.items, c);
}

/// First-order match: bind each `pattern` fvar (by name) so substituting yields `target`.
fn arithMatchPattern(self: *Prove, pattern: []const term.Node.Fvar, pat: TermId, target: TermId, binds: *std.AutoHashMapUnmanaged(StrId, TermId)) Error!bool {
    const pn = self.pool.get(pat);
    if (pn == .fvar) {
        for (pattern) |pv| {
            if (pv.name == pn.fvar.name) {
                if (binds.get(pv.name)) |prev| return self.pool.alphaEq(prev, target);
                binds.put(self.ctx.arena, pv.name, target) catch return error.OutOfMemory;
                return true;
            }
        }
        const tn = self.pool.get(target);
        return tn == .fvar and tn.fvar.name == pn.fvar.name and tn.fvar.sort == pn.fvar.sort;
    }
    const tn = self.pool.get(target);
    if (std.meta.activeTag(pn) != std.meta.activeTag(tn)) return false;
    switch (pn) {
        .bvar => return pn.bvar == tn.bvar,
        .fvar => unreachable,
        .app => |a| {
            if (a.sym != tn.app.sym or a.args_len != tn.app.args_len) return false;
            const pa = try self.ctx.arena.dupe(TermId, self.pool.args(a));
            const ta = try self.ctx.arena.dupe(TermId, self.pool.args(tn.app));
            for (pa, ta) |x, y| if (!try self.arithMatchPattern(pattern, x, y, binds)) return false;
            return true;
        },
        .pred => |a| {
            if (a.sym != tn.pred.sym or a.args_len != tn.pred.args_len) return false;
            const pa = try self.ctx.arena.dupe(TermId, self.pool.args(a));
            const ta = try self.ctx.arena.dupe(TermId, self.pool.args(tn.pred));
            for (pa, ta) |x, y| if (!try self.arithMatchPattern(pattern, x, y, binds)) return false;
            return true;
        },
        .eq => |p| return (try self.arithMatchPattern(pattern, p.lhs, tn.eq.lhs, binds)) and (try self.arithMatchPattern(pattern, p.rhs, tn.eq.rhs, binds)),
        .not => |t| return self.arithMatchPattern(pattern, t, tn.not, binds),
        .bin => |bb| return bb.op == tn.bin.op and (try self.arithMatchPattern(pattern, bb.lhs, tn.bin.lhs, binds)) and (try self.arithMatchPattern(pattern, bb.rhs, tn.bin.rhs, binds)),
        .quant => |q| return q.q == tn.quant.q and q.sort == tn.quant.sort and (try self.arithMatchPattern(pattern, q.body, tn.quant.body, binds)),
    }
}

/// The Farkas certifier — order-composition / infeasibility over the difference-logic edges.
/// (Not exercised by the target fixtures; declines for now — a follow-up port.)
/// A proved strict-order hypothesis `less_than(lo, hi)`: its endpoints (as terms) and the label
/// of the step proving it (a restated `->` antecedent, or a derived scaled/summed edge).
const OrderHyp = struct { lo: TermId, hi: TermId, ref: StrId };

/// The Farkas certifier over the difference-logic fragment. A goal
/// `forall v..; H1 -> … -> Hn -> C` whose Hi are strict-order atoms `less_than(s, t)` is
/// certified by composing them with `lessThanTransitive`. Three conclusion shapes:
///   (a) order composition `less_than(s, t)` (s != t): fold a path s < … < t;
///   (b) self-loop `less_than(x, x)`: fold a cycle;
///   (c) INFEASIBILITY of an arbitrary conclusion: fold a cycle to `less_than(x, x)`, contradict
///       with `lessThanIrreflexive`, then `absurd`.
/// Stage 1 (scaling) lifts a hypothesis by a literal coefficient via
/// `multiplicationPreservesOrder`; stage 2 (sum) combines two edges over distinct variables via
/// `additionPreservesOrder`. Declines (false) on any out-of-fragment shape.
fn arithFarkasCert(self: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, symbols_in: presburger_mod.Symbols) Error!bool {
    var symbols = symbols_in;
    const less_than = symbols.less_than orelse return false;

    // 1. peel the ∀ prefix into eigenvariables; the body is `H1 -> … -> Hn -> C`.
    const peel = try self.arithPeel(goal_p);

    // A pure-order fixture (only `less_than` + a bare sort in scope, no arithmetic op) leaves
    // `symbols.nat` unanchored; recover it from the quantified eigenvariables' sort so the order
    // lemmas (`lessThanTransitive`/`lessThanIrreflexive`) can be built.
    if (symbols.nat == null and peel.eigen.len != 0) symbols.nat = peel.eigen[0].sort;
    if (symbols.nat == null) return false;
    if ((try self.arithLemmaFormula("lessThanTransitive", symbols)) == null) return false;

    // 2. peel the `->` antecedent chain — each must be a strict-order atom — recording each as a
    //    difference-logic edge (nodes = distinct endpoint terms) with the label that will restate
    //    it by hypothesis inside its assume block. `residual[k]` = the formula proved inside
    //    assume[k] (the conclusion of the remaining chain).
    var edges: std.ArrayList(farkas.Edge) = .empty;
    var hyps: std.ArrayList(OrderHyp) = .empty;
    var node_ids: std.ArrayList(TermId) = .empty;
    var blk_labels: std.ArrayList(StrId) = .empty; // the assume-block label per antecedent
    var ante_formulae: std.ArrayList(TermId) = .empty;
    var body = peel.body;
    while (true) {
        const node = self.pool.get(body);
        if (node != .bin or node.bin.op != .implies) break;
        const ante = node.bin.lhs;
        const an = self.pool.get(ante);
        if (an != .pred or !self.symIs(an.pred.sym, less_than) or an.pred.args_len != 2) return false;
        const args = self.pool.args(an.pred);
        const blk_label = try self.freshNamed("given-order");
        const restate_label = try self.freshNamed("order-hyp"); // the OrderHyp ref (the fold cites this)
        try edges.append(self.ctx.arena, .{
            .lo = try self.farkasNodeId(&node_ids, args[0]),
            .hi = try self.farkasNodeId(&node_ids, args[1]),
        });
        try hyps.append(self.ctx.arena, .{ .lo = args[0], .hi = args[1], .ref = restate_label });
        try blk_labels.append(self.ctx.arena, blk_label);
        try ante_formulae.append(self.ctx.arena, ante);
        body = node.bin.rhs;
    }
    if (edges.items.len == 0) return false; // nothing to combine: not Farkas
    const base_count = edges.items.len;

    // the fold + derived-edge steps live in an INNER block that runs inside the innermost assume
    // (where every antecedent hypothesis is in scope).
    var inner: std.ArrayList(ast.Step) = .empty;

    // 2b. COEFFICIENT SCALING: derive `less_than(mul(k,lo), mul(k,hi))` edges for each literal k
    //     the conclusion / hypotheses mention.
    var literals: std.ArrayList(usize) = .empty;
    try self.collectFarkasScaleLiterals(symbols, body, &literals);
    for (hyps.items[0..base_count]) |h| {
        try self.collectFarkasScaleLiterals(symbols, h.lo, &literals);
        try self.collectFarkasScaleLiterals(symbols, h.hi, &literals);
    }
    if (literals.items.len != 0) {
        if (!try self.emitFarkasScaledEdges(cert, &inner, symbols, literals.items, base_count, &edges, &hyps, &node_ids)) return false;
    }

    // 2c. SUM PATH: if the conclusion is `less_than(add(_,_), add(_,_))` no single edge proves,
    //     derive a summed edge from a pair of base hypotheses.
    if (symbols.add != null) {
        const cn0 = self.pool.get(body);
        const wants_sum = cn0 == .pred and self.symIs(cn0.pred.sym, less_than) and cn0.pred.args_len == 2 and
            self.isFarkasAddSum(symbols, self.pool.args(cn0.pred)[0]);
        if (wants_sum and base_count >= 2) {
            if (!try self.emitFarkasSumEdge(cert, &inner, symbols, body, base_count, &edges, &hyps, &node_ids)) return false;
        }
    }

    // 3. prove the conclusion `body` from the order edges, dispatching on its shape.
    const concl_label = (try self.emitFarkasConclusion(cert, &inner, symbols, less_than, body, edges.items, hyps.items, &node_ids)) orelse return false;

    // 4. wrap `inner` in nested assume blocks (innermost antecedent first): each block restates
    //    its hypothesis, runs the (progressively) exported proof, and `implies_intro` exports
    //    `H_k -> … -> C`. Mirrors `wrapSimplifyPremises`.
    _ = concl_label;
    var carry_steps = inner.items;
    var carry_formula = body; // the conclusion proved inside the current level
    var k = base_count;
    while (k > 0) {
        k -= 1;
        const blk_label = blk_labels.items[k];
        const restate_label = hyps.items[k].ref;
        var blk_body = try std.ArrayList(ast.Step).initCapacity(self.ctx.arena, carry_steps.len + 1);
        // restate the assumption (label = the OrderHyp `ref` the fold cites) via `hypothesis`
        // citing the enclosing assume block.
        blk_body.appendAssumeCapacity(try cert.b.claimStep(restate_label, try cert.b.termExpr(ante_formulae.items[k]), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, blk_label)));
        blk_body.appendSliceAssumeCapacity(carry_steps);

        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, try cert.b.assumeStep(blk_label, try cert.b.termExpr(ante_formulae.items[k]), blk_body.items));
        const exported = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = ante_formulae.items[k], .rhs = carry_formula } });
        _ = try cert.claim(&lvl, exported, "implies_intro", &.{}, &.{blk_label});
        carry_formula = exported;
        carry_steps = try lvl.toOwnedSlice(self.ctx.arena);
    }

    // 5. wrap in the ∀ fix/forall_intro shell.
    const wrapped = try self.wrapArithForall(cert, peel.eigen, peel.body, carry_steps);
    try out.appendSlice(self.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Intern a term as an abstract Farkas node identity (by structural order).
fn farkasNodeId(self: *Prove, list: *std.ArrayList(TermId), t: TermId) Error!usize {
    for (list.items, 0..) |x, i| {
        if (self.pool.termOrder(x, t) == .eq) return i;
    }
    try list.append(self.ctx.arena, t);
    return list.items.len - 1;
}

/// Prove the Farkas conclusion `body`, returning the label of a step proving it (or null to
/// decline). (a)/(b): if `body` is an order atom `less_than(s, t)`, compose a chain s < … < t
/// (a cycle when s == t). (c): otherwise fold ANY cycle to `less_than(x, x)`, contradict with
/// `lessThanIrreflexive`, and `absurd` proves the (arbitrary) conclusion.
fn emitFarkasConclusion(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: presburger_mod.Symbols, less_than: term.SymId, body: TermId, edges: []const farkas.Edge, hyps: []const OrderHyp, node_ids: *std.ArrayList(TermId)) Error!?StrId {
    const cn = self.pool.get(body);
    const is_order = cn == .pred and self.symIs(cn.pred.sym, less_than) and cn.pred.args_len == 2;

    if (is_order) {
        const cargs = self.pool.args(cn.pred);
        const from = try self.farkasNodeId(node_ids, cargs[0]);
        const to = try self.farkasNodeId(node_ids, cargs[1]);
        if (try farkas.compose(self.ctx.arena, edges, from, to)) |path| {
            return try self.emitFarkasFold(cert, block, symbols, path.chain, hyps);
        }
        // no direct chain: fall through to the infeasibility cap.
    }

    // (c) INFEASIBILITY CAP.
    if ((try self.arithLemmaFormula("lessThanIrreflexive", symbols)) == null) return null;
    const refutation = (try farkas.refute(self.ctx.arena, edges, null)) orelse return null;
    const cycle_label = try self.emitFarkasFold(cert, block, symbols, refutation.chain, hyps);
    const cnode = node_ids.items[refutation.node];

    // cite lessThanIrreflexive, forall_elim at cnode → `not less_than(cnode, cnode)`; absurd
    // against the folded `less_than(cnode, cnode)` proves the (arbitrary) `body`.
    const irr_stmt = (try self.arithLemmaFormula("lessThanIrreflexive", symbols)).?;
    const irr_label = try cert.citeLemma(block, "lessThanIrreflexive", irr_stmt);
    const not_lt = try cert.elimChain(block, irr_label, irr_stmt, &.{cnode});
    return try cert.claim(block, body, "absurd", &.{}, &.{ cycle_label, not_lt.label });
}

/// Fold an order chain (edge indices, each hi linking to the next lo) into a single proof
/// `less_than(chain-first-lo, chain-last-hi)` by composing consecutive hypotheses with
/// `lessThanTransitive`. Returns the label of that proof (the sole hypothesis for a one-edge
/// chain).
fn emitFarkasFold(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: presburger_mod.Symbols, chain: []const usize, hyps: []const OrderHyp) Error!StrId {
    var acc_label = hyps[chain[0]].ref;
    const acc_lo = hyps[chain[0]].lo;
    var acc_hi = hyps[chain[0]].hi;

    const tr_stmt = (try self.arithLemmaFormula("lessThanTransitive", symbols)).?;
    for (chain[1..]) |idx| {
        const next = hyps[idx];
        // lessThanTransitive(acc_lo, acc_hi, next.hi):
        //   less_than(acc_lo,acc_hi) -> less_than(acc_hi,next.hi) -> less_than(acc_lo,next.hi)
        const tr_label = try cert.citeLemma(block, "lessThanTransitive", tr_stmt);
        const elim = try cert.elimChain(block, tr_label, tr_stmt, &.{ acc_lo, acc_hi, next.hi });
        const inner = self.pool.get(elim.formula).bin.rhs; // less_than(acc_hi,next.hi) -> less_than(acc_lo,next.hi)
        const mp1 = try cert.claim(block, inner, "modus_ponens", &.{}, &.{ elim.label, acc_label });
        const concl = self.pool.get(inner).bin.rhs; // less_than(acc_lo, next.hi)
        acc_label = try cert.claim(block, concl, "modus_ponens", &.{}, &.{ mp1, next.ref });
        acc_hi = next.hi;
    }
    return acc_label;
}

/// If `t` is a ground successor tower `succ^k(ZERO)`, return k, else 0.
fn farkasLiteral(self: *Prove, symbols: presburger_mod.Symbols, t: TermId) usize {
    var k: usize = 0;
    var cur = t;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and self.symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
            k += 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and self.symIs(node.app.sym, symbols.zero) and node.app.args_len == 0) return k;
        return 0;
    }
}

/// Scan `t` for `mul(<literal>, x)` subterms, collecting distinct literal coefficients k >= 2.
fn collectFarkasScaleLiterals(self: *Prove, symbols: presburger_mod.Symbols, t: TermId, out: *std.ArrayList(usize)) Error!void {
    switch (self.pool.get(t)) {
        .app, .pred => |a| {
            if (self.symIs(a.sym, symbols.mul) and a.args_len == 2) {
                const args = self.pool.args(a);
                const k = self.farkasLiteral(symbols, args[0]);
                if (k >= 2) {
                    for (out.items) |x| {
                        if (x == k) break;
                    } else try out.append(self.ctx.arena, k);
                }
            }
            for (self.pool.args(a)) |arg| try self.collectFarkasScaleLiterals(symbols, arg, out);
        },
        .eq => |p| {
            try self.collectFarkasScaleLiterals(symbols, p.lhs, out);
            try self.collectFarkasScaleLiterals(symbols, p.rhs, out);
        },
        .not => |i| try self.collectFarkasScaleLiterals(symbols, i, out),
        .bin => |bn| {
            try self.collectFarkasScaleLiterals(symbols, bn.lhs, out);
            try self.collectFarkasScaleLiterals(symbols, bn.rhs, out);
        },
        .quant => |q| try self.collectFarkasScaleLiterals(symbols, q.body, out),
        else => {},
    }
}

/// Is `t` an `add(_, _)` application?
fn isFarkasAddSum(self: *Prove, symbols: presburger_mod.Symbols, t: TermId) bool {
    const node = self.pool.get(t);
    return node == .app and self.symIs(node.app.sym, symbols.add) and node.app.args_len == 2;
}

/// For each base hypothesis and literal k, emit a SCALED edge `less_than(mul(k,lo), mul(k,hi))`
/// via `multiplicationPreservesOrder` (k = succ(c), so forall_elim at c = succ^{k-1}(ZERO)),
/// appending it to `edges`/`hyps`/`node_ids`. Returns false (declines) if the lemma or the
/// mul/succ/zero symbols are absent.
fn emitFarkasScaledEdges(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: presburger_mod.Symbols, literals: []const usize, base_count: usize, edges: *std.ArrayList(farkas.Edge), hyps: *std.ArrayList(OrderHyp), node_ids: *std.ArrayList(TermId)) Error!bool {
    const succ = symbols.succ orelse return false;
    const zero_sym = symbols.zero orelse return false;
    const mpo_stmt = (try self.arithLemmaFormula("multiplicationPreservesOrder", symbols)) orelse return false;
    const zero = try self.pool.addApp(.app, zero_sym, &.{});

    for (literals) |k| {
        // c = succ^{k-1}(ZERO), so succ(c) = k.
        var c = zero;
        for (0..k - 1) |_| c = try self.pool.addApp(.app, succ, &.{c});
        for (0..base_count) |bi| {
            const h = hyps.items[bi];
            // multiplicationPreservesOrder(h.lo, h.hi, c):
            //   less_than(h.lo,h.hi) -> less_than(mul(succ(c),h.lo), mul(succ(c),h.hi))
            const mpo_label = try cert.citeLemma(block, "multiplicationPreservesOrder", mpo_stmt);
            const elim = try cert.elimChain(block, mpo_label, mpo_stmt, &.{ h.lo, h.hi, c });
            const concl = self.pool.get(elim.formula).bin.rhs; // the scaled order atom
            const scaled_label = try cert.claim(block, concl, "modus_ponens", &.{}, &.{ elim.label, h.ref });
            const scaled = self.pool.get(concl).pred;
            const sargs = self.pool.args(scaled);
            try edges.append(self.ctx.arena, .{
                .lo = try self.farkasNodeId(node_ids, sargs[0]),
                .hi = try self.farkasNodeId(node_ids, sargs[1]),
            });
            try hyps.append(self.ctx.arena, .{ .lo = sargs[0], .hi = sargs[1], .ref = scaled_label });
        }
    }
    return true;
}

/// The conclusion is `less_than(add(A,B), add(C,D))`. Find base hypotheses proving A<C and B<D,
/// derive the summed edge `less_than(add(A,B), add(C,D))`, and append it. Returns false
/// (declines) when the matching hypotheses or the needed lemmas are absent.
fn emitFarkasSumEdge(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: presburger_mod.Symbols, body: TermId, base_count: usize, edges: *std.ArrayList(farkas.Edge), hyps: *std.ArrayList(OrderHyp), node_ids: *std.ArrayList(TermId)) Error!bool {
    const add = symbols.add orelse return false;
    const less_than = symbols.less_than orelse return false;
    const cargs = self.pool.args(self.pool.get(body).pred);
    const lhs_args = self.pool.args(self.pool.get(cargs[0]).app); // [A, B]
    const rhs_args = self.pool.args(self.pool.get(cargs[1]).app); // [C, D]
    const a = lhs_args[0];
    const bb = lhs_args[1];
    const cc = rhs_args[0];
    const dd = rhs_args[1];
    // find base hyps A<C and B<D.
    var ha: ?OrderHyp = null;
    var hb: ?OrderHyp = null;
    for (hyps.items[0..base_count]) |h| {
        if (self.pool.termOrder(h.lo, a) == .eq and self.pool.termOrder(h.hi, cc) == .eq) ha = h;
        if (self.pool.termOrder(h.lo, bb) == .eq and self.pool.termOrder(h.hi, dd) == .eq) hb = h;
    }
    const first = ha orelse return false;
    const second = hb orelse return false;

    const apo_stmt = (try self.arithLemmaFormula("additionPreservesOrder", symbols)) orelse return false;
    const comm_stmt = (try self.arithLemmaFormula("addIsCommutative", symbols)) orelse return false;
    const tr_stmt = (try self.arithLemmaFormula("lessThanTransitive", symbols)) orelse return false;

    const p = first.lo;
    const q = first.hi;
    const r = second.lo;
    const s = second.hi;

    // lift p<q by c:=r via additionPreservesOrder → add(r,p) < add(r,q).
    const apo1_label = try cert.citeLemma(block, "additionPreservesOrder", apo_stmt);
    const apo1 = try cert.elimChain(block, apo1_label, apo_stmt, &.{ p, q, r });
    const lifted1 = self.pool.get(apo1.formula).bin.rhs; // less_than(add(r,p), add(r,q))
    const rp_lt_rq = try cert.claim(block, lifted1, "modus_ponens", &.{}, &.{ apo1.label, first.ref });

    // commute add(r,p)=add(p,r), add(r,q)=add(q,r); rewrite both.
    const pr = try self.pool.addApp(.app, add, &.{ p, r });
    const rq = try self.pool.addApp(.app, add, &.{ r, q });
    const qr = try self.pool.addApp(.app, add, &.{ q, r });
    const eq_rp = try emitFarkasCommEq(cert, block, comm_stmt, r, p); // add(r,p)=add(p,r)
    const eq_rq = try emitFarkasCommEq(cert, block, comm_stmt, r, q); // add(r,q)=add(q,r)
    const pr_lt_rq_f = try self.pool.addApp(.pred, less_than, &.{ pr, rq });
    const pr_lt_rq = try cert.claim(block, pr_lt_rq_f, "rewrite", &.{}, &.{ eq_rp, rp_lt_rq });
    const pr_lt_qr_f = try self.pool.addApp(.pred, less_than, &.{ pr, qr });
    const pr_lt_qr = try cert.claim(block, pr_lt_qr_f, "rewrite", &.{}, &.{ eq_rq, pr_lt_rq });

    // lift r<s by c:=q via additionPreservesOrder → add(q,r) < add(q,s).
    const apo2_label = try cert.citeLemma(block, "additionPreservesOrder", apo_stmt);
    const apo2 = try cert.elimChain(block, apo2_label, apo_stmt, &.{ r, s, q });
    const lifted2 = self.pool.get(apo2.formula).bin.rhs; // less_than(add(q,r), add(q,s))
    const qr_lt_qs = try cert.claim(block, lifted2, "modus_ponens", &.{}, &.{ apo2.label, second.ref });

    // chain add(p,r) < add(q,r) < add(q,s) via lessThanTransitive.
    const qs = try self.pool.addApp(.app, add, &.{ q, s });
    const tr_label = try cert.citeLemma(block, "lessThanTransitive", tr_stmt);
    const chain = try cert.elimChain(block, tr_label, tr_stmt, &.{ pr, qr, qs });
    const chain_inner = self.pool.get(chain.formula).bin.rhs;
    const chain2 = try cert.claim(block, chain_inner, "modus_ponens", &.{}, &.{ chain.label, pr_lt_qr });
    const summed_f = self.pool.get(chain_inner).bin.rhs; // less_than(add(p,r), add(q,s))
    const summed_label = try cert.claim(block, summed_f, "modus_ponens", &.{}, &.{ chain2, qr_lt_qs });

    try edges.append(self.ctx.arena, .{
        .lo = try self.farkasNodeId(node_ids, pr),
        .hi = try self.farkasNodeId(node_ids, qs),
    });
    try hyps.append(self.ctx.arena, .{ .lo = pr, .hi = qs, .ref = summed_label });
    return true;
}

/// Emit `add(x,y) = add(y,x)` via addIsCommutative(x, y). Returns the equation step's label.
fn emitFarkasCommEq(cert: *ArithCert, block: *std.ArrayList(ast.Step), comm_stmt: TermId, x: TermId, y: TermId) Error!StrId {
    const comm_label = try cert.citeLemma(block, "addIsCommutative", comm_stmt);
    const elim = try cert.elimChain(block, comm_label, comm_stmt, &.{ x, y });
    return elim.label;
}

/// The Cooper certifier (period-1 witness). Peel the goal's ∀ prefix into `fix` blocks; the
/// body must be `exists y; disj`. Trace the Cooper elimination, reconstruct each boundary
/// witness as a term, and prove the body at the first witness whose opened disjunction has a
/// provable arm (equation/order under the fix vars), lifting through the or-intro path with an
/// `exists_intro`. Wraps in the `fix`/`forall_intro` shell. Declines on period>1 (induction —
/// not ported) or a nested/multi-var shape.
fn arithCooperCert(self: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, symbols: presburger_mod.Symbols) Error!bool {
    if (symbols.nat == null) return false;
    const peel = try self.arithPeel(goal_p);
    const bn = self.pool.get(peel.body);
    if (bn != .quant or bn.quant.q != .exists) return false;

    const traced = presburger_mod.trace(self.ctx.arena, self.pool, symbols, &.{}, peel.body) catch return error.OutOfMemory;
    if (traced != .replay) return false;
    const replay = traced.replay;
    if (replay.period != 1) return false; // induction path not ported

    // reconstruct candidate boundary witnesses as terms.
    var candidates: std.ArrayList(TermId) = .empty;
    for (replay.disjuncts) |d| {
        const bw = switch (d) {
            .minus_inf => continue,
            .boundary => |x| x,
        };
        if (try self.arithBuildWitness(replay, replay.boundaries[bw.b_index], bw.j, peel.eigen, symbols)) |wtn| {
            try candidates.append(self.ctx.arena, wtn);
        }
    }

    // prove `exists y; disj` at the first candidate that closes an arm.
    var body_steps: std.ArrayList(ast.Step) = .empty;
    const ok = try self.arithEmitExistsWitness(cert, &body_steps, peel.body, candidates.items, symbols);
    if (!ok) return false;
    const wrapped = try self.wrapArithForall(cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(self.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Prove `exists y; disj` in `block` at one of `candidates`: open the body at the witness,
/// prove a provable arm of the (possibly disjunctive) instance, lift through the or-intro
/// path, and emit `exists_intro`. Returns false if no candidate closes.
fn arithEmitExistsWitness(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), exists_body: TermId, candidates: []const TermId, symbols: presburger_mod.Symbols) Error!bool {
    const en = self.pool.get(exists_body);
    if (en != .quant or en.quant.q != .exists) return false;
    for (candidates) |wtn| {
        const instance = try self.pool.open(en.quant.body, wtn);
        // try each arm of the right/left or-nest.
        var arm_steps: std.ArrayList(ast.Step) = .empty;
        const found = (try self.arithProveDisjArm(cert, &arm_steps, instance, symbols)) orelse continue;
        try block.appendSlice(self.ctx.arena, arm_steps.items);
        // lift the arm through the or-intro path (innermost first).
        var arm_label = found.label;
        var arm_formula = found.formula;
        var pi = found.path.len;
        while (pi > 0) {
            pi -= 1;
            const disj = try self.arithDisjAt(instance, found.path[0..pi]);
            const rule: []const u8 = if (found.path[pi]) "or_intro_right" else "or_intro_left";
            arm_label = try cert.claim(block, disj, rule, &.{}, &.{arm_label});
            arm_formula = disj;
        }
        // exists_intro at the witness.
        const arg1 = try self.ctx.arena.alloc(*const ast.Expr, 1);
        arg1[0] = try cert.b.termExpr(wtn);
        const label = try self.freshNamed("arith");
        const refs = try self.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = cert.b.tok(arm_label);
        try block.append(self.ctx.arena, try cert.b.claimStep(label, try cert.b.termExpr(exists_body), .by, try self.internStr("exists_intro"), arg1, refs));
        return true;
    }
    return false;
}

const ArithArm = struct { label: StrId, formula: TermId, path: []const bool };

/// Prove one arm of a right/left `or`-nest `instance` via the equation/order body cert; return
/// the arm's step label + formula + the or-intro path to it, or null if no arm is provable.
fn arithProveDisjArm(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), instance: TermId, symbols: presburger_mod.Symbols) Error!?ArithArm {
    var path: std.ArrayList(bool) = .empty;
    var cur = instance;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .bin and node.bin.op == .or_op) {
            var probe: std.ArrayList(ast.Step) = .empty;
            if (try self.arithBodyEqCert(cert, &probe, node.bin.lhs, &.{}, symbols)) {
                try block.appendSlice(self.ctx.arena, probe.items);
                const label = try self.arithLastLabel(probe.items);
                try path.append(self.ctx.arena, false);
                return .{ .label = label, .formula = node.bin.lhs, .path = try self.ctx.arena.dupe(bool, path.items) };
            }
            try path.append(self.ctx.arena, true);
            cur = node.bin.rhs;
            continue;
        }
        var probe: std.ArrayList(ast.Step) = .empty;
        if (try self.arithBodyEqCert(cert, &probe, cur, &.{}, symbols)) {
            try block.appendSlice(self.ctx.arena, probe.items);
            const label = try self.arithLastLabel(probe.items);
            return .{ .label = label, .formula = cur, .path = try self.ctx.arena.dupe(bool, path.items) };
        }
        return null;
    }
}

/// Descend `instance` (a right/left `or`-nest) along `path` (false=left, true=right).
fn arithDisjAt(self: *Prove, instance: TermId, path: []const bool) Error!TermId {
    var cur = instance;
    for (path) |go_right| {
        const node = self.pool.get(cur);
        cur = if (go_right) node.bin.rhs else node.bin.lhs;
    }
    return cur;
}

/// Reconstruct a boundary witness `boundaries[i] + j` (a linear form over the fix vars) as a
/// term: coeff 0 → a constant tower over ZERO; coeff 1 on the single eigenvariable → a tower
/// over it. Higher coeff / 2+ vars → null. Port of the old `buildWitness`.
fn arithBuildWitness(self: *Prove, replay: presburger_mod.Replay, dump: presburger_mod.LinearDump, j: i128, fix_vars: []const term.Node.Fvar, symbols: presburger_mod.Symbols) Error!?TermId {
    var fix_index: ?usize = null;
    for (dump.coeffs, 0..) |co, id| {
        if (co == 0) continue;
        if (co != 1) return null;
        const pos = std.mem.indexOfScalar(u32, replay.free_ids, @intCast(id)) orelse return null;
        if (fix_index != null) return null;
        fix_index = pos;
    }
    // DEGENERATE-WITNESS GUARD: a witness that is exactly a fixed eigenvariable (coeff-1 on a
    // fix var, zero constant/offset) — e.g. Cooper picking `y := x` for `exists y; x = y or …`,
    // where the left arm holds reflexively — trips the schema-instance binder machinery on
    // re-elaboration (the existential var and the fixed var collapse to one de Bruijn slot,
    // deriving `forall :; exists b1; b1 = b1 …`). The proof is semantically valid but the
    // instance can't re-check it; decline this candidate so the cert either finds a
    // non-degenerate witness or declines cleanly (the honest "no certifier" boundary) rather
    // than emitting an un-recheckable proof. (Deferred: the reflexive-arm / witness==fixvar
    // Cooper case — task #76.)
    if (fix_index != null and dump.konst + j == 0) return null;
    const offset = dump.konst + j;
    const base = if (fix_index) |pos| blk: {
        if (pos >= fix_vars.len) return null;
        break :blk try self.pool.add(.{ .fvar = fix_vars[pos] });
    } else blk: {
        const zero = symbols.zero orelse return null;
        break :blk try self.pool.addApp(.app, zero, &.{});
    };
    return try self.buildArithTowerSigned(offset, base, symbols);
}

/// Peel `goal`'s ∀ prefix into fresh eigenvariables (outermost first); return the body + the
/// eigenvariables (for the `fix`/`forall_intro` re-generalization shell). Used by each
/// arithmetic certifier so a `forall …; body` goal skeletonizes to `body` at fixed vars.
const ArithPeel = struct { body: TermId, eigen: []const term.Node.Fvar, opened: []const TermId };
fn arithPeel(self: *Prove, goal: TermId) Error!ArithPeel {
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var opened: std.ArrayList(TermId) = .empty;
    var body = goal;
    while (true) {
        const node = self.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = self.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{ .name = try self.freshNamed(if (hint.len > 0) hint else "q"), .sort = node.quant.sort };
        body = try self.pool.open(node.quant.body, try self.pool.add(.{ .fvar = fv }));
        try eigen.append(self.ctx.arena, fv);
        try opened.append(self.ctx.arena, body);
    }
    return .{ .body = body, .eigen = eigen.items, .opened = opened.items };
}

/// Wrap `inner` steps (proving `body`) in nested `fix` blocks for `eigen` (outermost first),
/// concluding each level with `forall_intro`. Returns the wrapped steps + the eigen-closed
/// prop the outermost `forall_intro` proves (the schema body must use THIS prop, so its
/// binder hints match the fix blocks). (Same shell as `wrapSimplifyForall`.)
const WrappedArith = struct { steps: []const ast.Step, prop: TermId };
fn wrapArithForall(self: *Prove, cert: *ArithCert, eigen: []const term.Node.Fvar, body: TermId, inner: []const ast.Step) Error!WrappedArith {
    if (eigen.len == 0) return .{ .steps = inner, .prop = body };
    var steps = inner;
    var prop = body;
    var i: usize = eigen.len;
    while (i > 0) {
        i -= 1;
        const fv = eigen[i];
        const fixr = try cert.fixStep("arith-fix", fv.name, fv.sort, steps);
        const closed = try self.pool.close(prop, fv.name);
        prop = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, fixr.step);
        _ = try cert.claim(&lvl, prop, "forall_intro", &.{}, &.{fixr.label});
        steps = try lvl.toOwnedSlice(self.ctx.arena);
    }
    return .{ .steps = steps, .prop = prop };
}

/// The EQUATION / ORDER cert. Peels the goal's ∀ prefix, then certifies the body:
///   - an equation `s = t`: canonicalize both sides to a shared normal form (the ring
///     `Polynomial` path when `mul` is present; else an additive AC + inverse-elimination
///     path), emit the `EqCert` join;
///   - an order atom `less_than(s, t)`: find the difference `d` with `add(s, succ(d)) = t`
///     an additive identity, prove that equation, and cite `lessThanIntro` (`add(a,succ(d))=b
///     -> less_than(a,b)`).
/// Wraps the body proof in the `fix`/`forall_intro` shell. Returns false (declines) on any
/// shape/normal-form mismatch — the caller tries the next certifier.
fn arithEquationCert(self: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const peel = try self.arithPeel(goal_p);
    var body_steps: std.ArrayList(ast.Step) = .empty;
    const ok = try self.arithBodyEqCert(cert, &body_steps, peel.body, prems, symbols);
    if (!ok) return false;
    const wrapped = try self.wrapArithForall(cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(self.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Certify one (∀-free) equation/order body into `block`; returns false if out of scope.
fn arithBodyEqCert(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), body: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const node = self.pool.get(body);
    if (node == .eq) {
        return self.arithEmitEquation(cert, block, node.eq.lhs, node.eq.rhs, prems, symbols);
    }
    if (node == .pred and self.symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2) {
        return self.arithEmitOrder(cert, block, body, prems, symbols);
    }
    // EXISTS-witness search: `exists y; inner` — try constant witnesses succ^k(ZERO), k=0..33,
    // proving `inner[y:=witness]` by the equation/order cert, then `exists_intro` (the old
    // arithCertCore C2c). Handles e.g. `exists y; add(y,y) = succ(succ(ZERO))` (witness y=1).
    if (node == .quant and node.quant.q == .exists) {
        const zero = symbols.zero orelse return false;
        const zero_t = try self.pool.addApp(.app, zero, &.{});
        for (0..34) |k| {
            const witness = (try self.buildArithTowerSigned(@intCast(k), zero_t, symbols)) orelse break;
            const instance = try self.pool.open(node.quant.body, witness);
            var probe: std.ArrayList(ast.Step) = .empty;
            if (try self.arithBodyEqCert(cert, &probe, instance, prems, symbols)) {
                try block.appendSlice(self.ctx.arena, probe.items);
                const inst_label = try self.arithLastLabel(probe.items);
                const arg1 = try self.ctx.arena.alloc(*const ast.Expr, 1);
                arg1[0] = try cert.b.termExpr(witness);
                const label = try self.freshNamed("arith");
                const refs = try self.ctx.arena.alloc(lexer.Token, 1);
                refs[0] = cert.b.tok(inst_label);
                try block.append(self.ctx.arena, try cert.b.claimStep(label, try cert.b.termExpr(body), .by, try self.internStr("exists_intro"), arg1, refs));
                return true;
            }
        }
        return false;
    }
    return false;
}

/// Emit a proof of the equation `s = t` into `block`; false if it can't join. Dispatches on
/// whether the goal has `mul` (ring `Polynomial` canonicalizer) or is additive-only (AC +
/// inverse elimination), plus a PREMISE-COMBINATION fallback (goal = ±1·premise). The cited
/// premises join as ground rewrite rules where their sides occur literally.
fn arithEmitEquation(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    if (self.pool.alphaEq(s, t)) {
        _ = try cert.claim(block, try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } }), "reflexivity", &.{}, &.{});
        return true;
    }
    const eq_goal = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });

    // build the ring/additive rule set (well-known lemmas cited by name) + premise rules.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    const have_mul = symbols.mul != null and (self.usesSym(symbols.mul.?, s) or self.usesSym(symbols.mul.?, t));
    const qualifier: StrId = if (cert.c.schema) |sel| sel.name else InternPool.Index.none;
    if (have_mul) {
        // FIRST try the ring `Polynomial` canonicalizer (distribution/fold + AC) — handles
        // symbolic ring identities like `mul(2, n) = add(n, n)`. If the NFs disagree it may
        // still be a GROUND numeric identity (`mul(2, 2) = 4`) the ring form can't evaluate —
        // fall through to the additive path (which carries the mul RECURSION rules).
        if (try self.readPolyOps(eq_goal)) |ops| {
            const pr = try Polynomial.polyRules(self, ops, qualifier, cert.c.rule.start);
            if (try Polynomial.polyCanon(self, pr, s)) |rs| {
                if (try Polynomial.polyCanon(self, pr, t)) |rt| {
                    if (self.pool.alphaEq(rs.nf, rt.nf)) {
                        var ec: EqCert = .{ .b = cert.b, .pool = self.pool, .rules = pr.rules, .cites = pr.cites, .fresh_ctx = self, .freshFn = eqCertFresh };
                        _ = try ec.emitJoin(block, s, t, rs, rt);
                        return true;
                    }
                }
            }
        }
    }
    // additive path: elimination + succ/mul RECURSION pre-rules, then AC-sort + inverse-cancel.
    const add_sym = symbols.add orelse return false;
    try self.pushAdditiveElim(&rules, &cites, symbols, qualifier, cert.c.rule.start);
    const pre_count = rules.items.len;
    const sort: term.SortId = @enumFromInt(@intFromEnum(self.termSort(s)));
    try self.pushACTriple(&rules, &cites, add_sym, sort, "addIsAssociative", "addIsCommutative", "addLeftSwap", cert.c.rule.start);
    const assoc_idx = pre_count;
    const comm_idx = pre_count + 1;
    const swap_idx = pre_count + 2;
    const pre_rules = rules.items[0..pre_count];

    const s_pre = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, pre_rules, s, 1000) catch |e| switch (e) {
        error.Limit => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    const t_pre = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, pre_rules, t, 1000) catch |e| switch (e) {
        error.Limit => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    // pre-normalization alone may already agree (pure numerals / leafless towers where the
    // AC sort is a no-op) — join directly, skipping acPlan (which declines on leafless sums).
    if (self.pool.alphaEq(s_pre.nf, t_pre.nf)) {
        var ec: EqCert = .{ .b = cert.b, .pool = self.pool, .rules = rules.items, .cites = cites.items, .fresh_ctx = self, .freshFn = eqCertFresh };
        _ = try ec.emitJoin(block, s, t, s_pre, t_pre);
        return true;
    }
    // canonicalize each side to a fixpoint: AC-sort + bubble-cancel inverse pairs + re-normalize,
    // repeating until stable (arithCanon carries `symbols` so its cancelInverses has neg/zero).
    const rs = (try self.arithCanon(symbols, rules.items, pre_rules, assoc_idx, comm_idx, swap_idx, s_pre)) orelse return false;
    const rt = (try self.arithCanon(symbols, rules.items, pre_rules, assoc_idx, comm_idx, swap_idx, t_pre)) orelse return false;
    if (self.pool.alphaEq(rs.nf, rt.nf)) {
        var ec: EqCert = .{ .b = cert.b, .pool = self.pool, .rules = rules.items, .cites = cites.items, .fresh_ctx = self, .freshFn = eqCertFresh };
        _ = try ec.emitJoin(block, s, t, rs, rt);
        return true;
    }
    // PREMISE COMBINATION: goal = ±1·(an equality premise). Certify via addCancelLeft.
    return self.arithPremiseCombination(cert, block, s, t, prems, symbols);
}

/// Canonicalize `start` (with its initial pre-normalize `Result`) to a fixpoint by alternating
/// AC-sort (`acPlan`) and pre-rule normalize (elim + adjacent inverse-cancel + ZERO-drop),
/// concatenating every trace. The sort places an inverse pair adjacent so the next normalize's
/// addNegRight/Left cancels it. Returns the final `Result` (NF + full trace), null on decline.
fn arithCanon(self: *Prove, symbols: presburger_mod.Symbols, rules: []const simplify_mod.Rule, pre_rules: []const simplify_mod.Rule, assoc_idx: usize, comm_idx: usize, swap_idx: usize, pre: simplify_mod.Result) Error!?simplify_mod.Result {
    // cancelInverses (below) needs neg/zero/add/succ/prev to bubble + cancel an inverse pair; the
    // AC sort itself only reorders over `add`, so acPlan gets the add-only view.
    const acsym: presburger_mod.Symbols = .{ .add = symbols.add };
    var nf = pre.nf;
    var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
    try trace.appendSlice(self.ctx.arena, pre.trace);
    var iter: usize = 0;
    while (iter < 6) : (iter += 1) {
        const plan = (try self.acPlan(acsym, rules, assoc_idx, comm_idx, swap_idx, nf)) orelse return null;
        try trace.appendSlice(self.ctx.arena, plan.trace);
        // BUBBLE-cancel non-adjacent inverse pairs (`x … neg(x)` separated by other summands):
        // reuse Polynomial's cancelInverses, which moves the pair together before applying
        // addNegRight/Left — sort adjacency alone (the re-normalize below) misses separated pairs.
        const cancelled = (try Polynomial.cancelInverses(self, symbols, rules, comm_idx, swap_idx, 0, plan.sorted, &trace)) orelse plan.sorted;
        // re-normalize the (bubble-cancelled) sorted form (drop any residual ZERO, fold).
        const renorm = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, pre_rules, cancelled, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        try trace.appendSlice(self.ctx.arena, renorm.trace);
        if (self.pool.alphaEq(renorm.nf, plan.sorted)) {
            // stable: sort + cancel produced no change this round.
            return .{ .nf = renorm.nf, .trace = trace.items };
        }
        nf = renorm.nf;
    }
    return .{ .nf = nf, .trace = trace.items };
}

/// Emit a proof of `less_than(s, t)` via `lessThanIntro`: synthesize the difference witness
/// `d` (from the normalized towers), prove `add(s, succ(d)) = t`, then cite `lessThanIntro`,
/// forall_elim at (s, d, t), and modus_ponens the equation. Declines (false) when the towers
/// don't yield a nonneg difference or the equation can't join. (Peano shape; the ℤ nonneg-
/// antecedent variant is not needed by the fixtures.)
fn arithEmitOrder(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), body: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    _ = prems;
    const succ = symbols.succ orelse return false;
    const add = symbols.add orelse return false;
    const pred = self.pool.get(body).pred;
    const args = self.pool.args(pred);
    const s = args[0];
    const t = args[1];

    // find the difference d such that add(s, succ(d)) = t. Try d = ZERO, then peel: since the
    // engine already decided validity, search a small tower / structural difference. Simple
    // structural approach: if t = add(s, succ(x)) syntactically, d = x; else if t = succ^k(s)-
    // shaped, compute via normalized towers. Use the additive normalizer to canonicalize.
    const d = (try self.arithOrderDiff(s, t, symbols)) orelse return false;
    const succ_d = try self.pool.addApp(.app, succ, &.{d});
    const eq_lhs = try self.pool.addApp(.app, add, &.{ s, succ_d });

    // prove add(s, succ(d)) = t via the equation cert.
    if (!try self.arithEmitEquation(cert, block, eq_lhs, t, &.{}, symbols)) return false;
    const eq_label = try self.arithLastLabel(block.items);

    // cite lessThanIntro, forall_elim at (s, d, t), modus_ponens the equation → less_than(s,t).
    const intro_stmt = (try self.arithLemmaFormula("lessThanIntro", symbols)) orelse return false;
    const intro_label = try cert.citeLemma(block, "lessThanIntro", intro_stmt);
    const elim = try cert.elimChain(block, intro_label, intro_stmt, &.{ s, d, t });
    _ = try cert.claim(block, body, "modus_ponens", &.{}, &.{ elim.label, eq_label });
    return true;
}

/// Synthesize the difference `d` with `add(s, succ(d)) = t` for a valid `less_than(s, t)`.
/// Uses the additive-tower parse: t-tower minus s-tower (leaves + offset), minus one for the
/// `succ`. Returns null if the difference isn't a nonneg tower over the shared leaves.
fn arithOrderDiff(self: *Prove, s: TermId, t: TermId, symbols: presburger_mod.Symbols) Error!?TermId {
    // canonicalize both sides additively (fold sub/neg, sort) so the tower parse is clean.
    var rules: std.ArrayList(simplify_mod.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    try self.pushAdditiveElim(&rules, &cites, symbols, .none, 0);
    const rs = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules.items, s, 1000) catch return null;
    const rt = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, rules.items, t, 1000) catch return null;
    const tower_s = (try self.parseArithTower(rs.nf, symbols)) orelse return null;
    const tower_t = (try self.parseArithTower(rt.nf, symbols)) orelse return null;
    if (tower_t.offset < tower_s.offset + 1) return null;
    // multiset difference t - s
    var remaining: std.ArrayList(TermId) = .empty;
    try remaining.appendSlice(self.ctx.arena, tower_t.leaves);
    for (tower_s.leaves) |sl| {
        const found = for (remaining.items, 0..) |rl, i| {
            if (self.pool.termOrder(rl, sl) == .eq) break i;
        } else return null;
        _ = remaining.swapRemove(found);
    }
    const comb = (try self.buildArithComb(remaining.items, symbols)) orelse return null;
    return try self.buildArithTowerSigned(tower_t.offset - tower_s.offset - 1, comb, symbols);
}

const ArithTower = struct { offset: i128, leaves: []const TermId };

/// Parse `succ^j(prev^k(right-nested add of leaves))`, folding numeral summands into a signed
/// offset. Anything else → null (out of the additive fragment). Port of the old `parseTower`.
fn parseArithTower(self: *Prove, t: TermId, symbols: presburger_mod.Symbols) Error!?ArithTower {
    var offset: i128 = 0;
    var cur = t;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and self.symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
            offset += 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and self.symIs(node.app.sym, symbols.prev) and node.app.args_len == 1) {
            offset -= 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    var leaves: std.ArrayList(TermId) = .empty;
    while (true) {
        if (self.arithNumeral(cur, symbols)) |v| {
            offset += v;
            break;
        }
        if (self.isArithLeaf(cur, symbols)) {
            try leaves.append(self.ctx.arena, cur);
            break;
        }
        const node = self.pool.get(cur);
        if (node != .app) return null;
        if (self.symIs(node.app.sym, symbols.add) and node.app.args_len == 2) {
            const a = try self.ctx.arena.dupe(TermId, self.pool.args(node.app));
            if (self.arithNumeral(a[0], symbols)) |v| {
                offset += v;
                cur = a[1];
                continue;
            }
            if (!self.isArithLeaf(a[0], symbols)) return null;
            try leaves.append(self.ctx.arena, a[0]);
            cur = a[1];
            continue;
        }
        return null;
    }
    return .{ .offset = offset, .leaves = leaves.items };
}

/// Signed numeral value of `t` (`succ^n(ZERO)`→+n, `prev^n(ZERO)`→−n, `neg` flips), else null.
fn arithNumeral(self: *Prove, t: TermId, symbols: presburger_mod.Symbols) ?i128 {
    var cur = t;
    var sign: i128 = 1;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and self.symIs(node.app.sym, symbols.neg) and node.app.args_len == 1) {
            sign = -sign;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    var mag: i128 = 0;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .app and self.symIs(node.app.sym, symbols.succ) and node.app.args_len == 1) {
            mag += 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and self.symIs(node.app.sym, symbols.prev) and node.app.args_len == 1) {
            mag -= 1;
            cur = self.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    const node = self.pool.get(cur);
    if (node == .app and self.symIs(node.app.sym, symbols.zero) and node.app.args_len == 0) return sign * mag;
    return null;
}

/// A tower leaf: an fvar, an opaque atom, or `neg` of a leaf (so inverse pairs can cancel).
fn isArithLeaf(self: *Prove, t: TermId, symbols: presburger_mod.Symbols) bool {
    const node = self.pool.get(t);
    if (node == .fvar) return true;
    if (node == .app and self.symIs(node.app.sym, symbols.neg) and node.app.args_len == 1) {
        return self.isArithLeaf(self.pool.args(node.app)[0], symbols);
    }
    if (node != .app) return false;
    const sym = node.app.sym;
    return !(self.symIs(sym, symbols.add) or self.symIs(sym, symbols.succ) or
        self.symIs(sym, symbols.prev) or self.symIs(sym, symbols.neg) or
        self.symIs(sym, symbols.sub) or self.symIs(sym, symbols.zero) or self.symIs(sym, symbols.one));
}

/// Right-nested `add`-comb of `leaves` (ZERO for empty).
fn buildArithComb(self: *Prove, leaves: []const TermId, symbols: presburger_mod.Symbols) Error!?TermId {
    if (leaves.len == 0) {
        const zero = symbols.zero orelse return null;
        return try self.pool.addApp(.app, zero, &.{});
    }
    var cur = leaves[leaves.len - 1];
    var i = leaves.len - 1;
    while (i > 0) {
        i -= 1;
        const add = symbols.add orelse return null;
        cur = try self.pool.addApp(.app, add, &.{ leaves[i], cur });
    }
    return cur;
}

/// `succ^n(comb)` for n≥0, `prev^|n|(comb)` for n<0 (needs ℤ `prev`; null for ℕ negatives).
fn buildArithTowerSigned(self: *Prove, offset: i128, comb: TermId, symbols: presburger_mod.Symbols) Error!?TermId {
    var cur = comb;
    if (offset >= 0) {
        const succ = symbols.succ orelse return if (offset == 0) comb else null;
        var n = offset;
        while (n > 0) : (n -= 1) cur = try self.pool.addApp(.app, succ, &.{cur});
        return cur;
    }
    const prev = symbols.prev orelse return null;
    var n = -offset;
    while (n > 0) : (n -= 1) cur = try self.pool.addApp(.app, prev, &.{cur});
    return cur;
}

/// Append the well-known ℤ elimination rules (sub/neg/prev folding toward an add-of-atoms
/// form) as hardcoded shapes cited by name, gated on the theory providing each symbol. These
/// let an additive goal over sub/neg normalize before the AC sort (e.g. `add(a, sub(b,a))`).
fn pushAdditiveElim(self: *Prove, rules: *std.ArrayList(simplify_mod.Rule), cites: *std.ArrayList(EqCert.RuleCite), symbols: presburger_mod.Symbols, qualifier: StrId, loc: u32) Error!void {
    const add = symbols.add orelse return;
    const sort: term.SortId = @enumFromInt(@intFromEnum(self.ctx.interner.symResult(@enumFromInt(@intFromEnum(add)))));
    // succ FLOAT: addSuccLeft add(succ(a),b)=succ(add(a,b)); addSuccRight add(a,succ(b))=
    // succ(add(a,b)) — lift succ to the tower prefix so the tower parse is clean.
    if (symbols.succ) |succ| {
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, succ, &.{a.t}), bb.t });
            const rhs = try self.pool.addApp(.app, succ, &.{try self.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addSuccLeft", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, add, &.{ a.t, try self.pool.addApp(.app, succ, &.{bb.t}) });
            const rhs = try self.pool.addApp(.app, succ, &.{try self.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addSuccRight", qualifier, loc);
        }
    }
    // ZERO drop: addZeroLeft add(ZERO,b)=b; addZeroRight add(n,ZERO)=n.
    if (symbols.zero) |zero| {
        const z = try self.pool.addApp(.app, zero, &.{});
        {
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, add, &.{ z, bb.t });
            try self.pushQualified(rules, cites, &.{.{ .fvar = bb.name, .sort = sort }}, lhs, bb.t, "addZeroLeft", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, add, &.{ a.t, z });
            try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "addZeroRight", qualifier, loc);
        }
        // ONE unfold: oneIsSuccZero ONE = succ(ZERO) — dissolve a bare `ONE` constant into the
        // succ-tower so numeral goals (`add(ONE, ONE) = succ(succ(ZERO))`) reduce to a common
        // form. Nullary rule; gated on the theory declaring `oneIsSuccZero` (+ ONE/succ present).
        if (symbols.one) |one| if (symbols.succ) |succ| {
            const one_t = try self.pool.addApp(.app, one, &.{});
            const succ_z = try self.pool.addApp(.app, succ, &.{z});
            try self.pushQualified(rules, cites, &.{}, one_t, succ_z, "oneIsSuccZero", qualifier, loc);
        };
    }
    // mul RECURSION (ground numeric evaluation): mulZeroLeft mul(ZERO,b)=ZERO; mulSuccLeft
    // mul(succ(a),b)=add(mul(a,b),b) — expands `mul(n, x)` to a sum for numeral n.
    if (symbols.mul) |mul| if (symbols.zero) |zero| if (symbols.succ) |succ| {
        const z = try self.pool.addApp(.app, zero, &.{});
        {
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, mul, &.{ z, bb.t });
            try self.pushQualified(rules, cites, &.{.{ .fvar = bb.name, .sort = sort }}, lhs, z, "mulZeroLeft", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, mul, &.{ try self.pool.addApp(.app, succ, &.{a.t}), bb.t });
            const rhs = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, mul, &.{ a.t, bb.t }), bb.t });
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "mulSuccLeft", qualifier, loc);
        }
        // mulZeroRight mul(n,ZERO)=ZERO; mulSuccRight mul(a,succ(b))=add(mul(a,b),a) — the right
        // mirrors, so a numeral on EITHER factor expands.
        {
            const a = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, mul, &.{ a.t, z });
            try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, z, "mulZeroRight", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, mul, &.{ a.t, try self.pool.addApp(.app, succ, &.{bb.t}) });
            const rhs = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, mul, &.{ a.t, bb.t }), a.t });
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "mulSuccRight", qualifier, loc);
        }
    };
    // definitionOfSubtraction: sub(a,b) = add(a, neg(b))
    if (symbols.sub != null and symbols.neg != null) {
        const a = try self.freshACFvar(sort);
        const bb = try self.freshACFvar(sort);
        const lhs = try self.pool.addApp(.app, symbols.sub.?, &.{ a.t, bb.t });
        const rhs = try self.pool.addApp(.app, add, &.{ a.t, try self.pool.addApp(.app, symbols.neg.?, &.{bb.t}) });
        try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "definitionOfSubtraction", qualifier, loc);
    }
    if (symbols.neg) |neg| {
        // negAdd: neg(add(a,b)) = add(neg(a), neg(b))
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, neg, &.{try self.pool.addApp(.app, add, &.{ a.t, bb.t })});
            const rhs = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, neg, &.{a.t}), try self.pool.addApp(.app, neg, &.{bb.t}) });
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "negAdd", qualifier, loc);
        }
        // negNeg: neg(neg(a)) = a
        {
            const a = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, neg, &.{try self.pool.addApp(.app, neg, &.{a.t})});
            try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "negNeg", qualifier, loc);
        }
        // addNegRight: add(a, neg(a)) = ZERO; addNegLeft: add(neg(a), a) = ZERO — cancel an
        // inverse pair the AC sort brings adjacent (the addZero rules then drop the ZERO).
        if (symbols.zero) |zero| {
            const z = try self.pool.addApp(.app, zero, &.{});
            {
                const a = try self.freshACFvar(sort);
                const lhs = try self.pool.addApp(.app, add, &.{ a.t, try self.pool.addApp(.app, neg, &.{a.t}) });
                try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, z, "addNegRight", qualifier, loc);
            }
            {
                const a = try self.freshACFvar(sort);
                const lhs = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, neg, &.{a.t}), a.t });
                try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, z, "addNegLeft", qualifier, loc);
            }
            // negZero: neg(ZERO) = ZERO (nullary).
            {
                const lhs = try self.pool.addApp(.app, neg, &.{z});
                try self.pushQualified(rules, cites, &.{}, lhs, z, "negZero", qualifier, loc);
            }
        }
        // negSucc: neg(succ(a)) = prev(neg(a)); negPrev: neg(prev(a)) = succ(neg(a)) — push neg
        // through succ/prev toward the leaves so a `neg`-of-numeral becomes a prev/succ tower.
        if (symbols.succ) |succ| if (symbols.prev) |prev| {
            {
                const a = try self.freshACFvar(sort);
                const lhs = try self.pool.addApp(.app, neg, &.{try self.pool.addApp(.app, succ, &.{a.t})});
                const rhs = try self.pool.addApp(.app, prev, &.{try self.pool.addApp(.app, neg, &.{a.t})});
                try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, rhs, "negSucc", qualifier, loc);
            }
            {
                const a = try self.freshACFvar(sort);
                const lhs = try self.pool.addApp(.app, neg, &.{try self.pool.addApp(.app, prev, &.{a.t})});
                const rhs = try self.pool.addApp(.app, succ, &.{try self.pool.addApp(.app, neg, &.{a.t})});
                try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, rhs, "negPrev", qualifier, loc);
            }
        };
    }
    // succ/prev collapse + prev FLOAT (ℤ): prevSucc prev(succ(a))=a; succPrev succ(prev(a))=a;
    // addPrevLeft add(prev(a),b)=prev(add(a,b)); addPrevRight add(a,prev(b))=prev(add(a,b)) —
    // lift prev to the tower prefix (mirror of the succ float) so the tower parse is clean.
    if (symbols.prev) |prev| if (symbols.succ) |succ| {
        {
            const a = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, prev, &.{try self.pool.addApp(.app, succ, &.{a.t})});
            try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "prevSucc", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, succ, &.{try self.pool.addApp(.app, prev, &.{a.t})});
            try self.pushQualified(rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "succPrev", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, prev, &.{a.t}), bb.t });
            const rhs = try self.pool.addApp(.app, prev, &.{try self.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addPrevLeft", qualifier, loc);
        }
        {
            const a = try self.freshACFvar(sort);
            const bb = try self.freshACFvar(sort);
            const lhs = try self.pool.addApp(.app, add, &.{ a.t, try self.pool.addApp(.app, prev, &.{bb.t}) });
            const rhs = try self.pool.addApp(.app, prev, &.{try self.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try self.pushQualified(rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addPrevRight", qualifier, loc);
        }
    };
}

/// `pushHardcoded` but with the theory-selector `qualifier` stamped onto the cite (so
/// `arithmetic(theory)` resolves the lemma in the theory's namespace).
fn pushQualified(self: *Prove, rules: *std.ArrayList(simplify_mod.Rule), cites: *std.ArrayList(EqCert.RuleCite), binders_in: []const simplify_mod.Binder, lhs: TermId, rhs: TermId, name_text: []const u8, qualifier: StrId, loc: u32) Error!void {
    // Skip a rule whose lemma this file does NOT declare (unqualified only): pushing it would
    // let `normalize` cite an absent lemma, failing the generated proof. A qualified cite
    // (theory selector) targets another namespace we can't check here, so it's kept.
    const name = self.ctx.interner.internString(name_text) catch return error.OutOfMemory;
    if (qualifier == InternPool.Index.none) {
        const fid = self.ctx.pool_file.get(self.file).?;
        if (self.ctx.declOf(fid, name) == null) return;
    }
    // dupe onto the arena — callers pass inline `&.{…}` literals (stack temporaries).
    const binders = try self.ctx.arena.dupe(simplify_mod.Binder, binders_in);
    var formula = try self.pool.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        const closed = try self.pool.close(formula, binders[i].fvar);
        formula = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = binders[i].sort, .hint = binders[i].fvar, .body = closed } });
    }
    try rules.append(self.ctx.arena, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = formula });
    try cites.append(self.ctx.arena, .{ .global = .{ .head = .{ .tag = .identifier, .start = loc, .end = loc, .name = name, .qualifier = qualifier }, .is_axiom = false } });
}

/// Certify `s = t` as a linear combination of an equality PREMISE `P_l = P_r`: it holds iff
/// `add(P_l, s) = add(P_r, t)` is a pure additive identity. Emit that identity, rewrite the
/// premise (P_l→P_r), then cancel with addCancelLeft. Every step kernel-checked. Only fires
/// for a LOCAL/GLOBAL premise cited at this scope.
fn arithPremiseCombination(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const add = symbols.add orelse return false;
    for (prems) |p| {
        const pn = self.pool.get(p.formula);
        if (pn != .eq) continue;
        const pl = pn.eq.lhs;
        const pr = pn.eq.rhs;
        const comb_lhs = try self.pool.addApp(.app, add, &.{ pl, s });
        const comb_rhs = try self.pool.addApp(.app, add, &.{ pr, t });
        // certify the combined identity as an additive identity (no premise rules).
        var probe_steps: std.ArrayList(ast.Step) = .empty;
        var probe_cert: ArithCert = .{ .p = self, .b = cert.b, .c = cert.c };
        if (!try self.arithEmitEquation(&probe_cert, &probe_steps, comb_lhs, comb_rhs, &.{}, symbols)) continue;

        // PLAN OK — emit for real. combined identity add(P_l,s) = add(P_r,t).
        var join_steps: std.ArrayList(ast.Step) = .empty;
        _ = try self.arithEmitEquation(cert, &join_steps, comb_lhs, comb_rhs, &.{}, symbols);
        try block.appendSlice(self.ctx.arena, join_steps.items);
        const comb_label = try self.arithLastLabel(join_steps.items);

        // the premise, cited at this scope (LOCAL restated hyp / GLOBAL cite).
        const prem_label = if (p.local) p.hyp else try cert.citeGlobalPremise(block, p);
        // rewrite P_l→P_r in the combined identity's LHS: add(P_r, s) = add(P_r, t).
        const rewritten = try self.pool.add(.{ .eq = .{ .lhs = try self.pool.addApp(.app, add, &.{ pr, s }), .rhs = comb_rhs } });
        const rewritten_label = try cert.claim(block, rewritten, "rewrite", &.{}, &.{ prem_label, comb_label });
        // addCancelLeft(P_r, s, t): add(P_r,s)=add(P_r,t) -> s=t. cite + elim + mp.
        const cancel_stmt = (try self.arithLemmaFormula("addCancelLeft", symbols)) orelse return false;
        const cancel_label = try cert.citeLemma(block, "addCancelLeft", cancel_stmt);
        const elim = try cert.elimChain(block, cancel_label, cancel_stmt, &.{ pr, s, t });
        const goal_eq = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
        _ = try cert.claim(block, goal_eq, "modus_ponens", &.{}, &.{ elim.label, rewritten_label });
        return true;
    }
    return false;
}

/// The last step's label in an emitted slice (its concluding equation).
fn arithLastLabel(self: *Prove, steps: []const ast.Step) Error!StrId {
    _ = self;
    return tokName(steps[steps.len - 1].label);
}

/// Build a well-known lemma's exact `forall …` statement from the arithmetic `symbols`. The
/// cert cites the lemma by name and states THIS formula on the cite step (the kernel re-checks
/// it against the resolved fact, and forall_elim opens it at the arguments). The shapes match
/// the std peano/integer statements: a mis-shape simply fails the generated ProveTask's
/// kernel check. `null` when a needed symbol is absent.
fn arithLemmaFormula(self: *Prove, name: []const u8, symbols: presburger_mod.Symbols) Error!?TermId {
    const sort = symbols.nat orelse return null;
    const mkfv = struct {
        fn f(p: *Prove, s: term.SortId, hint: []const u8) Error!ArithVar {
            const nm = try p.freshNamed(hint);
            return .{ .name = nm, .t = try p.pool.add(.{ .fvar = .{ .name = nm, .sort = s } }) };
        }
    }.f;
    if (std.mem.eql(u8, name, "addCancelLeft")) {
        // forall c, a, b; add(c, a) = add(c, b) -> a = b
        const add = symbols.add orelse return null;
        const cc = try mkfv(self, sort, "c");
        const a = try mkfv(self, sort, "a");
        const bb = try mkfv(self, sort, "b");
        const lhs = try self.pool.add(.{ .eq = .{ .lhs = try self.pool.addApp(.app, add, &.{ cc.t, a.t }), .rhs = try self.pool.addApp(.app, add, &.{ cc.t, bb.t }) } });
        const rhs = try self.pool.add(.{ .eq = .{ .lhs = a.t, .rhs = bb.t } });
        const body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = lhs, .rhs = rhs } });
        return try self.closeForallChain(body, &.{ cc, a, bb }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanIntro")) {
        // forall a, d, b; add(a, succ(d)) = b -> less_than(a, b)
        const add = symbols.add orelse return null;
        const less_than = symbols.less_than orelse return null;
        const succ = symbols.succ orelse return null;
        const a = try mkfv(self, sort, "a");
        const d = try mkfv(self, sort, "d");
        const bb = try mkfv(self, sort, "b");
        const eq = try self.pool.add(.{ .eq = .{ .lhs = try self.pool.addApp(.app, add, &.{ a.t, try self.pool.addApp(.app, succ, &.{d.t}) }), .rhs = bb.t } });
        const lt = try self.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = eq, .rhs = lt } });
        return try self.closeForallChain(body, &.{ a, d, bb }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanTransitive")) {
        // forall a, b, c; less_than(a, b) -> less_than(b, c) -> less_than(a, c)
        const less_than = symbols.less_than orelse return null;
        const a = try mkfv(self, sort, "a");
        const bb = try mkfv(self, sort, "b");
        const cc = try mkfv(self, sort, "c");
        const ab = try self.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const bc = try self.pool.addApp(.pred, less_than, &.{ bb.t, cc.t });
        const ac = try self.pool.addApp(.pred, less_than, &.{ a.t, cc.t });
        const body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = ab, .rhs = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = bc, .rhs = ac } }) } });
        return try self.closeForallChain(body, &.{ a, bb, cc }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanIrreflexive")) {
        // forall n; not less_than(n, n)
        const less_than = symbols.less_than orelse return null;
        const n = try mkfv(self, sort, "n");
        const nn = try self.pool.addApp(.pred, less_than, &.{ n.t, n.t });
        const body = try self.pool.add(.{ .not = nn });
        return try self.closeForallChain(body, &.{n}, sort);
    }
    if (std.mem.eql(u8, name, "additionPreservesOrder")) {
        // forall a, b, c; less_than(a, b) -> less_than(add(c, a), add(c, b))
        const add = symbols.add orelse return null;
        const less_than = symbols.less_than orelse return null;
        const a = try mkfv(self, sort, "a");
        const bb = try mkfv(self, sort, "b");
        const cc = try mkfv(self, sort, "c");
        const ab = try self.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const ca = try self.pool.addApp(.app, add, &.{ cc.t, a.t });
        const cb = try self.pool.addApp(.app, add, &.{ cc.t, bb.t });
        const lifted = try self.pool.addApp(.pred, less_than, &.{ ca, cb });
        const body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = ab, .rhs = lifted } });
        return try self.closeForallChain(body, &.{ a, bb, cc }, sort);
    }
    if (std.mem.eql(u8, name, "multiplicationPreservesOrder")) {
        // forall a, b, c; less_than(a, b) -> less_than(mul(succ(c), a), mul(succ(c), b))
        const less_than = symbols.less_than orelse return null;
        const succ = symbols.succ orelse return null;
        const mul = symbols.mul orelse return null;
        const a = try mkfv(self, sort, "a");
        const bb = try mkfv(self, sort, "b");
        const cc = try mkfv(self, sort, "c");
        const ab = try self.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const succ_c = try self.pool.addApp(.app, succ, &.{cc.t});
        const ma = try self.pool.addApp(.app, mul, &.{ succ_c, a.t });
        const mb = try self.pool.addApp(.app, mul, &.{ succ_c, bb.t });
        const lifted = try self.pool.addApp(.pred, less_than, &.{ ma, mb });
        const body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = ab, .rhs = lifted } });
        return try self.closeForallChain(body, &.{ a, bb, cc }, sort);
    }
    if (std.mem.eql(u8, name, "addIsCommutative")) {
        // forall a, b; add(a, b) = add(b, a)
        const add = symbols.add orelse return null;
        const a = try mkfv(self, sort, "a");
        const bb = try mkfv(self, sort, "b");
        const ab = try self.pool.addApp(.app, add, &.{ a.t, bb.t });
        const ba = try self.pool.addApp(.app, add, &.{ bb.t, a.t });
        const body = try self.pool.add(.{ .eq = .{ .lhs = ab, .rhs = ba } });
        return try self.closeForallChain(body, &.{ a, bb }, sort);
    }
    return null;
}

/// A fresh var pair: its interned name + its fvar term (for lemma-shape construction).
const ArithVar = struct { name: StrId, t: TermId };

/// Close `body` in `forall v0, v1, …;` over the fresh vars (outermost = vars[0]).
fn closeForallChain(self: *Prove, body: TermId, vars: []const ArithVar, sort: term.SortId) Error!TermId {
    var f = body;
    var i = vars.len;
    while (i > 0) {
        i -= 1;
        const closed = try self.pool.close(f, vars[i].name);
        f = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = vars[i].name, .body = closed } });
    }
    return f;
}

// -- the AC flatten / build / sort substrate (ported from the eager elaborate.zig) -----

/// Flatten an `op`-tree into its atom summands (any maximal subterm that is not itself an
/// `op(_, _)`), left-to-right.
pub fn flattenSum(self: *Prove, op_sym: term.SymId, id: TermId, out: *std.ArrayList(TermId)) Error!void {
    const node = self.pool.get(id);
    if (node == .app and node.app.sym == op_sym and node.app.args_len == 2) {
        // copy arg ids before recursing: pool.args aliases pool.extra, which a walk that grows
        // the pool would dangle.
        const args = self.pool.args(node.app);
        const a0 = args[0];
        const a1 = args[1];
        try self.flattenSum(op_sym, a0, out);
        try self.flattenSum(op_sym, a1, out);
        return;
    }
    try out.append(self.ctx.arena, id);
}

/// Build a right-nested `op(l0, op(l1, … ln))` comb from the leaves (non-empty).
fn buildRightNested(self: *Prove, op_sym: term.SymId, leaves: []const TermId) Error!TermId {
    var cur = leaves[leaves.len - 1];
    var i = leaves.len - 1;
    while (i > 0) {
        i -= 1;
        cur = try self.pool.addApp(.app, op_sym, &.{ leaves[i], cur });
    }
    return cur;
}

/// In-place insertion sort by `termOrder` (stable, small lists).
fn sortTerms(self: *Prove, items: []TermId) void {
    var i: usize = 1;
    while (i < items.len) : (i += 1) {
        const v = items[i];
        var j = i;
        while (j > 0 and self.pool.termOrder(items[j - 1], v) == .gt) : (j -= 1) {
            items[j] = items[j - 1];
        }
        items[j] = v;
    }
}

const AcPlan = struct { sorted: TermId, trace: []const simplify_mod.Rewrite };

/// Re-associate `start` to a right-nested comb (via associativity only, terminating), then
/// bubble-sort its atoms into canonical `termOrder`, accumulating one trace. `assoc_idx` is
/// the rule-array index of the associativity rule (after the distribute pre-rules); `comm_idx`
/// / `swap_idx` the commutativity / swap rules.
pub fn acPlan(self: *Prove, symbols: presburger_mod.Symbols, rules: []const simplify_mod.Rule, assoc_idx: usize, comm_idx: usize, swap_idx: usize, start: TermId) Error!?AcPlan {
    const op_sym = symbols.add.?; // the reordered operator (the AC vocabulary's `add` slot)
    // phase 1: right-nest via associativity ONLY (a single-rule slice, terminating).
    const assoc_only = rules[assoc_idx .. assoc_idx + 1];
    const rn = simplify_mod.normalize(self.ctx.arena, self.pool, self.ctx.interner, assoc_only, start, 1000) catch |e| switch (e) {
        error.Limit => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    // phase 2: flatten the right-nested comb and bubble-sort.
    var leaves: std.ArrayList(TermId) = .empty;
    try self.flattenSum(op_sym, rn.nf, &leaves);
    var trace: std.ArrayList(simplify_mod.Rewrite) = .empty;
    // phase-1 normalized over the single-rule slice, so its trace rule_idx is 0-relative;
    // rebase it to the full-array index.
    for (rn.trace) |rw| {
        var r = rw;
        r.rule_idx = rw.rule_idx + assoc_idx;
        try trace.append(self.ctx.arena, r);
    }
    const sorted = (try self.sortTrace(rules, comm_idx, swap_idx, op_sym, leaves.items, &trace)) orelse return null;
    return .{ .sorted = sorted, .trace = trace.items };
}

/// Bubble-sort a comb's summands, appending one rewrite per adjacent swap (the swap lemma
/// inside the comb, the commutativity lemma for the final pair). Returns the sorted whole
/// comb, or null when a fabricated rewrite fails to match its lemma. `leaves` is mutated.
fn sortTrace(
    self: *Prove,
    rules: []const simplify_mod.Rule,
    comm_idx: usize,
    swap_idx: usize,
    op_sym: term.SymId,
    leaves_in: []const TermId,
    trace: *std.ArrayList(simplify_mod.Rewrite),
) Error!?TermId {
    const leaves = try self.ctx.arena.dupe(TermId, leaves_in);
    var whole = try self.buildRightNested(op_sym, leaves);
    if (leaves.len > 1) {
        for (0..leaves.len - 1) |pass| {
            for (0..leaves.len - 1 - pass) |i| {
                if (self.pool.termOrder(leaves[i], leaves[i + 1]) != .gt) continue;
                // the FINAL adjacent pair is a bare `op(x, y)` → commutativity; an interior
                // pair sits at the head of a longer tail `op(x, op(y, r))` → the swap lemma.
                const tail_pair = i + 2 == leaves.len;
                const rule_idx = if (tail_pair) comm_idx else swap_idx;
                const sub_before = try self.buildRightNested(op_sym, leaves[i..]);
                std.mem.swap(TermId, &leaves[i], &leaves[i + 1]);
                const sub_after = try self.buildRightNested(op_sym, leaves[i..]);
                const after = try self.buildRightNested(op_sym, leaves);
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

/// Concatenate two rewrite traces (short-circuiting an empty side).
fn concatTrace(self: *Prove, a: []const simplify_mod.Rewrite, bb: []const simplify_mod.Rewrite) Error![]const simplify_mod.Rewrite {
    if (a.len == 0) return bb;
    if (bb.len == 0) return a;
    var out: std.ArrayList(simplify_mod.Rewrite) = .empty;
    try out.appendSlice(self.ctx.arena, a);
    try out.appendSlice(self.ctx.arena, bb);
    return out.items;
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
