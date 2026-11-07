//! Prove — the DEMAND WALK DRIVER (Step 8, W5): the semantic half of a ProveTask's
//! step-walk. It plugs into `Walk`'s driver seam (readPass / process / caseConclude /
//! exitBlock) and accumulates the kernel-checkable lowering (steps + blocks) as the walk
//! advances; `finish` runs the kernel over the whole proof and the use-all-facts pass.
//!
//! Every kernel justification arm is lowered here; every name resolves LOCAL (Walk's
//! LocalStepKV/LocalIdentKV) then GLOBAL (IdentKV/FactKV, populated by the read pass) —
//! never through an eager environment.
//!
//! `USING` STEPS AND THE SCAFFOLDING RULE. A `using` step is an engine word (`model`,
//! `import`, `instantiation`) or an ACCELERATED TACTIC. Every tactic lives in its own file
//! under `Accelerants/` as one variant of the `Tactic` union below, and passes through three
//! phases the scaffolding drives in order: READ (demand what later phases will read — the
//! only phase that may park), DECIDE (accept or reject; `--fast` stops here and admits), and
//! CERTIFY (build the synthetic schema the kernel checks; strict only). The scaffolding —
//! the read passes, `admit`, `demandUsing`/`lowerUsing`, `accelerantPremises`, root seeding —
//! contains NO TACTIC-SPECIFIC LOGIC: it dispatches through the union once
//! (`switch (tactic) { inline else => |a| … }`) and reads each tactic's declared
//! `schema_slot`/`premise_shape`/`lemma_args` off its type. No rule-name comparison, no word
//! list, no `switch (word)` arm naming a tactic belongs anywhere else in this file or in
//! `RefScan`; a behaviour that must vary per tactic becomes a const or a phase hook on the
//! tactic. The converse holds too: a tactic file holds no scaffolding — it supplies the three
//! phase functions and nothing about how or when they are called.
//!
//! ORDINAL ALIGNMENT: Walk assigns StepOrdinals/BlockOrdinals in walk order; this driver
//! appends exactly ONE main kernel step per walked leaf step (synthetics — multi-arg
//! apply_at intermediates — carry no ordinal) and one kernel block per entered block,
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
const Expand = @import("../Expand.zig");
const Elab = @import("Elab.zig");
const Schema = @import("Schema.zig");
const Accelerant = @import("Accelerant.zig");
const common = @import("Accelerants/common.zig");
const Verify = @import("../../Verify.zig");
const EqCert = @import("EqCert.zig");
const polycanon = @import("Accelerants/polycanon.zig");
const rewrite = @import("Accelerants/rewrite.zig");
const presburger = @import("Accelerants/presburger.zig");
const smt = @import("smt.zig");
const farkas = @import("Accelerants/farkas.zig");
const FactKV = @import("../../FactKV.zig");
const FetchTask = @import("../../Engine/FetchTask.zig");
const ModelTask = @import("../../Engine/ModelTask.zig");
const ProveTask = @import("../ProveTask.zig");
const testrig = @import("Accelerants/testrig.zig");

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
/// Per lowered step (index-aligned with `low_steps`): the step's formula in SOURCE space —
/// elaborated with the model OFF. In an ordinary proof this is the lowered formula itself; in a
/// MODEL TRANSFER the lowered formula is relativized to the target and this is the un-remapped
/// original (same hygienic fvars, source global symbols). Accelerant PRODUCERS read premises
/// from here (`producerPremiseFormula`): they build their synthetic in source space, and the
/// instance ProveTask adopts the model. See `demandUsing`.
source_formulas: std.ArrayList(TermId) = .empty,
/// SOURCE-SPACE AST (a model transfer only): the decl expanded WITHOUT the model, paired per
/// step formula / arg / goal with the model-expanded AST the Walk drives (`sourceExpr`). The
/// source twin of a step is elaborated from THIS — the source proof's own text — not from the
/// model AST with the model switched off: a source symbol the model maps ONTO A DEFINE was
/// already substituted by its parent-space body there, which is not source space at all.
source_ast: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, *const ast.Expr) = null,
low_blocks: std.ArrayList(kernel.Block) = .empty,
/// Walk StepOrdinal -> kernel StepId (main steps only; synthetics skip)
ordinal_step: std.ArrayList(kernel.StepId) = .empty,
/// Walk BlockOrdinal -> kernel BlockId (index 0 = root)
ordinal_block: std.ArrayList(kernel.BlockId) = .empty,
/// open `case` contexts, innermost last (pushed at case-process, popped at conclude)
case_stack: std.ArrayList(CaseCtx) = .empty,
/// hygienic fresh-name counter (shared with Elab via pointer)
fresh_counter: u32 = 0,
/// ADMIT MODE (`--fast <accelerant>`): when set, a producer does ITS OWN cheap acceptance
/// check for the trusted step and returns WITHOUT building a certificate (the step is
/// accelerated — accepted, not proved). Set only for the duration of a trusted `admit` call.
/// A producer that ADMITS sets `admit_ok = true` and returns null (no cert); a producer that
/// REJECTS fails (→ error.Recover) as usual. `admit` distinguishes admit-null from reject.
admit_mode: bool = false,
admit_ok: bool = false,
/// the `using` WORDS this proof ADMITTED (`--fast`): each trusted step's word is inserted here.
/// The ProveTask records this against the published fact for the summary's disclosure.
admitted: Verify.Word.Set = Verify.Word.Set.initEmpty(),
/// HOLE NAMES this proof transitively rests on — a cited hole, or a cited fact that itself rests
/// on holes (inherited in `resolveFactRef` from `ctx.hole_taint`). Deduped. Recorded against the
/// published fact for the summary's blast-radius report ONLY (never a proof verdict). [[hole-mechanism]]
holes_used: std.ArrayList(InternPool.StrId) = .empty,
/// AXIOM fact Indexes this proof transitively rests on — a cited axiom, or a cited theorem that
/// itself rests on axioms (inherited in `resolveFactRef` from `ctx.axiom_taint`). Deduped.
/// Recorded against the published fact for the `--axioms` report ONLY. [[axiom-tracking-plan]]
axioms_used: std.ArrayList(InternPool.Index) = .empty,
/// KNOWN PROPOSITIONS (see Elab.Known): what binders, hypotheses and proved steps have TAUGHT,
/// looked up by identity at every guarded application. `blocks` points at `low_blocks`.
known: Elab.Known = undefined,
/// the kernel block of the step being PROCESSED — the block a use's lookup is made from. Only
/// the process pass checks obligations (the read pass re-elaborates without checking).
current_block: ?kernel.BlockId = null,
/// SCHEMA CONTEXT (set only when this Prove drives a schema INSTANCE): the bound args
/// (installed on every Elab it builds) + the param names (skipped by the read pass). Null/
/// empty for an ordinary proof. See [[schema-reification-blocker]] rebuild (Step 12).
schema_args: ?*const Schema.SchemaArgs = null,
/// SOURCE-space twins of `schema_args` (the same map outside a model transfer) — what a
/// source-space Elab substitutes for the params. See `source_formulas` / `sourceElab`.
schema_args_source: ?*const Schema.SchemaArgs = null,
schema_params: []const StrId = &.{},
/// MODEL this proof runs THROUGH (Step 13): when non-`.universe`, this Prove is
/// re-proving a source theorem in a model namespace — every global (sym via Elab, fact
/// via resolveFactRef) is filtered `applyModel(model, source)`, so source names remap to
/// their targets. `.universe` = an ordinary (identity) proof.
model: InternPool.Index = .universe,
/// TRUE while an accelerant's synthetic is produced in the PAINTED (target) namespace.
painted_production: bool = false,
/// THE PROOF TREE: this proof's own `(namespace, name)`. Every ProveTask this proof demands
/// inherits it as `parent`, so the chain records "X was proved because Y's proof needed it".
/// Null only for a context with no owning fact (the statement-elaboration helper). See
/// `Context.proof_parent`.
self_key: ?FactKV.Key = null,
/// VALUE-PARAM GUARD WRAPPERS around a model-transferred schema instance's proof (injected by
/// the instance ProveTask): the outermost `guard_wrappers` block levels are `assume good(p)`
/// blocks whose export claims (`good(p) -> …`) are TARGET-space steps with no source-space
/// twin (a source proof never states its model's guard) — the source twin is skipped there.
/// Zero for every other proof.
guard_wrappers: u32 = 0,
/// A PRODUCER's outstanding demand: an accelerant producer that needs an identifier not in
/// the goal (polynomial's `ZERO` for inverse cancellation, `add` for numeral expansion —
/// `completePolyOps`) racks the FetchTask, records it here, and returns null WITHOUT a
/// diagnostic; `demandUsing` then reports `.blocked` (the step's read pass suspends and the
/// producer re-runs on resume, idempotently). Null = no demand outstanding.
producer_blocker: ?Engine.TaskIndex = null,
/// The LOCAL premise refs the last produced accelerant synthetic actually kept as antecedents
/// (`Synthetic.premises`) — a producer DROPS a cited rule its certificate never fired, so the
/// call site must discharge exactly these, not every local ref the author wrote. Set by
/// `demandUsing` per step; read by `lowerUsing` (`accelerantPremises`). Null = not produced
/// this pass (an admitted/trusted step, or a non-accelerant word).
producer_premise_refs: ?[]const lexer.Token = null,
/// Per-eigen RELATIVIZATION guards peeled off a `_quantified` accelerant's TRANSFERRED goal
/// (`∀a; inH(a) -> …` — set by peelForallEq, parallel to its eigen list). The ∀-re-closers
/// (wrapSimplifyForall / closeOverEigen) re-add them per level, matching the kernel's guarded
/// generalize derivation. Empty outside a transfer / for unguarded goals.
quant_guards: []const ?TermId = &.{},

/// `goal_source` = the case goal in SOURCE space (== `goal` unless under a model transfer); the
/// concluding step records it alongside its lowered (target-space) formula — see `source_formulas`.
const CaseCtx = struct { goal: TermId, goal_source: TermId, disj: kernel.SRef, loc: u32 };

pub fn init(ctx: *Context, h: *Engine.Handle, source: []const u8, file: InternPool.Index, ns: InternPool.Index) Allocator.Error!*Prove {
    const p = try ctx.arena.create(Prove);
    const pool = try ctx.arena.create(term.Pool);
    pool.* = .init(ctx.arena, ctx.gpa); // durable nodes on the main arena; work-stacks on the GPA
    p.* = .{ .ctx = ctx, .h = h, .pool = pool, .source = source, .file = file, .ns = ns };
    p.known = .{ .blocks = &p.low_blocks };
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

pub fn elab(self: *Prove, w: *const Walk) Elab {
    var e = Elab.init(self.ctx.arena, self.ctx.io, self.ctx, self.ctx.interner, &self.ctx.idents, self.pool, self.ctx.sink, self.source, w, self.ns, &self.fresh_counter);
    e.schema_args = self.schema_args; // null in an ordinary proof; set for a schema instance
    e.model = self.model; // .universe (identity) in an ordinary proof; M for a model transfer
    // obligations are checked in the PROCESS pass only (a read-pass elaboration is redone there).
    if (self.current_block) |kb| {
        e.known = &self.known;
        e.known_block = kb;
    }
    return e;
}

/// An Elab in SOURCE space: the model OFF (global symbols resolve un-remapped) and the
/// obligation sinks detached (a source-space pass records no TCCs — the target-space pass
/// already did). Used to build the accelerant producers' inputs under a model transfer
/// (`demandUsing`) and to record `source_formulas` at lowering. Only meaningful when
/// `self.model` is a real model; callers use the ordinary term otherwise.
/// The source-space AST for a model-AST expression (itself when unchanged / not a transfer).
fn sourceExpr(self: *const Prove, e: *const ast.Expr) *const ast.Expr {
    const m = self.source_ast orelse return e;
    return m.get(e) orelse e;
}

fn sourceElab(self: *Prove, w: *const Walk) Elab {
    var e = self.elab(w);
    e.model = .universe;
    e.source_space = true; // locals resolve at their SOURCE sort (see Elab.source_space)
    e.schema_args = self.schema_args_source orelse self.schema_args; // params at source terms
    e.known = null;
    return e;
}

/// True when this proof runs under a model transfer (its lowered formulas are relativized).
fn underModel(self: *const Prove) bool {
    return self.model != InternPool.Index.none and self.model != .universe;
}

/// ACCELERANTS BUILD IN SOURCE SPACE AND THE INSTANCE ADOPTS THE MODEL. Under any model
/// transfer a synthetic is a plain source theorem, relativized by its instance ProveTask
/// through the (possibly composed) model into exactly the claim's space; every producer input
/// carries a source-space twin (goal, `source_formulas`, binder `source_sort`,
/// `schema_args_source`, raw cited facts). A GUARDED model (a sort mapped onto a refined
/// target) needs nothing from the producer: the guard is the ambient model's business — the
/// instance injects `guard(p) ->` for each value param whose image sort is refined (ProveTask's
/// instance setup; the r-values of a model live in its PARENT space, so the guard predicate is
/// the parent's, never re-interpreted through the model) and the call site discharges it
/// (`withGuardPremises`), exactly as a `∀` binder's guard is injected and discharged.
fn sourceSpaceAccelerants(self: *const Prove) bool {
    return self.underModel();
}

// -- small utilities -------------------------------------------------------------------

pub fn text(self: *const Prove, tok: lexer.Token) []const u8 {
    return self.source[tok.start..tok.end];
}

/// A stamped token's interned name — the parser stamped every engine-parsed token, so past
/// parsing names are integers, never re-derived from source text.
pub fn tokName(tok: lexer.Token) StrId {
    std.debug.assert(tok.name != InternPool.Index.none);
    return tok.name;
}

/// A term's sort: an fvar's own sort, an app's head result sort; `.prop` for non-term
/// structure. (The operand sort for polynomial's rule-pattern fvars comes from here.)
pub fn termSort(self: *const Prove, t: TermId) SortId {
    return switch (self.pool.get(t)) {
        .fvar => |v| v.sort,
        .app => |a| @enumFromInt(@intFromEnum(self.ctx.interner.symResult(@enumFromInt(@intFromEnum(a.sym))))),
        // not a term node — a proposition. Returns the marker, which matches no real sort, so
        // every consumer's `!= v.sort` test rejects it (none of them wants a proposition here).
        else => Elab.prop_sort,
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

pub fn fail(self: *Prove, offset: u32, comptime fmt: []const u8, args: anytype) Error {
    self.ctx.sink.add(self.diagFile(), offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
}

/// The file this proof's offsets index — its own `file`, as a dense FileId. Derived rather
/// than tracked on the sink so a diagnostic's file is a value (see diagnostics.zig).
fn diagFile(self: *const Prove) u32 {
    const fid = self.ctx.fileOf(self.file) orelse return 0;
    return @intFromEnum(fid);
}

/// A fresh name whose suffix is a SOURCE LOCATION rather than the mint counter — for a
/// PROOF BINDER, whose identity the source fixes. See `bindProofVar`'s note: the counter made
/// a binder's name depend on how much of the proof preceded it, and that name reaches
/// `Schema.instanceHash`. Two binders cannot share a start offset, so this disambiguates as
/// well as the counter did while being stable under edits elsewhere in the proof.
pub fn freshNamedAt(self: *Prove, prefix: []const u8, loc: u32) Error!StrId {
    const s = std.fmt.allocPrint(self.ctx.arena, "{s}#{d}", .{ prefix, loc }) catch return error.OutOfMemory;
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

pub fn freshNamed(self: *Prove, prefix: []const u8) Error!StrId {
    self.fresh_counter += 1;
    const s = std.fmt.allocPrint(self.ctx.arena, "{s}#{d}", .{ prefix, self.fresh_counter }) catch return error.OutOfMemory;
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

pub fn renderTerm(self: *Prove, id: TermId) Error![]const u8 {
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
pub fn resolveRefs(ctx: *Context, h: *Engine.Handle, file: InternPool.Index, ns: InternPool.Index, model: InternPool.Index, parent: ?FactKV.Key, refs: []const RefScan.Ref) Allocator.Error!?Engine.TaskIndex {
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
        // MODEL-HOME fallback (13e): relativization introduces TARGET-file symbols (the guard
        // pred `inH`, its closure facts) into a transferred proof's re-elaborated synthetics;
        // those names have no decl in the SOURCE file. If the name is undeclared in the target
        // file but declared in the model's HOME file (where the model — and its guard
        // vocabulary — was written), retarget the demand there.
        if (r.ns == null and model != InternPool.Index.none and model != .universe) {
            const home = ctx.interner.keyOf(model).model.home;
            if (home != InternPool.Index.none and home != target_file) miss: {
                if (ctx.fileOf(target_file)) |tfid| {
                    if (ctx.declOf(tfid, r.name) != null) break :miss; // declared at source — no fallback
                }
                const hfid = ctx.fileOf(home) orelse break :miss;
                if (ctx.declOf(hfid, r.name) == null) break :miss; // not in home either
                target_file = home;
                target_ns = try ctx.interner.namespace(.universe, home);
            }
        }
        switch (r.domain) {
            .ident => {
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
            // a SCHEMA is a fact-with-params — it resolves through the FACT table (its
            // ProveTask publishes a `.schema` locator instead of a ground fact); the
            // instantiate handler then demands the monomorphized instance FACT separately.
            .fact, .schema => {
                const state = ctx.facts.lookup(ctx.io, .{ .namespace = target_ns, .name = r.name }) orelse {
                    blocker = try h.rackIndexed(try ProveTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file, .parent = parent }));
                    continue;
                };
                switch (state) {
                    .in_flight => |owner| {
                        if (owner != h.self_index) blocker = owner;
                    },
                    .proven => |src| {
                        // In a model TRANSFER, a cited SOURCE THEOREM needs its TRANSFERRED version
                        // `(model, target_file).name` (re-proved under the model). ONLY a theorem —
                        // an AXIOM must go through the obligation overlay (mapped → local fact, or
                        // FAIL if the substitution affects it and the model leaves it unmapped);
                        // giving an axiom a free transferred leaf would let an unmapped axiom
                        // through (unsound). `resolveFactRef` prefers the transferred fact when
                        // present. (A schema isn't transferred this way — its instance carries the
                        // model — so `.fact` domain only.)
                        if (r.domain == .fact and model != InternPool.Index.none and model != .universe and
                            ctx.interner.keyOf(src) == .fact and ctx.interner.keyOf(src).fact.kind == .theorem)
                        {
                            const tns = try ctx.interner.namespace(model, target_file);
                            const tstate = ctx.facts.lookup(ctx.io, .{ .namespace = tns, .name = r.name });
                            if (ctx.verify.trace_facts) {
                                const what: []const u8 = if (tstate == null) "ABSENT -> racking its ProveTask (blocks)" else switch (tstate.?) {
                                    .proven => "proven",
                                    .in_flight => |o| if (o == h.self_index) "in_flight owned by SELF" else "in_flight owned by ANOTHER task — read pass sets NO blocker",
                                };
                                const line = std.fmt.allocPrint(ctx.arena, "[read pass] transferred copy of {s} under model#{d}: {s}\n", .{ ctx.interner.stringBytes(r.name), @intFromEnum(model), what }) catch "";
                                ctx.traceLine(line);
                            }
                            // ABSENT: rack its re-proof and wait. IN FLIGHT under another task:
                            // wait on THAT task — the same rule as the universe key above. The
                            // old code only racked on absent and set no blocker on in_flight, so a
                            // citer whose other refs resolved first ran its process pass while the
                            // transferred copy was still being proved, and `resolveFactRef` fell
                            // through to the UNTRANSFERRED source copy — a statement in the source
                            // sort against a claim in the target sort. Order-dependent (the run
                            // queue is a stack), so it surfaced only in a large directory sweep.
                            if (tstate == null) {
                                blocker = try h.rackIndexed(try ProveTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file, .model = model, .parent = parent }));
                            } else if (tstate.? == .in_flight and tstate.?.in_flight != h.self_index) {
                                blocker = tstate.?.in_flight;
                            }
                        }
                    },
                }
            },
        }
    }
    return blocker;
}

/// Elaborate a target fact's STATEMENT (its stated formula, relativized under `model`) into a
/// caller-provided scratch `pool`, PUBLISHING NOTHING and CLAIMING NO FactKV key. This is the
/// pure "statement elaborator" the trusted `--fast` admission uses to obtain the citation's
/// Walk `(file, name)` to the ORIGIN that actually STATES the fact, following re-export
/// aliases (`theorem sqrtOne = sqrt_theory.sqrtOne` has no formula of its own — identity is by
/// ORIGIN). Each hop's file is PARSE-demanded, so the caller may suspend. Stops at a local
/// fact, at a name it cannot resolve (the caller's own `declOf` reports that cleanly), or
/// after 16 hops (a cycle is diagnosed elsewhere; do not spin).
///
/// Both the read pass and `process` call this, so a trusted citation's whole chain is parsed
/// before the α-match runs — the invariant being that `--fast` must never report an error
/// strict does not, and strict reaches the origin via `ProveTask.factAlias`.
fn factOrigin(
    self: *Context,
    h: *Engine.Handle,
    file: *InternPool.Index,
    name: *StrId,
) Allocator.Error!enum { ready, suspended } {
    var hops: u8 = 0;
    while (hops < 16) : (hops += 1) {
        switch (try self.demandParse(h, file.*)) {
            .parsed => {},
            .parsing => |t| {
                h.suspendOn(t);
                return .suspended;
            },
            .unparsed => return .ready, // undiscovered — the caller diagnoses
        }
        const f = self.fileOf(file.*) orelse return .ready;
        const d = self.declOf(f, name.*) orelse return .ready;
        const alias = ast.aliasOf(d) orelse return .ready; // a local fact: the origin
        // `ns.thm` hops to ns's file; a bare `thm` re-exports within this file.
        if (alias.target.qualifier != InternPool.Index.none) {
            const self_ns = try self.interner.namespace(.universe, file.*);
            // The qualifier is an import NAME. If nobody has racked its fetch yet, giving up
            // here (`return .ready`, which this used to do) hands the caller an UNRESOLVED
            // alias, which it can only diagnose as "'X' has no stated formula" — an error
            // strict never gives, since strict reaches the origin through `factAlias` after the
            // read pass fetched the import. Rack the fetch and suspend instead, exactly as
            // `resolveRefs` does for a qualified ref; the caller re-runs once it lands.
            // (Surfaced by `--fast` reading a `simplify` rule's statement: four `fact X = ns.y`
            // re-exports in std/integer/order.b4m and std/permutation/alternating.b4m.)
            const state = self.idents.lookup(self.io, .{ .namespace = self_ns, .name = alias.target.qualifier }) orelse {
                const t = try h.rackIndexed(try FetchTask.new(self.arena, .{
                    .file = file.*,
                    .name = alias.target.qualifier,
                    .loc = alias.target.start,
                    .loc_file = file.*,
                }));
                h.suspendOn(t);
                return .suspended;
            };
            const ix = switch (state) {
                .done => |ix| ix,
                .in_flight => |owner| {
                    if (owner != h.self_index) h.suspendOn(owner);
                    return .suspended;
                },
            };
            if (self.interner.keyOf(ix) != .import) return .ready;
            // the import Item holds a NAMESPACE index; its file is one level down.
            file.* = self.interner.keyOf(self.interner.keyOf(ix).import.namespace).namespace.file;
        }
        name.* = tokName(alias.target);
    }
    return .ready;
}

/// stated proposition WITHOUT proving it — reusing the SAME relativization logic the strict
/// goal phase runs (`ProveTask.elaborateGoalInto`): RefScan → resolveRefs → Elab with `model`.
///
/// Suspendable via the CALLER's handle `h`: `.suspended` = a demand raced ahead (parse in
/// flight, or an ident FetchTask racked — `h.suspendOn` was already called; the caller returns).
/// `.ready` = the elaborated statement TermId (into `pool`). `.failed` = a diagnosed error (a
/// schema / hole / missing decl / non-fact / Recover during elaboration).
///
/// It only ever demands PARSE (ParseTask) + resolveRefs (which may rack FetchTasks for IDENT-
/// domain symbol refs — fine). A statement carries no fact CITATIONS, so no ProveTask is racked.
pub fn elaborateFactStatement(
    self: *Context,
    h: *Engine.Handle,
    file_arg: InternPool.Index,
    name_arg: StrId,
    model: InternPool.Index,
    pool: *term.Pool,
) Allocator.Error!union(enum) { ready: term.TermId, suspended: void, failed: void } {
    // FOLLOW ALIASES to the origin that actually STATES the formula. A re-export
    // (`theorem sqrtOne = sqrt_theory.sqrtOne`) has no formula of its own — identity is by
    // ORIGIN — so reading the statement here has to chase the chain, exactly as the strict
    // path does (`ProveTask.factAlias`). Without this an admitted `[using import(I) thm]`
    // failed on an aliased `thm` while strict passed, breaking the invariant that `--fast`
    // never reports an error strict does not.
    var file = file_arg;
    var name = name_arg;
    switch (try factOrigin(self, h, &file, &name)) {
        .ready => {},
        .suspended => return .suspended,
    }
    const fid = self.fileOf(file) orelse {
        self.sink.add(0, 0, "internal: elaborate a statement in an undiscovered file", .{}) catch return error.OutOfMemory;
        return .failed;
    };
    // Every diagnostic below indexes the STATEMENT's own file — `fid` — not the caller's.
    // (This used to save/restore an ambient sink field; passing the file is the same
    // intent without the invariant that only one task may be running.)
    const diag_file: u32 = @intFromEnum(fid);
    const source = self.files.get(@intFromEnum(fid)).source;

    // resolve the decl by name; a STATEMENT lives on a local axiom/theorem (an alias has no
    // formula of its own, a schema / hole is not a ground statement).
    const decl = self.declOf(fid, name) orelse {
        self.sink.add(diag_file, 0, "reference not found: '{s}'", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory;
        return .failed;
    };
    const fact = ast.factOf(decl) orelse {
        self.sink.add(diag_file, ast.declName(decl).start, "'{s}' has no stated formula (an alias or a non-fact)", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory;
        return .failed;
    };
    if (fact.params != null) {
        self.sink.add(diag_file, fact.name.start, "'{s}' is a schema; its statement is not a ground formula", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory;
        return .failed;
    }
    // DEFINE EXPANSION first (see Engine/Expand): the statement is made define-free before its
    // read pass or elaboration sees it.
    const formula = switch (try Expand.expandFormula(self, h, file, fact.formula, .{ .model = model })) {
        .ready => |f| f,
        .suspended => return .suspended,
        .failed => return .failed,
    };

    // RESOLUTION ns = the file's UNIVERSE ns (source names resolve there, then applyModel
    // redirects for a transfer). A fresh Walk (no proof-local binders) + fresh counter own
    // the standalone-call scratch state.
    const resolve_ns = try self.interner.namespace(.universe, file);
    const walk = try self.arena.create(Walk);
    walk.* = Walk.init(self.arena, self.interner, source, self.sink);

    var scanner = RefScan.init(self.arena, self.interner, source, walk);
    scanner.ctx = self;
    scanner.file = file;
    const refs = try scanner.scanFormula(formula);
    if (try resolveRefs(self, h, file, resolve_ns, model, null, refs)) |blocker| {
        h.suspendOn(blocker);
        return .suspended;
    }

    const fresh_counter = try self.arena.create(u32);
    fresh_counter.* = 0;

    var e = Elab.init(self.arena, self.io, self, self.interner, &self.idents, pool, self.sink, source, walk, resolve_ns, fresh_counter);
    e.model = model; // remap source globals for a model transfer (identity for .universe)
    const typed = e.requireProp(e.elaborateExpr(formula) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    }, formula) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    return .{ .ready = typed.id };
}

// -- the Walk driver seam --------------------------------------------------------------

pub fn readPass(self: *Prove, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!?Engine.TaskIndex {
    _ = block;
    // A TRUSTED `using` step (`--fast <word>`) is NOT proved: no synthetic schema, no transfer/
    // instance ProveTask, no cited-fact proof demands — racking any of those would pay for the
    // whole transitive proof subtree that `--fast` exists to skip. Its read pass only makes the
    // AST it must SHAPE-CHECK available (parse the source file; resolve a model's overlay), then
    // `process` α-matches the statement + emits `.accelerated`. Nothing is published, so a later
    // EXPLICIT (strict) demand of the same fact still does the full check (redone work is fine).
    if (step.body == .claim and self.trusted(step.body.claim)) {
        // a transferred SCHEMA is an instantiation in disguise — strict even when trusted.
        const schema_transfer = if (self.trustWord(step.body.claim)) |wd| wd == .model and switch (try self.transfersSchema(step.body.claim)) {
            .yes => true,
            .no => false,
            .blocked => |t| return t,
        } else false;
        if (!schema_transfer) return self.trustedReadPass(w, step);
    }
    var scanner = RefScan.init(self.ctx.arena, self.ctx.interner, self.source, w);
    scanner.schema_params = self.schema_params; // skip param names when driving a schema instance
    scanner.ctx = self.ctx;
    scanner.file = self.file;
    const refs = try scanner.scanStep(step);
    if (try resolveRefs(self.ctx, self.h, self.file, self.ns, self.model, self.self_key, refs)) |blocker| return blocker;

    // an `instantiate` step additionally DEMANDS the monomorphized instance FACT (its own
    // ProveTask) — the schema name + args are now resolved, so build the instance and
    // suspend until it's proved. `process`/`lowerInstantiate` then just looks it up.
    if (step.body == .claim) {
        const c = step.body.claim;
        if (c.rule.name == InternPool.RuleStr.instantiation.id()) {
            var e = self.elab(w);
            switch (try self.demandInstance(&e, null, c)) {
                .proven => return null, // ready — process can run lowerInstantiate
                .blocked => |t| return t,
                .failed => return null, // diagnosed; process will re-hit .failed and reject
            }
        }
        // a `[by model(M) src.thm]` step DEMANDS the transferred fact (its own ProveTask in
        // (M, src_file)); the model name resolved above, so demand the transfer + suspend.
        if (c.rule.name == InternPool.RuleStr.model.id()) {
            switch (try self.demandTransfer(c)) {
                // a transferred SCHEMA is cited as the discharging schema's instance at this
                // proof's own arguments — demand that instance too.
                .proven => |ix| if (self.ctx.interner.keyOf(ix) == .schema) switch (try self.demandSchemaTransfer(c, ix)) {
                    .proven => return null,
                    .blocked => |t| return t,
                    .failed => return null,
                } else return null,
                .blocked => |t| return t,
                .failed => return null,
            }
        }
        // an ACCELERANT step (`using <accel> …`) DEMANDS its generated synthetic-schema
        // instance; the shared `demandUsing` builds+registers the schema (idempotent) and
        // racks the instance ProveTask. RE-ENTRANT: first pass racks + suspends.
        if (c.kind == .using and isAccelerant(c.rule.name)) {
            // PHASE 1, the tactic's own hook: whatever its producer needs resolved beyond the
            // cited facts (well-known operator symbols, an induction schema, a selector's
            // vocabulary). Which tactic is the union's business, not a word test here.
            if (self.tacticOf(c)) |tactic| {
                const extra: Allocator.Error!?Engine.TaskIndex = switch (tactic) {
                    inline else => |a| a.read(self, w, c),
                };
                if (try extra) |blocker| return blocker;
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

/// `demandParse` the file of every QUALIFIED citation in a trusted step — the head, when the
/// tactic's schema slot holds one, and each ref. Returns a blocker to suspend on, as the rest of
/// the read pass does. Only the FILE is demanded: no fact's proof, so no cascade.
///
/// The namespace resolution is deliberately silent on failure. An unresolvable qualifier is a
/// real error, but the process pass diagnoses it with position and context; failing here would
/// report it from the read pass instead, and a read-pass diagnostic is not unwritten if the
/// process pass later succeeds.
fn demandQualifiedCiteFiles(self: *Prove, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    const tactic = self.tacticOf(c) orelse return null; // model/import: `trustSourceFile` below
    var toks: std.ArrayList(lexer.Token) = .empty;
    if (c.schema) |t| switch (tactic.schemaSlot()) {
        .head, .lemma => try toks.append(self.ctx.arena, t),
        .theory_selector, .none => {},
    };
    for (c.refs) |r| try toks.append(self.ctx.arena, r);
    for (toks.items) |tok| {
        if (tok.qualifier == InternPool.Index.none) continue;
        const state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tok.qualifier }) orelse continue;
        const ix = switch (state) {
            .done => |x| x,
            .in_flight => continue,
        };
        const nsix = switch (self.ctx.interner.keyOf(ix)) {
            .import => |m| m.namespace,
            else => continue,
        };
        const nsfile = switch (self.ctx.interner.keyOf(nsix)) {
            .namespace => |m| m.file,
            else => continue,
        };
        switch (try self.ctx.demandParse(self.h, nsfile)) {
            .parsed => {},
            .parsing => |t| return t,
            .unparsed => {}, // undiscovered — the process pass diagnoses
        }
    }
    return null;
}

/// Demand the STATEMENT of every fact an accelerated-tactic step cites — head, lemma args,
/// refs — so a trusted decision never parks reading one. Which slots hold citations is read off
/// the tactic's type. A local step is not a fact and is skipped; an unresolvable qualifier is
/// skipped too (the process pass diagnoses it with position and context).
fn demandCitedStatements(self: *Prove, w: *const Walk, tactic: Tactic, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    var toks: std.ArrayList(lexer.Token) = .empty;
    if (c.schema) |t| switch (tactic.schemaSlot()) {
        .head, .lemma => try toks.append(self.ctx.arena, t),
        .theory_selector, .none => {},
    };
    if (tactic.lemmaArgs()) for (c.args) |a| {
        if (a.* == .name) try toks.append(self.ctx.arena, a.name);
    };
    try toks.appendSlice(self.ctx.arena, c.refs);
    for (toks.items) |t| {
        if (w.findStep(tokName(t)) != null) continue; // a local step, not a fact
        // A name its file does not declare is a TYPO. Leave it to the process pass, which
        // diagnoses it with position and context (`seedAndCheckLocalRoot`) — elaborating it
        // here would add a second, worse-located diagnostic, and `--fast` must report exactly
        // what strict does.
        const file = self.citedFactFile(t) orelse continue;
        if (!self.citationDeclared(t)) continue;
        switch (try elaborateFactStatement(self.ctx, self.h, file, tokName(t), self.model, self.pool)) {
            .ready, .failed => {},
            .suspended => return self.h.blocked_on,
        }
    }
    return null;
}

/// The file a cited fact token names: its own file when unqualified, else the import's file.
/// Null when the qualifier does not (yet) resolve to an import — the process pass diagnoses.
pub fn citedFactFile(self: *Prove, t: lexer.Token) ?InternPool.Index {
    if (t.qualifier == InternPool.Index.none) return self.file;
    const st = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = t.qualifier }) orelse return null;
    const ix = switch (st) {
        .done => |x| x,
        .in_flight => return null,
    };
    if (self.ctx.interner.keyOf(ix) != .import) return null;
    return self.ctx.interner.keyOf(self.ctx.interner.keyOf(ix).import.namespace).namespace.file;
}

/// Does the file a cited fact token names DECLARE that name? A trusted decision reads a cited
/// statement only when so — a name nothing declares is a typo for the process pass to report.
pub fn citationDeclared(self: *Prove, t: lexer.Token) bool {
    const file = self.citedFactFile(t) orelse return false;
    const fid = self.ctx.fileOf(file) orelse return false;
    return self.ctx.declOf(fid, tokName(t)) != null;
}

/// The read pass for a TRUSTED `using` step: make the AST that `process` will SHAPE-CHECK
/// available WITHOUT demanding any fact's PROOF. It resolves only IDENT-domain refs (sorts,
/// funcs, preds, and the model/import NAME — cheap FetchTask/ModelTask, no proof cascade) and
/// `demandParse`s the source file(s) whose decl AST the α-match reads. It NEVER racks a
/// ProveTask, registers a synthetic schema, or touches FactKV. Returns a blocker to suspend on.
fn trustedReadPass(self: *Prove, w: *Walk, step: *const ast.Step) Allocator.Error!?Engine.TaskIndex {
    const c = step.body.claim;
    // resolve the IDENT-domain refs only (skip fact/schema — those are the proof demands we
    // are here to AVOID). Model/import NAMES are ident-domain, so they resolve here.
    var scanner = RefScan.init(self.ctx.arena, self.ctx.interner, self.source, w);
    scanner.schema_params = self.schema_params;
    scanner.ctx = self.ctx;
    scanner.file = self.file;
    const refs = try scanner.scanStep(step);
    const idents = try self.ctx.arena.alloc(RefScan.Ref, refs.len);
    var n: usize = 0;
    for (refs) |r| switch (r.domain) {
        .ident, .model => { // an import NAME scans as `.ident` (resolved via IdentKV)
            idents[n] = r;
            n += 1;
        },
        .fact, .schema => {}, // a PROOF demand — skipped under trust
    };
    if (try resolveRefs(self.ctx, self.h, self.file, self.ns, self.model, self.self_key, idents[0..n])) |blocker| return blocker;

    // An ACCELERANT admits from the local goal — its producer matches THIS proof's goal AST —
    // so it needs no source file for the α-match. But a citation inside it still has to RESOLVE,
    // and a QUALIFIED one names another file: `[using specialize peano.addZeroLeft]`. Parse that
    // file here so `seedAndCheckLocalRoot` can check the name in the process pass. Without it
    // `Context.fileOf` returns null there and a typo'd qualified head went unchecked — `--fast`
    // printed "fully verified" where strict reported "reference not found".
    if (try self.demandQualifiedCiteFiles(c)) |blocker| return blocker;

    // An accelerated tactic's DECISION may read the STATEMENTS of what the step cites — its
    // head, its lemma args, its refs — and reading a statement can park (the declaring file
    // must be parsed; a re-export's alias chain resolved). Demand them here, where parking is
    // free: `elaborateFactStatement` racks no ProveTask, so this is a parse plus an ident
    // fetch, never a proof cascade. WHICH tokens are citations is the tactic's own declaration
    // (`schema_slot`, `lemma_args`), not a word list. A `.failed` is left for the producer to
    // report. Then the tactic's own phase-1 hook, for whatever else its decision needs.
    if (self.tacticOf(c)) |tactic| {
        if (try self.demandCitedStatements(w, tactic, c)) |blocker| return blocker;
        const extra: Allocator.Error!?Engine.TaskIndex = switch (tactic) {
            inline else => |a| a.read(self, w, c),
        };
        if (try extra) |blocker| return blocker;
    }

    // parse the source file whose decl AST the α-match reads (model: src.thm's file; import:
    // I's file; instantiation: the schema's file).
    const src_file = self.trustSourceFile(c) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return null, // diagnosed; process re-hits + rejects
    };
    if (src_file) |sf| switch (try self.ctx.demandParse(self.h, sf)) {
        .parsed => {},
        .parsing => |t| return t,
        .unparsed => {}, // undiscovered — process's resolve diagnoses cleanly
    };
    // DRIVE THE WHOLE ADMISSION HERE. `process`'s α-match may not suspend (its `.suspended`
    // arm is a read-pass bug), and elaborating the cited statement can demand more than one
    // parse: a re-export ALIAS sends it to the ORIGIN's file, whose own formula then needs its
    // refs resolved. Running `elaborateFactStatement` now — into a throwaway pool, the result
    // discarded — settles every one of those demands while suspending is still legal. `process`
    // then re-runs it against the real pool and finds everything resolved.
    if (src_file) |sf| if (self.trustedCiteName(c)) |cited| {
        var scratch: term.Pool = .init(self.ctx.arena, self.ctx.arena);
        switch (try elaborateFactStatement(self.ctx, self.h, sf, cited, .universe, &scratch)) {
            .ready, .failed => {}, // `process` re-runs it and reports any failure there
            // elaborateFactStatement already called suspendOn; hand back that blocker.
            .suspended => return self.h.blocked_on,
        }
    };
    return null;
}

/// Seed `tok` as a use-all-facts root if it names a LOCAL STEP. A `ns.`-qualified token names a
/// global fact and is skipped without touching `localName` (which would diagnose it). Used by
/// the admit path: an admitted accelerant builds no certificate, so nothing else carries the
/// citation edges its refs would have had.
///
/// A name that resolves to nothing is SILENTLY skipped here, because `c.schema` — the other
/// caller — is overloaded: for `specialize` it is a lemma-or-step head, but for
/// `polynomial(peano)` / `arithmetic(integer)` it is a THEORY MODULE, which is neither a step
/// nor a fact. `seedAndCheckLocalRoot` is the validating form, for the `refs` list.
fn seedLocalRoot(self: *Prove, w: *const Walk, tok: lexer.Token) Error!void {
    if (tok.qualifier != InternPool.Index.none) return;
    const target = w.resolveStep(tokName(tok)) orelse return;
    if (target == .step) try self.known.reachable.append(self.ctx.arena, @intFromEnum(self.ordinal_step.items[@intFromEnum(target.step)]));
}

/// As `seedLocalRoot`, but also DIAGNOSES a ref that names nothing at all. An admitted
/// accelerant is not checked here, so a typo'd ref would otherwise pass `--fast` and fail only
/// under strict — the one direction the fast/strict invariant does not allow (`--fast` must
/// never accept what strict rejects, just as it must never reject what strict accepts).
/// Resolving to a local step or block is fine, and so is naming a global fact; naming neither
/// is a typo. For `c.refs` (always logical inputs) and for `specialize`'s head — the only
/// rule word whose `c.schema` must resolve (see `seedLocalRoot` on that slot's overloading).
fn seedAndCheckLocalRoot(self: *Prove, w: *const Walk, tok: lexer.Token) Error!void {
    // A `ns.`-QUALIFIED token names a global fact, never a local step, so it seeds no root —
    // but it must still RESOLVE. Returning here unconditionally is what let `--fast` admit a
    // typo'd qualified head: `[using specialize peano.noSuchLemma]` named nothing, nothing
    // checked it, and the step was admitted "fully verified" while strict reported
    // "reference not found". `--fast` and strict must agree in BOTH directions.
    if (tok.qualifier != InternPool.Index.none) {
        const ns = try self.resolveQualifier(tok); // diagnoses an unknown namespace
        switch (self.qualifiedFactStatus(ns, tokName(tok))) {
            .names_a_fact => {},
            // The target FILE is not loaded. `demandQualifiedCiteFiles` parses it in the read
            // pass, so reaching here means the qualifier did not resolve to an import at all —
            // which the process pass diagnoses with better position and context than a
            // "not found" from here would carry.
            .file_not_loaded => {},
            .no_such_fact => return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)}),
        }
        return;
    }
    const name = tokName(tok);
    const target = w.resolveStep(name) orelse {
        if (self.namesAFact(name)) return;
        return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
    };
    if (target == .step) try self.known.reachable.append(self.ctx.arena, @intFromEnum(self.ordinal_step.items[@intFromEnum(target.step)]));
}

/// Does `name` name a global fact — one already demanded (FactKV), or declared in this file's
/// AST and not yet demanded? Mirrors `resolveStepRef`'s two-sided test, but counts an ALIAS to
/// a fact too (`theorem addSuccLeft = peano.addSuccLeft`): `ast.factOf` returns null for an
/// alias, and a re-exported lemma is the ordinary way a file names another theory's fact, so
/// testing only for a local fact decl would reject every aliased rewrite lemma.
/// Whether a QUALIFIED citation (`peano.addSuccLeft`) names a fact in `ns` — with
/// `file_not_loaded` kept DISTINCT from `no_such_fact`, because they warrant opposite
/// responses. Existence only: under `--fast` the cited fact may not be proven yet, so this
/// must NOT demand `.proven` the way `resolveFactIn` does.
const QualifiedFactStatus = enum { names_a_fact, file_not_loaded, no_such_fact };
fn qualifiedFactStatus(self: *Prove, ns: InternPool.Index, name: StrId) QualifiedFactStatus {
    if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = name }) != null) return .names_a_fact;
    const nsfile = switch (self.ctx.interner.keyOf(ns)) {
        .namespace => |m| m.file,
        else => return .file_not_loaded,
    };
    // not parsed in this run — no information, so no verdict
    const fid = self.ctx.fileOf(nsfile) orelse return .file_not_loaded;
    const d = self.ctx.declOf(fid, name) orelse return .no_such_fact;
    return switch (d.*) {
        // `.fact` is the ALIAS form (`fact X = ns.y`), which is how a file names another
        // theory's lemma; omitting it rejected every aliased rewrite lemma under `--fast`
        // while strict accepted it.
        .axiom, .hole, .theorem, .fact => .names_a_fact,
        else => .no_such_fact,
    };
}

/// `qualifiedFactStatus` at this proof's own namespace, for an UNQUALIFIED name — where a
/// not-loaded file cannot arise (it is this file).
fn namesAFact(self: *Prove, name: StrId) bool {
    return self.qualifiedFactStatus(self.ns, name) == .names_a_fact;
}

/// The NAME of the fact a trusted engine-word citation reads, paired with `trustSourceFile`'s
/// file. `model` cites `src.thm` in `refs[0]`; `import` cites `thm` there too (the import name
/// itself is in `schema`). Null for an accelerant, which admits from the local goal.
fn trustedCiteName(self: *Prove, c: ast.Step.Claim) ?StrId {
    const word = self.trustWord(c) orelse return null;
    return switch (word) {
        .model, .import => if (c.refs.len == 1) tokName(c.refs[0]) else null,
        else => null,
    };
}

/// The source FILE whose decl AST a trusted engine-word citation is admitted against, or null
/// for an accelerant (which admits from the local goal alone). Resolves the model/import/
/// schema NAME (already ident-resolved in `trustedReadPass`) to its defining file.
fn trustSourceFile(self: *Prove, c: ast.Step.Claim) Error!?InternPool.Index {
    const word = self.trustWord(c) orelse return null;
    return switch (word) {
        // model: `src.thm` — qualified names the source file via its import; unqualified is
        // same-file (the citing file).
        .model => blk: {
            if (c.refs.len != 1) break :blk null;
            const rtok = c.refs[0];
            if (rtok.qualifier == InternPool.Index.none) break :blk self.file;
            break :blk try self.qualifierFile(rtok);
        },
        // import: `I.thm` lives in I's file.
        .import => blk: {
            const itok = c.schema orelse break :blk null;
            break :blk try self.importFile(itok);
        },
        else => null, // an accelerant — no remote decl to parse
    };
}

/// The file a qualified token `ns.name`'s `ns` import points at (its imported namespace's file).
fn qualifierFile(self: *Prove, tok: lexer.Token) Error!?InternPool.Index {
    const ns = try self.resolveQualifier(tok);
    return self.ctx.interner.keyOf(ns).namespace.file;
}

/// The file the import `I` (a local `.import` ident) points at.
fn importFile(self: *Prove, itok: lexer.Token) Error!?InternPool.Index {
    const st = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tokName(itok) }) orelse return null;
    const ix = switch (st) {
        .done => |x| x,
        .in_flight => return null,
    };
    return switch (self.ctx.interner.keyOf(ix)) {
        .import => |m| self.ctx.interner.keyOf(m.namespace).namespace.file,
        else => null,
    };
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
    self.current_block = kb;
    defer self.current_block = null;
    self.known.missed = false;
    self.known.misses.clearRetainingCapacity();
    switch (step.body) {
        .claim => |c| {
            var e = self.elab(w);
            const f = try e.requireProp(try e.elaborateExpr(c.formula), c.formula);
            const just = try self.lowerJustification(w, &e, kb, f.id, c);
            try self.settleMisses(&e, kb);
            // under a model transfer, also keep the claim in SOURCE space (an accelerant citing
            // this step as a premise builds in source space — see `source_formulas`).
            const f_source: ?TermId = if (self.sourceSpaceAccelerants() and !self.inGuardWrapper(kb)) blk: {
                var se = self.sourceElab(w);
                const src_f = self.sourceExpr(c.formula);
                break :blk (try se.requireProp(try se.elaborateExpr(src_f), src_f)).id;
            } else null;
            try self.appendMainStep(w, .{
                .formula = f.id,
                .just = just,
                .block = kb,
                .label = label,
                .loc = step.label.start,
            }, f_source);
            // a PROVED step TEACHES its formula (and every conjunct of it) to the rest of its
            // block (appended first, so a step never discharges its own obligation).
            try self.teachAll(&e, f.id, kb, @intCast(self.low_steps.items.len - 1));
        },
        .assume => |blk| {
            var e = self.elab(w);
            const f = try e.requireProp(try e.elaborateExpr(blk.formula), blk.formula);
            try self.settleMisses(&e, kb);
            try self.newBlock(w, label, kb, .{ .assume = f.id });
            // the hypothesis (and every conjunct of it) is KNOWN inside the block it opens.
            try self.teachAll(&e, f.id, self.lastBlock(), null);
        },
        .fix => |blk| {
            const b = try self.bindProofVar(w, .{ .name = blk.name, .sort = blk.sort });
            try self.newBlock(w, label, kb, .{ .fix = .{ .v = b.v, .guard = b.guard } });
            try self.teachBinder(b);
        },
        .unpack => |blk| {
            const source_ref = try self.resolveStepRef(w, blk.from);
            const b = try self.bindProofVar(w, .{ .name = blk.name, .sort = blk.sort });
            try self.newBlock(w, label, kb, .{ .unpack = .{ .v = b.v, .source = source_ref } });
            try self.teachBinder(b);
        },
        .case => |c| {
            var e = self.elab(w);
            const goal = try e.requireProp(try e.elaborateExpr(c.goal), c.goal);
            try self.settleMisses(&e, kb);
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
            // (possibly nested, for N>2) common_conclusion tree over the disjunction structure.
            // under a model transfer, also keep the goal in SOURCE space (see `source_formulas`).
            const goal_source: TermId = if (self.sourceSpaceAccelerants()) blk: {
                var se = self.sourceElab(w);
                const src_g = self.sourceExpr(c.goal);
                break :blk (try se.requireProp(try se.elaborateExpr(src_g), src_g)).id;
            } else goal.id;
            try self.case_stack.append(self.ctx.arena, .{ .goal = goal.id, .goal_source = goal_source, .disj = disj, .loc = step.label.start });
        },
    }
}

/// The `case` step's conclusion, after both arm blocks walked: emit the common_conclusion step.
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
    self.current_block = kb;
    defer self.current_block = null;
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
    }, cc.goal_source);
    try self.known.teach(self.ctx.arena, cc.goal, kb, @intCast(self.low_steps.items.len - 1));
}

/// SETTLE the step's failed obligation lookups. Under a MODEL TRANSFER the model's NOMINATED
/// dischargers may derive one — a base fact for a constant (`src.C: TGT(fact)`), a closure fact
/// instantiated for a compound (`src.op: F -| closure`), deterministically from the nomination
/// (`dischargeGoal` → `setupClosure`; no search) — and the derivation's step then TEACHES it.
/// Whatever remains is diagnosed here as `unproved obligation`, and the step is rejected.
fn settleMisses(self: *Prove, e: *Elab, kb: kernel.BlockId) Error!void {
    if (self.known.misses.items.len == 0) return;
    const misses = try self.ctx.arena.dupe(Elab.Known.Miss, self.known.misses.items);
    self.known.misses.clearRetainingCapacity();
    var unresolved = false;
    for (misses) |m| {
        // RE-LOOK-UP FIRST. A miss is recorded while a term is elaborated, but an
        // ACCELERANT's generated intermediate terms are elaborated during
        // `lowerJustification` — by which point `known` may already teach the guard from a
        // step in scope. The original code only ever SETTLED a miss under a model transfer
        // and otherwise went straight to the diagnostic, so a guard proved two steps above
        // was reported as unproved: the symptom written up in SIMPLIFY-ISSUES.md, where a
        // `simplify` owed `less_or_equal(j, i)` that an earlier step had proved.
        //
        // This is a pure RE-CHECK against the same visibility rule `requireKnown` uses
        // (`Known.lookup`'s ancestor-or-self test), so it discharges nothing that was not
        // already proved and visible — it just stops asking before the answer exists.
        if (self.known.lookup(m.prop, kb)) |t| {
            if (t.step) |st| self.known.reachable.append(self.ctx.arena, st) catch return error.OutOfMemory;
            continue;
        }
        if (self.model != InternPool.Index.none and self.model != .universe) {
            if (try self.dischargeGoal(kb, m.loc, m.prop)) |sref| {
                try self.known.teach(self.ctx.arena, m.prop, kb, @intFromEnum(sref.id));
                continue;
            }
        }
        self.ctx.sink.add(self.diagFile(), m.loc, "unproved obligation: '{s}'", .{try e.renderProp(m.prop)}) catch return error.OutOfMemory;
        unresolved = true;
    }
    if (unresolved) return error.Recover;
}

/// Teach `prop` and every member of its `and`-tree (and-elimination is structural: a
/// hypothesis `A and (B and C)` makes A, B and C known — the same standing as an antecedent
/// teaching its consequent). The teaching step/block is the same for each member; `refForKnown`
/// extracts a conjunct from a block hypothesis with `emitConjunctExtract`.
fn teachAll(self: *Prove, e: *Elab, prop: TermId, block: kernel.BlockId, step: ?u32) Error!void {
    var members: std.ArrayList(TermId) = .empty;
    try e.conjuncts(prop, &members);
    for (members.items) |m| try self.known.teach(self.ctx.arena, m, block, step);
}

/// The kernel block most recently created by `newBlock` (the block a fix/assume/unpack opened).
fn lastBlock(self: *const Prove) kernel.BlockId {
    return @enumFromInt(self.low_blocks.items.len - 1);
}

/// A refined binder TEACHES its guard inside the block it opens: each qualifier's atom (what a
/// guarded use of the variable requires) and the conjoined guard (what the kernel's guarded
/// generalize / a `requires` over the conjunction states).
fn teachBinder(self: *Prove, b: BoundVar) Error!void {
    const blk = self.lastBlock();
    for (b.quals) |q| try self.known.teach(self.ctx.arena, q, blk, null);
    if (b.guard) |g| if (b.quals.len != 1) try self.known.teach(self.ctx.arena, g, blk, null);
}

/// Build the (possibly nested) common_conclusion justification for a `case` over a LEFT-NESTED
/// disjunction. `disj_ref`/`disj_formula` are the disjunction step + its term; `arms` are
/// the walked arm assume-blocks, one per disjunct, in left-to-right disjunct order.
///   - 2 arms: one `common_conclusion{disj, arms[0], arms[1]}`.
///   - N>2: the disjunction is `LHS or arms[N-1]` where LHS is the (N-1)-way nested
///     disjunction; build a SYNTHETIC block that assumes LHS, re-derives it as a
///     hypothesis, recurses over `arms[0..N-1]` inside it, concludes the goal, and the
///     top common_conclusion uses that synthetic block as its left, `arms[N-1]` as its right.
/// (Ported from the eager Prover's emitCaseTree, retargeted to synthetic blocks.)
fn emitCaseTree(self: *Prove, parent: kernel.BlockId, loc: u32, disj_ref: kernel.SRef, disj_formula: TermId, arms: []const kernel.BRef, goal: TermId) Error!kernel.Justification {
    {
        const node = self.pool.get(disj_formula);
        if (node != .bin or node.bin.op != .or_op) {
            return self.fail(loc, "case: 'on' step is '{s}', not a disjunction", .{try self.renderTerm(disj_formula)});
        }
    }
    std.debug.assert(arms.len >= 2);
    // ITERATIVE (was linear recursion peeling one arm off the right per level, nesting a synthetic
    // block each time). DESCEND: at each level >2 create the block + emit its hypothesis, recording
    // the level; the disjunction's LHS (the first N-1 arms) is the next level. Stop at the 2-arm
    // base. UNWIND: build the innermost common_conclusion, then for each recorded level emit `goal` via the
    // inner justification, close the block, and wrap in the outer common_conclusion. Depth = arm count.
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    const Level = struct { block: kernel.BlockId, disj_ref: kernel.SRef, right_arm: kernel.BRef };
    var levels: std.ArrayList(Level) = .empty;

    var cur_disj_ref = disj_ref;
    var cur_disj_formula = disj_formula;
    var cur_arms = arms;
    while (cur_arms.len > 2) {
        const node = self.pool.get(cur_disj_formula); // an or-tree by construction
        const lhs = node.bin.lhs; // the (N-1)-way disjunction
        const lb = try self.newSyntheticBlock(try self.freshNamed("case"), parent, .{ .assume = lhs });
        const hyp = try self.emitSynthetic(lb, loc, lhs, .{ .hypothesis = .{ .id = lb, .loc = loc } });
        try levels.append(wa, .{ .block = lb, .disj_ref = cur_disj_ref, .right_arm = cur_arms[cur_arms.len - 1] });
        // descend into the block: the LHS disjunction over the first N-1 arms.
        cur_disj_ref = hyp;
        cur_disj_formula = lhs;
        cur_arms = cur_arms[0 .. cur_arms.len - 1];
    }
    // base: a 2-arm common_conclusion over the current (possibly innermost-block) disjunction.
    var just: kernel.Justification = .{ .common_conclusion = .{ .disj = cur_disj_ref, .left = cur_arms[0], .right = cur_arms[1] } };
    // unwind: innermost level last-recorded → pop; emit `goal` in its block via `just`, close, wrap.
    var i = levels.items.len;
    while (i > 0) {
        i -= 1;
        const lv = levels.items[i];
        _ = try self.emitSynthetic(lv.block, loc, goal, just);
        self.closeSyntheticBlock(lv.block);
        just = .{ .common_conclusion = .{ .disj = lv.disj_ref, .left = .{ .id = lv.block, .loc = loc }, .right = lv.right_arm } };
    }
    return just;
}

/// A block descoped: seal its kernel step range (same closing the eager path did).
/// Is `kb` one of the injected value-param guard-wrapper levels (see `guard_wrappers`)? The
/// wrappers are the outermost levels, so this is a block-depth test.
fn inGuardWrapper(self: *const Prove, kb: kernel.BlockId) bool {
    if (self.guard_wrappers == 0) return false;
    var depth: u32 = 0;
    var b = kb;
    while (self.low_blocks.items[@intFromEnum(b)].parent) |p| {
        depth += 1;
        b = p;
    }
    return depth < self.guard_wrappers;
}

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
/// `source_formula` = the step's formula in SOURCE space when it differs from the lowered one
/// (a model transfer); null = same as `step.formula`. Kept index-aligned in `source_formulas`.
fn appendMainStep(self: *Prove, w: *const Walk, step: kernel.Step, source_formula: ?TermId) Error!void {
    std.debug.assert(w.next_step == self.ordinal_step.items.len);
    const id: kernel.StepId = @enumFromInt(self.low_steps.items.len);
    try self.low_steps.append(self.ctx.arena, step);
    try self.source_formulas.append(self.ctx.arena, source_formula orelse step.formula);
    try self.ordinal_step.append(self.ctx.arena, id);
}

/// The formula of a cited local step AS AN ACCELERANT PRODUCER'S INPUT: source space. Under a
/// model transfer the lowered formula (`low_steps[..].formula`) is relativized to the target;
/// a producer must not mix that with its source-space goal, so it reads the source-space twin
/// recorded at lowering. Identical to the lowered formula in an ordinary proof.
pub fn producerPremiseFormula(self: *const Prove, sref: kernel.SRef) TermId {
    // While a producer runs in SOURCE mode, `self.model` is toggled to the universe
    // (demandUsing) → the source twin. Under a guarded model's legacy target-space production
    // the model stays set → the lowered (target) formula. Both coincide in an ordinary proof.
    if (self.model == .universe) return self.source_formulas.items[@intFromEnum(sref.id)];
    return self.low_steps.items[@intFromEnum(sref.id)].formula;
}

/// Append a SYNTHETIC kernel step (multi-arg apply_at intermediate) — no ordinal.
pub fn emitSynthetic(self: *Prove, kb: kernel.BlockId, loc: u32, formula: TermId, just: kernel.Justification) Error!kernel.SRef {
    const id: kernel.StepId = @enumFromInt(self.low_steps.items.len);
    try self.low_steps.append(self.ctx.arena, .{
        .formula = formula,
        .just = just,
        .block = kb,
        .label = try self.freshNamed("simplify"),
        .loc = loc,
    });
    // a synthetic intermediate is never an accelerant premise; keep `source_formulas` aligned.
    try self.source_formulas.append(self.ctx.arena, formula);
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
/// its id — for the nested common_conclusion spine of an N-arm `case`. `first_step` opens at the
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

const BoundVar = struct { v: term.Node.Fvar, guard: ?TermId, quals: []const TermId = &.{} };

/// A fix/unpack binder: resolve its (possibly refined/inline-`where`) sort, mint the
/// hygienic fvar at the CARRIER, and — for a refined sort — build its guard `inH(v)`
/// (conjoined over multiple qualifiers). The fvar (carrier sort) goes to the Walk via
/// pending_binder; the guard is returned for the block's `fix.guard` slot ([by predicate]
/// surfaces it; generalize makes it the antecedent).
fn bindProofVar(self: *Prove, w: *Walk, b: ast.Binder) Error!BoundVar {
    const name = try self.localName(b.name);
    if (w.findIdent(name) != null) {
        return self.fail(b.name.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(b.name)});
    }
    var e = self.elab(w);
    const refined = try e.resolveBinderSort(b); // handles inline `S where inH`
    const sort: SortId = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(refined)))));
    const quals = self.ctx.interner.qualifiersOf(self.ctx.arena, @enumFromInt(@intFromEnum(refined))) catch return error.OutOfMemory;
    // THE BINDER'S IDENTITY IS ITS SOURCE SITE, not a counter. `freshNamed` would spell this
    // `<name>#<fresh_counter>`, and that counter counts every fresh name minted EARLIER IN THIS
    // PROOF — so adding an unrelated step above a `fix` renamed its variable, which changed the
    // hash of any schema instance taking that variable as an argument (`Schema.instanceHash`
    // folds a non-lambda-param fvar's NAME BYTES). One written instantiation then minted two
    // instances and the prover proved it twice.
    //
    // `<name>#<loc>` is fixed by the source instead. It still disambiguates every binder — two
    // binders cannot share a start offset — so distinct binders stay distinct, which is load
    // bearing: an instance keyed on an eigenvar mentions THAT variable in its statement, so two
    // proofs binding different variables genuinely need two instances. See
    // drafts/schema-hash-decode/, where collapsing them by position broke std/subgroup.b4m.
    //
    // Same reasoning as `Schema.hashEntity`, which hashes `(name, loc)` for exactly this reason.
    //
    // A SYNTHETIC binder keeps the counter. An accelerant's generated `fix` (ArithCert.fixStep,
    // the Cooper/arith certs, the guard projection) reaches here with a token built by
    // `Accelerant.Builder.tok`, which stamps `start = end = loc` — ONE location for the whole
    // generated proof — so a loc-keyed name would collide every synthetic binder in one
    // producer's output. `start == end` is the established synthetic-token test (see Elab.text).
    // Synthetics need no source-stable identity anyway: they are regenerated deterministically
    // from the same goal, so the counter is already reproducible for them.
    const stem = self.ctx.interner.stringBytes(name);
    const fvar = if (b.name.start == b.name.end)
        try self.freshNamed(stem)
    else
        try self.freshNamedAt(stem, b.name.start);
    // under a model transfer `sort` is the model's IMAGE of the written sort; also record the
    // written (SOURCE) sort, so a source-space pass (accelerant producer inputs) sees this
    // binder in its own space. Identical outside a transfer.
    const source_sort: SortId = if (self.sourceSpaceAccelerants()) blk: {
        var se = self.sourceElab(w);
        const src_refined = try se.resolveBinderSort(b);
        break :blk @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(src_refined)))));
    } else sort;
    // record the REFINED sort too: `sort` is its carrier, and an accelerant that abstracts this
    // binder into a schema param needs the refinement to re-emit its guard (see `paramGuards`).
    const refined_ix: InternPool.Index = @enumFromInt(@intFromEnum(refined));
    w.pending_binder = .{
        .sort = sort,
        .source_sort = source_sort,
        .fvar = fvar,
        .refined = if (self.ctx.interner.isRefined(refined_ix)) refined_ix else InternPool.Index.none,
    };
    // build the guard over the fresh fvar (conjunction if multiple qualifiers), keeping each
    // qualifier's atom (what the binder TEACHES, see `teachBinder`).
    var guard: ?TermId = null;
    const atoms = try self.ctx.arena.alloc(TermId, quals.len);
    for (quals, atoms) |qual, *atom| {
        const fv = try self.pool.add(.{ .fvar = .{ .name = fvar, .sort = sort } });
        const app = try e.qualifierApp(qual, fv); // an opaque pred applies; a define'd guard term substitutes
        atom.* = app;
        guard = if (guard) |prev| try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = prev, .rhs = app } }) else app;
    }
    return .{ .v = .{ .name = fvar, .sort = sort }, .guard = guard, .quals = atoms };
}

/// Produce a PROVEN step whose formula is the guard `g` (`good(t)`), and return its SRef —
/// for auto-discharging a refined-sort `apply_at`'s leaked guard. Sources, in order:
///   (1) a prior in-scope step already asserting `g` → cite it directly (no new step);
///   (2) an enclosing fix-block whose guard is `g` → emit a `[by predicate]` (hypothesis);
///   (3) a MODEL-NOMINATED discharger (13e): the model named a fact establishing the guard of
///       `t`'s head symbol. BASE (`t` a const): the fact's formula IS `g` → cite it directly
///       (the kernel re-checks fact.formula == g, so the nomination is verified, not trusted).
///       COMPOSITE (`t = op(a…)`): the fact is a CLOSURE `∀…; (⋀ guard(argᵢ)) -> guard(op(…))`;
///       apply_at it at the args, RECURSIVELY discharge each guarded-arg premise, both
///       the results, modus_ponens. (Recursion re-enters `emitDischargeStep` per premise.)
/// Returns null if `g` isn't dischargeable any of these ways (the caller falls back to the
/// plain, guard-leaking elim). Emits ordinary kernel steps into `low_steps`; the final proof is
/// kernel-checked once at the end (no mid-synthesis kernel call).
fn emitDischargeStep(self: *Prove, kb: kernel.BlockId, loc: u32, g: TermId) Error!?kernel.SRef {
    return self.dischargeGoal(kb, loc, g);
}

/// If `g` is a CONJUNCT of the and-tree `whole` (a multi-qualifier block guard/assumption),
/// restate `whole` (`[by hypothesis]` on block `blk`) and and_elim down to `g`; else null.
pub fn emitConjunctExtract(self: *Prove, kb: kernel.BlockId, loc: u32, whole: TermId, g: TermId, blk: kernel.BlockId) Error!?kernel.SRef {
    var path: std.ArrayList(bool) = .empty;
    if (!try self.conjunctPath(whole, g, &path)) return null;
    if (path.items.len == 0) return null; // whole == g — the caller's direct case
    const base = try self.emitSynthetic(kb, loc, whole, .{ .hypothesis = .{ .id = blk, .loc = loc } });
    return try self.emitConjunctExtractFrom(kb, loc, whole, g, base);
}

/// and_elim down from an EXISTING step `base` proving the and-tree `whole` to its conjunct `g`
/// (`base` itself when `g` is `whole`); null if `g` is not a conjunct.
pub fn emitConjunctExtractFrom(self: *Prove, kb: kernel.BlockId, loc: u32, whole: TermId, g: TermId, base: kernel.SRef) Error!?kernel.SRef {
    var path: std.ArrayList(bool) = .empty;
    if (!try self.conjunctPath(whole, g, &path)) return null;
    var step = base;
    var cur_t = whole;
    for (path.items) |left| {
        const n = self.pool.get(cur_t);
        cur_t = if (left) n.bin.lhs else n.bin.rhs;
        step = try self.emitSynthetic(kb, loc, cur_t, if (left) .{ .and_lhs = step } else .{ .and_rhs = step });
    }
    return step;
}

/// The left/right path from and-tree `tree` down to the LEFTMOST conjunct α-equal to `g` (true =
/// left turn), appended to `path`; returns whether found. Iterative DFS (was native recursion) —
/// depth-safe over a deep conjunction. Each frame carries `(node, path-to-it)`; children pushed
/// RIGHT-then-LEFT so the LEFT subtree is explored first (matches the recursion's leftmost find).
/// The path snapshots live in a GPA-backed arena, freed on return; the found path is copied into
/// `path` (on the caller's arena).
pub fn conjunctPath(self: *Prove, tree: TermId, g: TermId, path: *std.ArrayList(bool)) Error!bool {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();
    const Frame = struct { node: TermId, prefix: []const bool };
    var stack: std.ArrayList(Frame) = .empty;
    try stack.append(a, .{ .node = tree, .prefix = &.{} });
    while (stack.pop()) |f| {
        if (self.pool.alphaEq(f.node, g)) {
            try path.appendSlice(self.ctx.arena, f.prefix);
            return true;
        }
        const n = self.pool.get(f.node);
        if (n != .bin or n.bin.op != .and_op) continue; // dead end
        // push RIGHT first so LEFT pops first (leftmost-match order).
        const right = try std.mem.concat(a, bool, &.{ f.prefix, &.{false} });
        const left = try std.mem.concat(a, bool, &.{ f.prefix, &.{true} });
        try stack.append(a, .{ .node = n.bin.rhs, .prefix = right });
        try stack.append(a, .{ .node = n.bin.lhs, .prefix = left });
    }
    return false;
}

/// AUTO-WEAKENING: prove a RELATIVIZED `goal = ∀v1; g11(v1) -> g12(v1) -> ∀v2; g21(v2) -> …
/// -> Core` from a cited fact whose formula `fact_f = ∀v1; ∀v2; … -> Core` holds
/// UNCONDITIONALLY (mapped to itself under a guarded model). Since `∀v;P ⊢ ∀v; guard(v)->P`,
/// synthesize: per binder an UNGUARDED `fix` with one nested `assume` PER GUARD (a
/// multi-qualifier sort injects several, in claim order); innermost cite the fact +
/// multi-arg apply_at to Core; unwind with discharge per assume + generalize per
/// fix — deriving exactly the claim's guard CHAIN. Returns the OUTERMOST generalize
/// justification, or null if `goal` isn't a guarded relativization of `fact_f`.
fn emitWeakening(self: *Prove, kb: kernel.BlockId, loc: u32, stmt: InternPool.Index, fact_f: TermId, goal: TermId) Error!?kernel.Justification {
    // Walk goal + fact in PARALLEL, classifying each leading `->` on the goal by DIFF against the
    // source: an injected relativization GUARD appears on the goal but NOT at the corresponding
    // position of the source (source has a `∀` or the core there) → strip it, associating it with
    // the MOST RECENTLY peeled binder (guards are injected right after their binder opens; a
    // multi-qualifier sort injects several). A GENUINE antecedent appears in BOTH (matching) →
    // part of the Core, left in place. Stop at a non-`∀`/`->` head or a genuine antecedent.
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var guards_per: std.ArrayList(std.ArrayList(TermId)) = .empty;
    // Source antecedents the goal's guard chain SUBSUMES (see the `.implies` arm): each is
    // discharged at the innermost step by projecting `antecedent` out of `guard`.
    const Subsumed = struct { guard: TermId, antecedent: TermId };
    var subsumed: std.ArrayList(Subsumed) = .empty;
    var g = goal;
    var f = fact_f;
    while (true) {
        const gn = self.pool.get(g);
        if (gn == .quant and gn.quant.q == .forall) {
            const fn_ = self.pool.get(f);
            if (fn_ != .quant or fn_.quant.q != .forall) return null; // fact has fewer binders
            const fv = try self.freshNamed("w");
            const sort: SortId = @enumFromInt(@intFromEnum(gn.quant.sort));
            const fvar: term.Node.Fvar = .{ .name = fv, .sort = sort };
            const fvt = try self.pool.add(.{ .fvar = fvar });
            try eigen.append(self.ctx.arena, fvar);
            try guards_per.append(self.ctx.arena, .empty);
            g = try self.pool.open(gn.quant.body, fvt);
            f = try self.pool.open(fn_.quant.body, fvt);
            continue;
        }
        if (gn == .bin and gn.bin.op == .implies) {
            const fn_ = self.pool.get(f);
            // GENUINE antecedent: the source ALSO has a leading `->` with the SAME antecedent →
            // it's part of the Core, not a guard. Stop peeling (the rest, incl. this `->`, is Core).
            if (fn_ == .bin and fn_.bin.op == .implies and self.pool.alphaEq(gn.bin.lhs, fn_.bin.lhs)) break;
            // SUBSUMED antecedent: the source's leading `->` antecedent is a CONJUNCT of the
            // goal's injected guard. This is the multi-qualifier case — the ambient sort refines
            // a base whose own guard is what the source states as a premise (`Perm = Fn where
            // invertible` under `SymPerm = Perm where hasFiniteSupport`, against a source axiom
            // reading `invertible(f) -> …`). The guard chain already carries the premise, so
            // consume BOTH: strip the goal's conjunction as a guard and the source's antecedent
            // as discharged by it. `subsumed` records which guard discharges which antecedent so
            // the innermost step can project it back out.
            if (fn_ == .bin and fn_.bin.op == .implies and eigen.items.len > 0) {
                var probe: std.ArrayList(bool) = .empty;
                if (try self.conjunctPath(gn.bin.lhs, fn_.bin.lhs, &probe) and probe.items.len > 0) {
                    try guards_per.items[guards_per.items.len - 1].append(self.ctx.arena, gn.bin.lhs);
                    try subsumed.append(self.ctx.arena, .{ .guard = gn.bin.lhs, .antecedent = fn_.bin.lhs });
                    g = gn.bin.rhs;
                    f = fn_.bin.rhs;
                    continue;
                }
            }
            // else INJECTED guard (absent from the source here) → strip, associate with the binder.
            if (eigen.items.len == 0) return null; // a guard before any binder — not relativization
            try guards_per.items[guards_per.items.len - 1].append(self.ctx.arena, gn.bin.lhs);
            g = gn.bin.rhs;
            continue;
        }
        break;
    }
    if (eigen.items.len == 0) return null; // nothing to weaken
    if (!self.pool.alphaEq(g, f)) return null; // cores differ — not a plain weakening

    // Build the block spine outer→inner: per binder an UNGUARDED fix, then one assume per
    // guard (claim order = nesting order).
    const nblocks = eigen.items.len;
    const fix_blk = try self.ctx.arena.alloc(kernel.BlockId, nblocks);
    const asm_blk = try self.ctx.arena.alloc([]kernel.BlockId, nblocks);
    var parent = kb;
    for (eigen.items, 0..) |ev, i| {
        fix_blk[i] = try self.newSyntheticBlock(try self.freshNamed("weaken"), parent, .{ .fix = .{ .v = ev, .guard = null } });
        parent = fix_blk[i];
        const gs = guards_per.items[i].items;
        const abs_ = try self.ctx.arena.alloc(kernel.BlockId, gs.len);
        for (gs, abs_) |gg, *ab| {
            ab.* = try self.newSyntheticBlock(try self.freshNamed("weaken-assume"), parent, .{ .assume = gg });
            parent = ab.*;
        }
        asm_blk[i] = abs_;
    }
    // innermost: cite the fact, then multi-arg apply_at at all eigenvars → Core.
    const inner = parent;
    var cur = try self.emitSynthetic(inner, loc, fact_f, .{ .cite_ref = .{ .stmt = stmt, .loc = loc } });
    var cur_f = fact_f;
    for (eigen.items) |ev| {
        const fvt = try self.pool.add(.{ .fvar = ev });
        const opened = try self.pool.open(self.pool.get(cur_f).quant.body, fvt);
        cur = try self.emitSynthetic(inner, loc, opened, .{ .apply_at = .{ .step = cur, .with = fvt, .with_loc = loc } });
        cur_f = opened;
    }
    // Discharge each SUBSUMED antecedent: the guard chain carries it as a conjunct, so project
    // it out (and_elim down the enclosing `assume`'s conjunction) and modus_ponens. In claim
    // order, which is the order the walk stripped them.
    for (subsumed.items) |sb| {
        const node = self.pool.get(cur_f);
        if (node != .bin or node.bin.op != .implies) break;
        // find the `assume` block whose hypothesis IS `sb.guard`, and project the antecedent
        // out of it. The blocks were built above, so look them up by formula rather than
        // through `known` (which is not populated for synthetic blocks).
        var src: ?kernel.SRef = null;
        outer: for (asm_blk, 0..) |abs_, bi| {
            for (abs_, 0..) |ab, gi| {
                if (self.pool.alphaEq(guards_per.items[bi].items[gi], sb.guard)) {
                    const whole = try self.emitSynthetic(inner, loc, sb.guard, .{ .hypothesis = .{ .id = ab, .loc = loc } });
                    src = try self.emitConjunctExtractFrom(inner, loc, sb.guard, sb.antecedent, whole);
                    break :outer;
                }
            }
        }
        const ant = src orelse break;
        cur = try self.emitSynthetic(inner, loc, node.bin.rhs, .{ .modus_ponens = .{ .implication = cur, .antecedent = ant } });
        cur_f = node.bin.rhs;
    }
    // unwind inner→outer: discharge per assume (rebuilding the guard chain), generalize
    // per fix. Every export but the OUTERMOST is an emitted synthetic in its enclosing block;
    // the outermost is returned as the claim's justification.
    var conc = g; // Core (== fact core)
    var just: kernel.Justification = undefined;
    var i: usize = nblocks;
    while (i > 0) {
        i -= 1;
        const gs = guards_per.items[i].items;
        var j: usize = gs.len;
        while (j > 0) {
            j -= 1;
            self.closeSyntheticBlock(asm_blk[i][j]);
            just = .{ .discharge = .{ .id = asm_blk[i][j], .loc = loc } };
            conc = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = gs[j], .rhs = conc } });
            const encl = if (j > 0) asm_blk[i][j - 1] else fix_blk[i];
            _ = try self.emitSynthetic(encl, loc, conc, just);
        }
        self.closeSyntheticBlock(fix_blk[i]);
        just = .{ .generalize = .{ .id = fix_blk[i], .loc = loc } };
        const ev = eigen.items[i];
        const closed = try self.pool.close(conc, ev.name);
        conc = try self.pool.add(.{ .quant = .{ .q = .forall, .sort = ev.sort, .hint = ev.name, .body = closed } });
        if (i > 0) {
            const encl = if (asm_blk[i - 1].len > 0) asm_blk[i - 1][asm_blk[i - 1].len - 1] else fix_blk[i - 1];
            _ = try self.emitSynthetic(encl, loc, conc, just);
        }
    }
    _ = &cur;
    return just;
}

/// ITERATIVE guard-discharge driver — replaces the former mutual recursion
/// emitDischargeStep↔emitModelDischarge↔emitClosureDischarge↔emitConjDischarge (Zig will disallow
/// recursion; the depth was composite-witness op-nesting). Produce a PROVEN step whose formula is
/// `g0`, returning its SRef, or null if `g0` isn't dischargeable.
///
/// The recursion is a tree over the WITNESS structure: discharging `g = guard(op(a,b))` via a
/// closure needs the SRefs of discharging `guard(a)` / `guard(b)` first, then emits its own
/// elim/both/modus_ponens. Modeled as a worklist of `Op` frames + a `results` SRef stack,
/// two-color (a compound op is pushed, its sub-goals solved, then it COMBINES from their results).
///
/// `Op` variants:
///   - `.solve` a single guard goal: dischargeLocal → SRef; else a model CLOSURE applies → cite +
///     apply_at NOW (no children), then push `.mp_chain` + a `.conj` per `->` premise; else a
///     top-level conjunction → push `.conj`; else FAIL.
///   - `.conj` discharge a conjunction TREE: `and` → push `.and_fold` + `.conj`(lhs)+`.conj`(rhs);
///     leaf → `.solve` it.
///   - `.and_fold` / `.mp_chain` COMBINE: pop child SRefs, emit both / the modus_ponens chain.
/// A failed sub-goal sets `failed` (like the recursion's `orelse return null`), abandoning the
/// driver (any steps already emitted are orphaned — exactly as the recursion left them).
fn dischargeGoal(self: *Prove, kb: kernel.BlockId, loc: u32, g0: TermId) Error!?kernel.SRef {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();

    const Op = union(enum) {
        solve: TermId, // discharge a single guard goal g
        conj: TermId, // discharge a conjunction tree f (fold of leaf solves)
        and_fold: TermId, // pop 2 child SRefs → both(f) → push
        mp_chain: struct { cur: kernel.SRef, cur_formula: TermId, g: TermId, nprem: usize }, // pop nprem premise SRefs → cite-elim'd `cur` mp'd down to g
    };
    var work: std.ArrayList(Op) = .empty;
    var results: std.ArrayList(kernel.SRef) = .empty;
    var failed = false;
    try work.append(a, .{ .solve = g0 });

    while (work.pop()) |op| {
        if (failed) break;
        switch (op) {
            .solve => |g| {
                // what the proof KNOWS, by identity — the only local source.
                if (try self.refForKnown(kb, loc, g)) |sref| {
                    try results.append(a, sref);
                    continue;
                }
                // model closure? — g = pred(t), t = op(args); cite+elim, then the `->` premises.
                if (self.model != InternPool.Index.none and self.model != .universe) {
                    switch (try self.setupClosure(kb, loc, g, a, &work)) {
                        .base => |sref| {
                            try results.append(a, sref);
                            continue;
                        },
                        .setup => continue, // closure frames pushed
                        .none => {},
                    }
                }
                // top-level conjunction (source 4).
                const n = self.pool.get(g);
                if (n == .bin and n.bin.op == .and_op) {
                    try work.append(a, .{ .conj = g });
                    continue;
                }
                failed = true; // undischargeable
            },
            .conj => |f| {
                const n = self.pool.get(f);
                if (n == .bin and n.bin.op == .and_op) {
                    // push FOLD then children (right, left) → left folds first (results order).
                    try work.append(a, .{ .and_fold = f });
                    try work.append(a, .{ .conj = n.bin.rhs });
                    try work.append(a, .{ .conj = n.bin.lhs });
                } else {
                    try work.append(a, .{ .solve = f }); // a leaf guard
                }
            },
            .and_fold => |f| {
                const r = results.pop().?;
                const l = results.pop().?;
                try results.append(a, try self.emitSynthetic(kb, loc, f, .{ .both = .{ .left = l, .right = r } }));
            },
            .mp_chain => |mc| {
                // the nprem premise SRefs are the top of `results`, in premise order (premise 0
                // pushed first = deeper). modus_ponens the cited-elim'd `cur` down the `->` chain.
                const prems = results.items[results.items.len - mc.nprem ..];
                var cur = mc.cur;
                var cur_formula = mc.cur_formula;
                for (prems) |p_step| {
                    const node = self.pool.get(cur_formula);
                    // cur_formula is `Pi -> rest`; mp off Pi.
                    cur = try self.emitSynthetic(kb, loc, node.bin.rhs, .{ .modus_ponens = .{ .implication = cur, .antecedent = p_step } });
                    cur_formula = node.bin.rhs;
                }
                results.items.len -= mc.nprem;
                std.debug.assert(self.pool.alphaEq(cur_formula, mc.g)); // reached the conclusion == g
                try results.append(a, cur);
            },
        }
    }
    if (failed or results.items.len == 0) return null;
    return results.items[0];
}

/// Try to SET UP a model-closure discharge of `g = pred(t)` (t = op(args)) onto `work`: find the
/// first nominated fact that either IS `g` (base — cite, push its SRef, done) or applies as a
/// CLOSURE (cite + apply_at the args NOW — those steps need no children — then push an
/// `.mp_chain` combiner + a `.conj` sub-goal per `->` premise). Returns true if a discharge was set
/// up (base pushed a result, or closure pushed frames), false if no fact applied (caller continues).
fn setupClosure(self: *Prove, kb: kernel.BlockId, loc: u32, g: TermId, a: std.mem.Allocator, work: anytype) Error!union(enum) { base: kernel.SRef, setup, none } {
    const gnode = self.pool.get(g);
    if (gnode != .pred) return .none;
    const gargs = self.pool.args(gnode.pred);
    if (gargs.len != 1) return .none;
    const t = gargs[0];
    const tnode = self.pool.get(t);
    const head: InternPool.Index = switch (tnode) {
        .app => |ap| @enumFromInt(@intFromEnum(ap.sym)),
        else => return .none,
    };
    var facts: std.ArrayList(InternPool.Index) = .empty;
    try self.ctx.interner.modelDischargers(self.model, head, &facts, self.ctx.arena);
    for (facts.items) |fact| {
        const formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
        const cite_just: kernel.Justification = .{ .cite_ref = .{ .stmt = fact, .loc = loc } };
        // BASE: the fact IS the guard → cite; the kernel re-checks formula == g. The driver pushes
        // the returned SRef onto its results stack.
        if (self.pool.alphaEq(formula, g)) {
            return .{ .base = try self.emitSynthetic(kb, loc, g, cite_just) };
        }
        // CLOSURE: cite + apply_at at the args (no children); then push mp_chain + premises.
        if (tnode != .app) continue;
        const args = self.pool.args(tnode.app);
        var cur = try self.emitSynthetic(kb, loc, formula, cite_just);
        var cur_formula = formula;
        var ok = true;
        for (args) |arg| {
            const node = self.pool.get(cur_formula);
            if (node != .quant or node.quant.q != .forall) {
                ok = false;
                break;
            }
            const opened = try self.pool.open(node.quant.body, arg);
            cur = try self.emitSynthetic(kb, loc, opened, .{ .apply_at = .{ .step = cur, .with = arg, .with_loc = loc } });
            cur_formula = opened;
        }
        if (!ok) continue;
        // count the `->` premise chain down to g; collect the premises (each a conjunction tree).
        var premises: std.ArrayList(TermId) = .empty;
        var f = cur_formula;
        while (!self.pool.alphaEq(f, g)) {
            const node = self.pool.get(f);
            if (node != .bin or node.bin.op != .implies) {
                ok = false;
                break;
            }
            try premises.append(a, node.bin.lhs);
            f = node.bin.rhs;
        }
        if (!ok) continue;
        // push the mp-chain combiner, then a `.conj` per premise (premise 0 pushed FIRST = its
        // result deepest, matching `.mp_chain`'s premise-order read).
        try work.append(a, .{ .mp_chain = .{ .cur = cur, .cur_formula = cur_formula, .g = g, .nprem = premises.items.len } });
        var i = premises.items.len;
        while (i > 0) {
            i -= 1;
            try work.append(a, .{ .conj = premises.items[i] });
        }
        return .setup;
    }
    return .none;
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
pub fn resolveStepRef(self: *Prove, w: *const Walk, tok: lexer.Token) Error!kernel.SRef {
    const name = try self.localName(tok);
    const target = w.resolveStep(name) orelse {
        // nicety: a global fact cited where a step label belongs — name the fix. Check both the
        // FactKV (already-demanded) and the file's AST (a same-file fact decl that nothing
        // demanded, e.g. the cited axiom in `apply_at(t) myAxiom`), so it fires regardless.
        const is_fact = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = self.ns, .name = name }) != null or
            (tok.qualifier == InternPool.Index.none and if (self.ctx.fileOf(self.file)) |fid|
                if (self.ctx.declOf(fid, name)) |d| ast.factOf(d) != null else false
            else
                false);
        if (is_fact) {
            return self.fail(tok.start, "'{s}' is a fact, not a proof step; introduce it as a step first with `[by cite {s}]`, then reference that step", .{
                self.text(tok), self.text(tok),
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

/// `--trace-facts`: report what a citation RESOLVED TO. Two theorems in different theories
/// can share a name, and a model transfer publishes a second copy of its source's facts under
/// the same names in a `(model, file)` namespace — so which copy a step actually got is not
/// answerable from the source. `why` says which resolution path produced it. Stderr; the
/// verdict is unaffected.
fn traceFact(self: *Prove, tok: lexer.Token, ix: InternPool.Index, why: []const u8) void {
    if (!self.ctx.verify.trace_facts) return;
    const a = self.ctx.arena;
    var line: []const u8 = std.fmt.allocPrint(a, "{s}: cite {s}\n    -> {s}\n", .{
        self.siteOf(self.file, tok.start),
        self.text(tok),
        self.describeNamespaceOf(ix),
    }) catch return;
    if (self.ctx.interner.keyOf(ix) == .fact) {
        const f = self.ctx.interner.keyOf(ix).fact;
        line = std.fmt.allocPrint(a, "{s}       {s} {s}\n", .{ line, @tagName(f.kind), self.ctx.interner.stringBytes(f.name) }) catch return;
        if (self.pool.copyIn(self.ctx.interner, f.formula)) |t| {
            if (self.renderTerm(t)) |stmt| {
                line = std.fmt.allocPrint(a, "{s}       {s}\n", .{ line, stmt }) catch return;
            } else |_| {}
        } else |_| {}
    }
    line = std.fmt.allocPrint(a, "{s}       via {s}\n", .{ line, why }) catch return;
    self.ctx.traceLine(line);
}

/// `file:line:col` for a source offset. The offset must belong to `file` — a fact's `loc`
/// indexes the file it was DECLARED in, which is generally not the citing file, so an offset
/// past the end means we were handed the wrong file and the site is reported as unknown
/// rather than read out of bounds.
fn siteOf(self: *Prove, file: InternPool.Index, off: u32) []const u8 {
    const fid = self.ctx.fileOf(file) orelse return "?";
    const f = self.ctx.files.get(@intFromEnum(fid));
    if (off >= f.source.len) return std.fmt.allocPrint(self.ctx.arena, "offset {d} (not in {s})", .{ off, f.path }) catch "?";
    const lc = std.zig.findLineColumn(f.source, off);
    return std.fmt.allocPrint(self.ctx.arena, "{s}:{d}:{d}", .{ f.path, lc.line + 1, lc.column + 1 }) catch "?";
}

/// Which FILE a published fact was declared in — searched by scanning the file table for the
/// one whose namespace holds it. A fact Index records its `loc` but not its file, so the trace
/// recovers it here (a linear scan is fine for a diagnostic).
fn fileOfFact(self: *Prove, ix: InternPool.Index) ?InternPool.Index {
    const key = self.ctx.interner.keyOf(ix);
    const name: StrId = switch (key) {
        .fact => |f| f.name,
        .schema => |k| return k.file,
        else => return null,
    };
    var files_it = self.ctx.files.iterator();
    while (files_it.next()) |f| {
        const pf = self.ctx.fileIndex(f.path) catch continue;
        const ns = self.ctx.interner.namespace(.universe, pf) catch continue;
        if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = name })) |st| {
            if (st == .proven and st.proven == ix) return pf;
        }
    }
    return null;
}

/// Describe where a resolved fact CAME FROM: the namespace the citing task is resolving in
/// (`universe` for an ordinary proof, or the model it is proving under) plus the fact's own
/// declaration site. The distinction is the point of the trace — a citation that should have
/// stayed in the universe but came back through a model is the bug this exists to show.
fn describeNamespaceOf(self: *Prove, ix: InternPool.Index) []const u8 {
    const key = self.ctx.interner.keyOf(ix);
    const loc: u32 = switch (key) {
        .fact => |f| f.loc,
        .schema => |k| k.loc,
        else => return "(not a fact)",
    };
    const ns_text = if (self.model == InternPool.Index.none or self.model == .universe)
        "universe"
    else
        std.fmt.allocPrint(self.ctx.arena, "model#{d}", .{@intFromEnum(self.model)}) catch "model?";
    const decl_file = self.fileOfFact(ix) orelse self.file;
    return std.fmt.allocPrint(self.ctx.arena, "resolved in ns={s}, declared at {s}", .{ ns_text, self.siteOf(decl_file, loc) }) catch "?";
}

/// An axiom/theorem citation: GLOBAL fact via FactKV (the read pass made it proven, or
/// left an in_flight-self / failed entry — diagnosed here).
pub fn resolveFactRef(self: *Prove, tok: lexer.Token) Error!InternPool.Index {
    const ns = try self.resolveQualifier(tok);
    return self.resolveFactIn(tok, ns);
}

/// `resolveFactRef` with the namespace already chosen: the fact `tok` names in `ns`, with the
/// TRANSFER redirect (a source theorem → its copy re-proved under this proof's model) and the
/// axiom overlay applied. Shared by the bare/qualified `cite` and the `[using import(I) thm]`
/// citation, whose namespace is the import's — an import cite inside a transferred proof used to
/// skip the redirect and hand the kernel the UNTRANSFERRED source statement.
fn resolveFactIn(self: *Prove, tok: lexer.Token, ns: InternPool.Index) Error!InternPool.Index {
    const state = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = tokName(tok) }) orelse {
        return self.fail(tok.start, "unknown statement '{s}'", .{self.text(tok)});
    };
    const src = switch (state) {
        .proven => |x| x,
        .in_flight => return self.fail(tok.start, "cites '{s}', whose proof has not completed (self-citation or a failed/cyclic dependency)", .{self.text(tok)}),
    };
    // In a TRANSFER, a cited SOURCE THEOREM resolves to its TRANSFERRED version (re-proved under
    // the model), keyed `(model, ns.file).name` — the read pass demanded it. ONLY a theorem: an
    // AXIOM stays on the `applyModel` overlay path (mapped → local discharging fact), never a free
    // transferred leaf (see the read-pass note).
    if (self.model != InternPool.Index.none and self.model != .universe and
        self.ctx.interner.keyOf(src) == .fact and self.ctx.interner.keyOf(src).fact.kind == .theorem)
    {
        const nsfile = self.ctx.interner.keyOf(ns).namespace.file;
        const tns = try self.ctx.interner.namespace(self.model, nsfile);
        if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = tns, .name = tokName(tok) })) |st| switch (st) {
            .proven => |x| if (self.ctx.interner.keyOf(x) != .schema) {
                self.inheritHoles(x);
                self.inheritAxioms(x);
                self.traceFact(tok, x, "TRANSFER redirect: the citing task runs under a model, so the cited theorem resolved to its transferred copy");
                return x;
            },
            // the transferred copy is being proved RIGHT NOW by another task (or by this one):
            // falling through hands the citation the UNTRANSFERRED source copy, whose statement
            // is in the source sort — the mismatch `--trace-facts` exists to expose.
            .in_flight => |owner| self.traceFact(tok, src, if (owner == self.h.self_index)
                "TRANSFER redirect FELL THROUGH: the transferred copy is in_flight owned by THIS task (self-cycle) — using the untransferred source copy"
            else
                "TRANSFER redirect FELL THROUGH: the transferred copy is in_flight owned by ANOTHER task — using the untransferred source copy"),
        } else {
            self.traceFact(tok, src, "TRANSFER redirect FELL THROUGH: no transferred copy was ever demanded for this citation — using the untransferred source copy");
        }
    }
    const ix = switch (state) {
        // in a model transfer, a source-axiom citation remaps (via the overlay) to its
        // discharging LOCAL fact — an obligation. `.universe` = identity (ordinary proof).
        .proven => |x| self.ctx.interner.applyModel(self.model, x),
        .in_flight => unreachable, // handled above
    };
    // a SCHEMA lives in the fact table too (a fact-with-params), but it is NOT a citable ground
    // fact — it has no closed formula. It must be MONOMORPHIZED via `[using instantiation …]`.
    // Reject here so every fact-formula reader below can assume a real `.fact` Index.
    if (self.ctx.interner.keyOf(ix) == .schema)
        return self.fail(tok.start, "'{s}' is a schema; use `[using instantiation {s}(...)]`, not a fact citation", .{ self.text(tok), self.text(tok) });
    self.inheritHoles(ix);
    self.inheritAxioms(ix);
    self.traceFact(tok, ix, if (self.model == InternPool.Index.none or self.model == .universe) "direct lookup" else "overlay (applyModel) under the citing task's model");
    return ix;
}

/// HOLE TAINT inheritance (summary blast-radius only): if the cited fact `ix` rests on holes,
/// add each hole name to THIS proof's `holes_used` (deduped). Citing a hole — or a fact that
/// rests on one — makes the current proof rest on it. NEVER affects the proof verdict; a hole is
/// an axiom everywhere the KERNEL is concerned. See [[hole-mechanism]].
fn inheritHoles(self: *Prove, ix: InternPool.Index) void {
    const names = self.ctx.holeTaintOf(ix) orelse return;
    outer: for (names) |h| {
        for (self.holes_used.items) |seen| if (seen == h) continue :outer; // already tracked
        self.holes_used.append(self.ctx.arena, h) catch return; // OOM: best-effort taint
    }
}

/// AXIOM DEPENDENCY inheritance (the `--axioms` report): the cited fact's own axiom set becomes
/// part of this proof's. An AXIOM is its own seed — a theorem is not (it carries whatever its
/// proof rested on). Deduped; never affects the proof verdict.
fn inheritAxioms(self: *Prove, ix: InternPool.Index) void {
    if (self.ctx.axiomTaintOf(ix)) |axs| {
        outer: for (axs) |a| {
            for (self.axioms_used.items) |seen| if (seen == a) continue :outer;
            self.axioms_used.append(self.ctx.arena, a) catch return; // OOM: best-effort
        }
    }
}

/// The namespace a (possibly `ns.`-qualified) stamped token resolves in: unqualified =
/// this proof's ns; qualified = the import named by `tok.qualifier`. (Multi-level
/// qualification was diagnosed at parse — the stamped qualifier is at most one level.)
pub fn resolveQualifier(self: *Prove, tok: lexer.Token) Error!InternPool.Index {
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
    /// the schema's ORIGIN namespace (universe-of-`file`) — where its parameter sort tokens
    /// resolve. NOT the citing qualifier's namespace: a fact-alias resolves to the same schema
    /// from a different namespace, and its param sorts still live in the declaring file.
    ns: InternPool.Index,
    name: StrId, // the schema's name (keys the AST registry + the instance payload)
    /// the schema's Fact (params + formula) — a schema is an axiom/theorem/hole whose
    /// `Fact.params != null` (extracted via `ast.factOf`, decl-kind-agnostic).
    fact: ast.Fact,
    source: []const u8,
};

/// Resolve a schema name token (optionally `ns.`-qualified) to its file/ns + AST decl.
/// A schema resolves through the FACT table — its ProveTask published a `.schema` locator
/// (the read pass guarantees it `proven`); the decl itself comes from the by-name AST
/// registry (so a synthetic schema, and a fact-alias-to-a-schema, resolve too).
fn resolveSchemaRef(self: *Prove, tok: lexer.Token) Error!ResolvedSchema {
    const ns = try self.resolveQualifier(tok);
    const st = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = ns, .name = tokName(tok) }) orelse
        return self.fail(tok.start, "unknown schema '{s}'", .{self.text(tok)});
    const ix = switch (st) {
        .proven => |x| x,
        .in_flight => return self.fail(tok.start, "unknown schema '{s}'", .{self.text(tok)}),
    };
    const loc = switch (self.ctx.interner.keyOf(ix)) {
        .schema => |s| s,
        else => return self.fail(tok.start, "'{s}' is not a schema", .{self.text(tok)}),
    };
    const fid = self.ctx.fileOf(loc.file).?;
    const decl = self.ctx.declOf(fid, loc.name) orelse
        return self.fail(tok.start, "internal: schema '{s}' locator has no decl", .{self.text(tok)});
    // a schema is an axiom/theorem/hole with params; extract its Fact decl-kind-agnostically.
    const fact = ast.factOf(decl) orelse
        return self.fail(tok.start, "'{s}' is not a schema", .{self.text(tok)});
    const origin_ns = self.ctx.interner.namespace(.universe, loc.file) catch return error.OutOfMemory;
    return .{
        .file = loc.file,
        .ns = origin_ns,
        .name = loc.name,
        .fact = fact,
        .source = self.ctx.files.get(@intFromEnum(fid)).source,
    };
}

/// Elaborate the instantiation args in the CALLER's Elab `e` (caller scope + ns, so args
/// may reference caller-local binders), binding each schema param to a `Schema.SchemaArg`.
/// A value param → the elaborated arg term; an N-ary param → a lambda arg (or a bare
/// symbol eta-expanded). Sort tokens resolve in the SCHEMA's ns via a schema-scoped Elab.
/// `source_space`: bind the args in SOURCE space (the param sorts resolve un-remapped and `e`
/// is a source-space Elab) — the twins a source-space pass inside the instance substitutes.
fn bindSchemaArgs(self: *Prove, e: *Elab, rs: ResolvedSchema, c: ast.Step.Claim, source_space: bool) Error!*Schema.SchemaArgs {
    return self.bindSchemaArgsUnder(e, rs, c, source_space, null);
}

/// As `bindSchemaArgs`, but resolving the schema's parameter SORTS under an explicit model
/// rather than the citing proof's ambient one. Needed when a cite names a model that the
/// current proof is not itself running under: `[using model(M) src.sch(arg)]` with no discharge
/// instantiates the SOURCE schema, so `src.sch`'s parameter sorts must remap through M (the
/// container's `Item` becoming the carrier's `Grp`) while the arg is read in the citer's space.
fn bindSchemaArgsUnder(self: *Prove, e: *Elab, rs: ResolvedSchema, c: ast.Step.Claim, source_space: bool, model_override: ?InternPool.Index) Error!*Schema.SchemaArgs {
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
    se.model = if (source_space) .universe else (model_override orelse self.model);

    const args = try self.ctx.arena.create(Schema.SchemaArgs);
    args.* = .empty;
    for (params, c.args) |p, arg_raw| {
        // in source space an arg is read from the source AST (see `source_ast`).
        const arg_expr = if (source_space) self.sourceExpr(arg_raw) else arg_raw;
        const pname = tokName(p.name);
        // Switch on the KIND, not the arity. These used to coincide ("no args" ⇒ "is a value"),
        // but a nullary PRED `q()` has zero args and is still predicate-shaped — it binds a whole
        // proposition, so it takes the generator path with an empty argument list, not the value
        // path (which would ask for a result sort a pred does not have).
        if (p.kind == .value) {
            // VALUE param: elaborate the arg at the use site; sort-check vs the param sort.
            const want = try se.resolveSortTok(p.resultSort().?); // a VALUE param: token present
            const typed = try e.elaborateExpr(arg_expr);
            // a value param declared `Prop` has no carrier either (see the generator case below).
            const want_carrier: InternPool.Index = if (want == Elab.prop_sort) @enumFromInt(@intFromEnum(want)) else self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(want)));
            const got_carrier = if (typed.sort == Elab.prop_sort) @intFromEnum(typed.sort) else @intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort))));
            if (@intFromEnum(want_carrier) != got_carrier) {
                return self.fail(Elab.exprLoc(arg_expr), "expected sort '{s}', got '{s}'", .{
                    self.ctx.interner.sortName(@enumFromInt(@intFromEnum(want))), self.sortName(typed.sort),
                });
            }
            // store the CARRIER: terms are carrier-level (fvars mint at carriers; sigs check
            // carriers), so a refined `want` (a param sort remapped to `H` under a model) must
            // not leak into the instance's expressions — refinement rides as guards, not sorts.
            const want_stored: SortId = if (typed.sort == Elab.prop_sort) want else @enumFromInt(@intFromEnum(want_carrier));
            try args.put(self.ctx.arena, pname, .{ .value = .{ .id = typed.id, .sort = want_stored } });
        } else {
            // N-ary GENERATOR param: a lambda arg (or a bare symbol → eta-expand). Sorts are
            // stored at their CARRIERS (a refined resolution leaks guards-as-sorts otherwise).
            const arg_sorts = try self.ctx.arena.alloc(SortId, p.argSorts().len);
            for (p.argSorts(), arg_sorts) |st, *out| {
                const rs_sort = try se.resolveSortTok(st);
                out.* = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(rs_sort)))));
            }
            const rr = if (p.resultSort()) |rt| try se.resolveSortTok(rt) else Elab.prop_sort;
            // A `=> Prop` generator param yields a PROPOSITION, which has no sort and therefore
            // no carrier to lower to — `carrierOf` would index the absent marker. The common
            // case (`prop: Nat -> Prop`) takes this branch.
            const result_sort: SortId = if (rr == Elab.prop_sort) rr else @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(rr)))));
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
        // A NULLARY pred argument is written `q()` — a zero-argument call, the same spelling
        // its declaration and its uses carry. There is nothing to eta-expand, and the callee
        // need not be a global: commonly it is the CALLER's own nullary-pred parameter being
        // passed along (`s1(q())` inside `a(q())`). Elaborate it in the caller's scope, which
        // resolves a schema param, a local binder, or a global alike.
        .call => |c| {
            if (arg_sorts.len != 0 or c.args.len != 0) {
                return self.fail(Elab.exprLoc(arg_expr), "schema parameter expects a {d}-argument lambda or a bare symbol, got an application", .{arg_sorts.len});
            }
            const prop = try e.elaborateExpr(arg_expr);
            return .{ .lambda = .{ .body = prop.id, .params = &.{}, .arg_sorts = &.{}, .result_sort = result_sort } };
        },
        .name => |tok| {
            if (arg_sorts.len == 0) {
                const prop = try e.elaborateExpr(arg_expr);
                return .{ .lambda = .{ .body = prop.id, .params = &.{}, .arg_sorts = &.{}, .result_sort = result_sort } };
            }
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
    const sym = e.resolveSymbolTok(tok) orelse e.lookupIdentPub(self.ns, try self.localName(tok)) orelse
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

/// Reify a bound arg map durably (one `DurableArg` per param, in `pnames` order).
fn reifyArgs(self: *Prove, pnames: []const StrId, args: *const Schema.SchemaArgs) Allocator.Error![]const ProveTask.DurableArg {
    const durable = try self.ctx.arena.alloc(ProveTask.DurableArg, pnames.len);
    for (pnames, durable) |pname, *out| {
        const arg = args.get(pname).?;
        out.* = switch (arg) {
            .value => |v| .{ .value = .{ .off = try self.pool.reify(v.id, self.ctx.interner), .sort = v.sort } },
            .lambda => |l| .{ .lambda = .{ .off = try self.pool.reify(l.body, self.ctx.interner), .params = l.params, .arg_sorts = l.arg_sorts, .result_sort = l.result_sort } },
        };
    }
    return durable;
}

/// `se`: a SOURCE-space Elab for binding the args' source twins under a model transfer (the
/// accelerant plumbing passes one with the producer's fvar binds in scope); null → one is
/// derived from `e`'s walk. Unused outside a transfer.
fn demandInstance(self: *Prove, e: *Elab, se: ?*Elab, c: ast.Step.Claim) Allocator.Error!InstanceOutcome {
    const rs = self.resolveSchemaRef(c.schema.?) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    // the schema's PARAM SORT tokens are ITS file's names: demand them in its namespace before
    // binding the args. A schema is checked only at an instantiation, so nothing has fetched
    // them yet — a QUALIFIED cite from another file (`a.tauto`) found `Fn` absent from a's
    // namespace and failed "unknown sort" at the declaration; an aliased cite only worked when
    // the citing file happened to declare the same sort name.
    if (try self.demandSchemaParamSorts(rs)) |blocker| return .{ .blocked = blocker };
    const args = self.bindSchemaArgs(e, rs, c, false) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    // SOURCE-space twins of the args (see `source_formulas`): bound with the model off, so a
    // source-space pass inside the instance substitutes source terms for the params. The same
    // map outside a model transfer.
    const args_source: *Schema.SchemaArgs = if (self.sourceSpaceAccelerants() and !self.painted_production) blk: {
        var derived = self.sourceElab(e.walk);
        const sp: *Elab = se orelse &derived;
        break :blk self.bindSchemaArgs(sp, rs, c, true) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return .failed,
        };
    } else args;
    const params = rs.fact.params.?;
    const schema_name = tokName(c.schema.?);
    // stable ordered param-name list for the hash + payload: the schema's params, then — under
    // a model transfer — the args' FREE VARIABLES of refined image sort (`freeFvarParams`).
    var pnames_list: std.ArrayList(StrId) = .empty;
    for (params) |p| try pnames_list.append(self.ctx.arena, tokName(p.name));
    if (self.underModel()) {
        const base = try self.ctx.arena.dupe(StrId, pnames_list.items);
        self.freeFvarParams(rs, base, &pnames_list, args, args_source) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return .failed,
        };
    }
    const pnames = pnames_list.items;

    const hash = Schema.instanceHash(self.ctx.interner, self.pool, schema_name, pnames, args);
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
                self.ctx.sink.add(self.diagFile(), c.schema.?.start, "cyclic schema instantiation of '{s}'", .{self.text(c.schema.?)}) catch return error.OutOfMemory;
                return .failed;
            }
            return .{ .blocked = owner };
        },
    };
    // ABSENT: reify the args (and their source twins) durably + rack the instance ProveTask.
    const durable = try self.reifyArgs(pnames, args);
    const durable_source = if (args_source == args) durable else try self.reifyArgs(pnames, args_source);
    const blocker = try self.h.rackIndexed(try ProveTask.new(self.ctx.arena, .{
        .file = rs.file,
        .name = inst_name,
        .loc = c.schema.?.start,
        .loc_file = self.file,
        .model = self.model, // monomorphize the schema body UNDER the transfer's model
        .parent = self.self_key, // proof tree: this instance exists because THIS proof cited it
        .instance = .{ .schema_name = rs.name, .params = pnames, .args = durable, .args_source = durable_source },
    }));
    return .{ .blocked = blocker };
}

/// Demand (fetch) every sort token of `rs`'s parameter list in the schema's own namespace —
/// `T` in `x: T` and `T -> Prop`. `Prop` and already-resolved `.symbol` tokens need nothing.
/// Returns a blocker to suspend on, or null when all are done.
fn demandSchemaParamSorts(self: *Prove, rs: ResolvedSchema) Allocator.Error!?Engine.TaskIndex {
    var refs: std.ArrayList(RefScan.Ref) = .empty;
    for (rs.fact.params.?) |p| {
        for (p.argSorts()) |t| try appendSortRef(self.ctx.arena, &refs, t);
        // a PRED param has no result token to demand (its result is `Prop`, which is reserved).
        if (p.resultSort()) |rt| try appendSortRef(self.ctx.arena, &refs, rt);
    }
    if (refs.items.len == 0) return null;
    return resolveRefs(self.ctx, self.h, rs.file, rs.ns, self.model, self.self_key, refs.items);
}

fn appendSortRef(arena: Allocator, refs: *std.ArrayList(RefScan.Ref), tok: lexer.Token) Allocator.Error!void {
    if (tok.tag == .symbol) return;
    if (tok.qualifier == InternPool.Index.none and tok.name == InternPool.Index.prop_name) return;
    try refs.append(arena, .{
        .ns = if (tok.qualifier == InternPool.Index.none) null else tok.qualifier,
        .name = tokName(tok),
        .domain = .ident,
        .loc = tok.start,
    });
}

/// FREE VARIABLES of a schema instance's args — a caller-local `fix`/`unpack` variable riding
/// into the instance inside a lambda body or a compound value arg — whose SOURCE sort's image
/// under the transfer model is REFINED become EXTRA value params of the instance, named after
/// themselves and bound to themselves (in both spaces). `buildInstanceState` then wraps the
/// instance's proof in `assume guard(v)` exactly as for a refined schema value param, so a
/// discharge INSIDE the instance body (a nested accelerant whose own instance leads with
/// `guard(v) ->`) finds the guard it needs, and the call site discharges `guard(v)` from its
/// enclosing block (`withGuardPremises`): the guard travels with the variable. Before this, an
/// integer-induction proof transferred through a guarded model (std/group/power.b4m's powerAdd
/// onto Perm) failed at the induction body's inner `specialize` with "cannot discharge the
/// guard premise 'invertible(g)'". A variable that would shadow a schema param or a global of
/// the schema's namespace is left alone (the body may name that global).
fn freeFvarParams(self: *Prove, rs: ResolvedSchema, base: []const StrId, out: *std.ArrayList(StrId), args: *Schema.SchemaArgs, args_source: *Schema.SchemaArgs) Error!void {
    var seen_source: std.ArrayList(term.Node.Fvar) = .empty;
    var seen_target: std.ArrayList(term.Node.Fvar) = .empty;
    for (base) |pname| {
        if (args_source.get(pname)) |arg| try self.collectArgFvars(arg, &seen_source);
        if (args.get(pname)) |arg| try self.collectArgFvars(arg, &seen_target);
    }
    for (seen_source.items) |fv| {
        var clash = false;
        for (base) |pname| {
            if (pname == fv.name) clash = true;
        }
        if (clash) continue;
        if (self.ctx.idents.lookup(self.ctx.io, .{ .namespace = rs.ns, .name = fv.name }) != null) continue;
        const src_sort: InternPool.Index = @enumFromInt(@intFromEnum(fv.sort));
        const image = self.ctx.interner.applyModel(self.model, src_sort);
        if (!self.ctx.interner.isRefined(image)) continue;
        // the target-space twin: the same variable at the image's carrier (as the target args hold it).
        var tsort: SortId = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(image)));
        for (seen_target.items) |tv| {
            if (tv.name == fv.name) tsort = tv.sort;
        }
        const sv = try self.pool.add(.{ .fvar = .{ .name = fv.name, .sort = fv.sort } });
        const tv = try self.pool.add(.{ .fvar = .{ .name = fv.name, .sort = tsort } });
        try args_source.put(self.ctx.arena, fv.name, .{ .value = .{ .id = sv, .sort = fv.sort } });
        try args.put(self.ctx.arena, fv.name, .{ .value = .{ .id = tv, .sort = tsort } });
        try out.append(self.ctx.arena, fv.name);
    }
}

/// The free variables of one schema arg: a compound value arg's, or a lambda body's minus the
/// lambda's own (kept-free) params. A BARE variable value arg contributes nothing — its param
/// already carries the guard.
fn collectArgFvars(self: *Prove, arg: Schema.SchemaArg, out: *std.ArrayList(term.Node.Fvar)) Error!void {
    switch (arg) {
        .value => |v| {
            if (self.pool.get(v.id) == .fvar) return;
            try self.collectFreeFvars(v.id, out);
        },
        .lambda => |l| {
            var all: std.ArrayList(term.Node.Fvar) = .empty;
            try self.collectFreeFvars(l.body, &all);
            outer: for (all.items) |fv| {
                for (l.params) |p| {
                    if (p == fv.name) continue :outer;
                }
                for (out.items) |e| {
                    if (e.name == fv.name) continue :outer;
                }
                try out.append(self.ctx.arena, fv);
            }
        },
    }
}

/// The `instantiate` justification (in `process`, after the read pass demanded + proved the
/// instance fact): look it up, copyIn its formula, and emit `schema_instance` with the
/// caller's premise step-refs. The kernel peels the instance's `->` antecedents against the
/// premises and requires the final consequent == the citing claim.
fn lowerInstantiate(self: *Prove, w: *const Walk, e: *Elab, kb: kernel.BlockId, goal: TermId, c: ast.Step.Claim) Error!kernel.Justification {
    if (c.schema == null) return self.fail(c.rule.start, "instantiate requires a schema name", .{});
    const outcome = try self.demandInstance(e, null, c);
    const fact = switch (outcome) {
        .proven => |ix| blk: {
            self.inheritHoles(ix);
            self.inheritAxioms(ix);
            break :blk ix;
        },
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: instantiate not resolved before process (read-pass bug)", .{}),
    };
    const formula_off = self.ctx.interner.keyOf(fact).fact.formula;
    const instance = try self.pool.copyIn(self.ctx.interner, formula_off);
    const premises = try self.ctx.arena.alloc(kernel.SRef, c.refs.len);
    for (c.refs, premises) |r, *out| out.* = try self.resolveStepRef(w, r);
    // under a model transfer the instance may lead with injected guard premises (see
    // `withGuardPremises`) — discharge them here like the accelerant site does.
    return self.withGuardPremises(kb, c.rule.start, instance, goal, premises);
}

// -- model transfer --------------------------------------------------------------------

/// Demand the TRANSFERRED FACT for `[by model(M) src.thm]`: resolve M's `.model` Index
/// (read pass racked its ModelTask), split `src.thm` into (source file, name), and demand
/// that fact in namespace `(M, src_file)` — a ProveTask carrying `model = M` re-proves the
/// source theorem's proof with every global overlay-remapped. Returns the transferred fact
/// Index, or a blocker to suspend on. Called from the READ PASS (and re-checked in process).
fn demandTransfer(self: *Prove, c: ast.Step.Claim) Allocator.Error!InstanceOutcome {
    if (c.schema == null) {
        self.ctx.sink.add(self.diagFile(), c.rule.start, "model citation requires a model name: `[by model(M) src.thm]`", .{}) catch return error.OutOfMemory;
        return .failed;
    }
    if (c.refs.len != 1) {
        self.ctx.sink.add(self.diagFile(), c.rule.start, "`[by model(M) …]` cites exactly one transferred theorem", .{}) catch return error.OutOfMemory;
        return .failed;
    }
    // resolve M (a `.model` Index). A BARE name resolves in the citing file's namespace; a
    // QUALIFIED one (`I.M`) resolves the qualifier to an import and then M in THAT file's
    // namespace — the same two-step every qualified reference takes. A model interprets an
    // abstract theory with concrete symbols, and that interpretation is as reusable as any
    // theorem it proves, so a consumer may name its importer's model rather than re-declaring
    // the same mapping.
    const mtok = c.schema.?;
    var model_ns = self.ns;
    if (mtok.qualifier != InternPool.Index.none) {
        const qst = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = mtok.qualifier }) orelse
            return .{ .blocked = try self.h.rackIndexed(try FetchTask.new(self.ctx.arena, .{ .file = self.file, .name = mtok.qualifier, .loc = mtok.start, .loc_file = self.file })) };
        switch (qst) {
            .in_flight => |owner| return .{ .blocked = owner },
            .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
                .import => |imp| model_ns = imp.namespace,
                else => {
                    self.ctx.sink.add(self.diagFile(), mtok.start, "'{s}' does not name an import, so '{s}' cannot be a model in it", .{ self.ctx.interner.stringBytes(mtok.qualifier), self.text(mtok) }) catch return error.OutOfMemory;
                    return .failed;
                },
            },
        }
    }
    const mstate = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = model_ns, .name = tokName(mtok) }) orelse {
        // not yet resolved in the owning file: demand it there (a cross-file model needs its
        // declaring file walked), then re-enter.
        if (model_ns != self.ns) {
            const owner_file = self.ctx.interner.keyOf(model_ns).namespace.file;
            return .{ .blocked = try self.h.rackIndexed(try FetchTask.new(self.ctx.arena, .{ .file = owner_file, .name = tokName(mtok), .loc = mtok.start, .loc_file = self.file })) };
        }
        self.ctx.sink.add(self.diagFile(), mtok.start, "unknown model '{s}'", .{self.text(mtok)}) catch return error.OutOfMemory;
        return .failed;
    };
    const model_ix = switch (mstate) {
        .done => |ix| ix,
        .in_flight => |owner| return .{ .blocked = owner },
    };
    if (self.ctx.interner.keyOf(model_ix) != .model) {
        self.ctx.sink.add(self.diagFile(), mtok.start, "'{s}' is not a model", .{self.text(mtok)}) catch return error.OutOfMemory;
        return .failed;
    }
    // the source theorem: QUALIFIED `src.thm` names the source file via its import; an
    // UNQUALIFIED `thm` is a SAME-FILE source theorem (the source theory + model + citation
    // all live in one file — the natural shape for e.g. a subgroup on its group's sort), so
    // the source file IS the citing file. The transferred fact's identity ns is (M, src_file),
    // DISTINCT from the citing proof's own (universe, self.file) fact, so no collision.
    const rtok = c.refs[0];
    // `definition(N) src.f` cites the clause axiom the source's definition block published
    // under a mangled name — re-derived here, so from this point the transfer machinery sees
    // an ordinary fact name and needs no further special case.
    const base = if (c.definition_arm) |arm|
        self.ctx.interner.definitionClauseName(self.ctx.arena, self.ctx.interner.stringBytes(tokName(rtok)), arm) catch return error.OutOfMemory
    else
        tokName(rtok);
    const src_file = if (rtok.qualifier == InternPool.Index.none) self.file else blk: {
        const qtext = self.ctx.interner.stringBytes(rtok.qualifier);
        // the qualifier is an IMPORT of the citing file; like every other qualified
        // reference (resolveRefs), an unfetched one is DEMANDED — racked and suspended on —
        // never diagnosed as unknown. (Before: a passive lookup, so a source theory none of
        // whose OWN symbols the file had touched — an alias-only re-export like
        // std/group/listing.b4m — read as "unknown namespace".)
        const imp_state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = rtok.qualifier }) orelse {
            return .{ .blocked = try self.h.rackIndexed(try FetchTask.new(self.ctx.arena, .{ .file = self.file, .name = rtok.qualifier, .loc = rtok.start, .loc_file = self.file })) };
        };
        break :blk switch (imp_state) {
            .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
                .import => |imp| self.ctx.interner.keyOf(imp.namespace).namespace.file,
                else => {
                    self.ctx.sink.add(self.diagFile(), rtok.start, "'{s}' is not a namespace", .{qtext}) catch return error.OutOfMemory;
                    return .failed;
                },
            },
            .in_flight => |owner| return .{ .blocked = owner },
        };
    };
    // COMPOSE with the AMBIENT model, if any. When this proof is itself a model transfer
    // (`self.model != universe` — e.g. proving `ring.thm` under IntegerRing), a nested
    // `[using model(M) src.thm]` step must transfer `src.thm` down BOTH models: `model_ix`
    // (source → THIS proof's target space) then the ambient `self.model` (that space → the
    // outer target). `composeModel` bakes the second hop into a fresh interned model whose
    // parent is the ambient one, so unmapped sources fall through. When self.model IS the
    // universe (the common case — a standalone proof, or a top-level transfer), the effective
    // model is `model_ix` unchanged (behavior-neutral).
    const effective_model = if (self.model == InternPool.Index.universe)
        model_ix
    else blk: {
        const composed = self.ctx.interner.composeModel(self.ctx.io, self.model, model_ix) catch return error.OutOfMemory;
        try self.ctx.copyModelDefineTargets(composed, self.model, model_ix); // define targets ride along
        break :blk composed;
    };
    // demand the transferred fact in namespace (effective_model, src_file). A distinct ambient
    // model composes to a distinct model → a distinct namespace → a distinct fact (each is its
    // own relativization); the in_flight/proven dedup below keys on that namespace, so it holds.
    const tns = self.ctx.interner.namespace(effective_model, src_file) catch return error.OutOfMemory;
    if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = tns, .name = base })) |st| switch (st) {
        .proven => |ix| {
            // a SCHEMA source has no transferred proof of its own: it is the model's obligation
            // `src.sch <- local`, and what the citer gets is the DISCHARGING schema.
            if (self.ctx.interner.keyOf(ix) == .schema) {
                // the obligation was recorded against the schema's UNIVERSE locator (what
                // ModelTask resolved), not this transfer namespace's.
                const uns = self.ctx.interner.namespace(.universe, src_file) catch return error.OutOfMemory;
                const universe_ix = if (self.ctx.facts.lookup(self.ctx.io, .{ .namespace = uns, .name = base })) |ust| switch (ust) {
                    .proven => |u| u,
                    .in_flight => ix,
                } else ix;
                const mapped = self.ctx.interner.applyModel(effective_model, universe_ix);
                if (mapped == universe_ix) {
                    // NO DISCHARGE. With EXPLICIT args that is not an error: instantiate the
                    // SOURCE schema directly, under the model's interpretation. The args are
                    // read in the CITER's space while the schema's parameter sorts remap
                    // through the model (`bindSchemaArgs` with source_space=false already does
                    // exactly that), so a container lemma over `Item` instantiates at a `Grp`
                    // map. Nothing is substituted FOR the source, so no discharge is wanted —
                    // the instance is the source's own proof re-checked under the model, which
                    // is what an ordinary transfer does for a plain theorem.
                    //
                    // Without args there is nothing to instantiate at, so a discharge (or an
                    // enclosing schema body, handled in demandSchemaTransfer) is the only
                    // meaning available — keep the diagnostic.
                    if (c.args.len != 0) return try self.demandSchemaTransferUnder(c, universe_ix, effective_model);
                    self.ctx.sink.add(self.diagFile(), rtok.start, "'{s}' is a schema obligation the model does not discharge (`{s} <- <local schema>`)", .{ self.text(rtok), self.text(rtok) }) catch return error.OutOfMemory;
                    return .failed;
                }
                return .{ .proven = mapped };
            }
            return .{ .proven = ix };
        },
        .in_flight => |owner| {
            if (owner == self.h.self_index) {
                self.ctx.sink.add(self.diagFile(), rtok.start, "model transfer of '{s}' depends on itself", .{self.text(rtok)}) catch return error.OutOfMemory;
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
        .model = effective_model,
        .parent = self.self_key, // proof tree: the TRANSFER's parent is the citing proof
    }));
    return .{ .blocked = blocker };
}

/// Does `[using model(M) src.thm]` cite a SCHEMA source? Such a citation is the discharging
/// schema's instantiation (see `demandSchemaTransfer`), and `instantiation` is never trustable
/// (#93) — so it stays strict even under `--fast model`. Answered off the source declaration;
/// `.blocked` while the import or its parse is pending (the read pass suspends).
fn transfersSchema(self: *Prove, c: ast.Step.Claim) Allocator.Error!union(enum) { yes, no, blocked: Engine.TaskIndex } {
    if (c.refs.len != 1) return .no;
    if (c.definition_arm != null) return .no; // a definition clause is a ground fact
    const rtok = c.refs[0];
    var src_file = self.file;
    if (rtok.qualifier != InternPool.Index.none) {
        const st = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = rtok.qualifier }) orelse
            return .{ .blocked = try self.h.rackIndexed(try FetchTask.new(self.ctx.arena, .{ .file = self.file, .name = rtok.qualifier, .loc = rtok.start, .loc_file = self.file })) };
        switch (st) {
            .in_flight => |owner| return if (owner != self.h.self_index) .{ .blocked = owner } else .no,
            .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
                .import => |imp| src_file = self.ctx.interner.keyOf(imp.namespace).namespace.file,
                else => return .no,
            },
        }
    }
    switch (try self.ctx.demandParse(self.h, src_file)) {
        .parsed => {},
        .parsing => |t| return .{ .blocked = t },
        .unparsed => return .no,
    }
    const fid = self.ctx.fileOf(src_file) orelse return .no;
    const decl = self.ctx.declOf(fid, tokName(rtok)) orelse return .no;
    const fact = ast.factOf(decl) orelse return .no;
    return if (fact.params != null) .yes else .no;
}

/// The `[by model(M) src.thm]` justification (in process, after the read pass proved the
/// transferred fact): copyIn its formula and cite it as a proven theorem. (The transferred
/// fact's formula is already in TARGET terms — proved under M's overlay.)
fn lowerModel(self: *Prove, kb: kernel.BlockId, goal: TermId, c: ast.Step.Claim) Error!kernel.Justification {
    const outcome = try self.demandTransfer(c);
    const fact = switch (outcome) {
        .proven => |ix| blk: {
            self.inheritHoles(ix);
            self.inheritAxioms(ix);
            break :blk ix;
        },
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: model transfer not resolved before process (read-pass bug)", .{}),
    };
    // a transferred SCHEMA: the step is the discharging schema's instance at this proof's
    // arguments (demanded in the read pass) — a schema_instance, like `instantiation`.
    if (self.ctx.interner.keyOf(fact) == .schema) {
        const inst = switch (try self.demandSchemaTransfer(c, fact)) {
            .proven => |ix| blk: {
                self.inheritHoles(ix);
                self.inheritAxioms(ix);
                break :blk ix;
            },
            .failed => return error.Recover,
            .blocked => return self.fail(c.rule.start, "internal: transferred schema instance not resolved before process (read-pass bug)", .{}),
        };
        const instance = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(inst).fact.formula);
        return self.withGuardPremises(kb, c.rule.start, instance, goal, try self.ctx.arena.alloc(kernel.SRef, 0));
    }
    const loc = c.refs[0].start;
    return .{ .cite_ref = .{ .stmt = fact, .loc = loc } };
}

/// The instance a transferred SCHEMA citation stands for. `[using model(M) src.sch]` where
/// `src.sch` is a parameterized axiom discharged by a local schema (`src.sch <- local`) has no
/// ground fact to cite: the citing proof must itself be a schema instance whose parameters
/// stand in for the source schema's, and the step IS the discharging schema instantiated at
/// those same arguments — positionally, since ModelTask required a schema with a matching
/// parameter list. Demands that instance exactly like `demandInstance` (read pass racks +
/// suspends; process finds it proven).
fn demandSchemaTransfer(self: *Prove, c: ast.Step.Claim, schema_ix: InternPool.Index) Allocator.Error!InstanceOutcome {
    return self.demandSchemaTransferUnder(c, schema_ix, null);
}

/// As `demandSchemaTransfer`, with `cite_model` the model named at the cite when the schema is
/// the SOURCE (no discharge) rather than a discharge — its parameter sorts then remap through
/// that model instead of the proof's ambient one.
fn demandSchemaTransferUnder(self: *Prove, c: ast.Step.Claim, schema_ix: InternPool.Index, cite_model: ?InternPool.Index) Allocator.Error!InstanceOutcome {
    const rtok = c.refs[0];
    const sk = self.ctx.interner.keyOf(schema_ix).schema;
    // A schema cite comes in TWO shapes, and the arguments say which:
    //
    //   `[using model(M) src.sch(myPred)]` — EXPLICIT args. The cite names what to instantiate
    //      the discharging schema at, so it works anywhere a step does (the common case: a
    //      consumer wanting a generic source lemma at a predicate of its own).
    //   `[using model(M) src.sch]`         — NO args. Only meaningful inside a SCHEMA BODY,
    //      where the citing schema's own parameters stand in for the source's; `self.schema_args`
    //      carries them. Outside one there is nothing to instantiate at, which is an authoring
    //      error, so it is diagnosed rather than silently doing nothing.
    const explicit_args = c.args.len != 0;
    const args_in = if (explicit_args) null else self.schema_args orelse {
        self.ctx.sink.add(self.diagFile(), rtok.start, "'{s}' transfers as a SCHEMA, so it must be instantiated: either name the arguments at the cite (`[using model(M) {s}(<arg>…)]`) or cite it from inside a schema body whose own parameters stand in for its", .{ self.text(rtok), self.text(rtok) }) catch return error.OutOfMemory;
        return .failed;
    };
    const citing_params = self.schema_params;
    // the discharging schema's own parameter names, off its declaration.
    const tfid = self.ctx.fileOf(sk.file) orelse {
        self.ctx.sink.add(self.diagFile(), rtok.start, "internal: the discharging schema's file is undiscovered", .{}) catch return error.OutOfMemory;
        return .failed;
    };
    const decl = self.ctx.declOf(tfid, sk.name) orelse {
        self.ctx.sink.add(self.diagFile(), rtok.start, "reference not found: '{s}'", .{self.ctx.interner.stringBytes(sk.name)}) catch return error.OutOfMemory;
        return .failed;
    };
    const params = (if (ast.factOf(decl)) |f| f.params else null) orelse {
        self.ctx.sink.add(self.diagFile(), rtok.start, "'{s}' discharges the schema '{s}' but is not a schema", .{ self.ctx.interner.stringBytes(sk.name), self.text(rtok) }) catch return error.OutOfMemory;
        return .failed;
    };
    if (!explicit_args and params.len != citing_params.len) {
        self.ctx.sink.add(self.diagFile(), rtok.start, "'{s}' (discharging '{s}') takes {d} parameter(s); this schema takes {d}", .{ self.ctx.interner.stringBytes(sk.name), self.text(rtok), params.len, citing_params.len }) catch return error.OutOfMemory;
        return .failed;
    }
    const pnames = try self.ctx.arena.alloc(StrId, params.len);
    for (params, pnames) |p, *out| out.* = tokName(p.name);
    // EXPLICIT args: bind them against the DISCHARGING schema directly, exactly as
    // `instantiation` does — so `model(M) src.sch(pred)` and `instantiation local(pred)` take
    // the same path from here, and the arity/sort diagnostics are the shared ones.
    // AMBIENT args: re-key the citing schema's arguments by the discharging schema's param names.
    const args, const args_source = if (explicit_args) blk: {
        const rs = ResolvedSchema{
            .file = sk.file,
            .ns = self.ctx.interner.namespace(.universe, sk.file) catch return error.OutOfMemory,
            .name = sk.name,
            .fact = ast.factOf(decl).?,
            .source = self.ctx.files.get(@intFromEnum(tfid)).source,
        };
        var w = Walk.init(self.ctx.arena, self.ctx.interner, self.source, self.ctx.sink);
        var e = self.elab(&w);
        const bound = self.bindSchemaArgsUnder(&e, rs, c, false, cite_model) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return .failed, // diagnosed by bindSchemaArgs
        };
        // SOURCE-SPACE TWIN. The instance runs passes in BOTH spaces: the statement in target
        // terms, a source-space pass over the body. The source pass elaborates the schema's own
        // binders UN-remapped (`Elem`, not `Thing`), so the args it substitutes must record
        // SOURCE sorts too — otherwise a generator param's `arg_sorts` say `Thing` while the
        // body's binder says `Elem`, and `applyGeneratorParam` rejects the application inside
        // the SOURCE file ("expected sort 'Thing', got 'Elem'").
        //
        // Re-bind with `source_space = true`, which resolves the schema's param sorts without
        // the model. NOTE this is NOT gated on `sourceSpaceAccelerants()` (= "is the CITING
        // PROOF under a model"): here the model is named at the CITE, so that question is the
        // wrong one and answers false.
        const src_bound: *Schema.SchemaArgs = if (cite_model != null) blk2: {
            // The author wrote the lambda ONCE, in target terms — there is no source-space AST
            // twin to re-read (`source_ast` is populated only for a proof that is itself a
            // transfer). So reuse the BOUND body and restate only the recorded SORTS on the
            // source side: the body term is identical either way (its binders are fresh fvars,
            // and the arg carries no captures to re-resolve), while `arg_sorts`/`result_sort`
            // are what the source-space pass compares against the schema's un-remapped binders.
            // a schema-scoped Elab with NO model: resolves the schema's own param sorts at
            // their source values (`Elem`, not `Thing`).
            var src_walk = Walk.init(self.ctx.arena, self.ctx.interner, rs.source, self.ctx.sink);
            var src_se = Elab.init(self.ctx.arena, self.ctx.io, self.ctx, self.ctx.interner, &self.ctx.idents, self.pool, self.ctx.sink, rs.source, &src_walk, rs.ns, &self.fresh_counter);
            src_se.model = .universe;
            const twin = try self.ctx.arena.create(Schema.SchemaArgs);
            twin.* = .empty;
            for (params, pnames) |p2, pname| {
                const a = bound.get(pname) orelse continue;
                switch (a) {
                    .value => try twin.put(self.ctx.arena, pname, a),
                    .lambda => |l| {
                        const src_args = try self.ctx.arena.alloc(SortId, p2.argSorts().len);
                        for (p2.argSorts(), src_args) |st, *out| {
                            const rsrt = src_se.resolveSortTok(st) catch return .failed;
                            out.* = if (rsrt == Elab.prop_sort) rsrt else @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(rsrt)))));
                        }
                        const rrr = if (p2.resultSort()) |rt| (src_se.resolveSortTok(rt) catch return .failed) else Elab.prop_sort;
                        // `=> Prop` has no sort and so no carrier (see bindSchemaArgsUnder).
                        const rrr_carrier: SortId = if (rrr == Elab.prop_sort) rrr else @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(rrr)))));
                        try twin.put(self.ctx.arena, pname, .{ .lambda = .{
                            .body = l.body,
                            .params = l.params,
                            .arg_sorts = src_args,
                            .result_sort = rrr_carrier,
                        } });
                    },
                }
            }
            break :blk2 twin;
        } else bound;
        break :blk .{ bound, src_bound };
    } else blk: {
        const rekeyed = try self.rekeyArgs(citing_params, pnames, args_in.?, rtok) orelse return .failed;
        const src_in = self.schema_args_source orelse args_in.?;
        const src: *Schema.SchemaArgs = if (src_in == args_in.?) rekeyed else (try self.rekeyArgs(citing_params, pnames, src_in, rtok) orelse return .failed);
        break :blk .{ rekeyed, src };
    };

    const hash = Schema.instanceHash(self.ctx.interner, self.pool, sk.name, pnames, args);
    const inst_name_bytes = std.fmt.allocPrint(self.ctx.arena, "{s}{{{x}}}", .{ self.ctx.interner.stringBytes(sk.name), hash }) catch return error.OutOfMemory;
    const inst_name = self.ctx.interner.internString(inst_name_bytes) catch return error.OutOfMemory;
    // The instance is proved under `cite_model orelse self.model` (see the rack below), so its
    // IDENTITY namespace must be the same — publishing in one namespace while proving in
    // another makes the fact unfindable and re-racks it forever.
    const inst_ns = self.ctx.interner.namespace(cite_model orelse self.model, sk.file) catch return error.OutOfMemory;
    const key = FactKV.Key{ .namespace = inst_ns, .name = inst_name };
    if (self.ctx.facts.lookup(self.ctx.io, key)) |state| switch (state) {
        .proven => |ix| return .{ .proven = ix },
        .in_flight => |owner| {
            if (owner == self.h.self_index) {
                self.ctx.sink.add(self.diagFile(), rtok.start, "cyclic schema instantiation of '{s}'", .{self.ctx.interner.stringBytes(sk.name)}) catch return error.OutOfMemory;
                return .failed;
            }
            return .{ .blocked = owner };
        },
    };
    const durable = try self.reifyArgs(pnames, args);
    const durable_source = if (args_source == args) durable else try self.reifyArgs(pnames, args_source);
    const blocker = try self.h.rackIndexed(try ProveTask.new(self.ctx.arena, .{
        .file = sk.file,
        .name = inst_name,
        .loc = rtok.start,
        .loc_file = self.file,
        // the schema BODY is proved under the cite's model when the schema is the SOURCE (so
        // its own sorts/symbols remap to the carrier's); under the ambient model otherwise.
        .model = cite_model orelse self.model,
        .parent = self.self_key, // proof tree: a transferred schema's instance
        .instance = .{ .schema_name = sk.name, .params = pnames, .args = durable, .args_source = durable_source },
    }));
    return .{ .blocked = blocker };
}

/// `args` (keyed by `from` names) re-keyed positionally by `to` names. Null = diagnosed.
fn rekeyArgs(self: *Prove, from: []const StrId, to: []const StrId, args: *const Schema.SchemaArgs, loc_tok: lexer.Token) Allocator.Error!?*Schema.SchemaArgs {
    const out = try self.ctx.arena.create(Schema.SchemaArgs);
    out.* = .empty;
    for (from, to) |f, t| {
        const a = args.get(f) orelse {
            self.ctx.sink.add(self.diagFile(), loc_tok.start, "internal: schema parameter '{s}' has no bound argument", .{self.ctx.interner.stringBytes(f)}) catch return error.OutOfMemory;
            return null;
        };
        try out.put(self.ctx.arena, t, a);
    }
    return out;
}

/// The `[using import(I) thm]` justification: cite theorem `thm` from import `I`'s file across
/// the file boundary — the explicit accelerant seam (vs. a bare `[by cite I.thm]` qualified
/// citation, which is identical mechanically today; the accelerant is the trust boundary a
/// future `--fast` scopes to). The read pass resolved `I` (ident) + demanded `thm` in I's
/// namespace, so both are ready; look up the fact and cite it. Acceptance is SHAPE-only — the
/// kernel re-matches `thm`'s formula against the claim (as every `cite_ref` does).
fn lowerImport(self: *Prove, c: ast.Step.Claim) Error!kernel.Justification {
    const itok = c.schema orelse return self.fail(c.rule.start, "import citation requires an import name: `[using import(I) thm]`", .{});
    if (c.refs.len != 1) return self.fail(c.rule.start, "`[using import(I) …]` cites exactly one imported theorem", .{});
    const rtok = c.refs[0];
    // resolve import I (a local ident that must be an `.import`) → the imported namespace.
    const istate = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tokName(itok) }) orelse
        return self.fail(itok.start, "unknown import '{s}'", .{self.text(itok)});
    const imp_ix = switch (istate) {
        .done => |ix| ix,
        .in_flight => return self.fail(itok.start, "unknown import '{s}'", .{self.text(itok)}),
    };
    const imp_ns = switch (self.ctx.interner.keyOf(imp_ix)) {
        .import => |m| m.namespace,
        else => return self.fail(itok.start, "'{s}' is not an import", .{self.text(itok)}),
    };
    // the cited fact, resolved in I's namespace exactly as `[by cite I.thm]` resolves — the
    // TRANSFER redirect under a model (the read pass demanded the transferred copy in
    // `(model, I's file)`), the axiom overlay, the schema rejection, and the holes/axioms
    // bookkeeping (an axiom reached only through `import(I)` must still show in `--axioms`).
    const fact = try self.resolveFactIn(rtok, imp_ns);
    // kind-agnostic like `by cite`: the kernel arm follows the RESOLVED fact's kind (an
    // imported axiom is as citable as an imported theorem).
    return .{ .cite_ref = .{ .stmt = fact, .loc = rtok.start } };
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

/// The `Verify.Word` a `using` claim's rule names — its `--fast` trust unit — or null if the
/// claim is not a `using` step (a `by` primitive is never trustable). The three ENGINE words
/// (`instantiation`/`model`/`import`) are RuleStr; an ACCELERANT is any other `using` word,
/// matched by interned name (no strcmp past this seam: the rule id is already an interned StrId;
/// this interns each candidate word once for the comparison).
fn trustWord(self: *Prove, c: ast.Step.Claim) ?Verify.Word {
    if (c.kind != .using) return null;
    if (InternPool.RuleStr.of(c.rule.name)) |kind| return switch (kind) {
        // `instantiation` is NOT trustable — `admit` is shape-only, but an instantiation's content
        // is the body's proof at the args (the only soundness gate). It always strict-proves (#93).
        .model => .model,
        .import => .import,
        else => null, // `instantiation` + any other RuleStr in a `using` step → not trustable
    };
    return wordOfRule(self.ctx.interner, c.rule.name);
}

/// The trustable ACCELERANT word a rule token names, matched by interned name (no strcmp past
/// the parser: the rule is already a StrId; each candidate word is interned once per call).
/// Engine words (`model`/`import`) are RuleStr and never reach here as accelerants.
pub fn wordOfRule(interner: *InternPool, rule: StrId) ?Verify.Word {
    inline for (@typeInfo(Verify.Word).@"enum".fields) |f| {
        const engine_word = comptime (std.mem.eql(u8, f.name, "model") or std.mem.eql(u8, f.name, "import"));
        if (!engine_word) {
            const id = interner.internString(f.name) catch return null;
            if (rule == id) return @field(Verify.Word, f.name);
        }
    }
    return null;
}

/// Is this `using` step TRUSTED under the current `--fast` set? (Its word is in `verify.trusted`.)
fn trusted(self: *Prove, c: ast.Step.Claim) bool {
    const word = self.trustWord(c) orelse return false;
    return self.ctx.verify.trusts(word);
}

// -- THE ACCELERATED TACTICS -----------------------------------------------------------------
//
// One variant per trustable `using` word; the payload is the tactic's own type (its file in
// `Accelerants/`), carrying what phase 1 extracted for this step. The scaffolding dispatches
// through this union ONCE — `switch (tactic) { inline else => |a| a.decide(…) }` — and reads
// each tactic's `schema_slot` / `premise_shape` / `lemma_args` off its type at comptime.
//
// THE RULE: scaffolding code has NO tactic-specific logic. No `c.rule.name == "…"`
// comparisons, no `switch (word)` arms naming individual tactics, no word lists — anywhere in
// the read pass, `admit`, `demandUsing`/`lowerUsing`, `accelerantPremises` or root seeding. A
// new tactic is one new file and one new variant here; a scaffolding behaviour that must vary
// per tactic becomes a `pub const` or a phase hook on the tactic, never a branch at the use
// site. (`model` and `import` are ENGINE words — they transfer or cite an existing fact and
// produce nothing — so they are not variants and are dispatched beside the union.)

pub const Tactic = union(enum) {
    specialize: @import("Accelerants/Specialize.zig"),
    tautology: @import("Accelerants/Tautology.zig"),
    simplify: @import("Accelerants/Simplify.zig"),
    simplify_quantified: @import("Accelerants/Simplify.zig"),
    chain: @import("Accelerants/Chain.zig"),
    assoc: @import("Accelerants/Assoc.zig"),
    assoc_quantified: @import("Accelerants/Assoc.zig"),
    assoc_commut: @import("Accelerants/Assoc.zig"),
    assoc_commut_quantified: @import("Accelerants/Assoc.zig"),
    polynomial: @import("Accelerants/Polynomial.zig"),
    polynomial_quantified: @import("Accelerants/Polynomial.zig"),
    extensionality: @import("Accelerants/Extensionality.zig"),
    extensionality_quantified: @import("Accelerants/Extensionality.zig"),
    arithmetic: @import("Accelerants/Arithmetic.zig"),
    arithmetic_quantified: @import("Accelerants/Arithmetic.zig"),

    /// The tactic a trustable word names, its payload constructed for that word's variant —
    /// or null for an engine word (`model`/`import`).
    pub fn of(word: Verify.Word) ?Tactic {
        return switch (word) {
            .model, .import => null,
            .specialize => .{ .specialize = .{} },
            .tautology => .{ .tautology = .{} },
            .simplify => .{ .simplify = .{ .quantified = false } },
            .simplify_quantified => .{ .simplify_quantified = .{ .quantified = true } },
            .chain => .{ .chain = .{} },
            .assoc => .{ .assoc = .{ .commut = false, .quantified = false } },
            .assoc_quantified => .{ .assoc_quantified = .{ .commut = false, .quantified = true } },
            .assoc_commut => .{ .assoc_commut = .{ .commut = true, .quantified = false } },
            .assoc_commut_quantified => .{ .assoc_commut_quantified = .{ .commut = true, .quantified = true } },
            .polynomial => .{ .polynomial = .{ .quantified = false } },
            .polynomial_quantified => .{ .polynomial_quantified = .{ .quantified = true } },
            .extensionality => .{ .extensionality = .{ .quantified = false } },
            .extensionality_quantified => .{ .extensionality_quantified = .{ .quantified = true } },
            .arithmetic => .{ .arithmetic = .{} },
            .arithmetic_quantified => .{ .arithmetic_quantified = .{} },
        };
    }

    /// The tactic a `using` rule token names, by interned name — for the scanner, which has a
    /// rule StrId and no claim. Null for an engine word or an unknown word.
    pub fn ofRule(interner: *InternPool, rule: StrId) ?Tactic {
        return Tactic.of(wordOfRule(interner, rule) orelse return null);
    }

    pub fn lemmaArgs(self: Tactic) bool {
        return switch (self) {
            inline else => |a| @TypeOf(a).lemma_args,
        };
    }
    pub fn schemaSlot(self: Tactic) Accelerant.SchemaSlot {
        return switch (self) {
            inline else => |a| @TypeOf(a).schema_slot,
        };
    }
    pub fn premiseShape(self: Tactic) Accelerant.PremiseShape {
        return switch (self) {
            inline else => |a| @TypeOf(a).premise_shape,
        };
    }
};

/// The accelerated tactic of a `using` claim, or null (a `by` step, or an engine word).
fn tacticOf(self: *Prove, c: ast.Step.Claim) ?Tactic {
    return Tactic.of(self.trustWord(c) orelse return null);
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
    // ACCELERANTS PRODUCE IN THE AMBIENT NAMESPACE. The producer sees `goal` exactly as the
    // claim's proof does — under a model transfer, already interpreted into the target space —
    // and its synthetic is built from those terms, so its symbols are stamped FINAL (see
    // `Accelerant.Builder.symTok`): the instance ProveTask runs under the same model and must
    // not interpret them a second time. `painted_production` tells `demandInstance` that no
    // source-space twin of the args exists (there is no source-space pass to feed).
    const prev_painted = self.painted_production;
    self.painted_production = true;
    defer self.painted_production = prev_painted;
    const syn = blk: {
        const produced = self.produceAccelerant(w, e, goal, c) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            // A `Recover` WITH `producer_blocker` set is a PARK, not a diagnosis: the producer
            // racked a demand and suspended. Report it blocked so the step re-runs.
            error.Recover => {
                if (self.producer_blocker) |blocker| {
                    self.producer_blocker = null;
                    return .{ .blocked = blocker };
                }
                return .failed;
            },
        };
        if (produced) |s| {
            self.producer_premise_refs = s.premises;
            break :blk s;
        }
        // a null WITHOUT a diagnostic = the producer racked a demand it needs first.
        if (self.producer_blocker) |blocker| {
            self.producer_blocker = null;
            return .{ .blocked = blocker };
        }
        return .failed; // producer diagnosed
    };
    // MODEL-MANGLE the synthetic's name (13e): the same source step produces DIFFERENT
    // synthetics standalone vs under a transfer (the transfer's terms are remapped +
    // relativized). The registry/FactKV keys carry no model, so an unmangled name would
    // collide keep-first with the standalone synthetic — the transferred instance would
    // resolve the UNRELATIVIZED schema. `{m<N>}` uses non-lexable braces (collision-free).
    var syn_name = syn.name;
    const fid = self.ctx.fileOf(self.file).?;
    const decl_ptr = self.ctx.arena.create(ast.Decl) catch return error.OutOfMemory;
    // the generated theorem STATES the preconditions of the terms it restates (see
    // `wrapObligations`); deterministic per step, so the keep-first registration is stable.
    var wb: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };
    const obligations = self.syntheticObligations(w, syn.seen) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    decl_ptr.* = self.wrapObligations(&wb, syn.decl, obligations) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .failed,
    };
    if (self.model != InternPool.Index.none and self.model != .universe) {
        const bytes = std.fmt.allocPrint(self.ctx.arena, "{s}{{m{d}}}", .{ self.ctx.interner.stringBytes(syn.name), @intFromEnum(self.model) }) catch return error.OutOfMemory;
        syn_name = self.ctx.interner.internString(bytes) catch return error.OutOfMemory;
        setSyntheticName(decl_ptr, syn_name);
    }
    // register the synthetic decl + publish its `.schema` locator into the FACT table ONCE
    // (both idempotent). A schema is a fact-with-params, so it lives in FactKV like any fact.
    _ = self.ctx.registerDecl(fid, decl_ptr) catch return error.OutOfMemory; // keep-first
    self.ctx.registerSynthetic(fid, c.rule.start, syn_name) catch return error.OutOfMemory; // by step, for the debug reprint
    const schema_key = FactKV.Key{ .namespace = self.ns, .name = syn_name };
    if (self.ctx.facts.lookup(self.ctx.io, schema_key) == null) {
        _ = self.ctx.facts.publishSchema(self.ctx.io, schema_key, .{
            .name = syn_name,
            .file = self.file,
            .loc = c.rule.start,
        }) catch return error.OutOfMemory;
    }
    // demand the instance via the ordinary schema path, using a synthesized claim that names
    // the synthetic schema + carries the accelerant's args (premises ride c.refs separately).
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };
    const inst_c: ast.Step.Claim = .{
        .formula = c.formula,
        .kind = .using,
        .rule = c.rule,
        .schema = b.tok(syn_name),
        .args = syn.args,
        .refs = syn.premises,
    };
    // Install the producer's caller-scope fvar bindings (display-name → the abstracted free
    // eigenvar) so each call-site arg elaborates back to its very fvar — needed when a free
    // fvar was INHERITED from a schema-instance monomorphization (no source binder resolves it;
    // see `Synthetic.fvar_binds`). A no-op for the common `fix`-bound case. Truncated after.
    // The binds were collected in SOURCE space (the fvar's source sort); the caller Elab `e` is
    // TARGET space, so map the sort through the ambient model (identity in the universe).
    // `se` is the SOURCE-space twin of `e` (binds at their recorded source sort): under a model
    // transfer the instance's arg twins are bound through it (demandInstance).
    const scope_mark = e.scopeMark();
    for (syn.fvar_binds) |bind| {
        // an fvar lives at a CARRIER (bindProofVar lowers a refined binder's sort): the model's
        // image of the source sort may be a REFINED target (`Src: GoodTgt`) — bind at its carrier,
        // so the arg elaborates to the very fvar the walk bound (sort is part of its identity).
        // PAINTED production: `bind.sort` was read off a TARGET-space term, so it is already the
        // image — the model does not apply to it (see `Elab.resolveSymbolTok`).
        const sort_ix: InternPool.Index = @enumFromInt(@intFromEnum(bind.sort));
        const target_sort: SortId = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(sort_ix)));
        e.pushBinder(bind.name, target_sort, bind.fvar) catch return error.OutOfMemory;
    }
    defer e.scopeTruncate(scope_mark);
    return self.demandInstance(e, null, inst_c);
}

/// Rewrite a synthetic fact decl's NAME token identity (the `{m<N>}` model-mangle). Only the
/// token's interned `name` changes; its start/end (display span) stay.
fn setSyntheticName(decl: *ast.Decl, name: StrId) void {
    switch (decl.*) {
        .axiom, .hole => |*a| switch (a.*) {
            .local => |*f| f.name.name = name,
            .alias => {},
        },
        .theorem => |*t| switch (t.*) {
            .local => |*l| l.fact.name.name = name,
            .alias => {},
        },
        else => {},
    }
}

/// The `using <accelerant>` justification (process): the instance fact is proven (read pass);
/// emit `schema_instance` citing the accelerant's premise refs — the kernel peels the
/// instance's `->` antecedents against them and requires the final consequent == the claim.
fn lowerUsing(self: *Prove, w: *const Walk, e: *Elab, kb: kernel.BlockId, goal: TermId, c: ast.Step.Claim) Error!kernel.Justification {
    const outcome = try self.demandUsing(w, e, goal, c);
    const fact = switch (outcome) {
        .proven => |ix| blk: {
            // the generated proof's own dependencies are this proof's (the `--axioms` report and
            // the hole blast-radius both follow the certificate, not the surface).
            self.inheritHoles(ix);
            self.inheritAxioms(ix);
            break :blk ix;
        },
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: accelerant instance not resolved before process (read-pass bug)", .{}),
    };
    const formula_off = self.ctx.interner.keyOf(fact).fact.formula;
    const instance = try self.pool.copyIn(self.ctx.interner, formula_off);
    // premises = the accelerant's own refs (the producer's premise order): the head-cite (if
    // the head is local) then the hyps, matching the synthetic body's antecedent order.
    const prems = try self.accelerantPremises(w, c);
    return self.withGuardPremises(kb, c.rule.start, instance, goal, prems);
}

/// The `schema_instance` justification for a proven instance, discharging its GUARD PREMISES.
/// Under a model transfer an instance's stated formula leads with `guard(arg) ->` for each
/// value param whose image sort is refined (injected by the instance ProveTask — the r-values
/// of a model live in its parent space, so these are the parent's guard predicates) — leading
/// antecedents with no caller ref. Count them (peel the `->` chain until the remainder
/// α-matches the goal; guards = total − the ref premises) and SYNTHESIZE a discharge step for
/// each in the CALLER's context: the enclosing fix-block guard, or closure recursion for a
/// composite (`emitDischargeStep`). Shared by the accelerant (`lowerUsing`) and the user
/// `[using instantiation …]` (`lowerInstantiate`) sites.
fn withGuardPremises(self: *Prove, kb: kernel.BlockId, loc: u32, instance: TermId, goal: TermId, prems: []const kernel.SRef) Error!kernel.Justification {
    var total: usize = 0;
    var walk_f = instance;
    while (!self.pool.alphaEq(walk_f, goal)) {
        const n = self.pool.get(walk_f);
        if (n != .bin or n.bin.op != .implies) break;
        total += 1;
        walk_f = n.bin.rhs;
    }
    if (total > prems.len) {
        // more antecedents than refs, and the remainder never reached the claim: the claim
        // is not this instance's conclusion at all (say so, rather than failing to discharge
        // an antecedent that was never a guard).
        if (!self.pool.alphaEq(walk_f, goal))
            return self.fail(loc, "the claim does not match the instance's conclusion:\n  claim:      {s}\n  instance:   {s}", .{ try self.renderTerm(goal), try self.renderTerm(instance) });
        const k = total - prems.len;
        const all = try self.ctx.arena.alloc(kernel.SRef, total);
        // MATCH BY POSITION, NOT BY PREFIX. The guards are not always a leading run: an
        // instance's param guards are injected in PARAM order, and `freeFvarParams` APPENDS
        // the args' free variables after the schema's own params — so for a LOCAL-head
        // `specialize` under a guarded model the chain is
        //   head -> guard(freevar) -> hyp -> goal
        // with the guard in position 1. Walking the first k antecedents as guards then tries
        // to discharge the HEAD and fails ("cannot discharge the guard premise", or a premise
        // mismatch downstream). Instead, walk the whole chain and at each antecedent take the
        // next caller ref when it MATCHES, else synthesize a discharge. (drafts/
        // guard-relativization-bug/)
        var gf = instance;
        var pi: usize = 0;
        for (0..total) |i| {
            const n = self.pool.get(gf);
            const ant = n.bin.lhs;
            if (pi < prems.len and
                self.pool.alphaEq(self.low_steps.items[@intFromEnum(prems[pi].id)].formula, ant))
            {
                all[i] = prems[pi];
                pi += 1;
            } else {
                all[i] = (try self.emitDischargeStep(kb, loc, ant)) orelse
                    return self.fail(loc, "cannot discharge the guard premise '{s}' at this call site", .{try self.renderTerm(ant)});
            }
            gf = n.bin.rhs;
        }
        if (pi != prems.len) {
            return self.fail(loc, "instantiate: {d} of {d} cited premise(s) matched no antecedent of '{s}'", .{ prems.len - pi, prems.len, try self.renderTerm(instance) });
        }
        _ = k;
        return .{ .schema_instance = .{ .instance = instance, .premises = all } };
    }
    return .{ .schema_instance = .{ .instance = instance, .premises = prems } };
}

/// Dispatch to the accelerant's producer by rule name. Returns null if the producer
/// diagnosed (a Recover is mapped to null by the caller). Add new accelerants here.
fn produceAccelerant(self: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    _ = e;
    const tactic = self.tacticOf(c) orelse
        return self.fail(c.rule.start, "unsupported by the demand prover: '{s}'", .{self.text(c.rule)});
    return switch (tactic) {
        inline else => |a| a.certify(self, w, goal, c),
    };
}

/// The premise refs an accelerant's `schema_instance` discharges, in the synthetic body's
/// antecedent order. Each accelerant's body has a matching antecedent order:
///   - tautology: exactly the cited refs (the schema body's `prem0 -> … -> goal`), no head.
///   - simplify(_quantified): only the LOCAL cited rules (a global rule is cited INSIDE the
///     synthetic proof, not discharged here) — matching `produceSimplify`'s antecedents.
///   - specialize: the head-cite step (only when the head is LOCAL — a global head is cited
///     inside the synthetic proof, not discharged here) followed by the hyps.
fn accelerantPremises(self: *Prove, w: *const Walk, c: ast.Step.Claim) Error![]const kernel.SRef {
    const tactic = self.tacticOf(c) orelse return self.fail(c.rule.start, "internal: premises of a non-accelerant step", .{});
    switch (tactic.premiseShape()) {
        // the LOCAL equation refs are the antecedents (globals — a lemma arg, an AC triple,
        // distribute pre-rules, well-known ring lemmas — are cited inside the cert) — except
        // any the producer DROPPED (a cited rule its cert never fired): it recorded the
        // surviving refs, and the instance's antecedents match those exactly.
        .local_refs_kept => {
            if (self.producer_premise_refs) |kept| return self.localRefsToSteps(w, kept);
            return self.localRefsToSteps(w, c.refs);
        },
        // no head: the antecedents ARE the cited refs, in order.
        .refs_in_order => {
            const out = try self.ctx.arena.alloc(kernel.SRef, c.refs.len);
            for (c.refs, out) |r, *o| o.* = try self.resolveStepRef(w, r);
            return out;
        },
        // head in `c.schema`, hyps in `c.refs`. A LOCAL head becomes the FIRST premise (its
        // formula is the synthetic schema's first antecedent); a GLOBAL head is not a premise.
        .head_then_refs => {
            const head = c.schema orelse return self.fail(c.rule.start, "internal: head-shaped premises without a head", .{});
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
        },
    }
}

/// Intern a comptime literal once (cached on the Context's interner; cheap dedup).
pub fn internStr(self: *Prove, comptime s: []const u8) Error!StrId {
    return self.ctx.interner.internString(s) catch error.OutOfMemory;
}

// -- scaffolding helpers the tactics call (the producers live in Accelerants/) ---------

/// `ants[0] -> ants[1] -> … -> consequent` as an AST expr (right-assoc `->`).
/// The OBLIGATIONS a synthetic's terms owe: for every term the producer delaborated (`seen`),
/// each guarded application's required proposition (a refined param's qualifier at the arg, a
/// `requires` guard at the args) — deduplicated by identity, in first-seen order. Only locally
/// closed subterms count (a proposition over a bound variable is a statement's business).
fn syntheticObligations(self: *Prove, w: *const Walk, seen: []const TermId) Error![]const TermId {
    var e = self.elab(w);
    e.known = null;
    var all: std.ArrayList(TermId) = .empty;
    for (seen) |t| try e.collectObligations(t, &all, true);
    // an obligation the synthetic CONTAINS as a conjunct of one of its formulas (a premise
    // `is_nonneg(m) and (… at(t, m) …)`, whose assumption teaches every conjunct; a goal it
    // proves) is its own business — a producer that delaborates a premise's atoms one by one
    // loses that context, so it is recovered here. It is NOT the caller's; the caller may not
    // even be able to name it.
    var internal: std.ArrayList(TermId) = .empty;
    for (seen) |t| try e.conjuncts(t, &internal);
    var out: std.ArrayList(TermId) = .empty;
    for (all.items) |p| {
        const contained = for (internal.items) |x| (if (x == p) break true) else false;
        if (!contained) try out.append(self.ctx.arena, p);
    }
    return out.items;
}

/// Prepend a synthetic's obligations as LEADING ANTECEDENTS of its schema body, `assume`d around
/// its proof (so every step inside knows them, as the citing proof did), and exported back out by
/// `discharge`. The call site discharges them from what it knows (`withGuardPremises` →
/// `refForKnown`), exactly like the premises it cites. The generated theorem thereby states the
/// preconditions of the terms it mentions instead of re-owing them where nothing can teach them.
fn wrapObligations(self: *Prove, b: *Accelerant.Builder, decl: ast.Decl, obls: []const TermId) Error!ast.Decl {
    if (obls.len == 0) return decl;
    const local = decl.theorem.local; // a producer's synthetic is always a local theorem
    var body = local.fact.formula;
    var steps = local.steps;
    var i = obls.len;
    while (i > 0) {
        i -= 1;
        const blk = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "obligation{d}", .{i}));
        const opened = try b.assumeStep(blk, try b.termExpr(obls[i]), steps);
        const exported = try b.implies(try b.termExpr(obls[i]), body);
        const export_label = if (i == 0) try b.intern("conclusion") else try b.intern(try std.fmt.allocPrint(self.ctx.arena, "obligation-export{d}", .{i}));
        const closed = try b.claimStep(export_label, exported, .by, try self.internStr("discharge"), &.{}, try common.oneRef(self, b, blk));
        const pair = try self.ctx.arena.alloc(ast.Step, 2);
        pair[0] = opened;
        pair[1] = closed;
        steps = pair;
        body = exported;
    }
    return .{ .theorem = .{ .local = .{ .fact = .{ .name = local.fact.name, .formula = body, .params = local.fact.params }, .steps = steps } } };
}

/// An SRef proving `prop` in block `kb`, from what the proof KNOWS (identity lookup — never a
/// search): a teaching STEP is cited directly (and marked consumed); a teaching BLOCK's
/// hypothesis is restated as a synthetic `hypothesis` step — the assumption itself, a refined
/// GUARD-ARITY PROJECTION for `[by predicate]` / `[by hypothesis]` on a refined `fix`.
///
/// The step claims `goal`; the block's guard is `whole`. When they are equal the plain
/// `.hypothesis` justification is right and this returns null. When `goal` is a strict
/// CONJUNCT of `whole`, the claim is still true and this builds the derivation: restate
/// `whole` by hypothesis, then `and_elim` down to `goal`'s PARENT, and return the final
/// `and_lhs`/`and_rhs` as the claim's own justification.
///
/// WHY THIS EXISTS. A guarded model transfer injects every qualifier on the target sort's
/// refinement chain, conjoined. A source theory written against a single-qualifier sort
/// (`Sub = Grp where inSubgroup`) therefore claims ONE conjunct where the transferred binder
/// carries SEVERAL — which happens exactly when the target's base sort is itself refined
/// (`Perm = Fn where invertible`). Without the projection such a theory can only be modeled
/// onto a universal base.
///
/// SOUNDNESS NOTE, and the current limit: this projects a conjunction DOWN to a conjunct, so
/// every step it licenses was already derivable — the kernel re-checks each `and_lhs`/`and_rhs`
/// it emits. What the engine does NOT yet check is the converse direction: a model may FORGET
/// to overload a guard predicate, and nothing here detects that. Those guarantees are future
/// work (see drafts/normality-as-a-model/).
fn projectBlockGuard(self: *Prove, kb: kernel.BlockId, bref: kernel.BRef, goal: TermId) Error!?kernel.Justification {
    const b = self.low_blocks.items[@intFromEnum(bref.id)];
    const whole = switch (b.kind) {
        .fix => |fx| fx.guard orelse return null,
        .assume => |a| a,
        // AN UNPACK BLOCK'S HYPOTHESIS IS ALSO A CONJUNCTION TO PROJECT FROM. Under a model
        // transfer a relativized `∃x: H` opens as `inH(w) and <body>`, so a `[by hypothesis]`
        // restating just `<body>` — which is what the SOURCE proof wrote — must and_elim past
        // the guard conjunct. `refForKnown` already did this for a KNOWN prop; without it here
        // the explicit hypothesis restatement inside a transferred unpack fails, which is how
        // every ℤ-order theorem citing `lessThanElim` broke (std/integer/order.b4m:802).
        .unpack => |uv| blk: {
            const src_f = self.low_steps.items[@intFromEnum(uv.source.id)].formula;
            const sn = self.pool.get(src_f);
            if (sn != .quant or sn.quant.q != .exists) return null;
            break :blk try self.pool.open(sn.quant.body, try self.pool.add(.{ .fvar = uv.v }));
        },
        else => return null,
    };
    if (whole == goal) return null; // the plain hypothesis arm handles it
    var path: std.ArrayList(bool) = .empty;
    if (!try self.conjunctPath(whole, goal, &path)) return null;
    if (path.items.len == 0) return null;
    // restate the whole guard, then and_elim down to the claim's PARENT; the last turn
    // becomes the claim's own justification.
    var step = try self.emitSynthetic(kb, bref.loc, whole, .{ .hypothesis = bref });
    var cur = whole;
    for (path.items[0 .. path.items.len - 1]) |left| {
        const n = self.pool.get(cur);
        cur = if (left) n.bin.lhs else n.bin.rhs;
        step = try self.emitSynthetic(kb, bref.loc, cur, if (left) .{ .and_lhs = step } else .{ .and_rhs = step });
    }
    return if (path.items[path.items.len - 1]) .{ .and_lhs = step } else .{ .and_rhs = step };
}

/// binder's guard (a multi-qualifier guard's conjunct extracted), an unpack witness's guard
/// conjunct. Null when nothing taught it here (a refined result's closure fact has no step).
fn refForKnown(self: *Prove, kb: kernel.BlockId, loc: u32, prop: TermId) Error!?kernel.SRef {
    const t = self.known.lookup(prop, kb) orelse return null;
    if (t.step) |s| {
        try self.known.reachable.append(self.ctx.arena, s);
        const whole = self.low_steps.items[s].formula;
        if (whole == prop) return .{ .id = @enumFromInt(s), .loc = loc };
        // taught as a CONJUNCT of that step: and_elim down to it.
        return try self.emitConjunctExtractFrom(kb, loc, whole, prop, .{ .id = @enumFromInt(s), .loc = loc });
    }
    const b = self.low_blocks.items[@intFromEnum(t.block)];
    switch (b.kind) {
        .assume => |a| {
            if (a == prop) return try self.emitSynthetic(kb, loc, prop, .{ .hypothesis = .{ .id = t.block, .loc = loc } });
            return try self.emitConjunctExtract(kb, loc, a, prop, t.block);
        },
        .fix => |fx| {
            const g = fx.guard orelse return null;
            if (g == prop) return try self.emitSynthetic(kb, loc, prop, .{ .hypothesis = .{ .id = t.block, .loc = loc } });
            return try self.emitConjunctExtract(kb, loc, g, prop, t.block);
        },
        .unpack => |uv| {
            // the unpacked hypothesis is the opened existential body `guard and P(w)`.
            const src_f = self.low_steps.items[@intFromEnum(uv.source.id)].formula;
            const sn = self.pool.get(src_f);
            if (sn != .quant or sn.quant.q != .exists) return null;
            const hyp = try self.pool.open(sn.quant.body, try self.pool.add(.{ .fvar = uv.v }));
            if (hyp == prop) return try self.emitSynthetic(kb, loc, prop, .{ .hypothesis = .{ .id = t.block, .loc = loc } });
            return try self.emitConjunctExtract(kb, loc, hyp, prop, t.block);
        },
        .root => return null,
    }
}

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

/// Collect distinct free fvars (by name) into `out`.
/// Collect the DISTINCT free vars of `id` into `out` (on the caller's arena). Iterative work-stack
/// (was native recursion) — depth-safe. The frontier stack is GPA-backed scratch (reclaimed here);
/// `out` stays durable. (Note: this collects fvars regardless of binder depth — a "free var" here
/// is any `.fvar` node, matching the original; bound vars are `.bvar` and contribute nothing.)
pub fn collectFreeFvars(self: *Prove, id: TermId, out: *std.ArrayList(term.Node.Fvar)) Error!void {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(a, id);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        switch (node) {
            .fvar => |v| {
                var seen = false;
                for (out.items) |e| if (e.name == v.name) {
                    seen = true;
                    break;
                };
                if (!seen) try out.append(self.ctx.arena, v);
            },
            else => try self.pool.pushChildren(&stack, a, node),
        }
    }
}

// -- justification lowering ------------------------------------------------------------

pub fn isBiconditionalShape(self: *const Prove, id: TermId) bool {
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

/// ADMIT a trusted `using` step: accept it WITHOUT generating/checking its proof. What
/// "admit" MEANS is the word's own business — it is NOT necessarily a shape check:
///   - accelerant: run the PRODUCER in ADMIT MODE (`self.admit_mode`), so each accelerant does
///     ITS OWN cheap acceptance (usually but not always a goal-shape match) and returns before
///     building any certificate. The accelerant owns what it trusts.
///   - model / import: elaborate the transferred / imported STATEMENT and α-match the claim.
///   - instantiation: elaborate the schema BODY at the bound args and α-match the claim (after
///     peeling the cited premises off the instance's `->` prefix).
/// Diagnoses + `error.Recover` on rejection (never silently accepts). The AST it reads was made
/// available by `trustedReadPass` (parse + ident resolution); this pass performs NO proof demand.
fn admit(self: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    const word = self.trustWord(c) orelse
        return self.fail(c.rule.start, "internal: admit on a non-using step", .{});
    switch (word) {
        // model: the transferred statement = the source theorem elaborated under M's overlay
        // (relativization included). α-match the claim.
        .model => try self.admitModel(goal, c),
        // import: the imported statement, elaborated in I's namespace (no model). α-match.
        .import => try self.admitImport(goal, c),
        // an accelerated tactic admits the claim on ITS OWN terms: its phase-2 `decide`.
        else => {
            const tactic = Tactic.of(word).?; // every non-engine word is a variant
            const decided: Error!void = switch (tactic) {
                inline else => |a| a.decide(self, w, e, goal, c),
            };
            decided catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => {
                    // A PARK during decide has no channel to propagate (this returns void), and
                    // should never happen: the READ PASS is where an admitted word's demands are
                    // racked. Reaching here parked means it missed one — a bug worth a visible
                    // diagnostic, not a silent reject (which drops the step's label).
                    if (self.producer_blocker != null) {
                        self.producer_blocker = null;
                        return self.fail(c.rule.start, "internal: '{s}' parked during admit (the read pass missed a demand)", .{self.text(c.rule)});
                    }
                    return error.Recover;
                },
            };
            // An admitted tactic builds no certificate, so nothing carries the citation edges
            // its premises would have had: its cited LOCAL steps are its use-all-facts roots (a
            // global fact cited by name is not a step and needs no root). What the schema slot
            // holds — whether it must resolve, and whether it can be a local step at all — is
            // the tactic's `schema_slot`, read off its type: a `head` is a fact-or-step that
            // must resolve (a typo'd head would otherwise pass `--fast` and fail strict); a
            // `lemma` may be local but a miss is left for strict; a `theory_selector` is an
            // import, never a step.
            if (c.schema) |t| switch (tactic.schemaSlot()) {
                .head => try self.seedAndCheckLocalRoot(w, t),
                .lemma => self.seedLocalRoot(w, t) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.Recover => {},
                },
                .theory_selector, .none => {},
            };
            // A `ns.`-QUALIFIED ref names a global fact, never a local step, so it contributes
            // no root — but it must still RESOLVE; `seedAndCheckLocalRoot` does both.
            for (c.refs) |r| try self.seedAndCheckLocalRoot(w, r);
        },
    }
}

/// Admit `[using model(M) src.thm]`: elaborate `src.thm`'s statement under M's overlay and
/// α-match `goal` (the claim). Uses the shared `elaborateFactStatement` — the SAME relativization
/// the strict transfer applies to the statement — so no divergence.
fn admitModel(self: *Prove, goal: TermId, c: ast.Step.Claim) Error!void {
    if (c.schema == null) return self.fail(c.rule.start, "model citation requires a model name: `[using model(M) src.thm]`", .{});
    if (c.refs.len != 1) return self.fail(c.rule.start, "`[using model(M) …]` cites exactly one transferred theorem", .{});
    const mtok = c.schema.?;
    // a QUALIFIED model name (`I.M`) resolves in I's namespace — same as the strict path.
    const model_ns = if (mtok.qualifier == InternPool.Index.none) self.ns else blk: {
        const qf = (try self.qualifierFile(mtok)) orelse
            return self.fail(mtok.start, "unknown namespace '{s}'", .{self.ctx.interner.stringBytes(mtok.qualifier)});
        break :blk self.ctx.interner.namespace(.universe, qf) catch return error.OutOfMemory;
    };
    const mstate = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = model_ns, .name = tokName(mtok) }) orelse
        return self.fail(mtok.start, "unknown model '{s}'", .{self.text(mtok)});
    const model_ix = switch (mstate) {
        .done => |ix| ix,
        .in_flight => return self.fail(mtok.start, "unknown model '{s}'", .{self.text(mtok)}),
    };
    if (self.ctx.interner.keyOf(model_ix) != .model)
        return self.fail(mtok.start, "'{s}' is not a model", .{self.text(mtok)});
    const rtok = c.refs[0];
    const src_file = if (rtok.qualifier == InternPool.Index.none) self.file else (try self.qualifierFile(rtok)) orelse
        return self.fail(rtok.start, "unknown namespace '{s}'", .{self.ctx.interner.stringBytes(rtok.qualifier)});
    switch (try elaborateFactStatement(self.ctx, self.h, src_file, tokName(rtok), model_ix, self.pool)) {
        .ready => |stmt| if (!self.pool.alphaEq(stmt, goal))
            return self.fail(c.rule.start, "the claim does not match the model transfer of '{s}':\n  claim:      {s}\n  transfer:   {s}", .{ self.text(rtok), try self.renderTerm(goal), try self.renderTerm(stmt) }),
        .suspended => return self.fail(c.rule.start, "internal: model admission not resolved before process (read-pass bug)", .{}),
        .failed => return error.Recover,
    }
}

/// Shape-check `[using import(I) thm]`: elaborate `thm`'s statement in I's file (no model) and
/// α-match `goal`.
fn admitImport(self: *Prove, goal: TermId, c: ast.Step.Claim) Error!void {
    const itok = c.schema orelse return self.fail(c.rule.start, "import citation requires an import name: `[using import(I) thm]`", .{});
    if (c.refs.len != 1) return self.fail(c.rule.start, "`[using import(I) …]` cites exactly one imported theorem", .{});
    const rtok = c.refs[0];
    const ifile = (try self.importFile(itok)) orelse return self.fail(itok.start, "unknown import '{s}'", .{self.text(itok)});
    switch (try elaborateFactStatement(self.ctx, self.h, ifile, tokName(rtok), .universe, self.pool)) {
        .ready => |stmt| if (!self.pool.alphaEq(stmt, goal))
            return self.fail(c.rule.start, "the claim does not match imported '{s}.{s}':\n  claim:    {s}\n  imported: {s}", .{ self.text(itok), self.text(rtok), try self.renderTerm(goal), try self.renderTerm(stmt) }),
        .suspended => return self.fail(c.rule.start, "internal: import admission not resolved before process (read-pass bug)", .{}),
        .failed => return error.Recover,
    }
}

fn lowerJustification(self: *Prove, w: *const Walk, e: *Elab, kb: kernel.BlockId, goal: TermId, c: ast.Step.Claim) Error!kernel.Justification {
    // TRUSTED (`--fast <word>`): the step is accelerated — its proof is NOT generated/checked.
    // The word ADMITS the step (its own fast check / an α-match), then we emit `.accelerated`
    // (the kernel checks nothing for it) and RECORD the word (for the summary disclosure). `by`
    // primitives never reach here trusted (trustWord returns null). Publishes nothing; a later
    // strict demand redoes the work.
    if (self.trusted(c)) {
        const schema_transfer = if (self.trustWord(c)) |wd| wd == .model and (try self.transfersSchema(c)) == .yes else false;
        if (!schema_transfer) {
            try self.admit(w, e, goal, c);
            if (self.trustWord(c)) |word| self.admitted.insert(word);
            // RECORD the cited steps: `.accelerated` keeps only the tactic name, so without
            // this the use-all-facts walk cannot see what an admitted accelerant consumed and
            // reports its refs dead — an error strict never gives. Refs that do not resolve to
            // a step (a block, a fact name) are skipped: the admitted step is not being
            // checked here, and strict is what diagnoses a bad ref.
            return .{ .accelerated = c.rule.name };
        }
    }
    // An ACCELERANT (`using <accel> …`) lowers to a schema_instance over its generated
    // synthetic schema (the instance was demanded + proven in the read pass).
    if (c.kind == .using and isAccelerant(c.rule.name)) return self.lowerUsing(w, e, kb, goal, c);
    // Otherwise the rule word dispatches by its RESERVED StrId (integer comparison — no
    // strcmp past parsing); a non-rule word here is a typo.
    const kind = InternPool.RuleStr.of(c.rule.name) orelse {
        return self.fail(c.rule.start, "unsupported by the demand prover: '{s}'", .{self.text(c.rule)});
    };
    switch (kind) {
        // `instantiation` resolves a SCHEMA (not a kernel rule) — the instance fact was
        // demanded (racked + proven) in the read pass; look it up, copyIn its formula, and
        // emit the kernel schema_instance justification (peels premises against `c.refs`).
        .instantiation => return self.lowerInstantiate(w, e, kb, goal, c),
        // `using model(M) src.thm` transfers a source theorem: the transferred fact was
        // demanded (proved in namespace (M, src_file)) in the read pass; cite it.
        .model => return self.lowerModel(kb, goal, c),
        // `using import(I) thm` cites an imported theorem across the file boundary — the
        // explicit accelerant seam (the read pass demanded `thm` in I's namespace); cite it.
        .import => return self.lowerImport(c),
        else => {},
    }
    const wants_args: usize = switch (kind) {
        .apply_at => if (c.args.len == 0) 1 else c.args.len,
        .witness => 1,
        else => 0,
    };
    if (c.args.len != wants_args) {
        return self.fail(c.rule.start, "'{s}' expects {d} argument(s), got {d}", .{
            self.text(c.rule), wants_args, c.args.len,
        });
    }
    switch (kind) {
        .instantiation, .model, .import => unreachable, // dispatched above
        // `[by definition p]` / `[by definition(N) f]` — cite a clause axiom a definition
        // block emitted. The fact is found by RE-MANGLING (symbol, arm), never by search:
        // the parser published it under `definition{<name>}{<arm>}`, a spelling no source
        // identifier can have. `(N)` is zero-indexed and selects a function's clause; a
        // predicate has one clause and is cited bare (arm 0).
        .definition => {
            try self.wantRefs(c, 1);
            const rtok = c.refs[0];
            const arm: usize = if (c.schema) |a| blk: {
                const txt = self.text(a);
                break :blk std.fmt.parseInt(usize, txt, 10) catch {
                    return self.fail(a.start, "`[by definition(N) …]` takes a clause NUMBER (zero-indexed); got '{s}'", .{txt});
                };
            } else 0;
            const mangled_id = self.ctx.interner.definitionClauseName(self.ctx.arena, self.text(rtok), arm) catch return error.OutOfMemory;
            var lookup = rtok;
            lookup.name = mangled_id;
            const stmt = self.resolveFactRef(lookup) catch |err| switch (err) {
                error.Recover => return self.fail(rtok.start, "'{s}' has no definition clause {d} (a definition block publishes one clause per arm, numbered from 0)", .{ self.text(rtok), arm }),
                else => return err,
            };
            return .{ .cite_ref = .{ .stmt = stmt, .loc = rtok.start } };
        },
        .axiom, .theorem, .cite => {
            try self.wantRefs(c, 1);
            const stmt = try self.resolveFactRef(c.refs[0]);
            const loc = c.refs[0].start;
            // AUTO-WEAKENING (model transfer): a source axiom holding UNCONDITIONALLY on the
            // carrier, mapped to itself, has a RELATIVIZED step claim `∀v; guard(v) -> …` while
            // the fact derives the bare `∀v; …`. Since `∀v; P ⊢ ∀v; guard(v) -> P`, synthesize the
            // weakening (nested guarded `fix` + cite + multi-arg apply_at + generalize).
            if (self.model != InternPool.Index.none and self.model != .universe) {
                const fact_f = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(stmt).fact.formula);
                if (!self.pool.alphaEq(fact_f, goal)) {
                    if (try self.emitWeakening(kb, loc, stmt, fact_f, goal)) |just| return just;
                }
            }
            return .{ .cite_ref = .{ .stmt = stmt, .loc = loc } };
        },
        .hypothesis, .predicate => {
            try self.wantRefs(c, 1);
            const bref = try self.resolveBlockRef(w, c.refs[0]);
            // GUARD-ARITY PROJECTION. A `[by predicate <fix>]` (or `[by hypothesis]` on a
            // refined `fix`) claims the binder's guard. Under a GUARDED MODEL TRANSFER whose
            // target sort refines a base that is ITSELF refined, the binder's guard is the
            // CONJUNCTION of every qualifier on the chain, while the source proof — written
            // against its own single-qualifier sort — claims one conjunct. The claim is still
            // true, so project: and_elim down the conjunction to the claimed conjunct.
            //
            // Without this a source theory can only be modeled onto a sort whose base is
            // UNIVERSAL, which is why `std/subgroup.b4m` would not transfer onto `Perm`
            // (= `Fn where invertible`): `Sub = Grp where inSubgroup` has one qualifier,
            // `Perm where inAlternating` has two. See drafts/normality-as-a-model/.
            if (try self.projectBlockGuard(kb, bref, goal)) |j| return j;
            return .{ .hypothesis = bref };
        },
        .modus_ponens => {
            try self.wantRefs(c, 2);
            return .{ .modus_ponens = .{
                .implication = try self.resolveStepRef(w, c.refs[0]),
                .antecedent = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .discharge => {
            try self.wantRefs(c, 1);
            return .{ .discharge = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .generalize => {
            try self.wantRefs(c, 1);
            return .{ .generalize = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .apply_at => {
            try self.wantRefs(c, 1);
            const start = try self.resolveStepRef(w, c.refs[0]);
            var cur_formula = self.low_steps.items[@intFromEnum(start.id)].formula;
            // Build the elim+discharge chain as a list of ops, each producing a formula from the
            // PREVIOUS step: an `elim` opens a `∀` at an arg; a `discharge` strips a leaked
            // refined-sort guard (`guard(t) -> …`, from a `∀x:H` stored `∀x; guard(x) -> …`) via
            // modus_ponens against a proof of the guard. A multi-guard / nested-binder sort leaks a
            // CHAIN of guards interleaved with binders — strip each before opening the next binder,
            // and any trailing guards after the last. FLUSH emits all but the last op as synthetics
            // and returns the last as the claim's justification (no reiterate rule exists).
            const Op = union(enum) {
                elim: struct { arg: TermId, loc: u32 },
                discharge: struct { guard: kernel.SRef, result: TermId, loc: u32 },
            };
            var ops: std.ArrayList(Op) = .empty;

            // strip leading guards off cur_formula, appending discharge ops; stops at a non-`->`
            // head, at the goal, or at a leading `->` whose antecedent isn't a dischargeable guard.
            const stripGuards = struct {
                fn run(s: *Prove, b: kernel.BlockId, g: TermId, cf: *TermId, list: *std.ArrayList(Op), loc: u32) Error!void {
                    while (true) {
                        const n = s.pool.get(cf.*);
                        if (s.pool.alphaEq(cf.*, g)) return;
                        if (n != .bin or n.bin.op != .implies) return;
                        const gstep = (try s.emitDischargeStep(b, loc, n.bin.lhs)) orelse return;
                        try list.append(s.ctx.arena, .{ .discharge = .{ .guard = gstep, .result = n.bin.rhs, .loc = loc } });
                        cf.* = n.bin.rhs;
                    }
                }
            }.run;

            for (c.args) |arg_expr| {
                const aloc = Elab.exprLoc(arg_expr);
                try stripGuards(self, kb, goal, &cur_formula, &ops, aloc);
                const node = self.pool.get(cur_formula);
                if (node != .quant or node.quant.q != .forall) {
                    return self.fail(aloc, "apply_at: '{s}' is not universally quantified here", .{try self.renderTerm(cur_formula)});
                }
                const arg = (try e.elaborateExpr(arg_expr)).id;
                try ops.append(self.ctx.arena, .{ .elim = .{ .arg = arg, .loc = aloc } });
                cur_formula = try self.pool.open(node.quant.body, arg);
            }
            const last_loc = Elab.exprLoc(c.args[c.args.len - 1]);
            try stripGuards(self, kb, goal, &cur_formula, &ops, last_loc);

            // FLUSH: emit ops[0..n-1] as synthetics; the last op's justification is the claim's.
            std.debug.assert(ops.items.len > 0);
            var cur = start;
            var cur_f = self.low_steps.items[@intFromEnum(start.id)].formula;
            for (ops.items, 0..) |op, i| {
                const result: TermId, const just: kernel.Justification = switch (op) {
                    .elim => |el| .{ try self.pool.open(self.pool.get(cur_f).quant.body, el.arg), .{ .apply_at = .{ .step = cur, .with = el.arg, .with_loc = el.loc } } },
                    .discharge => |d| .{ d.result, .{ .modus_ponens = .{ .implication = cur, .antecedent = d.guard } } },
                };
                if (i == ops.items.len - 1) return just;
                cur = try self.emitSynthetic(kb, switch (op) {
                    .elim => |el| el.loc,
                    .discharge => |d| d.loc,
                }, result, just);
                cur_f = result;
            }
            unreachable; // ops is non-empty; the last iteration returns
        },
        .witness => {
            try self.wantRefs(c, 1);
            const arg = try e.elaborateExpr(c.args[0]);
            const aloc = Elab.exprLoc(c.args[0]);
            var step = try self.resolveStepRef(w, c.refs[0]);
            // RELATIVIZED ∃ (model transfer): the goal `∃x; good(x) and P(x)` opens at the witness
            // to `good(w) and P(w)`, but the cited step provides only `P(w)`. Re-conjoin the guard:
            // discharge `good(w)` (source 2b — the witness's own unpack carries it) and both it
            // onto the step, so witness witnesses the full relativized body.
            const gnode = self.pool.get(goal);
            if (gnode == .quant and gnode.quant.q == .exists) {
                const body = try self.pool.open(gnode.quant.body, arg.id);
                const bn = self.pool.get(body);
                const step_f = self.low_steps.items[@intFromEnum(step.id)].formula;
                if (bn == .bin and bn.bin.op == .and_op and !self.pool.alphaEq(step_f, body) and self.pool.alphaEq(bn.bin.rhs, step_f)) {
                    if (try self.emitDischargeStep(kb, aloc, bn.bin.lhs)) |g_step| {
                        step = try self.emitSynthetic(kb, aloc, body, .{ .both = .{ .left = g_step, .right = step } });
                    }
                }
            }
            return .{ .witness = .{
                .step = step,
                .witness = arg.id,
                .witness_loc = aloc,
            } };
        },
        .unpacked => {
            try self.wantRefs(c, 1);
            return .{ .unpacked = try self.resolveBlockRef(w, c.refs[0]) };
        },
        .both => {
            try self.wantRefs(c, 2);
            if (self.isBiconditionalShape(goal)) {
                return self.fail(c.rule.start, "this goal is a biconditional '(X -> Y) and (Y -> X)' — use `make_equivalence` (which is the same rule, named for what it proves)", .{});
            }
            return .{ .both = .{
                .left = try self.resolveStepRef(w, c.refs[0]),
                .right = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .and_lhs => {
            try self.wantRefs(c, 1);
            return .{ .and_lhs = try self.resolveStepRef(w, c.refs[0]) };
        },
        .and_rhs => {
            try self.wantRefs(c, 1);
            return .{ .and_rhs = try self.resolveStepRef(w, c.refs[0]) };
        },
        .make_equivalence => {
            try self.wantRefs(c, 2);
            if (!self.isBiconditionalShape(goal)) {
                return self.fail(c.rule.start, "make_equivalence's goal must be a biconditional (from `P iff Q`); this goal is not of the form '(X -> Y) and (Y -> X)' — did you mean `both`?", .{});
            }
            return .{ .both = .{
                .left = try self.resolveStepRef(w, c.refs[0]),
                .right = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .equiv_forward => {
            try self.wantRefs(c, 1);
            return .{ .and_lhs = try self.resolveStepRef(w, c.refs[0]) };
        },
        .equiv_converse => {
            try self.wantRefs(c, 1);
            return .{ .and_rhs = try self.resolveStepRef(w, c.refs[0]) };
        },
        .either_left => {
            try self.wantRefs(c, 1);
            return .{ .either_left = try self.resolveStepRef(w, c.refs[0]) };
        },
        .either_right => {
            try self.wantRefs(c, 1);
            return .{ .either_right = try self.resolveStepRef(w, c.refs[0]) };
        },
        .common_conclusion => {
            try self.wantRefs(c, 3);
            return .{ .common_conclusion = .{
                .disj = try self.resolveStepRef(w, c.refs[0]),
                .left = try self.resolveBlockRef(w, c.refs[1]),
                .right = try self.resolveBlockRef(w, c.refs[2]),
            } };
        },
        .contradiction => {
            try self.wantRefs(c, 3);
            return .{ .contradiction = .{
                .block = try self.resolveBlockRef(w, c.refs[0]),
                .s1 = try self.resolveStepRef(w, c.refs[1]),
                .s2 = try self.resolveStepRef(w, c.refs[2]),
            } };
        },
        .ex_falso => {
            try self.wantRefs(c, 2);
            return .{ .ex_falso = .{
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
            // ONE REF = CONGRUENCE. `[by rewrite EQ]` on a claim `lhs = rhs` means "the target
            // is this claim's own reflexive instance": synthesize `lhs = lhs` by reflexivity
            // and rewrite in THAT. Hand-rolling it costs two steps, the first of which asserts
            // nothing — 265 of std's 376 `reflexivity` steps exist only to serve a following
            // `rewrite`. The TWO-ref form stays: rewriting inside an ALREADY-PROVED fact is a
            // different move.
            if (c.refs.len == 1) {
                const gnode = self.pool.get(goal);
                if (gnode != .eq)
                    return self.fail(c.rule.start, "one-ref 'rewrite' proves a congruence, so the claim must be an equation; got '{s}'", .{try self.renderTerm(goal)});
                const refl = try self.pool.add(.{ .eq = .{ .lhs = gnode.eq.lhs, .rhs = gnode.eq.lhs } });
                const target = try self.emitSynthetic(kb, c.rule.start, refl, .reflexivity);
                return .{ .rewrite = .{
                    .equation = try self.resolveStepRef(w, c.refs[0]),
                    .target = target,
                } };
            }
            try self.wantRefs(c, 2);
            return .{ .rewrite = .{
                .equation = try self.resolveStepRef(w, c.refs[0]),
                .target = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
        .equiv_rewrite => {
            try self.wantRefs(c, 2);
            return .{ .equiv_rewrite = .{
                .biconditional = try self.resolveStepRef(w, c.refs[0]),
                .target = try self.resolveStepRef(w, c.refs[1]),
            } };
        },
    }
}

// -- conclusion ------------------------------------------------------------------------

/// `Model@theorem` when this proof is a model TRANSFER, else empty (an ordinary proof needs
/// no prefix). The model's own name comes off its `.model` Item's home file + name.
fn transferLabel(self: *Prove) []const u8 {
    if (self.model == InternPool.Index.none or self.model == .universe) return "";
    const key = self.self_key orelse return "";
    // A model Item carries no name (it is structural); the NAME lives in IdentKV, in the
    // universe namespace of the file the model was declared in (`home`). Scan that namespace
    // for the entry bound to this model Index. A composed model (a nested transfer) has no
    // declared name — fall back to the theorem alone rather than printing `model#7`.
    const home = self.ctx.interner.keyOf(self.model).model.home;
    const thm = self.ctx.interner.stringBytes(key.name);
    if (home != InternPool.Index.none) {
        const home_ns = self.ctx.interner.namespace(.universe, home) catch return thm;
        if (self.ctx.idents.nameOf(self.ctx.io, home_ns, self.model)) |n| {
            return std.fmt.allocPrint(self.ctx.arena, "{s}@{s}", .{ self.ctx.interner.stringBytes(n), thm }) catch thm;
        }
    }
    return thm;
}

/// Walk done: seal the root, kernel-check the whole lowering against `goal`, then the
/// use-all-facts pass (unless --draft). True iff the theorem is established.
pub fn finish(self: *Prove, goal: TermId, goal_loc: u32) Allocator.Error!bool {
    self.low_blocks.items[0].last_step = @intCast(self.low_steps.items.len);
    var k: kernel.Kernel = .{
        .arena = self.ctx.arena,
        .pool = self.pool,
        .interner = self.ctx.interner,
        .sink = self.ctx.sink,
        // a rejection's offset indexes THIS proof's file, not the demander's
        .file = self.diagFile(),
        // Under a MODEL this proof is a TRANSFER: it re-proves a source theorem with every
        // global redirected through the overlay, so its claims are in TARGET terms while any
        // fact the model does not map is still in SOURCE terms. Label every rejection
        // `Model@theorem` so that is visible — without it the reader sees two formulas in
        // different vocabularies, in a file they did not write, with nothing naming the model.
        .context = self.transferLabel(),
    };
    const proven = try k.check(.{ .steps = self.low_steps.items, .blocks = self.low_blocks.items }, goal, goal_loc);
    if (!proven) return false;
    // The use-all-facts check is a lint over a COMPLETE citation graph, so it is STRICT-ONLY.
    //
    // Some steps are used ONLY WHEN A CERTIFICATE IS GENERATED. A proved step TEACHES its
    // formula to the rest of its block (`teachAll`), and a later guard obligation can be
    // discharged from it with NO citation in the source: `refForKnown` finds the taught fact
    // and appends that step to `known.reachable`, which is what marks it used (see the
    // `reachable` seeding in `checkAllStepsUsed`). That append happens while BUILDING the
    // certificate. Skip the certificate and the edge never forms, so a step the author wired
    // correctly looks dead.
    //
    // Gating on `admitted.count() == 0` was not enough: it made the lint fire or not depending
    // on which tactics a proof happened to use, so the same dead step was caught in a
    // `by`-only proof and missed in one using `specialize`. Keying it on the file's trust set
    // instead makes the rule one sentence — `--fast` does not dead-check — and preserves the
    // invariant that `--fast` never reports an error strict does not.
    if (!self.ctx.verify.draft and self.ctx.verify.trusted.count() == 0) {
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
    for (self.known.reachable.items) |di| try mark(reached, &work, arena, di);
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
            .apply_at => |r| try mark(reached, &work, arena, @intFromEnum(r.step.id)),
            .witness => |r| try mark(reached, &work, arena, @intFromEnum(r.step.id)),
            .both => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.left.id));
                try mark(reached, &work, arena, @intFromEnum(r.right.id));
            },
            .and_lhs, .and_rhs, .either_left, .either_right, .double_negation, .symmetry => |sr| try mark(reached, &work, arena, @intFromEnum(sr.id)),
            .rewrite => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.equation.id));
                try mark(reached, &work, arena, @intFromEnum(r.target.id));
            },
            .equiv_rewrite => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.biconditional.id));
                try mark(reached, &work, arena, @intFromEnum(r.target.id));
            },
            .ex_falso => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.s1.id));
                try mark(reached, &work, arena, @intFromEnum(r.s2.id));
            },
            .contradiction => |r| {
                if (lastStepOf(blocks, r.block.id)) |ls| try mark(reached, &work, arena, ls);
                try mark(reached, &work, arena, @intFromEnum(r.s1.id));
                try mark(reached, &work, arena, @intFromEnum(r.s2.id));
            },
            .common_conclusion => |r| {
                try mark(reached, &work, arena, @intFromEnum(r.disj.id));
                if (lastStepOf(blocks, r.left.id)) |ls| try mark(reached, &work, arena, ls);
                if (lastStepOf(blocks, r.right.id)) |ls| try mark(reached, &work, arena, ls);
            },
            .discharge, .generalize, .unpacked => |b| {
                if (lastStepOf(blocks, b.id)) |ls| try mark(reached, &work, arena, ls);
            },
            .hypothesis => {},
            .schema_instance => |r| for (r.premises) |p| try mark(reached, &work, arena, @intFromEnum(p.id)),
            .cite_ref, .reflexivity, .accelerated => {},
        }
    }
    var any_dead = false;
    for (steps, 0..) |s, i| {
        if (reached[i]) continue;
        const label = self.ctx.interner.stringBytes(s.label);
        if (std.mem.indexOfScalar(u8, label, '#') != null) continue; // synthetic
        self.ctx.sink.add(self.diagFile(), s.loc, "unused fact: step '{s}' is never used — no later step or the conclusion cites it (a proof must use every fact it introduces; use --draft while filling in a proof)", .{label}) catch return error.OutOfMemory;
        any_dead = true;
    }
    return !any_dead;
}

fn mark(reached: []bool, work: *std.ArrayList(u32), arena: Allocator, id: u32) Allocator.Error!void {
    if (id >= reached.len or reached[id]) return;
    reached[id] = true;
    try work.append(arena, id);
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;

test "freshNamedAt: a binder's name is keyed to its SOURCE OFFSET, independent of the mint counter" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;

    // Mint at one offset, then bump the counter the way intervening `fix`es and accelerant
    // labels do, then mint at the SAME offset again. The two names must agree: a binder's
    // identity is its source site, not how much of the proof preceded it.
    //
    // This is the defect this test exists for. With `freshNamed` the two mints differed
    // (measured `a#2` vs `a#4` on a real proof), and that name reaches `Schema.instanceHash`
    // via `hashTerm`'s name-bytes branch — so one written instantiation minted two instances
    // and the prover proved it twice. See drafts/schema-hash-decode/.
    const before = try p.freshNamedAt("a", 617);
    _ = try p.freshNamed("spacer");
    _ = try p.freshNamed("spacer");
    const after = try p.freshNamedAt("a", 617);
    try testing.expectEqual(before, after);
    try testing.expectEqualStrings("a#617", p.ctx.interner.stringBytes(before));

    // and a DIFFERENT offset is a different binder — load-bearing, not incidental. An instance
    // keyed on an eigenvar names THAT variable in its statement, so two proofs binding
    // different variables need two instances; collapsing them broke std/subgroup.b4m on the
    // second reverted attempt at this fix.
    const elsewhere = try p.freshNamedAt("a", 1660);
    try testing.expect(before != elsewhere);

    // `freshNamed` itself must still move with the counter — synthetic binders rely on it,
    // because an accelerant stamps one shared loc for a whole generated proof.
    const synth_first = try p.freshNamed("q");
    const synth_second = try p.freshNamed("q");
    try testing.expect(synth_first != synth_second);
}
