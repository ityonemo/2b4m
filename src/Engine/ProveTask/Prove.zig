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
const Verify = @import("../../Verify.zig");
const EqCert = @import("EqCert.zig");
const Polynomial = @import("Polynomial.zig");
const simplify_mod = @import("simplify.zig");
const presburger_mod = @import("presburger.zig");
const smt = @import("smt.zig");
const farkas = @import("farkas.zig");
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
/// SYNTHETIC (accelerant-generated) schema instance (13e): its formulas were DELABORATED
/// from already-elaborated terms, so re-elaboration must NOT re-inject refined-sort guards
/// (Elab.no_relativize). False for ordinary proofs and PARSED schema instances.
pre_relativized: bool = false,
/// Per-eigen RELATIVIZATION guards peeled off a `_quantified` accelerant's TRANSFERRED goal
/// (`∀a; inH(a) -> …` — set by peelForallEq, parallel to its eigen list). The ∀-re-closers
/// (wrapSimplifyForall / closeOverEigen) re-add them per level, matching the kernel's guarded
/// forall_intro derivation. Empty outside a transfer / for unguarded goals.
quant_guards: []const ?TermId = &.{},

const CaseCtx = struct { goal: TermId, disj: kernel.SRef, loc: u32 };

pub fn init(ctx: *Context, h: *Engine.Handle, source: []const u8, file: InternPool.Index, ns: InternPool.Index) Allocator.Error!*Prove {
    const p = try ctx.arena.create(Prove);
    const pool = try ctx.arena.create(term.Pool);
    pool.* = .init(ctx.arena, ctx.gpa); // durable nodes on the main arena; work-stacks on the GPA
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
    e.no_relativize = self.pre_relativized; // synthetic instance: skip guard re-injection
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
pub fn resolveRefs(ctx: *Context, h: *Engine.Handle, file: InternPool.Index, ns: InternPool.Index, model: InternPool.Index, refs: []const RefScan.Ref) Allocator.Error!?Engine.TaskIndex {
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
                if (ctx.pool_file.get(target_file)) |tfid| {
                    if (ctx.declOf(tfid, r.name) != null) break :miss; // declared at source — no fallback
                }
                const hfid = ctx.pool_file.get(home) orelse break :miss;
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
                    blocker = try h.rackIndexed(try ProveTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file }));
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
                            if (ctx.facts.lookup(ctx.io, .{ .namespace = tns, .name = r.name }) == null) {
                                blocker = try h.rackIndexed(try ProveTask.new(ctx.arena, .{ .file = target_file, .name = r.name, .loc = r.loc, .loc_file = file, .model = model }));
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
    file: InternPool.Index,
    name: StrId,
    model: InternPool.Index,
    pool: *term.Pool,
) Allocator.Error!union(enum) { ready: term.TermId, suspended: void, failed: void } {
    // the fact's file must be PARSED before its decl AST is readable.
    switch (try self.demandParse(h, file)) {
        .parsed => {},
        .parsing => |t| {
            h.suspendOn(t);
            return .suspended;
        },
        .unparsed => {}, // undiscovered — declOf below reports it cleanly
    }
    const fid = self.pool_file.get(file) orelse {
        self.sink.add(0, "internal: elaborate a statement in an undiscovered file", .{}) catch return error.OutOfMemory;
        return .failed;
    };
    // point diagnostics at the STATEMENT's own file (offsets below index its source).
    self.sink.current_file = @intFromEnum(fid);
    const source = self.files.items[@intFromEnum(fid)].source;

    // resolve the decl by name; a STATEMENT lives on a local axiom/theorem (an alias has no
    // formula of its own, a schema / hole is not a ground statement).
    const decl = self.declOf(fid, name) orelse {
        self.sink.add(0, "reference not found: '{s}'", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory;
        return .failed;
    };
    const fact = ast.factOf(decl) orelse {
        self.sink.add(ast.declName(decl).start, "'{s}' has no stated formula (an alias or a non-fact)", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory;
        return .failed;
    };
    if (fact.params != null) {
        self.sink.add(fact.name.start, "'{s}' is a schema; its statement is not a ground formula", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory;
        return .failed;
    }
    const formula = fact.formula;

    // RESOLUTION ns = the file's UNIVERSE ns (source names resolve there, then applyModel
    // redirects for a transfer). A fresh Walk (no proof-local binders) + fresh counter +
    // empty define stack own the standalone-call scratch state.
    const resolve_ns = try self.interner.namespace(.universe, file);
    const walk = try self.arena.create(Walk);
    walk.* = Walk.init(self.arena, self.interner, source, self.sink);

    var scanner = RefScan.init(self.arena, self.interner, source, walk);
    const refs = try scanner.scanFormula(formula);
    if (try resolveRefs(self, h, file, resolve_ns, model, refs)) |blocker| {
        h.suspendOn(blocker);
        return .suspended;
    }

    const fresh_counter = try self.arena.create(u32);
    fresh_counter.* = 0;
    const define_stack = try self.arena.create(std.ArrayList(InternPool.Index));
    define_stack.* = .empty;

    var e = Elab.init(self.arena, self.io, self, self.interner, &self.idents, pool, self.sink, source, walk, resolve_ns, fresh_counter);
    e.model = model; // remap source globals for a model transfer (identity for .universe)
    e.define_stack = define_stack;
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
        return self.trustedReadPass(w, step);
    }
    var scanner = RefScan.init(self.ctx.arena, self.ctx.interner, self.source, w);
    scanner.schema_params = self.schema_params; // skip param names when driving a schema instance
    const refs = try scanner.scanStep(step);
    if (try resolveRefs(self.ctx, self.h, self.file, self.ns, self.model, refs)) |blocker| return blocker;

    // an `instantiate` step additionally DEMANDS the monomorphized instance FACT (its own
    // ProveTask) — the schema name + args are now resolved, so build the instance and
    // suspend until it's proved. `process`/`lowerInstantiate` then just looks it up.
    if (step.body == .claim) {
        const c = step.body.claim;
        if (c.rule.name == InternPool.RuleStr.instantiation.id()) {
            var e = self.elab(w);
            switch (try self.demandInstance(&e, c, false)) {
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
                if (try self.demandArithIdents(c)) |blocker| return blocker;
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
    if (try resolveRefs(self.ctx, self.h, self.file, self.ns, self.model, idents[0..n])) |blocker| return blocker;

    // parse the source file whose decl AST the α-match reads (model: src.thm's file; import:
    // I's file; instantiation: the schema's file). An accelerant admits from the local goal,
    // decl — its producer matches THIS proof's goal AST — so it parses nothing here.
    const src_file = self.trustSourceFile(c) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return null, // diagnosed; process re-hits + rejects
    };
    if (src_file) |sf| switch (try self.ctx.demandParse(self.h, sf)) {
        .parsed => {},
        .parsing => |t| return t,
        .unparsed => {}, // undiscovered — process's resolve diagnoses cleanly
    };
    return null;
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

/// Demand (fetch + suspend) the well-known arithmetic operator idents DECLARED in this file,
/// so `readArithSymbols`' ident lookups find them `done` in the producer. Only declared names
/// are demanded (a missing one is skipped — no fetch, no "reference not found"). Returns a
/// blocker to suspend on, or null when all are resolved.
fn demandArithIdents(self: *Prove, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    const loc = c.rule.start;
    const wk = [_][]const u8{ "add", "mul", "succ", "prev", "ZERO", "ONE", "neg", "sub", "less_than", "nonneg" };
    const fid = self.ctx.pool_file.get(self.file).?;
    var refs: std.ArrayList(RefScan.Ref) = .empty;
    for (wk) |name| {
        const nid = self.ctx.interner.internString(name) catch return error.OutOfMemory;
        if (self.ctx.declOf(fid, nid) == null) continue; // not declared here → skip
        try refs.append(self.ctx.arena, .{ .ns = null, .name = nid, .domain = .ident, .loc = loc });
    }
    // the Cooper induction path instantiates the `induction` schema — demand its `.schema`
    // locator so the producer's schema lookup finds it `done`. Only when THIS file declares
    // `induction` as a schema (a parameterized axiom); a bare re-export or a theory-qualified
    // name is left to the ordinary resolver (the induction path declines if it can't resolve).
    const induction_id = self.ctx.interner.internString("induction") catch return error.OutOfMemory;
    if (c.schema == null) if (self.ctx.declOf(fid, induction_id)) |d| {
        if (ast.factOf(d)) |f| if (f.params != null) {
            try refs.append(self.ctx.arena, .{ .ns = null, .name = induction_id, .domain = .schema, .loc = loc });
        };
    };
    return resolveRefs(self.ctx, self.h, self.file, self.ns, self.model, refs.items);
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
    // base. UNWIND: build the innermost or_elim, then for each recorded level emit `goal` via the
    // inner justification, close the block, and wrap in the outer or_elim. Depth = arm count.
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
    // base: a 2-arm or_elim over the current (possibly innermost-block) disjunction.
    var just: kernel.Justification = .{ .or_elim = .{ .disj = cur_disj_ref, .left = cur_arms[0], .right = cur_arms[1] } };
    // unwind: innermost level last-recorded → pop; emit `goal` in its block via `just`, close, wrap.
    var i = levels.items.len;
    while (i > 0) {
        i -= 1;
        const lv = levels.items[i];
        _ = try self.emitSynthetic(lv.block, loc, goal, just);
        self.closeSyntheticBlock(lv.block);
        just = .{ .or_elim = .{ .disj = lv.disj_ref, .left = .{ .id = lv.block, .loc = loc }, .right = lv.right_arm } };
    }
    return just;
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
    const fvar = try self.freshNamed(self.ctx.interner.stringBytes(name));
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

/// Discharge the obligations accrued while elaborating the theorem's STATEMENT formula — a
/// guarded application in the stated goal (`div(ONE, ZERO) = …`) owes its precondition just as
/// one in a proof step does. The context is the ROOT block (kernel block 0): the statement has
/// no local hypotheses, so an obligation discharges only if it is SELF-relativized — a guarded
/// use under `forall d; d != ZERO -> …` closes to `∀d; d != ZERO -> (d != ZERO)` and peels
/// clean, while `div(ONE, ZERO)` in a bare statement has nothing to lean on and is rejected.
/// Mirrors the per-step `dischargeTccs`; called from the goal phase (`elaborateGoalInto`).
pub fn dischargeGoalTccs(self: *Prove) Error!void {
    return self.dischargeTccs(@enumFromInt(0), 0);
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
    // Iterative (was a `while` loop with one `.and_op` self-recursion): a work-stack of formulas
    // that must ALL discharge (an AND). Each is peeled (implies pushes its antecedent onto the
    // SHARED `hyps`; a forall opens under a fresh eigenvar) until it matches a hyp/TCC or splits on
    // `and`. Preserves the original's shared-`hyps` semantics (an implies antecedent from one
    // conjunct stays visible to later conjuncts — same pointer, sequential processing).
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    stack.append(wa, formula) catch return false;
    outer: while (stack.pop()) |start| {
        var f = start;
        while (true) {
            for (hyps.items) |h| if (self.pool.alphaEq(h, f)) continue :outer; // this conjunct discharged
            if (self.tccMatches(kb, f)) continue :outer;
            const node = self.pool.get(f);
            if (node == .bin and node.bin.op == .implies) {
                hyps.append(self.ctx.arena, node.bin.lhs) catch return false;
                f = node.bin.rhs;
                continue;
            }
            if (node == .bin and node.bin.op == .and_op) {
                // push rhs then lhs so LHS pops first — matches the original `lhs and rhs` order,
                // so an antecedent LHS pushes onto the shared `hyps` is visible to RHS.
                stack.append(wa, node.bin.rhs) catch return false;
                stack.append(wa, node.bin.lhs) catch return false;
                continue :outer;
            }
            if (node == .quant and node.quant.q == .forall) {
                const fresh = self.freshNamed("obl") catch return false;
                const fv = self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } }) catch return false;
                f = self.pool.open(node.quant.body, fv) catch return false;
                continue;
            }
            return false; // this conjunct couldn't discharge → whole thing fails
        }
    }
    return true; // every conjunct discharged
}

/// Produce a PROVEN step whose formula is the guard `g` (`good(t)`), and return its SRef —
/// for auto-discharging a refined-sort `forall_elim`'s leaked guard. Sources, in order:
///   (1) a prior in-scope step already asserting `g` → cite it directly (no new step);
///   (2) an enclosing fix-block whose guard is `g` → emit a `[by predicate]` (hypothesis);
///   (3) a MODEL-NOMINATED discharger (13e): the model named a fact establishing the guard of
///       `t`'s head symbol. BASE (`t` a const): the fact's formula IS `g` → cite it directly
///       (the kernel re-checks fact.formula == g, so the nomination is verified, not trusted).
///       COMPOSITE (`t = op(a…)`): the fact is a CLOSURE `∀…; (⋀ guard(argᵢ)) -> guard(op(…))`;
///       forall_elim it at the args, RECURSIVELY discharge each guarded-arg premise, and_intro
///       the results, modus_ponens. (Recursion re-enters `emitDischargeStep` per premise.)
/// Returns null if `g` isn't dischargeable any of these ways (the caller falls back to the
/// plain, guard-leaking elim). Emits ordinary kernel steps into `low_steps`; the final proof is
/// kernel-checked once at the end (no mid-synthesis kernel call).
fn emitDischargeStep(self: *Prove, kb: kernel.BlockId, loc: u32, g: TermId) Error!?kernel.SRef {
    return self.dischargeGoal(kb, loc, g);
}

/// The NON-RECURSIVE guard-discharge sources (no re-entry into the discharge cycle): (1) a prior
/// in-scope step already proving `g`; (2) an enclosing fix-block guard = `g` (or a conjunct of it);
/// (2c) an enclosing assume-block premise = `g` (or a conjunct); (2b) an unpack-witness `and` whose
/// left conjunct is `g`. Returns the SRef of the first hit, or null (the caller tries the recursive
/// model-closure / conjunction sources). Factored out so the iterative discharge driver can call it
/// as its leaf step.
fn dischargeLocal(self: *Prove, kb: kernel.BlockId, loc: u32, g: TermId) Error!?kernel.SRef {
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
            // a MULTI-QUALIFIER fix's guard is a CONJUNCTION (`inH(v) and inK(v)`); if g is
            // one of its conjuncts, restate the whole then and_elim down to it.
            if (try self.emitConjunctExtract(kb, loc, bg, g, c)) |sref| return sref;
        };
        // (2c) an enclosing ASSUME block whose assumption is g — a GUARD PREMISE of a
        // synthetic schema (13e): restate it on demand via [by hypothesis]. A conjunction
        // guard premise extracts its conjunct the same way.
        if (b.kind == .assume) {
            if (self.pool.alphaEq(b.kind.assume, g)) {
                return try self.emitSynthetic(kb, loc, g, .{ .hypothesis = .{ .id = c, .loc = loc } });
            }
            if (try self.emitConjunctExtract(kb, loc, b.kind.assume, g, c)) |sref| return sref;
        }
        // (2b) an enclosing UNPACK block whose witness carries the guard: the sound
        // relativization of `∃x; P` under a refined sort is `∃x; good(x) and P(x)`, so the
        // unpacked hypothesis is `good(w) and P(w)`. If `good(w) == g`, restate the hypothesis
        // (`[by hypothesis]`) then `and_elim_left` off the guard conjunct.
        if (b.kind == .unpack) {
            const uv = b.kind.unpack;
            const src_f = self.low_steps.items[@intFromEnum(uv.source.id)].formula;
            const sn = self.pool.get(src_f);
            if (sn == .quant and sn.quant.q == .exists) {
                const wfv = try self.pool.add(.{ .fvar = uv.v });
                const hyp = try self.pool.open(sn.quant.body, wfv);
                const hn = self.pool.get(hyp);
                if (hn == .bin and hn.bin.op == .and_op and self.pool.alphaEq(hn.bin.lhs, g)) {
                    const hyp_step = try self.emitSynthetic(kb, loc, hyp, .{ .hypothesis = .{ .id = c, .loc = loc } });
                    return try self.emitSynthetic(kb, loc, g, .{ .and_elim_left = hyp_step });
                }
            }
        }
        cur = b.parent;
    }
    return null;
}

/// If `g` is a CONJUNCT of the and-tree `whole` (a multi-qualifier block guard/assumption),
/// restate `whole` (`[by hypothesis]` on block `blk`) and and_elim down to `g`; else null.
fn emitConjunctExtract(self: *Prove, kb: kernel.BlockId, loc: u32, whole: TermId, g: TermId, blk: kernel.BlockId) Error!?kernel.SRef {
    var path: std.ArrayList(bool) = .empty;
    if (!try self.conjunctPath(whole, g, &path)) return null;
    if (path.items.len == 0) return null; // whole == g — the caller's direct case
    var step = try self.emitSynthetic(kb, loc, whole, .{ .hypothesis = .{ .id = blk, .loc = loc } });
    var cur_t = whole;
    for (path.items) |left| {
        const n = self.pool.get(cur_t);
        cur_t = if (left) n.bin.lhs else n.bin.rhs;
        step = try self.emitSynthetic(kb, loc, cur_t, if (left) .{ .and_elim_left = step } else .{ .and_elim_right = step });
    }
    return step;
}

/// The left/right path from and-tree `tree` down to the LEFTMOST conjunct α-equal to `g` (true =
/// left turn), appended to `path`; returns whether found. Iterative DFS (was native recursion) —
/// depth-safe over a deep conjunction. Each frame carries `(node, path-to-it)`; children pushed
/// RIGHT-then-LEFT so the LEFT subtree is explored first (matches the recursion's leftmost find).
/// The path snapshots live in a GPA-backed arena, freed on return; the found path is copied into
/// `path` (on the caller's arena).
fn conjunctPath(self: *Prove, tree: TermId, g: TermId, path: *std.ArrayList(bool)) Error!bool {
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
/// multi-arg forall_elim to Core; unwind with implies_intro per assume + forall_intro per
/// fix — deriving exactly the claim's guard CHAIN. Returns the OUTERMOST forall_intro
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
    // innermost: cite the fact, then multi-arg forall_elim at all eigenvars → Core.
    const inner = parent;
    const kind = self.ctx.interner.keyOf(stmt).fact.kind;
    var cur = try self.emitSynthetic(inner, loc, fact_f, switch (kind) {
        .axiom => .{ .axiom_ref = .{ .stmt = stmt, .loc = loc } },
        .theorem => .{ .theorem_ref = .{ .stmt = stmt, .loc = loc } },
    });
    var cur_f = fact_f;
    for (eigen.items) |ev| {
        const fvt = try self.pool.add(.{ .fvar = ev });
        const opened = try self.pool.open(self.pool.get(cur_f).quant.body, fvt);
        cur = try self.emitSynthetic(inner, loc, opened, .{ .forall_elim = .{ .step = cur, .with = fvt, .with_loc = loc } });
        cur_f = opened;
    }
    // unwind inner→outer: implies_intro per assume (rebuilding the guard chain), forall_intro
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
            just = .{ .implies_intro = .{ .id = asm_blk[i][j], .loc = loc } };
            conc = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = gs[j], .rhs = conc } });
            const encl = if (j > 0) asm_blk[i][j - 1] else fix_blk[i];
            _ = try self.emitSynthetic(encl, loc, conc, just);
        }
        self.closeSyntheticBlock(fix_blk[i]);
        just = .{ .forall_intro = .{ .id = fix_blk[i], .loc = loc } };
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
/// elim/and_intro/modus_ponens. Modeled as a worklist of `Op` frames + a `results` SRef stack,
/// two-color (a compound op is pushed, its sub-goals solved, then it COMBINES from their results).
///
/// `Op` variants:
///   - `.solve` a single guard goal: dischargeLocal → SRef; else a model CLOSURE applies → cite +
///     forall_elim NOW (no children), then push `.mp_chain` + a `.conj` per `->` premise; else a
///     top-level conjunction → push `.conj`; else FAIL.
///   - `.conj` discharge a conjunction TREE: `and` → push `.and_fold` + `.conj`(lhs)+`.conj`(rhs);
///     leaf → `.solve` it.
///   - `.and_fold` / `.mp_chain` COMBINE: pop child SRefs, emit and_intro / the modus_ponens chain.
/// A failed sub-goal sets `failed` (like the recursion's `orelse return null`), abandoning the
/// driver (any steps already emitted are orphaned — exactly as the recursion left them).
fn dischargeGoal(self: *Prove, kb: kernel.BlockId, loc: u32, g0: TermId) Error!?kernel.SRef {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();

    const Op = union(enum) {
        solve: TermId, // discharge a single guard goal g
        conj: TermId, // discharge a conjunction tree f (fold of leaf solves)
        and_fold: TermId, // pop 2 child SRefs → and_intro(f) → push
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
                if (try self.dischargeLocal(kb, loc, g)) |sref| {
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
                try results.append(a, try self.emitSynthetic(kb, loc, f, .{ .and_intro = .{ .left = l, .right = r } }));
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
/// CLOSURE (cite + forall_elim the args NOW — those steps need no children — then push an
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
        const kind = self.ctx.interner.keyOf(fact).fact.kind;
        const formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
        const cite_just: kernel.Justification = switch (kind) {
            .axiom => .{ .axiom_ref = .{ .stmt = fact, .loc = loc } },
            .theorem => .{ .theorem_ref = .{ .stmt = fact, .loc = loc } },
        };
        // BASE: the fact IS the guard → cite; the kernel re-checks formula == g. The driver pushes
        // the returned SRef onto its results stack.
        if (self.pool.alphaEq(formula, g)) {
            return .{ .base = try self.emitSynthetic(kb, loc, g, cite_just) };
        }
        // CLOSURE: cite + forall_elim at the args (no children); then push mp_chain + premises.
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
            cur = try self.emitSynthetic(kb, loc, opened, .{ .forall_elim = .{ .step = cur, .with = arg, .with_loc = loc } });
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
        // nicety: a global fact cited where a step label belongs — name the fix. Check both the
        // FactKV (already-demanded) and the file's AST (a same-file fact decl that nothing
        // demanded, e.g. the cited axiom in `forall_elim(t) myAxiom`), so it fires regardless.
        const is_fact = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = self.ns, .name = name }) != null or
            (tok.qualifier == InternPool.Index.none and if (self.ctx.pool_file.get(self.file)) |fid|
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

/// An axiom/theorem citation: GLOBAL fact via FactKV (the read pass made it proven, or
/// left an in_flight-self / failed entry — diagnosed here).
fn resolveFactRef(self: *Prove, tok: lexer.Token) Error!InternPool.Index {
    const ns = try self.resolveQualifier(tok);
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
                return x;
            },
            .in_flight => {},
        };
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
    return ix;
}

/// HOLE TAINT inheritance (summary blast-radius only): if the cited fact `ix` rests on holes,
/// add each hole name to THIS proof's `holes_used` (deduped). Citing a hole — or a fact that
/// rests on one — makes the current proof rest on it. NEVER affects the proof verdict; a hole is
/// an axiom everywhere the KERNEL is concerned. See [[hole-mechanism]].
fn inheritHoles(self: *Prove, ix: InternPool.Index) void {
    const names = self.ctx.hole_taint.get(ix) orelse return;
    outer: for (names) |h| {
        for (self.holes_used.items) |seen| if (seen == h) continue :outer; // already tracked
        self.holes_used.append(self.ctx.arena, h) catch return; // OOM: best-effort taint
    }
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
            // store the CARRIER: terms are carrier-level (fvars mint at carriers; sigs check
            // carriers), so a refined `want` (a param sort remapped to `H` under a model) must
            // not leak into the instance's expressions — refinement rides as guards, not sorts.
            const want_stored: SortId = if (typed.sort == Elab.prop_sort) want else @enumFromInt(@intFromEnum(want_carrier));
            try args.put(self.ctx.arena, pname, .{ .value = .{ .id = typed.id, .sort = want_stored } });
        } else {
            // N-ary GENERATOR param: a lambda arg (or a bare symbol → eta-expand). Sorts are
            // stored at their CARRIERS (a refined resolution leaks guards-as-sorts otherwise).
            const arg_sorts = try self.ctx.arena.alloc(SortId, p.arg_sorts.len);
            for (p.arg_sorts, arg_sorts) |st, *out| {
                const rs_sort = try se.resolveSortTok(st);
                out.* = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(rs_sort)))));
            }
            const rr = try se.resolveSortTok(p.result);
            const result_sort: SortId = @enumFromInt(@intFromEnum(self.ctx.interner.carrierOf(@enumFromInt(@intFromEnum(rr)))));
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

fn demandInstance(self: *Prove, e: *Elab, c: ast.Step.Claim, synthetic: bool) Allocator.Error!InstanceOutcome {
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
        .instance = .{ .schema_name = rs.name, .params = pnames, .args = durable, .synthetic = synthetic },
    }));
    return .{ .blocked = blocker };
}

/// The `instantiate` justification (in `process`, after the read pass demanded + proved the
/// instance fact): look it up, copyIn its formula, and emit `schema_instance` with the
/// caller's premise step-refs. The kernel peels the instance's `->` antecedents against the
/// premises and requires the final consequent == the citing claim.
fn lowerInstantiate(self: *Prove, w: *const Walk, e: *Elab, c: ast.Step.Claim) Error!kernel.Justification {
    if (c.schema == null) return self.fail(c.rule.start, "instantiate requires a schema name", .{});
    const outcome = try self.demandInstance(e, c, false);
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
    // the source theorem: QUALIFIED `src.thm` names the source file via its import; an
    // UNQUALIFIED `thm` is a SAME-FILE source theorem (the source theory + model + citation
    // all live in one file — the natural shape for e.g. a subgroup on its group's sort), so
    // the source file IS the citing file. The transferred fact's identity ns is (M, src_file),
    // DISTINCT from the citing proof's own (universe, self.file) fact, so no collision.
    const rtok = c.refs[0];
    const base = tokName(rtok);
    const src_file = if (rtok.qualifier == InternPool.Index.none) self.file else blk: {
        const qtext = self.ctx.interner.stringBytes(rtok.qualifier);
        const imp_state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = rtok.qualifier }) orelse {
            self.ctx.sink.add(rtok.start, "unknown namespace '{s}'", .{qtext}) catch return error.OutOfMemory;
            return .failed;
        };
        break :blk switch (imp_state) {
            .done => |ix| switch (self.ctx.interner.keyOf(ix)) {
                .import => |imp| self.ctx.interner.keyOf(imp.namespace).namespace.file,
                else => {
                    self.ctx.sink.add(rtok.start, "'{s}' is not a namespace", .{qtext}) catch return error.OutOfMemory;
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
    else
        self.ctx.interner.composeModel(self.ctx.io, self.model, model_ix) catch return error.OutOfMemory;
    // demand the transferred fact in namespace (effective_model, src_file). A distinct ambient
    // model composes to a distinct model → a distinct namespace → a distinct fact (each is its
    // own relativization); the in_flight/proven dedup below keys on that namespace, so it holds.
    const tns = self.ctx.interner.namespace(effective_model, src_file) catch return error.OutOfMemory;
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
        .model = effective_model,
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

/// The `[using import(I) thm]` justification: cite theorem `thm` from import `I`'s file across
/// the file boundary — the explicit accelerant seam (vs. a bare `[by cite I.thm]` qualified
/// citation, which is identical mechanically today; the accelerant is the trust boundary a
/// future `--fast` scopes to). The read pass resolved `I` (ident) + demanded `thm` in I's
/// namespace, so both are ready; look up the fact and cite it. Acceptance is SHAPE-only — the
/// kernel re-matches `thm`'s formula against the claim (as every `theorem_ref` does).
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
    // the cited theorem, proven in I's namespace (the read pass demanded it there).
    const fstate = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = imp_ns, .name = tokName(rtok) }) orelse
        return self.fail(rtok.start, "'{s}' is not a theorem in '{s}'", .{ self.text(rtok), self.text(itok) });
    const fact = switch (fstate) {
        .proven => |ix| ix,
        .in_flight => return self.fail(rtok.start, "cites '{s}', whose proof has not completed", .{self.text(rtok)}),
    };
    if (self.ctx.interner.keyOf(fact) == .schema)
        return self.fail(rtok.start, "'{s}' is a schema; use `[using instantiation …]`, not an import citation", .{self.text(rtok)});
    return .{ .theorem_ref = .{ .stmt = fact, .loc = rtok.start } };
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
    inline for (@typeInfo(Verify.Word).@"enum".fields) |f| {
        const engine_word = comptime (std.mem.eql(u8, f.name, "instantiation") or
            std.mem.eql(u8, f.name, "model") or
            std.mem.eql(u8, f.name, "import"));
        if (!engine_word) {
            if (c.rule.name == (self.internStr(f.name) catch return null)) return @field(Verify.Word, f.name);
        }
    }
    return null;
}

/// Is this `using` step TRUSTED under the current `--fast` set? (Its word is in `verify.trusted`.)
fn trusted(self: *Prove, c: ast.Step.Claim) bool {
    const word = self.trustWord(c) orelse return false;
    return self.ctx.verify.trusts(word);
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
    // MODEL-MANGLE the synthetic's name (13e): the same source step produces DIFFERENT
    // synthetics standalone vs under a transfer (the transfer's terms are remapped +
    // relativized). The registry/FactKV keys carry no model, so an unmangled name would
    // collide keep-first with the standalone synthetic — the transferred instance would
    // resolve the UNRELATIVIZED schema. `{m<N>}` uses non-lexable braces (collision-free).
    var syn_name = syn.name;
    const fid = self.ctx.pool_file.get(self.file).?;
    const decl_ptr = self.ctx.arena.create(ast.Decl) catch return error.OutOfMemory;
    decl_ptr.* = syn.decl;
    if (self.model != InternPool.Index.none and self.model != .universe) {
        const bytes = std.fmt.allocPrint(self.ctx.arena, "{s}{{m{d}}}", .{ self.ctx.interner.stringBytes(syn.name), @intFromEnum(self.model) }) catch return error.OutOfMemory;
        syn_name = self.ctx.interner.internString(bytes) catch return error.OutOfMemory;
        setSyntheticName(decl_ptr, syn_name);
    }
    // register the synthetic decl + publish its `.schema` locator into the FACT table ONCE
    // (both idempotent). A schema is a fact-with-params, so it lives in FactKV like any fact.
    _ = self.ctx.registerDecl(fid, decl_ptr) catch return error.OutOfMemory; // keep-first
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
    const scope_mark = e.scopeMark();
    for (syn.fvar_binds) |bind| {
        e.pushBinder(bind.name, bind.sort, bind.fvar) catch return error.OutOfMemory;
    }
    defer e.scopeTruncate(scope_mark);
    return self.demandInstance(e, inst_c, true);
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
        .proven => |ix| ix,
        .failed => return error.Recover,
        .blocked => return self.fail(c.rule.start, "internal: accelerant instance not resolved before process (read-pass bug)", .{}),
    };
    const formula_off = self.ctx.interner.keyOf(fact).fact.formula;
    const instance = try self.pool.copyIn(self.ctx.interner, formula_off);
    // premises = the accelerant's own refs (the producer's premise order): the head-cite (if
    // the head is local) then the hyps, matching the synthetic body's antecedent order.
    const prems = try self.accelerantPremises(w, c);
    // GUARD PREMISES (13e): under a transfer the synthetic's body leads with the abstracted
    // caller-locals' guards (`inH(a) -> …`) — antecedents with no caller ref token. Count them
    // (peel the instance's `->` chain until the remainder α-matches the goal; guards = total −
    // the ref premises) and SYNTHESIZE a discharge step for each in the CALLER's context (the
    // fix-block guard, source (2); or closure recursion for a composite).
    var total: usize = 0;
    var walk_f = instance;
    while (!self.pool.alphaEq(walk_f, goal)) {
        const n = self.pool.get(walk_f);
        if (n != .bin or n.bin.op != .implies) break;
        total += 1;
        walk_f = n.bin.rhs;
    }
    if (total > prems.len) {
        const k = total - prems.len;
        const all = try self.ctx.arena.alloc(kernel.SRef, total);
        var gf = instance;
        for (0..k) |i| {
            const n = self.pool.get(gf);
            all[i] = (try self.emitDischargeStep(kb, c.rule.start, n.bin.lhs)) orelse
                return self.fail(c.rule.start, "cannot discharge the guard premise '{s}' at this call site", .{try self.renderTerm(n.bin.lhs)});
            gf = n.bin.rhs;
        }
        @memcpy(all[k..], prems);
        return .{ .schema_instance = .{ .instance = instance, .premises = all } };
    }
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
    // ADMIT: the only pre-cert validation is the presence of a head; everything below RESOLVES
    // the head fact/step and builds the synthetic schema. Skip all of it under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
    var b: Accelerant.Builder = .{ .arena = self.ctx.arena, .interner = self.ctx.interner, .pool = self.pool, .loc = c.rule.start };

    // resolve HEAD → its formula term + how the schema proof cites it.
    const head_local = w.findStep(tokName(head)) != null;
    var head_formula: TermId = undefined;
    if (head_local) {
        const sref = try self.resolveStepRef(w, head);
        head_formula = self.low_steps.items[@intFromEnum(sref.id)].formula;
    } else {
        // resolveFactRef rejects a schema head (no ground formula) — a clean diagnostic, not a
        // crash — so `.fact` is safe here. (The generated cert cites it kind-agnostically with
        // `cite`, so the head's axiom-vs-theorem kind is never needed.)
        const fact = try self.resolveFactRef(head);
        head_formula = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(fact).fact.formula);
    }

    // Instantiate one ∀ per arg at a fresh param fvar, INTERLEAVED with `->` antecedents:
    // a head `∀k; guard(k) -> ∀s; …` opens `k`, then must descend past `guard(k) ->` to
    // reach `∀s`. `openNextForall` walks the leading `->` chain (preserving it) to the next
    // forall, opens it at the param, and rebuilds the `->` prefix around the opened body.
    // ABSTRACT the head formula's FREE caller-local eigenvars (an enclosing `fix k`) into value
    // params UP FRONT — a LOCAL head like `forall a,b; add(k,a)=add(k,b) -> a=b` carries the free
    // `k`, which must become a schema param (else the generated schema references `k`, absent from
    // its scope: "reference not found: 'k'"). Named `f1,f2,…` (distinct from the ∀-arg params
    // `p1..pN` below); substituted through head_formula before the ∀ peel. A GLOBAL head is closed
    // (no free eigenvars) so this is a no-op there.
    var free_fvars: std.ArrayList(term.Node.Fvar) = .empty;
    try self.collectFreeFvars(head_formula, &free_fvars);
    const fparams = try self.ctx.arena.alloc(ast.SchemaParam, free_fvars.items.len);
    const fargs = try self.ctx.arena.alloc(*const ast.Expr, free_fvars.items.len);
    // Bindings so each call-site arg (a display-trimmed fvar name) re-resolves to its very
    // fvar. A caller `fix`-bound eigenvar already resolves through the proof-local scope, but a
    // free fvar INHERITED from a schema-instance monomorphization (see `Synthetic.fvar_binds`)
    // has no source binder — the plumbing installs these into the caller Elab scope.
    const fbinds = try self.ctx.arena.alloc(Accelerant.Synthetic.FvarBind, free_fvars.items.len);
    for (free_fvars.items, 0..) |fv, i| {
        const fname = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "f{d}", .{i + 1}));
        const pf = try self.pool.add(.{ .fvar = .{ .name = fname, .sort = fv.sort } });
        head_formula = try self.pool.substFvar(head_formula, fv.name, pf);
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(fv.sort)));
        fparams[i] = .{ .name = b.tok(fname), .arg_sorts = &.{}, .result = b.tok(sort_name) };
        fargs[i] = try b.termExpr(try self.pool.add(.{ .fvar = fv })); // caller binder name at the call site
        fbinds[i] = .{ .name = try self.displayName(fv.name), .fvar = fv.name, .sort = fv.sort };
    }

    const nargs = c.args.len;
    const pnames = try self.ctx.arena.alloc(StrId, nargs);
    const arg_params = try self.ctx.arena.alloc(ast.SchemaParam, nargs);
    var tail = head_formula;
    for (0..nargs) |i| {
        pnames[i] = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "p{d}", .{i + 1}));
        const opened = try self.openNextForall(tail, pnames[i]) orelse {
            return self.fail(c.rule.start, "specialize: head is not universally quantified enough for {d} argument(s)", .{nargs});
        };
        tail = opened.body;
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(opened.sort)));
        arg_params[i] = .{ .name = b.tok(pnames[i]), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }
    // schema params = the free-eigenvar params FIRST, then the ∀-arg params.
    const params = try std.mem.concat(self.ctx.arena, ast.SchemaParam, &.{ fparams, arg_params });

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

    const steps = try self.buildSpecializeProof(&b, head, head_local, head_formula, pnames, ants.items, consequent);

    // deterministic hash-name from the head formula + arg count (re-entry stable).
    const hash = Schema.termHash(self.pool, head_formula) ^ (@as(u64, @intCast(nargs)) *% 0x9E3779B97F4A7C15);
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "specialize{{{x}}}", .{hash}));

    // call-site args mirror the params: the free-eigenvar args FIRST, then the user's ∀-args.
    const args = try std.mem.concat(self.ctx.arena, *const ast.Expr, &.{ fargs, c.args });
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = args,
        .premises = c.refs,
        .fvar_binds = fbinds,
    };
}

/// Build the synthetic schema's PROOF for specialize: prove `ants[0] -> … -> consequent`
/// from the head. Structure: assume each antecedent (nested blocks), and in the innermost
/// context walk the head interleaving forall_elim(param) and modus_ponens(the matching
/// assumed antecedent) to reach `consequent`; then implies_intro back out through each block.
/// A GLOBAL head is cited (axiom/theorem); a LOCAL head is antecedent #0 (assumed, restated
/// by hypothesis). Handles the contiguous case (no interior `->`) as the ants-empty subset.
fn buildSpecializeProof(self: *Prove, b: *Accelerant.Builder, head: lexer.Token, head_local: bool, head_formula: TermId, pnames: []const StrId, ants: []const TermId, consequent: TermId) Error![]const ast.Step {
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
        try inner.append(self.ctx.arena, try b.claimStep(law, try b.termExpr(head_formula), .by, try self.internStrRt("cite"), &.{}, try self.headRef(head)));
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
    // Descend the leading `->` chain to the first `forall`, opening it, then rewrap the `->`
    // prefix around the opened body. Iterative (was linear recursion + rebuild-unwind): collect
    // the implication LHSs on the way down, then fold them back over the opened body innermost-out.
    var prefix: std.ArrayList(TermId) = .empty; // implication LHSs, outer→inner
    defer prefix.deinit(self.ctx.gpa);
    var cur = id;
    const opened: OpenedForall = while (true) {
        const node = self.pool.get(cur);
        switch (node) {
            .quant => |q| {
                if (q.q != .forall) return null;
                const pf = try self.pool.add(.{ .fvar = .{ .name = pname, .sort = q.sort } });
                break .{ .body = try self.pool.open(q.body, pf), .sort = q.sort };
            },
            .bin => |bn| {
                if (bn.op != .implies) return null;
                try prefix.append(self.ctx.gpa, bn.lhs);
                cur = bn.rhs;
            },
            else => return null,
        }
    };
    // rewrap: `lhs_outer -> ( … -> ( lhs_inner -> opened.body ) )` — fold prefix inner-to-outer.
    var body = opened.body;
    var i = prefix.items.len;
    while (i > 0) {
        i -= 1;
        body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = prefix.items[i], .rhs = body } });
    }
    return .{ .body = body, .sort = opened.sort };
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
/// PARAMS: a tautology inside a `fix a { … }` has free caller-local eigenvars in its goal/
/// premises; `abstractGoal` lifts them (shared across goal + premises) into schema value
/// params `p1,p2,…`, mirrored by call-site args — the same machinery `arithmetic` uses. A
/// closed site abstracts nothing (empty params/args, the common case).
fn produceTautology(self: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return self.fail(c.rule.start, "tautology takes no arguments", .{});
    // ADMIT: the only pre-cert validation is the arg-count; the DECISION (smt.tautology) and the
    // cert build are the expensive path. Skip both under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
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

    // ABSTRACT the free caller-local eigenvars (an enclosing `fix a { … }` around this step)
    // into schema value params `p1,p2,…`, shared across the goal AND every premise formula (all
    // speak the same `fix` vars). Without this, delaborating the goal/premise to the empty-scope
    // schema body leaves those names unresolvable. The verdict above was decided on the ORIGINAL
    // terms (fvar substitution is uniform, so the propositional structure — atoms + truth table —
    // is identical); the cert is built on the ABSTRACTED terms so its body speaks the params.
    // A closed (no-`fix`) site abstracts nothing — params/args empty, the common case.
    const abstracted = try self.abstractGoal(&b, goal, prem_formulae, &.{});
    const abs = abstracted.abs;
    const goal_p = abstracted.goal_p;
    // rewrite each premise's formula into param space (the cert + the schema antecedents use it).
    const prems_p = try self.ctx.arena.alloc(TautAst.Prem, prems.len);
    for (prems, prems_p) |src, *out| {
        out.* = src;
        out.formula = try self.substFvarsToParams(src.formula, abs);
    }

    // GENERATE the certificate over the param-space goal/premises. Collect the atoms once (the
    // cert's split order), then replay.
    var atom_list: std.ArrayList(TermId) = .empty;
    for (prems_p) |p| smt.collectAtoms(self.ctx.arena, self.pool, &atom_list, p.formula) catch return error.OutOfMemory;
    smt.collectAtoms(self.ctx.arena, self.pool, &atom_list, goal_p) catch return error.OutOfMemory;

    const assignment = try self.ctx.arena.alloc(?bool, atom_list.items.len);
    @memset(assignment, null);
    const lit_blocks = try self.ctx.arena.alloc(?StrId, atom_list.items.len);
    @memset(lit_blocks, null);
    var cert: TautAst = .{
        .p = self,
        .b = &b,
        .goal = goal_p,
        .premises = prems_p,
        .atoms = atom_list.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
    };

    // the innermost block's steps: the whole cert, concluding `goal`.
    var inner: std.ArrayList(ast.Step) = .empty;
    try cert.deriveGoal(&inner);

    // wrap in nested `assume prem_i { restate hyp; … }` blocks, exporting each `->` back out.
    const steps = try self.wrapTautologyPremises(&b, prems_p, goal_p, inner.items);

    // schema body = `prem0 -> … -> goal` (an ordinary proof with no premises just = goal).
    var body_expr = try b.termExpr(goal_p);
    var i: usize = prems_p.len;
    while (i > 0) {
        i -= 1;
        body_expr = try b.implies(try b.termExpr(prems_p[i].formula), body_expr);
    }

    // deterministic hash-name from the abstracted goal + all premise formulae (re-entry stable).
    var hash = Schema.termHash(self.pool, goal_p);
    for (prems_p) |p| hash ^= Schema.termHash(self.pool, p.formula) *% 0x9E3779B97F4A7C15;
    const name = try b.intern(try std.fmt.allocPrint(self.ctx.arena, "tautology{{{x}}}", .{hash}));

    // the abstracted eigenvars become the schema's value params (mirrored args at the call site).
    const params = try self.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |pname, sort, *pp| {
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sort)));
        pp.* = .{ .name = b.tok(pname), .arg_sorts = &.{}, .result = b.tok(sort_name) };
    }

    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = c.refs,
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
    ///
    /// An iterative DFS over the decision tree (was self-recursion in the two split arms;
    /// depth is the ≤16-atom cap, but Zig will disallow recursion regardless). `expand`
    /// handles one node (premise-refute / true-derive / split); a split pushes `finish`
    /// (below) then the right-arm setup then the left-arm setup+expand, so the LEFT subtree
    /// fully drains before the RIGHT arm's `assignment[idx]` is set, and the `finish` frame
    /// (finishBlocks + or_elim + restore) runs after BOTH arms — identical to the recursive
    /// set/recurse/restore discipline. Scratch stacks on the pool's GPA. The goal-proving
    /// step is the block's last; callers read it from there (no label to return).
    fn deriveGoal(self: *TautAst, block: *std.ArrayList(ast.Step)) CertError!void {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        const Frame = union(enum) {
            expand: *std.ArrayList(ast.Step),
            // set the right arm's assignment, then expand it into `right.body`.
            arm_right: struct { idx: usize, right: *OpenBlock },
            // both arms drained: finish them into `block` + or_elim + restore assignment.
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
                    _ = try self.emit(blk, self.goal, "absurd", &.{ pr.label, refuted });
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
                _ = try self.emit(c.block, self.goal, "or_elim", &.{ c.lem, c.left.label, c.right.label });
            },
        };
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
        return self.deriveStructural(.true, block, f);
    }

    /// Emit a step proving `not f` (f evaluates false) in `block`; return its label.
    fn deriveFalse(self: *TautAst, block: *std.ArrayList(ast.Step), f: TermId) CertError!StrId {
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
    fn deriveStructural(self: *TautAst, root_mode: Mode, root_block: *std.ArrayList(ast.Step), root_f: TermId) CertError!StrId {
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
            // true.implies (true consequent): child already emitted into blk.body; finish + implies_intro.
            combine_true_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId },
            // true.implies (false antecedent): refutation on `results`; emit absurd inside blk.body, then finish + implies_intro.
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
                            // children into same block; combine emits and_intro/iff_intro.
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
                                // absurd(h, refuted) emitted after the refutation resolves — but the
                                // recursive version emits it INSIDE blk.body before finishBlock. A
                                // dedicated combine emits absurd then finishes + implies_intro.
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
                const rule: []const u8 = if (self.p.isBiconditionalShape(c.f)) "iff_intro" else "and_intro";
                try results.append(sa, try self.emit(c.block, c.f, rule, &.{ left, right }));
            },
            .combine_or_left => |c| {
                const l = results.pop().?;
                try results.append(sa, try self.emit(c.block, c.f, "or_intro_left", &.{l}));
            },
            .combine_or_right => |c| {
                const r = results.pop().?;
                try results.append(sa, try self.emit(c.block, c.f, "or_intro_right", &.{r}));
            },
            .combine_true_implies => |c| {
                // true-consequent branch: child already emitted into blk.body; discard its label.
                _ = results.pop().?;
                try self.finishBlock(c.block, c.blk, c.ante);
                try results.append(sa, try self.emit(c.block, c.f, "implies_intro", &.{c.blk.label}));
            },
            .combine_true_implies_absurd => |c| {
                const refuted = results.pop().?;
                _ = try self.emit(&c.blk.body, c.conseq, "absurd", &.{ c.hyp, refuted });
                try self.finishBlock(c.block, c.blk, c.ante);
                try results.append(sa, try self.emit(c.block, c.f, "implies_intro", &.{c.blk.label}));
            },
            .combine_false_and => |c| {
                const refuted = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                const elim = try self.emit(&blk.body, c.side, if (c.left_false) "and_elim_left" else "and_elim_right", &.{h});
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, elim, refuted }));
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
                _ = try self.emit(&right.body, c.lhs, "absurd", &.{ rh, not_right });
                try self.finishBlock(&blk.body, &right, c.rhs);
                const conc = try self.emit(&blk.body, c.lhs, "or_elim", &.{ h, left.label, right.label });
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, conc, not_left }));
            },
            .combine_false_implies => |c| {
                const not_conseq = results.pop().?;
                const ante = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                const conseq = try self.emit(&blk.body, c.rhs, "modus_ponens", &.{ h, ante });
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, conseq, not_conseq }));
            },
            .combine_false_not => |c| {
                const truth = results.pop().?;
                var blk = try self.openBlock();
                const h = try self.hyp(&blk, c.f);
                try self.finishBlock(c.block, &blk, c.f);
                try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, truth, h }));
            },
        };
        return results.items[0];
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
    // orient: peel `forall` binders as fresh pattern fvars, require an equation body. Under a
    // model TRANSFER the cited lemma is RELATIVIZED — `∀a; inH(a) -> ∀b; … -> lhs=rhs` — with
    // guard `->`s interleaved with the binders; SKIP them here to reach the equation (they are
    // discharged where the lemma is applied: emitInstance cites + forall_elims the lemma, and the
    // instance ProveTask runs under the model so the forall_elim discharge machinery strips them).
    var binders: std.ArrayList(simplify_mod.Binder) = .empty;
    var body = formula;
    while (true) {
        const node = self.pool.get(body);
        if (node == .quant and node.quant.q == .forall) {
            const fresh = try self.freshNamed("p#");
            const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            body = try self.pool.open(node.quant.body, fv);
            try binders.append(self.ctx.arena, .{ .fvar = fresh, .sort = node.quant.sort });
            continue;
        }
        // a relativization guard `inH(v) -> …` (transfer only): skip to the consequent.
        if (node == .bin and node.bin.op == .implies and self.model != InternPool.Index.none and self.model != .universe) {
            body = node.bin.rhs;
            continue;
        }
        break;
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
    // ADMIT: the goal-shape validation ran in the produce* caller; everything below RESOLVES the
    // cited rules (prepareRule → resolveFactRef) and runs the normalize decision. Skip under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
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

    // guard premises for the abstracted caller-locals (13e; no-op outside a transfer).
    const n_guards = try self.guardPremises(abs, &local_formulae, &local_cites);
    // the inner proposition the cert proves under its assumptions: `prem0 -> … -> (s = t)`.
    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    const inner_prop = try self.impliesChain(eq_prop, local_formulae.items);

    // wrap the cert in nested `assume <local-prem>` blocks (the `->` antecedents), then in
    // `fix` blocks for the ∀ eigenvariables (the quantified variant's re-generalization).
    steps = try self.wrapSimplifyPremises(&b, local_cites.items, local_formulae.items, eq_prop, steps, n_guards);
    steps = try self.wrapSimplifyForall(&b, eigen, inner_prop, steps);

    // the schema body proposition = the ∀-generalized `inner_prop` (params already in place).
    const full_prop = try self.closeOverEigen(inner_prop, eigen);
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

/// GUARD PREMISES for the abstracted caller-locals (13e): under a model TRANSFER, an
/// abstracted `fix`-eigenvar carries a refined-sort guard (`inH(a)`) in the CALLER's block.
/// The synthetic's discharge (a closure recursion bottoming out at the param fvar) needs that
/// guard available INSIDE the instance — so surface it as a leading LOCAL premise: the schema
/// body gains `inH(p) -> …`, the proof an enclosing `assume` block (no eager restate — the
/// discharge's assume-source (2c) emits the hypothesis step on demand, so an unused guard
/// leaves no dead step), and the CALL SITE discharges it from the fix guard (lowerUsing).
/// PREPENDS to `formulae`/`cites` (guards outermost); returns how many were added.
fn guardPremises(self: *Prove, abs: FvarAbstraction, formulae: *std.ArrayList(TermId), cites: *std.ArrayList(EqCert.RuleCite)) Error!usize {
    if (self.model == InternPool.Index.none or self.model == .universe) return 0;
    var add_f: std.ArrayList(TermId) = .empty;
    var add_c: std.ArrayList(EqCert.RuleCite) = .empty;
    for (abs.origs) |orig| {
        const g = self.callerGuard(orig) orelse continue;
        try add_f.append(self.ctx.arena, try self.substFvarsToParams(g, abs));
        try add_c.append(self.ctx.arena, .{ .local = .{ .hyp = try self.freshNamed("guard-prem") } });
    }
    if (add_f.items.len == 0) return 0;
    try formulae.insertSlice(self.ctx.arena, 0, add_f.items);
    try cites.insertSlice(self.ctx.arena, 0, add_c.items);
    return add_f.items.len;
}

/// The caller-block guard of a fix-eigenvar (by fvar identity), or null (unguarded/not a fix).
fn callerGuard(self: *Prove, fvar_name: StrId) ?TermId {
    for (self.low_blocks.items) |blk| if (blk.kind == .fix) {
        if (blk.kind.fix.v.name == fvar_name) return blk.kind.fix.guard;
    };
    return null;
}

/// Wrap the cert `inner` (proving the equation `eq_prop`) in nested `assume <local-prem>`
/// blocks — one per LOCAL rule premise, restating its hypothesis (under the deterministic
/// `prem-…` label the cert cites) and exporting `prem_i -> …` with `implies_intro` out
/// through each level. With no local premises the cert steps pass through verbatim. (Same
/// shape as tautology's `wrapTautologyPremises`.) The FIRST `n_guards` premises are GUARD
/// premises (13e): assume-wrapped but NOT eagerly restated — the discharge machinery emits
/// the hypothesis step on demand (an unused restate would be a dead step).
fn wrapSimplifyPremises(self: *Prove, b: *Accelerant.Builder, cites: []const EqCert.RuleCite, formulae: []const TermId, eq_prop: TermId, inner: []const ast.Step, n_guards: usize) Error![]const ast.Step {
    var body_steps = inner;
    var i: usize = formulae.len;
    while (i > 0) {
        i -= 1;
        const blk_label = try self.freshNamed("assume-prem");
        var blk_body = try std.ArrayList(ast.Step).initCapacity(self.ctx.arena, body_steps.len + 1);
        if (i >= n_guards) {
            const hyp_label = cites[i].local.hyp;
            blk_body.appendAssumeCapacity(try b.claimStep(hyp_label, try b.termExpr(formulae[i]), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(b, blk_label)));
        }
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
        // GUARD level (13e, a transferred `_quantified` goal): wrap the current steps in
        // `assume guard(v) { … }` + an implies_intro export INSIDE this fix — forall_intro
        // then derives the guarded `∀v; guard(v) -> …` (matching the relativized body), and
        // the discharge machinery finds `guard(v)` via the assume-source (2c).
        if (i < self.quant_guards.len) if (self.quant_guards[i]) |g| {
            const blk_label = try self.freshNamed("assume-guard");
            var gsteps: std.ArrayList(ast.Step) = .empty;
            try gsteps.append(self.ctx.arena, try b.assumeStep(blk_label, try b.termExpr(g), steps));
            prop = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = g, .rhs = prop } });
            try gsteps.append(self.ctx.arena, try b.claimStep(try self.freshNamed("export-guard"), try b.termExpr(prop), .by, try self.internStr("implies_intro"), &.{}, try self.oneRef(b, blk_label)));
            steps = try gsteps.toOwnedSlice(self.ctx.arena);
        };
        const sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(fv.sort)));
        const fix_label = try self.freshNamed("fix");
        const bname = b.tok(try self.displayName(fv.name));
        const fix_step: ast.Step = .{ .label = b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = b.tok(sort_name), .steps = steps } } };
        // plain ∀-close: the guard (if any) is already folded into `prop` above.
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

/// Re-close `prop` over the peeled ∀ eigenvariables (outermost = eigen[0]), re-adding each
/// level's peeled relativization guard (`∀v; inH(v) -> …`) — the schema-body counterpart of
/// the kernel's guarded forall_intro (the fix binder re-resolves to the refined sort under the
/// model, so its forall_intro derives the guarded form; the stated body must match).
fn closeOverEigen(self: *Prove, prop_in: TermId, eigen: []const term.Node.Fvar) Error!TermId {
    var prop = prop_in;
    var ei: usize = eigen.len;
    while (ei > 0) {
        ei -= 1;
        prop = try self.guardedQuant(prop, eigen[ei], ei);
    }
    return prop;
}

/// One level of `closeOverEigen`: `∀v; [guard(v) ->] prop`.
fn guardedQuant(self: *Prove, prop_in: TermId, fv: term.Node.Fvar, level: usize) Error!TermId {
    var prop = prop_in;
    if (level < self.quant_guards.len) if (self.quant_guards[level]) |g| {
        prop = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = g, .rhs = prop } });
    };
    const closed = try self.pool.close(prop, fv.name);
    return self.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
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
/// Collect the DISTINCT free vars of `id` into `out` (on the caller's arena). Iterative work-stack
/// (was native recursion) — depth-safe. The frontier stack is GPA-backed scratch (reclaimed here);
/// `out` stays durable. (Note: this collects fvars regardless of binder depth — a "free var" here
/// is any `.fvar` node, matching the original; bound vars are `.bvar` and contribute nothing.)
fn collectFreeFvars(self: *Prove, id: TermId, out: *std.ArrayList(term.Node.Fvar)) Error!void {
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
    // ADMIT: the pre-cert validation (goal is an equation, >=1 ref) is done; everything below
    // RESOLVES the cited equations (resolveFactRef) and runs the BFS connection search. Skip
    // under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
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
        try body_steps.append(self.ctx.arena, try b.claimStep(p.body_label, try b.termExpr(p.formula), .by, try self.internStr("cite"), &.{}, try self.headRef(p.head)));
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

    // guard premises for the abstracted caller-locals (13e; no-op outside a transfer).
    const n_guards = try self.guardPremises(abs, &local_formulae, &local_cites);
    // wrap the cert in nested `assume <local-eq>` blocks (the `->` antecedents), each restating
    // its hypothesis under `body_label` and exporting `prem_i -> … -> (start = target)` out.
    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = start, .rhs = target } });
    const steps = try self.wrapSimplifyPremises(&b, local_cites.items, local_formulae.items, eq_prop, body_steps.items, n_guards);

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
    // ADMIT: goal-shape (equation) validated in the caller + arg-count here. The next step
    // (`argRule` → resolveFactRef) RESOLVES the associativity lemma — which is exactly what an
    // admitted step must NOT require proved (e.g. assoc_oracle's `opAssoc` is unresolvable). Skip.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
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
    // ADMIT: the goal well-formedness check for polynomial is that it has add/mul structure
    // (readPolyOps, a pure structural read). Below builds the hardcoded rule set + canonicalizes
    // both sides (the decision). Skip that expensive path under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
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

/// A symbol's WELL-KNOWN name for vocabulary matching: under a TRANSFER the goal's syms are
/// TARGET images (`tadd`), but the well-known vocabulary (add/mul/…) is the SOURCE theory's —
/// reverse-map through the overlay to the source symbol's name.
fn vocabName(self: *Prove, ix: InternPool.Index) []const u8 {
    if (self.model != InternPool.Index.none and self.model != .universe) {
        var cur = self.model;
        while (true) {
            const m = self.ctx.interner.keyOf(cur).model;
            for (m.overlay) |mp| if (mp.tgt == ix and mp.src != ix)
                return self.ctx.interner.stringBytes(self.ctx.interner.nameOf(mp.src));
            if (cur == m.parent) break;
            cur = m.parent;
        }
    }
    return self.ctx.interner.stringBytes(self.ctx.interner.nameOf(ix));
}

/// Recursively match each app head's well-known NAME, filling `ops`. Pure goal inspection.
fn collectPolyOps(self: *Prove, id: TermId, ops: *Polynomial.Ops, have_add: *bool, have_mul: *bool) Error!void {
    // iterative single-tree collector (was native recursion). Records the polynomial vocabulary
    // ops by well-known name; field-setting is order-independent so a plain work-stack suffices.
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        if (node == .app) {
            const a = node.app;
            const name = self.vocabName(@enumFromInt(@intFromEnum(a.sym)));
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
        }
        // `.pred` is NOT descended (the original had no `.pred` arm — only app/eq/bin/not/quant).
        switch (node) {
            .app, .eq, .bin, .not, .quant => try self.pool.pushChildren(&stack, wa, node),
            else => {},
        }
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
    // ADMIT: goal-shape (equation) validated in the caller + arg-count here. Everything below
    // RESOLVES the (distribute pre-rules and, for the explicit form, the AC triple) lemmas and
    // runs the AC re-association search. Skip the resolution + decision under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
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
/// Is `f` a relativization guard over `fv` — a unary pred applied to exactly that fvar, or
/// an and-tree of such (the canonical multi-qualifier conjunction)?
fn isGuardOver(self: *Prove, f: TermId, fv: StrId) bool {
    // a conjunction of `pred(fv)` guards, ALL over the same fvar — iterative AND-walk.
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), self.ctx.gpa);
    const al = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(al);
    stack.append(al, f) catch return false;
    while (stack.pop()) |cur| {
        const n = self.pool.get(cur);
        if (n == .bin and n.bin.op == .and_op) {
            stack.append(al, n.bin.lhs) catch return false;
            stack.append(al, n.bin.rhs) catch return false;
            continue;
        }
        if (n != .pred) return false;
        const args = self.pool.args(n.pred);
        if (args.len != 1) return false;
        const a = self.pool.get(args[0]);
        if (!(a == .fvar and a.fvar.name == fv)) return false;
    }
    return true;
}

const PeeledEq = struct { body: TermId, eigen: []const term.Node.Fvar };
fn peelForallEq(self: *Prove, goal: TermId, c: ast.Step.Claim, comptime who: []const u8) Error!?PeeledEq {
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var guards: std.ArrayList(?TermId) = .empty;
    self.quant_guards = &.{};
    var body = goal;
    while (true) {
        const node = self.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = self.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{ .name = try self.freshNamed(if (hint.len > 0) hint else "q"), .sort = node.quant.sort };
        const fvt = try self.pool.add(.{ .fvar = fv });
        body = try self.pool.open(node.quant.body, fvt);
        try eigen.append(self.ctx.arena, fv);
        // TRANSFER: the goal is RELATIVIZED — peel this binder's injected guard (`inH(v) ->`,
        // a unary pred over exactly the just-opened fvar), recording it for the re-closers.
        var guard: ?TermId = null;
        if (self.model != InternPool.Index.none and self.model != .universe) {
            const bn = self.pool.get(body);
            if (bn == .bin and bn.bin.op == .implies and self.isGuardOver(bn.bin.lhs, fv.name)) {
                guard = bn.bin.lhs;
                body = bn.bin.rhs;
            }
        }
        try guards.append(self.ctx.arena, guard);
    }
    self.quant_guards = guards.items;
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

    // guard premises for the abstracted caller-locals (13e; no-op outside a transfer).
    const n_guards = try self.guardPremises(abs, &local_formulae, &local_cites);
    const eq_prop = try self.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
    const inner_prop = try self.impliesChain(eq_prop, local_formulae.items);
    steps = try self.wrapSimplifyPremises(b, local_cites.items, local_formulae.items, eq_prop, steps, n_guards);
    steps = try self.wrapSimplifyForall(b, eigen, inner_prop, steps);

    // the schema body proposition = the ∀-generalized `inner_prop`.
    const full_prop = try self.closeOverEigen(inner_prop, eigen);
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
    // ADMIT: the goal-shape + ext-lemma-present validation ran in the produce* caller. Everything
    // below RESOLVES the ext lemma + each unfold lemma (resolveFactRef) and builds the cert. Skip
    // under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
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
    const full_prop = try self.closeOverEigen(eq_prop, eigen);
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
    // walk only through bin/not into pred nodes (the original's restricted recursion), returning
    // the FIRST pred's set-arg head sym (leftmost — bin pushes rhs then lhs so lhs pops first).
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), self.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, id) catch return null;
    while (stack.pop()) |cur| {
        switch (self.pool.get(cur)) {
            .pred => |p| {
                const args = self.pool.args(p);
                if (args.len == 2) {
                    const set = self.pool.get(args[1]);
                    if (set == .app) return set.app.sym;
                }
            },
            .bin => |bn| {
                stack.append(a, bn.rhs) catch return null;
                stack.append(a, bn.lhs) catch return null;
            },
            .not => |inner| stack.append(a, inner) catch return null,
            else => {},
        }
    }
    return null;
}

/// Emit the extensionality certificate proving `s = t` into `block`: cite the ext lemma,
/// forall_elim it at (s, t) to reach `Ob1 -> (Ob2 ->) s = t`, prove each obligation, and
/// modus_ponens the chain. The lemma cite + each obligation step live directly in `block`.
fn emitExtEquation(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), lemma: ExtLemma, unfolds: []const ExtUnfold, s: TermId, t: TermId, c: ast.Step.Claim) Error!void {
    // step 0: cite the ext lemma.
    const law = try self.freshNamed("extensionality");
    const word: []const u8 = "cite";
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
    try cert.deriveGoal(block);
}

/// Recurse over `body`, and for each `member(x, op(args…))` subterm instantiate the cited
/// membership lemma whose characterized op matches, at (args…, x). Each instance is emitted as a
/// step in `block` and recorded as a tautology premise. Dedups by formula.
fn emitExtUnfoldMembership(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), body: TermId, x_id: TermId, unfolds: []const ExtUnfold, out: *std.ArrayList(TautAst.Prem)) Error!void {
    // ITERATIVE (was mutual recursion emitExtUnfoldMembership↔emitExtUnfoldOp). A worklist of
    // `Work` items: a `.membership` walks the body's bin/not/pred skeleton; a `.op` instantiates
    // the membership lemma for one `op(args)` and queues its set-typed args. Items are pushed
    // REVERSED so the leftmost/outermost is processed first — preserving the pre-order,
    // left-to-right premise-collection (+ dedup) order of the recursion. Scratch on ctx.gpa.
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    const Work = union(enum) { membership: TermId, op: term.Node.App };
    var stack: std.ArrayList(Work) = .empty;
    try stack.append(wa, .{ .membership = body });
    while (stack.pop()) |item| switch (item) {
        .membership => |m| {
            switch (self.pool.get(m)) {
                .pred => |p| {
                    const args = self.pool.args(p);
                    if (args.len == 2) {
                        const set = self.pool.get(args[1]);
                        if (set == .app) try stack.append(wa, .{ .op = set.app });
                    }
                },
                .bin => |bn| {
                    try stack.append(wa, .{ .membership = bn.rhs }); // rhs pushed first → lhs first
                    try stack.append(wa, .{ .membership = bn.lhs });
                },
                .not => |inner| try stack.append(wa, .{ .membership = inner }),
                else => {},
            }
        },
        .op => |app| try self.emitExtUnfoldOp(b, block, app, x_id, unfolds, out, wa, &stack),
    };
}

/// Process ONE `op(args…)` for extensionality unfolding: instantiate the matching cited membership
/// lemma at (args…, x) — cite + forall_elim per op-arg then x, dedup + record the premise — and
/// QUEUE the op's set-typed args onto `stack` (nested operators unfold too). Was self-recursive;
/// now pushes follow-up `.op` work instead. `Work`/`stack` are the driver's (comptime-typed).
fn emitExtUnfoldOp(self: *Prove, b: *Accelerant.Builder, block: *std.ArrayList(ast.Step), app: term.Node.App, x_id: TermId, unfolds: []const ExtUnfold, out: *std.ArrayList(TautAst.Prem), wa: std.mem.Allocator, stack: anytype) Error!void {
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
    // helper: queue the op's set-typed (app) args, REVERSED so arg 0 processes first.
    const queueArgs = struct {
        fn f(p: *Prove, oa: []const TermId, wal: std.mem.Allocator, st: anytype) Error!void {
            var i: usize = oa.len;
            while (i > 0) {
                i -= 1;
                const an = p.pool.get(oa[i]);
                if (an == .app) try st.append(wal, .{ .op = an.app });
            }
        }
    }.f;
    const u = lemma orelse {
        // no cited lemma for this op — leave the atom opaque, but unfold set-typed args.
        try queueArgs(self, op_args, wa, stack);
        return;
    };

    // cite the lemma; forall_elim at each op-arg, then at x.
    const cite_label = try self.freshNamed("membership-lemma");
    const word: []const u8 = "cite";
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

    // queue the operator's set-typed arguments (nested operators unfold too).
    try queueArgs(self, op_args, wa, stack);
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
    // collect one `nonneg(x)` per distinct nat-sorted fvar. Iterative work-stack; the `seen` dedup
    // makes emission order-independent. NOTE the original emits the fvar's `nonneg` on FIRST sight
    // in traversal order — dedup by name means the SET is identical regardless of stack order.
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        switch (node) {
            .fvar => |v| {
                if (v.sort != nat) continue;
                const gop = seen.getOrPut(self.ctx.arena, v.name) catch return error.OutOfMemory;
                if (gop.found_existing) continue;
                try out.append(self.ctx.arena, try self.pool.addApp(.pred, nn, &.{cur}));
            },
            else => try self.pool.pushChildren(&stack, wa, node),
        }
    }
}

fn collectArithSyms(self: *Prove, id: TermId, s: *presburger_mod.Symbols) Error!void {
    // resolve the arithmetic vocabulary by well-known name over the whole term. Iterative work-
    // stack; field-setting is order-independent (a name maps to one sym).
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        switch (node) {
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
                try self.pool.pushChildren(&stack, wa, node);
            },
            .eq, .not, .bin, .quant => try self.pool.pushChildren(&stack, wa, node),
            else => {},
        }
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
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), self.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, id) catch return true; // OOM conservative
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        switch (node) {
            .app, .pred => |ap| if (ap.sym == want) return true,
            else => {},
        }
        self.pool.pushChildren(&stack, a, node) catch return true;
    }
    return false;
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
    // ADMIT: the arg-count validation ran in produceArithmetic. Everything below RESOLVES the
    // cited premises (resolveFactRef) and runs the certifier/decision-procedure chain. Skip that
    // expensive path under `--fast`.
    if (self.admit_mode) {
        self.admit_ok = true;
        return null;
    }
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
    } else if (try self.arithMixedCert(&cert, &body_steps, goal_p, &proved_prop, prems, symbols)) {
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

    // guard premises for the abstracted caller-locals (13e; no-op outside a transfer).
    const n_guards = try self.guardPremises(abs, &local_formulae, &local_cites);
    const inner_prop = try self.impliesChain(goal_p, local_formulae.items);
    const steps = try self.wrapSimplifyPremises(b, local_cites.items, local_formulae.items, goal_p, body_steps, n_guards);

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

/// First-order match: bind each `pattern` fvar (by name) so substituting yields `target`. Iterative
/// parallel two-tree walk (was native recursion) over a work-stack of `(pat, target)` pairs that
/// must ALL match (a conjunction — stack order irrelevant; the `binds` re-encounter check is
/// order-independent). Scratch on ctx.gpa; OOM → no match.
fn arithMatchPattern(self: *Prove, pattern: []const term.Node.Fvar, pat: TermId, target: TermId, binds: *std.AutoHashMapUnmanaged(StrId, TermId)) Error!bool {
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList([2]TermId) = .empty;
    try stack.append(wa, .{ pat, target });
    while (stack.pop()) |pair| {
        const p = pair[0];
        const t = pair[1];
        const pn = self.pool.get(p);
        if (pn == .fvar) {
            const bound = for (pattern) |pv| {
                if (pv.name == pn.fvar.name) break true;
            } else false;
            if (bound) {
                if (binds.get(pn.fvar.name)) |prev| {
                    if (!self.pool.alphaEq(prev, t)) return false;
                } else binds.put(self.ctx.arena, pn.fvar.name, t) catch return error.OutOfMemory;
                continue;
            }
            const tn = self.pool.get(t);
            if (!(tn == .fvar and tn.fvar.name == pn.fvar.name and tn.fvar.sort == pn.fvar.sort)) return false;
            continue;
        }
        const tn = self.pool.get(t);
        if (std.meta.activeTag(pn) != std.meta.activeTag(tn)) return false;
        switch (pn) {
            .bvar => if (pn.bvar != tn.bvar) return false,
            .fvar => unreachable,
            .app => |a| {
                if (a.sym != tn.app.sym or a.args_len != tn.app.args_len) return false;
                for (self.pool.args(a), self.pool.args(tn.app)) |x, y| try stack.append(wa, .{ x, y });
            },
            .pred => |a| {
                if (a.sym != tn.pred.sym or a.args_len != tn.pred.args_len) return false;
                for (self.pool.args(a), self.pool.args(tn.pred)) |x, y| try stack.append(wa, .{ x, y });
            },
            .eq => |pp| {
                try stack.append(wa, .{ pp.lhs, tn.eq.lhs });
                try stack.append(wa, .{ pp.rhs, tn.eq.rhs });
            },
            .not => |tt| try stack.append(wa, .{ tt, tn.not }),
            .bin => |bb| {
                if (bb.op != tn.bin.op) return false;
                try stack.append(wa, .{ bb.lhs, tn.bin.lhs });
                try stack.append(wa, .{ bb.rhs, tn.bin.rhs });
            },
            .quant => |q| {
                if (!(q.q == tn.quant.q and q.sort == tn.quant.sort)) return false;
                try stack.append(wa, .{ q.body, tn.quant.body });
            },
        }
    }
    return true;
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
    // collect the distinct scale literals k>=2 from `mul(k, _)` subterms. Iterative work-stack; the
    // `out` dedup makes order-independent.
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, t);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        switch (node) {
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
                try self.pool.pushChildren(&stack, wa, node);
            },
            .eq, .not, .bin, .quant => try self.pool.pushChildren(&stack, wa, node),
            else => {},
        }
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

/// The MIXED-D2 certifier: a goal whose boolean structure mixes propositional atoms with
/// linear/order (theory) atoms. Peel the ∀ prefix + strip the leading `->` premises (surfaced
/// as local hypotheses), then prove the residual body by a propositional-skeleton proof
/// (excluded-middle split + `or_elim` per atom, like the tautology cert) whose leaves are
/// discharged EITHER propositionally (an assumed literal) OR by the arithmetic equation/order
/// certs (a theory atom, closed from the branch's assumed theory literals). Every step is
/// kernel-checked. Declines (false) when `smt.decideMixed` doesn't confirm validity, when the
/// atom count exceeds the limit, or when a theory leaf can't be discharged.
fn arithMixedCert(self: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const peel = try self.arithPeel(goal_p);
    // strip the body's leading `->` antecedents into local hypotheses (assume blocks); each
    // becomes a theory/prop premise available to the skeleton + theory leaves.
    var body = peel.body;
    var strip_assumes: std.ArrayList(TermId) = .empty; // the stripped antecedents, in order
    while (true) {
        const node = self.pool.get(body);
        if (node != .bin or node.bin.op != .implies) break;
        try strip_assumes.append(self.ctx.arena, node.bin.lhs);
        body = node.bin.rhs;
    }
    // the body must be genuinely MIXED — a boolean combination (bin/not) mentioning at least
    // one propositional (non-theory) atom; a pure equation/order/exists is another cert's job.
    const bn = self.pool.get(body);
    if (bn != .bin and bn != .not) return false;

    // collect the atoms (premises + stripped antecedents + body); decide validity.
    var decide_prems: std.ArrayList(TermId) = .empty;
    for (prems) |p| try decide_prems.append(self.ctx.arena, p.formula);
    try decide_prems.appendSlice(self.ctx.arena, strip_assumes.items);
    if (symbols.nonneg) |nn| if (symbols.nat) |nat| {
        var seen: std.AutoHashMapUnmanaged(StrId, void) = .empty;
        try self.collectArithNonneg(body, nat, nn, &seen, &decide_prems);
        for (decide_prems.items[0 .. prems.len + strip_assumes.items.len]) |pf| try self.collectArithNonneg(pf, nat, nn, &seen, &decide_prems);
    };
    const verdict = smt.decideMixed(self.ctx.arena, self.pool, symbols, decide_prems.items, body) catch return error.OutOfMemory;
    if (verdict != .valid) return false;

    // the skeleton's atoms (premises + stripped + body); over-cap declines.
    var atoms: std.ArrayList(TermId) = .empty;
    for (prems) |p| try smt.collectAtoms(self.ctx.arena, self.pool, &atoms, p.formula);
    for (strip_assumes.items) |a| try smt.collectAtoms(self.ctx.arena, self.pool, &atoms, a);
    try smt.collectAtoms(self.ctx.arena, self.pool, &atoms, body);
    if (atoms.items.len > smt.atom_limit) return false;

    const assignment = try self.ctx.arena.alloc(?bool, atoms.items.len);
    @memset(assignment, null);
    const lit_blocks = try self.ctx.arena.alloc(?StrId, atoms.items.len);
    @memset(lit_blocks, null);

    // the stripped antecedents each get an assume-block (restated hypothesis); the cited
    // premises (LOCAL restated / GLOBAL cited) provide their labels directly.
    var mixed: MixedAst = .{
        .p = self,
        .cert = cert,
        .body = body,
        .atoms = atoms.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
        .symbols = symbols,
    };

    // emit the cited-premise + stripped-antecedent hypotheses so their theory atoms are
    // available to the leaves, then the skeleton proof. We build inside the ∀-`fix` shell
    // (via wrapArithForall) after assembling the body proof.
    var body_steps: std.ArrayList(ast.Step) = .empty;
    // GLOBAL cited premises: cite them; LOCAL cited premises: restated hyp label lives in the
    // schema-antecedent wrapper (packageArith). Register both as leaf-usable premises.
    for (prems) |p| {
        const label = if (p.local) p.hyp else try cert.citeGlobalPremise(&body_steps, p);
        try mixed.premise_labels.append(self.ctx.arena, .{ .formula = p.formula, .label = label });
    }
    // stripped antecedents become assume blocks wrapping the rest; emit the skeleton inside the
    // innermost. Build the skeleton first, then nest the assume blocks outward.
    var inner: std.ArrayList(ast.Step) = .empty;
    // restate each stripped antecedent's hypothesis inside its block (labels created here).
    const strip_labels = try self.ctx.arena.alloc(StrId, strip_assumes.items.len);
    const strip_blocks = try self.ctx.arena.alloc(StrId, strip_assumes.items.len);
    for (strip_assumes.items, strip_labels, strip_blocks) |a, *lbl, *blk| {
        lbl.* = try self.freshNamed("mixed-hyp");
        blk.* = try self.freshNamed("mixed-assume");
        try mixed.premise_labels.append(self.ctx.arena, .{ .formula = a, .label = lbl.* });
    }
    if (!try mixed.deriveGoal(&inner)) return false;

    // nest the stripped antecedents' assume blocks (innermost = last antecedent), exporting
    // `a_i -> …` out through each with implies_intro.
    var wrapped_body = inner.items;
    var residual = body;
    var i = strip_assumes.items.len;
    while (i > 0) {
        i -= 1;
        var blk_body: std.ArrayList(ast.Step) = .empty;
        try blk_body.append(self.ctx.arena, try cert.b.claimStep(strip_labels[i], try cert.b.termExpr(strip_assumes.items[i]), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, strip_blocks[i])));
        try blk_body.appendSlice(self.ctx.arena, wrapped_body);
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(self.ctx.arena, try cert.b.assumeStep(strip_blocks[i], try cert.b.termExpr(strip_assumes.items[i]), blk_body.items));
        residual = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = strip_assumes.items[i], .rhs = residual } });
        _ = try cert.claim(&lvl, residual, "implies_intro", &.{}, &.{strip_blocks[i]});
        wrapped_body = lvl.items;
    }
    try body_steps.appendSlice(self.ctx.arena, wrapped_body);

    // re-generalize under the ∀ eigenvariables.
    const wrapped = try self.wrapArithForall(cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(self.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// The mixed-skeleton certificate emitter (D2): a propositional excluded-middle/or_elim
/// skeleton over the goal's atoms whose leaves are discharged EITHER by an assumed literal
/// (propositional) OR by the arithmetic equation/order certs (a theory atom, closed from the
/// branch's assumed theory literals). Mirrors `TautAst` but adds theory-leaf discharge.
const MixedAst = struct {
    p: *Prove,
    cert: *ArithCert,
    body: TermId,
    atoms: []const TermId,
    assignment: []?bool,
    /// per atom: the assume-block LABEL whose hypothesis is the (positive/negative) literal
    lit_blocks: []?StrId,
    symbols: presburger_mod.Symbols,
    /// premises (cited + stripped antecedents) usable as theory-leaf rewrite rules: formula +
    /// the label of a step/hypothesis proving it.
    premise_labels: std.ArrayList(struct { formula: TermId, label: StrId }) = .empty,

    fn pool(self: *const MixedAst) *term.Pool {
        return self.p.pool;
    }

    fn eval(self: *const MixedAst, f: TermId) ?bool {
        return smt.eval(self.pool(), self.atoms, self.assignment, f);
    }

    /// Is `atom` a theory (linear/order) atom the arithmetic certs can discharge?
    fn isTheory(self: *const MixedAst, atom: TermId) bool {
        return switch (self.pool().get(atom)) {
            .eq => true,
            .pred => |pr| self.p.symIs(pr.sym, self.symbols.less_than),
            else => false,
        };
    }

    /// The assume-block label whose hypothesis is the literal for a propositional atom `f`.
    fn litBlock(self: *const MixedAst, f: TermId) StrId {
        for (self.atoms, self.lit_blocks) |a, blk| {
            if (self.pool().alphaEq(a, f)) return blk.?;
        }
        unreachable;
    }

    /// The theory literals assumed TRUE on the current branch (assigned atoms + always-true
    /// premises), as `ArithPremise`s the equation/order certs use as rewrite rules. Each needs
    /// a citable step label: an assigned atom cites its split assume-block hypothesis (restated
    /// into `block`); a premise cites its own label.
    fn theoryPremises(self: *MixedAst, block: *std.ArrayList(ast.Step)) Error![]const ArithPremise {
        var out: std.ArrayList(ArithPremise) = .empty;
        // premises whose formula is a theory atom (or a conjunction of them — restate atoms).
        for (self.premise_labels.items) |pl| {
            if (self.isTheory(pl.formula)) {
                try out.append(self.p.ctx.arena, .{ .formula = pl.formula, .local = true, .hyp = pl.label, .head = undefined, .is_axiom = false });
            }
        }
        // atoms assigned TRUE that are theory atoms: restate their literal hypothesis.
        for (self.atoms, self.assignment) |a, v| {
            if (v != true) continue;
            if (!self.isTheory(a)) continue;
            const restated = try self.p.freshNamed("mixed-theory");
            try block.append(self.p.ctx.arena, try self.cert.b.claimStep(restated, try self.cert.b.termExpr(a), .by, try self.p.internStr("hypothesis"), &.{}, try self.p.oneRef(self.cert.b, self.litBlock(a))));
            try out.append(self.p.ctx.arena, .{ .formula = a, .local = true, .hyp = restated, .head = undefined, .is_axiom = false });
        }
        return out.items;
    }

    /// Prove `self.body` in `block`. A refuted premise closes by `absurd`; a true goal derives
    /// structurally (theory leaves via the arith certs); a fully-decided branch that is
    /// theory-UNSAT derives a theory contradiction; otherwise split on the first unassigned
    /// atom via excluded-middle + `or_elim`.
    fn deriveGoal(self: *MixedAst, block: *std.ArrayList(ast.Step)) Error!bool {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        const Frame = union(enum) {
            expand: *std.ArrayList(ast.Step),
            arm_right: struct { idx: usize, right: *OpenBlock },
            finish: struct { block: *std.ArrayList(ast.Step), idx: usize, atom: TermId, not_atom: TermId, lem: StrId, left: *OpenBlock, right: *OpenBlock },
        };
        var work: std.ArrayList(Frame) = .empty;
        var failed = false;
        try work.append(sa, .{ .expand = block });

        while (work.pop()) |frame| {
            if (failed) continue; // a leaf/theory discharge failed; drain, then return false.
            switch (frame) {
                .expand => |blk| {
                    // a premise assumed false on this branch → absurd (rare; premises are true).
                    const refuted_idx: ?usize = for (self.premise_labels.items, 0..) |pl, i| {
                        if (self.eval(pl.formula) == false) break i;
                    } else null;
                    if (refuted_idx) |ri| {
                        const pl = self.premise_labels.items[ri];
                        if (try self.deriveFalse(blk, pl.formula)) |refuted| {
                            _ = try self.cert.claim(blk, self.body, "absurd", &.{}, &.{ pl.label, refuted });
                        } else failed = true;
                        continue;
                    }
                    if (self.eval(self.body) == true) {
                        if ((try self.deriveTrue(blk, self.body)) == null) failed = true;
                        continue;
                    }
                    // find the first unassigned atom.
                    const unassigned = for (self.assignment, 0..) |v, i| {
                        if (v == null) break i;
                    } else null;
                    if (unassigned == null) {
                        // fully decided, body false, no premise refuted: theory-UNSAT branch.
                        if (!try self.deriveTheoryContradiction(blk)) failed = true;
                        continue;
                    }
                    const idx = unassigned.?;
                    const atom = self.atoms[idx];
                    const not_atom = try self.pool().add(.{ .not = atom });
                    const disj = try self.pool().add(.{ .bin = .{ .op = .or_op, .lhs = atom, .rhs = not_atom } });
                    const lem = try self.emitLem(blk, atom, not_atom, disj);

                    const left = try sa.create(OpenBlock);
                    left.* = try self.openBlock();
                    const right = try sa.create(OpenBlock);
                    right.* = try self.openBlock();

                    try work.append(sa, .{ .finish = .{ .block = blk, .idx = idx, .atom = atom, .not_atom = not_atom, .lem = lem, .left = left, .right = right } });
                    try work.append(sa, .{ .arm_right = .{ .idx = idx, .right = right } });
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
                    _ = try self.cert.claim(c.block, self.body, "or_elim", &.{}, &.{ c.lem, c.left.label, c.right.label });
                },
            }
        }
        return !failed;
    }

    /// A fully-decided theory-UNSAT branch: for each theory atom assigned FALSE, try to PROVE
    /// it (positively) from the true theory literals via the equation/order cert; on success,
    /// `absurd` the proof against the atom's assumed-false hypothesis, closing the branch to any
    /// goal. Returns false if no such contradiction can be built.
    fn deriveTheoryContradiction(self: *MixedAst, block: *std.ArrayList(ast.Step)) Error!bool {
        for (self.atoms, self.assignment) |a, v| {
            if (v != false) continue;
            if (!self.isTheory(a)) continue;
            var probe: std.ArrayList(ast.Step) = .empty;
            const tp = try self.theoryPremises(&probe);
            if (!try self.p.arithBodyEqCert(self.cert, &probe, a, tp, self.symbols)) continue;
            const proof = try self.p.arithLastLabel(probe.items);
            try block.appendSlice(self.p.ctx.arena, probe.items);
            // restate the assumed-false literal `not a` as a step (the assume-block hypothesis),
            // then `absurd` the positive proof against it (absurd wants s1 = P, s2 = not P).
            const not_a = try self.pool().add(.{ .not = a });
            const neg_ref = try self.emit(block, not_a, "hypothesis", &.{self.litBlock(a)});
            _ = try self.cert.claim(block, self.body, "absurd", &.{}, &.{ proof, neg_ref });
            return true;
        }
        return false;
    }

    const OpenBlock = struct { label: StrId, body: std.ArrayList(ast.Step) = .empty };

    fn openBlock(self: *MixedAst) Error!OpenBlock {
        return .{ .label = try self.p.freshNamed("mixed") };
    }

    fn finishBlock(self: *MixedAst, parent: *std.ArrayList(ast.Step), blk: *OpenBlock, formula: TermId) Error!void {
        try parent.append(self.p.ctx.arena, try self.cert.b.assumeStep(blk.label, try self.cert.b.termExpr(formula), blk.body.items));
    }

    fn hyp(self: *MixedAst, blk: *OpenBlock, formula: TermId) Error!StrId {
        const label = try self.p.freshNamed("mixed");
        try blk.body.append(self.p.ctx.arena, try self.cert.b.claimStep(label, try self.cert.b.termExpr(formula), .by, try self.p.internStr("hypothesis"), &.{}, try self.p.oneRef(self.cert.b, blk.label)));
        return label;
    }

    fn emit(self: *MixedAst, block: *std.ArrayList(ast.Step), formula: TermId, rule: []const u8, refs: []const StrId) Error!StrId {
        const toks = try self.p.ctx.arena.alloc(lexer.Token, refs.len);
        for (refs, toks) |r, *o| o.* = self.cert.b.tok(r);
        const label = try self.p.freshNamed("mixed");
        try block.append(self.p.ctx.arena, try self.cert.b.claimStep(label, try self.cert.b.termExpr(formula), .by, try self.p.internStrRt(rule), &.{}, toks));
        return label;
    }

    /// `atom or not atom` classically: not_intro on the negated disjunction, double_negation.
    fn emitLem(self: *MixedAst, block: *std.ArrayList(ast.Step), atom: TermId, not_atom: TermId, disj: TermId) Error!StrId {
        const not_disj = try self.pool().add(.{ .not = disj });
        const not_not = try self.pool().add(.{ .not = not_disj });
        var outer = try self.openBlock();
        const hyp_outer = try self.hyp(&outer, not_disj);
        var innerb = try self.openBlock();
        const hyp_inner = try self.hyp(&innerb, atom);
        const or_left = try self.emit(&innerb.body, disj, "or_intro_left", &.{hyp_inner});
        try self.finishBlock(&outer.body, &innerb, atom);
        const derived_not = try self.emit(&outer.body, not_atom, "not_intro", &.{ innerb.label, or_left, hyp_outer });
        const or_right = try self.emit(&outer.body, disj, "or_intro_right", &.{derived_not});
        try self.finishBlock(block, &outer, not_disj);
        const nn = try self.emit(block, not_not, "not_intro", &.{ outer.label, or_right, hyp_outer });
        return self.emit(block, disj, "double_negation", &.{nn});
    }

    /// Prove `f` (evaluates true) in `block`; return its label, or null on a theory-leaf
    /// discharge failure.
    fn deriveTrue(self: *MixedAst, block: *std.ArrayList(ast.Step), f: TermId) Error!?StrId {
        return self.deriveStructural(.true, block, f);
    }

    /// Prove `not f` (f evaluates false) in `block`; return its label, or null on failure.
    fn deriveFalse(self: *MixedAst, block: *std.ArrayList(ast.Step), f: TermId) Error!?StrId {
        return self.deriveStructural(.false, block, f);
    }

    const Mode = enum { true, false };

    /// The shared iterative engine behind `deriveTrue`/`deriveFalse` (was mutual native recursion
    /// over formula structure). Same post-order worklist as `TautAst.deriveStructural`, but a
    /// theory-leaf discharge can FAIL: on failure a leaf sets `failed`, the loop drains without
    /// emitting, and the entry returns null. Otherwise byte-identical step vocabulary + order.
    fn deriveStructural(self: *MixedAst, root_mode: Mode, root_block: *std.ArrayList(ast.Step), root_f: TermId) Error!?StrId {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        const Frame = union(enum) {
            expand: struct { mode: Mode, block: *std.ArrayList(ast.Step), f: TermId },
            combine_and: struct { block: *std.ArrayList(ast.Step), f: TermId },
            combine_or_left: struct { block: *std.ArrayList(ast.Step), f: TermId },
            combine_or_right: struct { block: *std.ArrayList(ast.Step), f: TermId },
            combine_true_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId },
            combine_true_implies_absurd: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId, conseq: TermId, hyp: StrId },
            combine_false_and: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, side: TermId, left_false: bool },
            combine_false_or: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, lhs: TermId, rhs: TermId },
            combine_false_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, rhs: TermId },
            combine_false_not: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId },
        };
        var work: std.ArrayList(Frame) = .empty;
        var results: std.ArrayList(StrId) = .empty;
        var failed = false;
        try work.append(sa, .{ .expand = .{ .mode = root_mode, .block = root_block, .f = root_f } });

        while (work.pop()) |frame| {
            if (failed) continue; // a theory leaf failed; drain without emitting.
            switch (frame) {
                .expand => |e| switch (e.mode) {
                    .true => switch (self.pool().get(e.f)) {
                        .bin => |bin| switch (bin.op) {
                            .and_op => {
                                try work.append(sa, .{ .combine_and = .{ .block = e.block, .f = e.f } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.lhs } });
                            },
                            .or_op => {
                                if (self.eval(bin.lhs) == true) {
                                    try work.append(sa, .{ .combine_or_left = .{ .block = e.block, .f = e.f } });
                                    try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.lhs } });
                                } else {
                                    try work.append(sa, .{ .combine_or_right = .{ .block = e.block, .f = e.f } });
                                    try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.rhs } });
                                }
                            },
                            .implies => {
                                const blk = try sa.create(OpenBlock);
                                blk.* = try self.openBlock();
                                if (self.eval(bin.rhs) == true) {
                                    try work.append(sa, .{ .combine_true_implies = .{ .block = e.block, .f = e.f, .blk = blk, .ante = bin.lhs } });
                                    try work.append(sa, .{ .expand = .{ .mode = .true, .block = &blk.body, .f = bin.rhs } });
                                } else {
                                    const h = try self.hyp(blk, bin.lhs);
                                    try work.append(sa, .{ .combine_true_implies_absurd = .{ .block = e.block, .f = e.f, .blk = blk, .ante = bin.lhs, .conseq = bin.rhs, .hyp = h } });
                                    try work.append(sa, .{ .expand = .{ .mode = .false, .block = &blk.body, .f = bin.lhs } });
                                }
                            },
                        },
                        .not => |inner| try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = inner } }),
                        else => {
                            // an atom assigned true. THEORY atom: discharge via arith cert; a
                            // failure bails the whole cert. Propositional: restate its assumption.
                            if (self.isTheory(e.f)) {
                                const tp = try self.theoryPremises(e.block);
                                if (!try self.p.arithBodyEqCert(self.cert, e.block, e.f, tp, self.symbols)) {
                                    failed = true;
                                } else {
                                    try results.append(sa, try self.p.arithLastLabel(e.block.items));
                                }
                            } else {
                                try results.append(sa, try self.emit(e.block, e.f, "hypothesis", &.{self.litBlock(e.f)}));
                            }
                        },
                    },
                    .false => switch (self.pool().get(e.f)) {
                        .bin => |bin| switch (bin.op) {
                            .and_op => {
                                const left_false = self.eval(bin.lhs) == false;
                                const side = if (left_false) bin.lhs else bin.rhs;
                                const nf = try self.pool().add(.{ .not = e.f });
                                try work.append(sa, .{ .combine_false_and = .{ .block = e.block, .f = e.f, .nf = nf, .side = side, .left_false = left_false } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = side } });
                            },
                            .or_op => {
                                const nf = try self.pool().add(.{ .not = e.f });
                                try work.append(sa, .{ .combine_false_or = .{ .block = e.block, .f = e.f, .nf = nf, .lhs = bin.lhs, .rhs = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bin.lhs } });
                            },
                            .implies => {
                                const nf = try self.pool().add(.{ .not = e.f });
                                try work.append(sa, .{ .combine_false_implies = .{ .block = e.block, .f = e.f, .nf = nf, .rhs = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.lhs } });
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
                    const rule: []const u8 = if (self.p.isBiconditionalShape(c.f)) "iff_intro" else "and_intro";
                    try results.append(sa, try self.emit(c.block, c.f, rule, &.{ left, right }));
                },
                .combine_or_left => |c| {
                    const l = results.pop().?;
                    try results.append(sa, try self.emit(c.block, c.f, "or_intro_left", &.{l}));
                },
                .combine_or_right => |c| {
                    const r = results.pop().?;
                    try results.append(sa, try self.emit(c.block, c.f, "or_intro_right", &.{r}));
                },
                .combine_true_implies => |c| {
                    _ = results.pop().?;
                    try self.finishBlock(c.block, c.blk, c.ante);
                    try results.append(sa, try self.emit(c.block, c.f, "implies_intro", &.{c.blk.label}));
                },
                .combine_true_implies_absurd => |c| {
                    const refuted = results.pop().?;
                    _ = try self.emit(&c.blk.body, c.conseq, "absurd", &.{ c.hyp, refuted });
                    try self.finishBlock(c.block, c.blk, c.ante);
                    try results.append(sa, try self.emit(c.block, c.f, "implies_intro", &.{c.blk.label}));
                },
                .combine_false_and => |c| {
                    const refuted = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    const elim = try self.emit(&blk.body, c.side, if (c.left_false) "and_elim_left" else "and_elim_right", &.{h});
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, elim, refuted }));
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
                    _ = try self.emit(&right.body, c.lhs, "absurd", &.{ rh, not_right });
                    try self.finishBlock(&blk.body, &right, c.rhs);
                    const conc = try self.emit(&blk.body, c.lhs, "or_elim", &.{ h, left.label, right.label });
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, conc, not_left }));
                },
                .combine_false_implies => |c| {
                    const not_conseq = results.pop().?;
                    const ante = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    const conseq = try self.emit(&blk.body, c.rhs, "modus_ponens", &.{ h, ante });
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, conseq, not_conseq }));
                },
                .combine_false_not => |c| {
                    const truth = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "not_intro", &.{ blk.label, truth, h }));
                },
            }
        }
        if (failed) return null;
        return results.items[0];
    }
};

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
    if (replay.period != 1) return self.arithCooperInduction(cert, out, peel, goal_p, proved_prop, symbols);

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
    const ok = try self.arithEmitExistsWitness(cert, &body_steps, peel.body, candidates.items, &.{}, symbols);
    if (!ok) return false;
    const wrapped = try self.wrapArithForall(cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(self.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Cooper layer 3 (period > 1): synthesize an induction on the single fixed variable to
/// certify a period-D `forall x; exists y; body`. Predicate P(k) = body[x:=k]; base P(ZERO)
/// and step `forall k; P(k) -> P(succ(k))` are proved by the witness search (the step unpacks
/// the IH witness and case-splits its disjunction, shifting the witness per residue arm using
/// the arm equation as a rewrite premise), then the `induction` schema is instantiated at P.
/// Declines (returns false) on a multi-fixed-variable goal or a missing symbol/lemma; every
/// emitted step is kernel-checked (an `instantiation induction(…)` step the generated
/// ProveTask re-demands + the kernel re-checks). The instance concludes `forall n; P(n)` =
/// the goal, so no ∀-re-generalization shell is needed.
fn arithCooperInduction(self: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), peel: ArithPeel, goal_p: TermId, proved_prop: *TermId, symbols: presburger_mod.Symbols) Error!bool {
    if (peel.eigen.len != 1) return false; // layer 3 = single induction variable
    const nat = symbols.nat orelse return false;
    const zero = symbols.zero orelse return false;
    const succ = symbols.succ orelse return false;
    // the `induction` schema must be declared in this proof's namespace (a parameterized
    // axiom) for the instantiation step to resolve.
    const induction_id = try self.internStrRt("induction");
    if (self.resolveArithSchema(induction_id) == null) return false;

    // P as a body closed over the induction variable: P(t) = open(p_closed, t).
    const x = peel.eigen[0];
    const p_closed = try self.pool.close(peel.body, x.name);
    const zero_t = try self.pool.addApp(.app, zero, &.{});

    // --- base case: P(ZERO) --------------------------------------------------------------
    const p_zero = try self.pool.open(p_closed, zero_t);
    const base_candidates = try self.arithWitnessCandidates(symbols, null);
    var base_steps: std.ArrayList(ast.Step) = .empty;
    if (!try self.arithEmitExistsWitness(cert, &base_steps, p_zero, base_candidates, &.{}, symbols)) return false;
    // the base's exists proof ends in a claim step proving `p_zero`; its label is citable.
    const base_cite = try self.arithLastLabel(base_steps.items);

    // --- step: forall k; P(k) -> P(succ(k)) ----------------------------------------------
    const k: term.Node.Fvar = .{ .name = try self.freshNamed("k"), .sort = nat };
    const k_id = try self.pool.add(.{ .fvar = .{ .name = k.name, .sort = nat } });
    const p_k = try self.pool.open(p_closed, k_id);
    const succ_k = try self.pool.addApp(.app, succ, &.{k_id});
    const p_succ_k = try self.pool.open(p_closed, succ_k);
    const step_impl = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = p_k, .rhs = p_succ_k } });

    // the IH existential var y0; the IH body (disjunction) opened at y0.
    const ihn = self.pool.get(p_k);
    if (ihn != .quant or ihn.quant.q != .exists) return false;
    const y0: term.Node.Fvar = .{ .name = try self.freshNamed("y"), .sort = ihn.quant.sort };
    const y0_id = try self.pool.add(.{ .fvar = .{ .name = y0.name, .sort = y0.sort } });
    const ih_body = try self.pool.open(ihn.quant.body, y0_id);

    // labels for the step's block structure (all `#`-mangled, collision-free).
    const ih_label = try self.freshNamed("inductive-hypothesis");
    const step_candidates = try self.arithWitnessCandidates(symbols, y0_id);

    // inside the unpack: restate the IH body (disjunction) by hypothesis, then case-split it,
    // each arm proving P(succ(k)) via the witness search using the arm equation as a premise.
    var unpack_body: std.ArrayList(ast.Step) = .empty;
    const ih_body_label = try self.freshNamed("ih-disjunct");
    const unpack_block_label = try self.freshNamed("with-witness");
    try unpack_body.append(self.ctx.arena, try cert.b.claimStep(ih_body_label, try cert.b.termExpr(ih_body), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, unpack_block_label)));
    if ((try self.arithEmitInductionCases(cert, &unpack_body, ih_body, ih_body_label, p_succ_k, step_candidates, symbols)) == null) return false;

    // the unpack block: `unpack y from <ih>` — draws the existential witness y0 out of the IH.
    const y0_sort_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(y0.sort)));
    const unpack_step: ast.Step = .{ .label = cert.b.tok(unpack_block_label), .body = .{ .unpack = .{
        .name = cert.b.tok(try self.displayName(y0.name)),
        .sort = cert.b.tok(y0_sort_name),
        .from = cert.b.tok(ih_label),
        .steps = unpack_body.items,
    } } };

    // the assume P(k) block: restate the IH, then unpack + case-split, exporting P(succ(k)).
    var assume_body: std.ArrayList(ast.Step) = .empty;
    const assume_block_label = try self.freshNamed("given-ih");
    try assume_body.append(self.ctx.arena, try cert.b.claimStep(ih_label, try cert.b.termExpr(p_k), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, assume_block_label)));
    try assume_body.append(self.ctx.arena, unpack_step);
    // export P(succ(k)) out of the unpack (exists_elim).
    _ = try cert.claim(&assume_body, p_succ_k, "exists_elim", &.{}, &.{unpack_block_label});
    const assume_step = try cert.b.assumeStep(assume_block_label, try cert.b.termExpr(p_k), assume_body.items);

    // the fix k block: assume P(k), conclude P(succ(k)), export the implication.
    var fix_body: std.ArrayList(ast.Step) = .empty;
    try fix_body.append(self.ctx.arena, assume_step);
    _ = try cert.claim(&fix_body, step_impl, "implies_intro", &.{}, &.{assume_block_label});
    const fixr = try cert.fixStep("cooper-step-fix", k.name, nat, fix_body.items);
    const step_forall = try self.closeForallVar(step_impl, k.name, nat);

    // assemble `out`: base steps, then the fix block, then the step's forall_intro, then the
    // induction instantiation. (base + step labels must precede the instantiation cite.)
    try out.appendSlice(self.ctx.arena, base_steps.items);
    try out.append(self.ctx.arena, fixr.step);
    const step_cite = try cert.claim(out, step_forall, "forall_intro", &.{}, &.{fixr.label});

    // --- instantiate the `induction` schema at P -----------------------------------------
    // build the predicate arg `fun x => P(x)` as a lambda AST expr (binder trims to the
    // eigenvar's display name, so the delaborated body's refs bind to it — single eigenvar,
    // no collision). The generated ProveTask re-demands the instance; the kernel re-checks it.
    const lambda_arg = try self.arithInductionLambda(cert.b, p_closed, x, nat);
    const args = try self.ctx.arena.alloc(*const ast.Expr, 1);
    args[0] = lambda_arg;
    const inst_label = try self.freshNamed("cooper-induction");
    const refs = try self.ctx.arena.alloc(lexer.Token, 2);
    refs[0] = cert.b.tok(base_cite);
    refs[1] = cert.b.tok(step_cite);
    try out.append(self.ctx.arena, .{ .label = cert.b.tok(inst_label), .body = .{ .claim = .{
        .formula = try cert.b.termExpr(goal_p),
        .kind = .using,
        .rule = cert.b.tok(try self.internStrRt("instantiation")),
        .schema = try self.wkCite("induction", cert.c),
        .args = args,
        .refs = refs,
    } } });
    proved_prop.* = goal_p;
    return true;
}

/// Candidate existential witnesses for the induction base/step: constant towers around ZERO
/// (`succ^0..3(ZERO)`, and over ℤ `prev^1..3(ZERO)`) and, in the step, the shifted IH witness
/// `y0` (`y0`, `succ(y0)`, `succ(succ(y0))`, and over ℤ `prev`-shifts). One of these proves the
/// residue-class arm at succ(k) (the bounded realization of the arbitrary-period shift table).
fn arithWitnessCandidates(self: *Prove, symbols: presburger_mod.Symbols, ih_witness: ?TermId) Error![]const TermId {
    var out: std.ArrayList(TermId) = .empty;
    const zero = symbols.zero orelse return out.items;
    const zero_t = try self.pool.addApp(.app, zero, &.{});
    for ([_]i128{ 0, 1, 2, 3, -1, -2, -3 }) |off| {
        if (try self.buildArithTowerSigned(off, zero_t, symbols)) |w| try out.append(self.ctx.arena, w);
    }
    if (ih_witness) |y0| {
        for ([_]i128{ 0, 1, 2, -1, -2 }) |off| {
            if (try self.buildArithTowerSigned(off, y0, symbols)) |w| try out.append(self.ctx.arena, w);
        }
    }
    return out.items;
}

/// Prove `goal` (= P(succ(k))) by an `or_elim` over `disj` (the IH witness disjunction at
/// y0). Each arm assumes one disjunct — an equation over k, y0 — restates it by hypothesis,
/// and proves `goal` by the witness search using that equation as a rewrite premise. Returns
/// the concluding `or_elim` step's label, or null if any arm fails.
///
/// A right-nested `or` was handled by self-recursion on the rhs; now an iterative
/// descend-then-unwind over the spine: DESCEND emits each level's left arm and seeds its
/// right-arm body (the next level's target block); UNWIND (innermost→outermost) wraps each
/// right body as its assume block and claims the level's `or_elim` — the same emission
/// order the recursion produced. Scratch stacks on the pool's GPA; the right bodies are
/// scratch-heap-allocated so their pointers stay stable across levels.
fn arithEmitInductionCases(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), disj: TermId, disj_label: StrId, goal: TermId, candidates: []const TermId, symbols: presburger_mod.Symbols) Error!?StrId {
    const root = self.pool.get(disj);
    if (root != .bin or root.bin.op != .or_op) return null;

    var scratch: std.heap.ArenaAllocator = .init(self.pool.gpa);
    defer scratch.deinit();
    const sa = scratch.allocator();

    const Level = struct {
        block: *std.ArrayList(ast.Step), // where this level's assume/or_elim steps land
        rhs: TermId,
        disj_label: StrId,
        left_label: StrId,
        right_label: StrId,
        right_body: *std.ArrayList(ast.Step),
    };
    var levels: std.ArrayList(Level) = .empty;

    var cur_disj = disj;
    var cur_label = disj_label;
    var cur_block = block;
    while (true) {
        const node = self.pool.get(cur_disj); // an `or` (root check above / descend condition below)
        // left arm: assume the lhs disjunct, prove goal at some witness using it as a premise.
        const left_label = try self.freshNamed("arm-left");
        const left_hyp = try self.freshNamed("arm-hyp");
        var left_body: std.ArrayList(ast.Step) = .empty;
        try left_body.append(self.ctx.arena, try cert.b.claimStep(left_hyp, try cert.b.termExpr(node.bin.lhs), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, left_label)));
        const lprem = try self.ctx.arena.dupe(ArithPremise, &.{.{ .formula = node.bin.lhs, .local = true, .hyp = left_hyp, .head = undefined, .is_axiom = false }});
        if (!try self.arithEmitExistsWitness(cert, &left_body, goal, candidates, lprem, symbols)) return null;
        try cur_block.append(self.ctx.arena, try cert.b.assumeStep(left_label, try cert.b.termExpr(node.bin.lhs), left_body.items));

        // right arm: the rhs disjunct (possibly itself an `or`, descended into).
        const right_label = try self.freshNamed("arm-right");
        const right_hyp = try self.freshNamed("arm-hyp");
        const right_body = try sa.create(std.ArrayList(ast.Step));
        right_body.* = .empty;
        try right_body.append(self.ctx.arena, try cert.b.claimStep(right_hyp, try cert.b.termExpr(node.bin.rhs), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, right_label)));
        try levels.append(sa, .{ .block = cur_block, .rhs = node.bin.rhs, .disj_label = cur_label, .left_label = left_label, .right_label = right_label, .right_body = right_body });

        const rn = self.pool.get(node.bin.rhs);
        if (rn == .bin and rn.bin.op == .or_op) {
            cur_disj = node.bin.rhs;
            cur_label = right_hyp;
            cur_block = right_body;
            continue;
        }
        const rprem = try self.ctx.arena.dupe(ArithPremise, &.{.{ .formula = node.bin.rhs, .local = true, .hyp = right_hyp, .head = undefined, .is_axiom = false }});
        if (!try self.arithEmitExistsWitness(cert, right_body, goal, candidates, rprem, symbols)) return null;
        break;
    }

    // unwind: close each level's right assume + or_elim, innermost first; the outermost
    // level's or_elim label (the last popped) is the result.
    var result: StrId = undefined;
    while (levels.pop()) |lvl| {
        try lvl.block.append(self.ctx.arena, try cert.b.assumeStep(lvl.right_label, try cert.b.termExpr(lvl.rhs), lvl.right_body.items));
        result = try cert.claim(lvl.block, goal, "or_elim", &.{}, &.{ lvl.disj_label, lvl.left_label, lvl.right_label });
    }
    return result;
}

/// Build the induction predicate arg `fun x: Nat => P(x)` as a lambda AST expr. The binder is
/// named by the eigenvar's display name (trimmed of the `#` mangle); the body delaborates
/// `p_closed` opened at the eigenvar, whose free-var refs trim to the same name and so re-bind
/// to the lambda binder (single eigenvar ⇒ no display collision).
fn arithInductionLambda(self: *Prove, b: *Accelerant.Builder, p_closed: TermId, x: term.Node.Fvar, nat: term.SortId) Error!*const ast.Expr {
    const x_id = try self.pool.add(.{ .fvar = .{ .name = x.name, .sort = nat } });
    const p_open = try self.pool.open(p_closed, x_id);
    const body = try b.termExpr(p_open);
    const bname = try self.displayName(x.name);
    const nat_name = self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(nat)));
    const binders = try self.ctx.arena.alloc(ast.Binder, 1);
    binders[0] = .{ .name = b.tok(bname), .sort = b.tok(nat_name) };
    const e = try self.ctx.arena.create(ast.Expr);
    e.* = .{ .lambda = .{ .tok = b.tok(InternPool.Index.none), .binders = binders, .body = body } };
    return e;
}

/// Resolve a schema by NAME in this proof's namespace (a `proven` FactKV `.schema` locator),
/// or null. A schema is a fact-with-params, so it lives in the FACT table.
fn resolveArithSchema(self: *Prove, name: StrId) ?InternPool.Index {
    const state = self.ctx.facts.lookup(self.ctx.io, .{ .namespace = self.ns, .name = name }) orelse return null;
    const ix = switch (state) {
        .proven => |x| x,
        .in_flight => return null,
    };
    return if (self.ctx.interner.keyOf(ix) == .schema) ix else null;
}

/// Close `body` (mentioning fvar `name`) into `forall name; …`.
fn closeForallVar(self: *Prove, body: TermId, name: StrId, sort: term.SortId) Error!TermId {
    const closed = try self.pool.close(body, name);
    return self.pool.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = name, .body = closed } });
}

/// Prove `exists y; disj` in `block` at one of `candidates`: open the body at the witness,
/// prove a provable arm of the (possibly disjunctive) instance, lift through the or-intro
/// path, and emit `exists_intro`. Returns false if no candidate closes.
fn arithEmitExistsWitness(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), exists_body: TermId, candidates: []const TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const en = self.pool.get(exists_body);
    if (en != .quant or en.quant.q != .exists) return false;
    for (candidates) |wtn| {
        const instance = try self.pool.open(en.quant.body, wtn);
        // try each arm of the right/left or-nest.
        var arm_steps: std.ArrayList(ast.Step) = .empty;
        const found = (try self.arithProveDisjArm(cert, &arm_steps, instance, prems, symbols)) orelse continue;
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
fn arithProveDisjArm(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), instance: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!?ArithArm {
    var path: std.ArrayList(bool) = .empty;
    var cur = instance;
    while (true) {
        const node = self.pool.get(cur);
        if (node == .bin and node.bin.op == .or_op) {
            var probe: std.ArrayList(ast.Step) = .empty;
            if (try self.arithBodyEqCert(cert, &probe, node.bin.lhs, prems, symbols)) {
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
        if (try self.arithBodyEqCert(cert, &probe, cur, prems, symbols)) {
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
///
/// The EXISTS case is a witness search: `exists y; inner` tries constant witnesses
/// succ^k(ZERO), k=0..33, proving `inner[y:=witness]` by the equation/order cert, then
/// `exists_intro` (the old arithCertCore C2c). Handles e.g. `exists y; add(y,y) =
/// succ(succ(ZERO))` (witness y=1). A NESTED exists recursed; now an explicit backtracking
/// frame stack — one frame per open exists level, `k` its next witness index; a child frame
/// lives for exactly one parent witness attempt (child exhausted → pop → parent advances).
/// On a leaf success the leaf steps + one `exists_intro` per level (innermost→outermost,
/// each citing the previous last label) flatten into `block` — the same step sequence the
/// recursive appendSlice chain produced. Scratch on the pool's GPA.
fn arithBodyEqCert(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), body: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const node = self.pool.get(body);
    if (node == .eq) {
        return self.arithEmitEquation(cert, block, node.eq.lhs, node.eq.rhs, prems, symbols);
    }
    if (node == .pred and self.symIs(node.pred.sym, symbols.less_than) and node.pred.args_len == 2) {
        return self.arithEmitOrder(cert, block, body, prems, symbols);
    }
    if (node != .quant or node.quant.q != .exists) return false;

    const zero = symbols.zero orelse return false;
    const zero_t = try self.pool.addApp(.app, zero, &.{});

    var scratch: std.heap.ArenaAllocator = .init(self.pool.gpa);
    defer scratch.deinit();
    const sa = scratch.allocator();

    const Frame = struct {
        formula: TermId, // the `exists y; inner` this level proves
        inner: TermId, // its quant body
        k: usize = 0, // next witness index (0..34)
        witness: TermId = undefined, // current attempt's witness (set before descending)
    };
    var stack: std.ArrayList(Frame) = .empty;
    try stack.append(sa, .{ .formula = body, .inner = node.quant.body });

    while (stack.items.len > 0) {
        const f = &stack.items[stack.items.len - 1];
        if (f.k >= 34) {
            // exhausted: this level fails; the parent advances to its next witness.
            _ = stack.pop();
            continue;
        }
        const witness = (try self.buildArithTowerSigned(@intCast(f.k), zero_t, symbols)) orelse {
            // tower construction failing stops the search at this level (the recursive `break`).
            _ = stack.pop();
            continue;
        };
        f.k += 1;
        f.witness = witness;
        const instance = try self.pool.open(f.inner, witness);
        const in = self.pool.get(instance);
        if (in == .quant and in.quant.q == .exists) {
            // nested exists: a child frame for this attempt. (f is invalidated by the append.)
            try stack.append(sa, .{ .formula = instance, .inner = in.quant.body });
            continue;
        }
        // leaf attempt into a fresh probe (discarded on failure, like the recursive version).
        var probe: std.ArrayList(ast.Step) = .empty;
        const ok = if (in == .eq)
            try self.arithEmitEquation(cert, &probe, in.eq.lhs, in.eq.rhs, prems, symbols)
        else if (in == .pred and self.symIs(in.pred.sym, symbols.less_than) and in.pred.args_len == 2)
            try self.arithEmitOrder(cert, &probe, instance, prems, symbols)
        else
            false;
        if (!ok) continue; // next witness at this level
        // SUCCESS: flatten — the leaf steps, then one exists_intro per level innermost first
        // (accumulated in `probe`), the whole sequence + the root's exists_intro into `block`.
        var inst_label = try self.arithLastLabel(probe.items);
        var i = stack.items.len;
        while (i > 0) {
            i -= 1;
            const fr = stack.items[i];
            const out: *std.ArrayList(ast.Step) = if (i == 0) blk: {
                try block.appendSlice(self.ctx.arena, probe.items);
                break :blk block;
            } else &probe;
            const arg1 = try self.ctx.arena.alloc(*const ast.Expr, 1);
            arg1[0] = try cert.b.termExpr(fr.witness);
            const label = try self.freshNamed("arith");
            const refs = try self.ctx.arena.alloc(lexer.Token, 1);
            refs[0] = cert.b.tok(inst_label);
            try out.append(self.ctx.arena, try cert.b.claimStep(label, try cert.b.termExpr(fr.formula), .by, try self.internStr("exists_intro"), arg1, refs));
            inst_label = label;
        }
        return true;
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
    // PREMISE ground rules: a cited equation premise `P_l = P_r` joins the normalizer as a
    // ground rewrite `P_l -> P_r`, firing where `P_l` occurs literally (e.g. the Cooper
    // induction-step arm rewrites the fixed var by its case hypothesis `k = add(y0, y0)`). A
    // self-embedding rule (`P_l` a subterm of `P_r`) would loop — skip it.
    try self.pushPremiseRules(&rules, &cites, prems);
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
    const d = (try self.arithOrderDiff(s, t, symbols)) orelse
        // no GROUND difference: try an order PREMISE + transitivity (e.g. prove
        // `less_than(a, succ(b))` from the premise `less_than(a, b)` by chaining a ground
        // edge `less_than(b, succ(b))`). Only fires when a premise anchors the difference.
        return self.arithEmitOrderFromPremise(cert, block, s, t, prems, symbols);
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

/// Prove `less_than(s, t)` from an order PREMISE `less_than(s, m)` (matching the goal's lower
/// bound) via `lessThanElim` + `lessThanIntro`: unpack the premise's witness `w` (so
/// `add(s, succ(w)) = m`), then the goal's own difference `d = arithOrderDiff(m, t)` gives
/// `add(m, succ(d)) = t`; substituting `m` yields `add(s, succ(add(succ(w), d))) = t`, i.e. the
/// goal's difference is `add(succ(w), d)`. Emit: the elim instance + mp, an `unpack w` block
/// proving the goal via `lessThanIntro` (the difference equation reduced under the witness
/// equation), and `exists_elim` exporting `less_than(s, t)`. Declines when no premise anchors
/// `s`, the goal→premise difference isn't a ground tower, or a lemma is absent.
fn arithEmitOrderFromPremise(self: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, prems: []const ArithPremise, symbols: presburger_mod.Symbols) Error!bool {
    const less_than = symbols.less_than orelse return false;
    const succ = symbols.succ orelse return false;
    const add = symbols.add orelse return false;
    const elim_stmt = (try self.arithLemmaFormula("lessThanElim", symbols)) orelse return false;
    const intro_stmt = (try self.arithLemmaFormula("lessThanIntro", symbols)) orelse return false;
    for (prems) |p| {
        const pn = self.pool.get(p.formula);
        if (pn != .pred or !self.symIs(pn.pred.sym, less_than) or pn.pred.args_len != 2) continue;
        const pargs = self.pool.args(pn.pred);
        const pl = pargs[0];
        const pr = pargs[1]; // premise: less_than(pl, pr)
        if (!self.pool.alphaEq(pl, s)) continue; // need the premise's lower bound = goal's

        // the goal's difference over the premise's upper bound `pr`: add(pr, succ(dg)) = t.
        const dg = (try self.arithOrderDiff(pr, t, symbols)) orelse continue;

        // cite the premise, instantiate lessThanElim at (pl, pr), MP → exists w; add(pl,succ(w))=pr.
        const prem_label = if (p.local) p.hyp else try cert.citeGlobalPremise(block, p);
        const elim_label = try cert.citeLemma(block, "lessThanElim", elim_stmt);
        const elim = try cert.elimChain(block, elim_label, elim_stmt, &.{ pl, pr });
        const exists_f = self.pool.get(elim.formula).bin.rhs; // exists w; add(pl, succ(w)) = pr
        const exists_label = try cert.claim(block, exists_f, "modus_ponens", &.{}, &.{ elim.label, prem_label });

        // unpack the witness w; inside prove less_than(s, t) via lessThanIntro at difference
        // `add(succ(w), dg)` (add(s, succ(add(succ(w), dg))) = t reduces under add(s,succ(w))=pr).
        const en = self.pool.get(exists_f);
        const w: term.Node.Fvar = .{ .name = try self.freshNamed("w"), .sort = en.quant.sort };
        const w_id = try self.pool.add(.{ .fvar = .{ .name = w.name, .sort = w.sort } });
        const wit_eq = try self.pool.open(en.quant.body, w_id); // add(pl, succ(w)) = pr
        const unpack_block = try self.freshNamed("order-witness");
        const wit_hyp = try self.freshNamed("witness-eq");
        var ub: std.ArrayList(ast.Step) = .empty;
        try ub.append(self.ctx.arena, try cert.b.claimStep(wit_hyp, try cert.b.termExpr(wit_eq), .by, try self.internStr("hypothesis"), &.{}, try self.oneRef(cert.b, unpack_block)));
        // FLIP the witness eq to `pr = add(s, succ(w))` (symmetry): the additive normalizer lifts
        // `add(s, succ(w))` to a `succ`-tower, so a forward rule `add(s,succ(w)) -> pr` would never
        // fire; the reverse rule `pr -> add(s, succ(w))` rewrites the opaque `pr` into the tower.
        const wn = self.pool.get(wit_eq).eq;
        const flipped = try self.pool.add(.{ .eq = .{ .lhs = wn.rhs, .rhs = wn.lhs } });
        const flip_hyp = try cert.claim(&ub, flipped, "symmetry", &.{}, &.{wit_hyp});
        // difference d = add(succ(w), dg); prove add(s, succ(d)) = t using the flipped witness eq.
        const d = try self.pool.addApp(.app, add, &.{ try self.pool.addApp(.app, succ, &.{w_id}), dg });
        const goal = try self.pool.addApp(.pred, less_than, &.{ s, t });
        const succ_d = try self.pool.addApp(.app, succ, &.{d});
        const eq_lhs = try self.pool.addApp(.app, add, &.{ s, succ_d });
        const wit_prem = try self.ctx.arena.dupe(ArithPremise, &.{.{ .formula = flipped, .local = true, .hyp = flip_hyp, .head = undefined, .is_axiom = false }});
        if (!try self.arithEmitEquation(cert, &ub, eq_lhs, t, wit_prem, symbols)) continue;
        const eq_label = try self.arithLastLabel(ub.items);
        const intro_label = try cert.citeLemma(&ub, "lessThanIntro", intro_stmt);
        const intro_elim = try cert.elimChain(&ub, intro_label, intro_stmt, &.{ s, d, t });
        _ = try cert.claim(&ub, goal, "modus_ponens", &.{}, &.{ intro_elim.label, eq_label });

        const unpack_step: ast.Step = .{ .label = cert.b.tok(unpack_block), .body = .{ .unpack = .{
            .name = cert.b.tok(try self.displayName(w.name)),
            .sort = cert.b.tok(self.ctx.interner.nameOf(@enumFromInt(@intFromEnum(w.sort)))),
            .from = cert.b.tok(exists_label),
            .steps = ub.items,
        } } };
        try block.append(self.ctx.arena, unpack_step);
        _ = try cert.claim(block, goal, "exists_elim", &.{}, &.{unpack_block});
        return true;
    }
    return false;
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
fn isArithLeaf(self: *Prove, t0: TermId, symbols: presburger_mod.Symbols) bool {
    // linear neg-peel recursion → loop.
    var t = t0;
    const node = while (true) {
        const n = self.pool.get(t);
        if (n == .app and self.symIs(n.app.sym, symbols.neg) and n.app.args_len == 1) {
            t = self.pool.args(n.app)[0];
            continue;
        }
        break n;
    };
    if (node == .fvar) return true;
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

/// Push each equation premise `P_l = P_r` as a ground rewrite rule (`P_l -> P_r`) with its
/// citation (LOCAL restated-hypothesis label / GLOBAL fact cite). A self-embedding rule
/// (`P_l` a subterm of `P_r`) is skipped — it would loop the normalizer.
fn pushPremiseRules(self: *Prove, rules: *std.ArrayList(simplify_mod.Rule), cites: *std.ArrayList(EqCert.RuleCite), prems: []const ArithPremise) Error!void {
    for (prems) |p| {
        const pn = self.pool.get(p.formula);
        if (pn != .eq) continue;
        if (self.containsSubterm(pn.eq.rhs, pn.eq.lhs)) continue;
        try rules.append(self.ctx.arena, .{ .binders = &.{}, .lhs = pn.eq.lhs, .rhs = pn.eq.rhs, .formula = p.formula });
        try cites.append(self.ctx.arena, if (p.local)
            .{ .local = .{ .hyp = p.hyp } }
        else
            .{ .global = .{ .head = p.head, .is_axiom = p.is_axiom } });
    }
}

/// Does `hay` contain `needle` (alpha-equal) as a subterm?
fn containsSubterm(self: *Prove, hay: TermId, needle: TermId) bool {
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), self.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, hay) catch return true; // OOM conservative
    while (stack.pop()) |cur| {
        if (self.pool.alphaEq(cur, needle)) return true;
        self.pool.pushChildren(&stack, a, self.pool.get(cur)) catch return true;
    }
    return false;
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
    if (std.mem.eql(u8, name, "lessThanElim")) {
        // forall a, b; less_than(a, b) -> exists d; add(a, succ(d)) = b
        const add = symbols.add orelse return null;
        const less_than = symbols.less_than orelse return null;
        const succ = symbols.succ orelse return null;
        const a = try mkfv(self, sort, "a");
        const bb = try mkfv(self, sort, "b");
        const d = try mkfv(self, sort, "d");
        const lt = try self.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const eq = try self.pool.add(.{ .eq = .{ .lhs = try self.pool.addApp(.app, add, &.{ a.t, try self.pool.addApp(.app, succ, &.{d.t}) }), .rhs = bb.t } });
        const closed_d = try self.pool.close(eq, d.name);
        const exists_d = try self.pool.add(.{ .quant = .{ .q = .exists, .sort = sort, .hint = d.name, .body = closed_d } });
        const body = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = lt, .rhs = exists_d } });
        return try self.closeForallChain(body, &.{ a, bb }, sort);
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
    // flatten a nested `op(op(a,b),c)` sum into `out` in LEFT-TO-RIGHT leaf order. Iterative work-
    // stack (was native recursion); order-sensitive → push the two args REVERSED (a1 then a0) so a0
    // pops + is emitted first, matching the recursion's lhs-before-rhs.
    var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = self.pool.get(cur);
        if (node == .app and node.app.sym == op_sym and node.app.args_len == 2) {
            const args = self.pool.args(node.app);
            try stack.append(wa, args[1]); // rhs pushed first → pops second
            try stack.append(wa, args[0]); // lhs pushed second → pops first
        } else {
            try out.append(self.ctx.arena, cur); // a leaf summand
        }
    }
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
        // an accelerant admits the claim on ITS OWN terms — run the producer in admit mode
        // (it returns a sentinel after its own acceptance check, building no cert).
        .simplify, .simplify_quantified, .assoc, .assoc_quantified, .assoc_commut, .assoc_commut_quantified, .polynomial, .polynomial_quantified, .arithmetic, .arithmetic_quantified, .tautology, .specialize, .chain, .extensionality, .extensionality_quantified => {
            const prev_mode = self.admit_mode;
            const prev_ok = self.admit_ok;
            self.admit_mode = true;
            self.admit_ok = false;
            defer {
                self.admit_mode = prev_mode;
                self.admit_ok = prev_ok;
            }
            // the producer either ADMITS (sets admit_ok, returns null — no cert) or REJECTS
            // (fails → error.Recover). A null return without admit_ok = the producer didn't
            // reach an admit decision (a producer not yet admit-aware) — treat as a reject.
            _ = try self.produceAccelerant(w, e, goal, c);
            if (!self.admit_ok) return self.fail(c.rule.start, "'{s}' cannot admit this step under `--fast` (no fast acceptance)", .{self.text(c.rule)});
        },
        // model: the transferred statement = the source theorem elaborated under M's overlay
        // (relativization included). α-match the claim.
        .model => try self.admitModel(goal, c),
        // import: the imported statement, elaborated in I's namespace (no model). α-match.
        .import => try self.admitImport(goal, c),
    }
}

/// Admit `[using model(M) src.thm]`: elaborate `src.thm`'s statement under M's overlay and
/// α-match `goal` (the claim). Uses the shared `elaborateFactStatement` — the SAME relativization
/// the strict transfer applies to the statement — so no divergence.
fn admitModel(self: *Prove, goal: TermId, c: ast.Step.Claim) Error!void {
    if (c.schema == null) return self.fail(c.rule.start, "model citation requires a model name: `[using model(M) src.thm]`", .{});
    if (c.refs.len != 1) return self.fail(c.rule.start, "`[using model(M) …]` cites exactly one transferred theorem", .{});
    const mtok = c.schema.?;
    const mstate = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = self.ns, .name = tokName(mtok) }) orelse
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
        try self.admit(w, e, goal, c);
        if (self.trustWord(c)) |word| self.admitted.insert(word);
        return .{ .accelerated = c.rule.name };
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
        .instantiation => return self.lowerInstantiate(w, e, c),
        // `using model(M) src.thm` transfers a source theorem: the transferred fact was
        // demanded (proved in namespace (M, src_file)) in the read pass; cite it.
        .model => return self.lowerModel(w, c),
        // `using import(I) thm` cites an imported theorem across the file boundary — the
        // explicit accelerant seam (the read pass demanded `thm` in I's namespace); cite it.
        .import => return self.lowerImport(c),
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
        .instantiation, .model, .import => unreachable, // dispatched above
        .axiom, .theorem, .cite => {
            try self.wantRefs(c, 1);
            const stmt = try self.resolveFactRef(c.refs[0]);
            const loc = c.refs[0].start;
            // AUTO-WEAKENING (model transfer): a source axiom holding UNCONDITIONALLY on the
            // carrier, mapped to itself, has a RELATIVIZED step claim `∀v; guard(v) -> …` while
            // the fact derives the bare `∀v; …`. Since `∀v; P ⊢ ∀v; guard(v) -> P`, synthesize the
            // weakening (nested guarded `fix` + cite + multi-arg forall_elim + forall_intro).
            if (self.model != InternPool.Index.none and self.model != .universe) {
                const fact_f = try self.pool.copyIn(self.ctx.interner, self.ctx.interner.keyOf(stmt).fact.formula);
                if (!self.pool.alphaEq(fact_f, goal)) {
                    if (try self.emitWeakening(kb, loc, stmt, fact_f, goal)) |just| return just;
                }
            }
            // Emit the justification matching the RESOLVED fact's kind, not the rule word.
            // Identity in an ordinary proof (a `by axiom` cites an axiom). In a MODEL
            // transfer a source-axiom citation may remap (via the obligation overlay) to a
            // discharging THEOREM — so `by axiom srcAx` legitimately lands on a theorem;
            // pick the kernel arm by the fact's actual kind (the kernel re-matches the
            // formula regardless — the kind gate is the only thing that'd wrongly reject).
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
                    return self.fail(aloc, "forall_elim: '{s}' is not universally quantified here", .{try self.renderTerm(cur_formula)});
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
                    .elim => |el| .{ try self.pool.open(self.pool.get(cur_f).quant.body, el.arg), .{ .forall_elim = .{ .step = cur, .with = el.arg, .with_loc = el.loc } } },
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
        .exists_intro => {
            try self.wantRefs(c, 1);
            const arg = try e.elaborateExpr(c.args[0]);
            const aloc = Elab.exprLoc(c.args[0]);
            var step = try self.resolveStepRef(w, c.refs[0]);
            // RELATIVIZED ∃ (model transfer): the goal `∃x; good(x) and P(x)` opens at the witness
            // to `good(w) and P(w)`, but the cited step provides only `P(w)`. Re-conjoin the guard:
            // discharge `good(w)` (source 2b — the witness's own unpack carries it) and and_intro it
            // onto the step, so exists_intro witnesses the full relativized body.
            const gnode = self.pool.get(goal);
            if (gnode == .quant and gnode.quant.q == .exists) {
                const body = try self.pool.open(gnode.quant.body, arg.id);
                const bn = self.pool.get(body);
                const step_f = self.low_steps.items[@intFromEnum(step.id)].formula;
                if (bn == .bin and bn.bin.op == .and_op and !self.pool.alphaEq(step_f, body) and self.pool.alphaEq(bn.bin.rhs, step_f)) {
                    if (try self.emitDischargeStep(kb, aloc, bn.bin.lhs)) |g_step| {
                        step = try self.emitSynthetic(kb, aloc, body, .{ .and_intro = .{ .left = g_step, .right = step } });
                    }
                }
            }
            return .{ .exists_intro = .{
                .step = step,
                .witness = arg.id,
                .witness_loc = aloc,
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
