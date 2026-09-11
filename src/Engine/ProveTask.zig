//! The prove task — produces a FACT (axiom or theorem) on demand. Racked by the parse
//! scan for each requested (root-file) theorem, and by a read pass for each CITED fact
//! that is absent from FactKV. See memory `provetask-step-walk-design`.
//!
//! ENTRY PROTOCOL (FactKV.claimOrLookup):
//!   - proven               -> someone already produced it; complete.
//!   - in_flight (another)  -> SUSPEND blocked on that task.
//!   - in_flight (SELF)     -> we own it and were RESUMED mid-proof — continue.
//!   - claimed              -> we own it; produce.
//!
//! PRODUCTION: find the declaration by name in the file's parsed AST.
//!   - AXIOM: a leaf — read-pass its formula (rack fetches, suspend), elaborate, reify,
//!     publish. No proof.
//!   - THEOREM: the real one — goal phase (read-pass + elaborate the stated formula),
//!     then the WALK phase: `Walk.drive` with the `Prove` driver steps through the proof
//!     (each step read-passes, suspending at the step on any missing global; resume
//!     re-drives from the reified cursor); on done, `Prove.finish` kernel-checks the
//!     whole lowering and the goal reifies + publishes.
//!   - hole / schema: not yet supported (diagnosed; red until the Phase-5 rebuilds).
//!
//! A FAILED proof publishes NOTHING: the FactKV entry stays in_flight-ours, so demanders
//! of this fact stay parked (a wedge — the engine still terminates; the root-cause
//! diagnostic is in the sink; wedge REPORTING is deferred).
//!
//! The payload is MUTABLE task state (run takes `*ProveTask`): the goal TermId, the Walk
//! (whose frame stack IS the resumable cursor), and the Prove driver all live across
//! suspends, arena-resident.

const std = @import("std");
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const InternPool = @import("../InternPool.zig");
const IdentKV = @import("../IdentKV.zig");
const FetchTask = @import("FetchTask.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const FactKV = @import("../FactKV.zig");
const Walk = @import("ProveTask/Walk.zig");
const RefScan = @import("ProveTask/RefScan.zig");
const Elab = @import("ProveTask/Elab.zig");
const Prove = @import("ProveTask/Prove.zig");
const Schema = @import("ProveTask/Schema.zig");
const Accelerant = @import("ProveTask/Accelerant.zig");
const Expand = @import("Expand.zig");

const ProveTask = @This();

/// the `.file` entity Index of the fact's home file (not the dense FileId — the pool
/// identity, which the namespace is built from). For a schema INSTANCE, this is the
/// SCHEMA's file (its body/steps resolve there; the fact is minted in its namespace).
file: InternPool.Index,
name: InternPool.StrId,
/// the DEMANDING reference's source offset — where "reference not found" / "not a fact"
/// points. Relative to `loc_file` (the citing file), NOT `file` (a cross-file citation
/// demands into an imported `file`). 0 for the root scan (the decl is its own site).
loc: u32 = 0,
/// the file `loc` indexes into; `null` = relative to `file` (a same-file / root demand).
loc_file: ?InternPool.Index = null,
/// the MODEL this fact is proved THROUGH (Step 13): `.universe` (default) = an ordinary
/// proof; a model M = a TRANSFER, where `[by model(M) src.thm]` racks a ProveTask keyed on
/// `(M, file)` that re-proves `src.thm`'s proof with every global remapped via M's overlay.
/// The fact is minted in the namespace `(model, file)`, so two models of one source give
/// distinct transferred facts.
model: InternPool.Index = .universe,
/// a SCHEMA INSTANCE payload (Step 12): present iff this task proves a monomorphized
/// schema instance rather than a named decl. Carries the schema decl locator + the bound
/// args (durable TermOffs — copied into the task's own scratchpad on the first run). When
/// set, `run` builds State from it directly, bypassing the name-scan `locate`.
instance: ?Instance = null,
/// resumable production state; created on the first owning entry.
st: ?*State = null,

/// A schema-instance production request. `args` are DURABLE (reify'd by the citer into
/// `extra`) so they survive the payload and cross into the instance's own scratchpad.
pub const Instance = struct {
    schema_name: StrId, // the schema decl's name — resolved via the by-name AST registry
    params: []const StrId, // param names, in order (for schema_args keys + read-pass skip)
    args: []const DurableArg, // one per param, in order
    /// SOURCE-space twins of `args` (same slice outside a model transfer): bound with the model
    /// OFF, so a source-space pass inside the instance (accelerant producers' inputs — see
    /// Prove.source_formulas) substitutes source terms for the params, never target ones.
    args_source: []const DurableArg,
    /// SYNTHETIC (accelerant-generated) schema: its formulas are delaborated from already-
    /// elaborated terms — re-elaboration must not re-inject refined-sort guards (13e).
    synthetic: bool = false,
};

/// A schema argument as durable pool data (mirrors `Schema.SchemaArg` with TermOffs).
/// `copyIn`'d into the instance task's scratchpad to rebuild the live `Schema.SchemaArg`.
pub const DurableArg = union(enum) {
    value: struct { off: InternPool.TermOff, sort: term.SortId },
    lambda: struct {
        off: InternPool.TermOff,
        params: []const StrId,
        arg_sorts: []const term.SortId,
        result_sort: term.SortId,
    },
};

const State = struct {
    source: []const u8,
    ns: InternPool.Index,
    decl: Decl,
    walk: *Walk,
    prove: *Prove,
    /// the elaborated stated formula (axiom assertion / theorem goal / schema-instance body);
    /// null until the goal phase completes.
    goal: ?term.TermId = null,
    goal_loc: u32,

    const Decl = union(enum) {
        axiom: struct { formula: *const ast.Expr },
        theorem: struct { formula: *const ast.Expr, steps: []const ast.Step },
        /// a schema INSTANCE: the schema's body is the goal, its steps are the proof, both
        /// elaborated with `prove.schema_args` (already installed) resolving the params.
        instance: struct { formula: *const ast.Expr, steps: ?[]const ast.Step },
        /// a `hole`: axiom-shaped (its assertion IS the fact, a leaf), but tracked as a hole —
        /// published like an axiom AND registered in `ctx.hole_taint` under its own name, so
        /// dependents inherit the taint. Default mode rejects a hole-resting result; --draft
        /// allows. `name` is the hole's own StrId (its taint seed).
        hole: struct { formula: *const ast.Expr, name: InternPool.StrId },
    };
};

/// Package a payload into a rack-ready `Engine.Task` (arena-allocated payload + typed
/// erased run), mirroring `ParseTask.new` / `FetchTask.new`.
pub fn new(arena: std.mem.Allocator, payload: ProveTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(ProveTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *ProveTask = @ptrCast(@alignCast(payload));
    return run(self, task, h);
}

pub fn run(self: *Context, task: *ProveTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    // diagnostics this run records belong to THIS task's file — point the sink at it (a
    // task runs synchronously to its next suspend, so it is the last writer before any of
    // its own `sink.add`s; sub-tasks reset it when they run). Prevents an imported fact's
    // offset from being rendered against another file's (shorter) source.
    if (self.pool_file.get(task.file)) |fid| self.sink.current_file = @intFromEnum(fid);
    // the fact's identity namespace is `(model, file)` — `.universe` for an ordinary proof,
    // model M for a transfer (so `(M,file) src.thm` is a distinct fact from the source).
    const ns = try self.interner.namespace(task.model, task.file);
    const key = FactKV.Key{ .namespace = ns, .name = task.name };
    switch (try self.facts.claimOrLookup(self.io, key, h.self_index)) {
        .proven => return,
        .in_flight => |owner| {
            if (owner != h.self_index) {
                h.suspendOn(owner);
                return;
            }
            // ours — resumed mid-proof; fall through and continue.
        },
        .claimed => {},
    }

    // the fact's file must be PARSED before `locate` can scan its decls (lazy parsing,
    // Step 11): demand its parse and suspend if it isn't ready. Runs before `locate` on
    // the first entry; on a resume `st` is already built so we skip straight past.
    if (task.st == null) switch (try self.demandParse(h, task.file)) {
        .parsed => {},
        .parsing => |t| return h.suspendOn(t),
        .unparsed => {}, // undiscovered — locate reports the internal wiring error
    };

    // FACT ALIAS (`theorem foo = bar.baz` / `axiom foo = bar.baz`): bind `foo` to the origin
    // fact's Index — no goal/steps to walk, no State. Handled here (before `locate`, which
    // builds the normal proof State) since it's a distinct, State-less flow. Idempotent across
    // resumes: an alias never sets `task.st`, so each resume re-peeks and re-resolves.
    if (task.st == null and task.instance == null) {
        switch (try factAlias(self, task, h, key)) {
            .handled => return,
            .not_alias => {},
        }
        // A SCHEMA (a params-carrying axiom/theorem/hole) is a fact with no ground formula:
        // publish its LOCATOR into FactKV and stop (no goal/steps to walk). The instantiation
        // path reads it back + re-reads params/body from the AST. State-less, like factAlias.
        switch (try schemaLocator(self, task, h, key)) {
            .handled => return,
            .not_alias => {},
        }
    }

    const st = task.st orelse blk: {
        const st = if (task.instance) |inst|
            (try buildInstanceState(self, task, h, ns, inst)) orelse return // diagnosed
        else
            (try locate(self, task, h, ns)) orelse return; // diagnosed; no publish
        task.st = st;
        break :blk st;
    };
    st.prove.h = h; // each (re)entry gets a fresh handle; racking goes through it

    // GOAL PHASE: the stated formula's own read pass + elaboration ("step -1"). Extracted
    // into `elaborateGoalInto` so the trusted `--fast` shape-check reuses the SAME
    // relativization logic (see `Prove.elaborateFactStatement`). A `.suspended` blocked on a
    // missing ref (already `suspendOn`'d); a `.done` with `st.goal` still null = a diagnosed
    // Recover (no publish) — return exactly as the inline code did.
    if (st.goal == null) switch (try elaborateGoalInto(self, task, h, st)) {
        .suspended => return,
        .done => if (st.goal == null) return, // diagnosed Recover — no publish
    };

    switch (st.decl) {
        .axiom => {
            // an axiom is a LEAF: its assertion IS the fact.
            const off = try st.prove.pool.reify(st.goal.?, self.interner);
            _ = try self.facts.publish(self.io, key, .axiom, off, st.goal_loc);
        },
        .theorem => |t| return proveSteps(self, task, h, st, key, t.steps),
        .instance => |i| {
            // a schema instance: re-check the schema's proof at this instance (comptime
            // semantics — the proof may hold for some args and fail for others). A
            // non-proof-carrying schema (an axiom-schema, no steps) → trust the
            // monomorphization and publish a leaf fact. (Trust of the CITING accelerant/
            // instantiation word is applied at the CITING STEP — a trusted citation never
            // racks this task at all — so there is no per-instance trust bit here.)
            if (i.steps) |steps| return proveSteps(self, task, h, st, key, steps);
            const off = try st.prove.pool.reify(st.goal.?, self.interner);
            _ = try self.facts.publish(self.io, key, .theorem, off, st.goal_loc);
        },
        .hole => |hh| {
            // a hole is treated as an AXIOM everywhere except HERE: publish the leaf (its
            // assertion IS the fact) so its dependents can proceed AND record the reached hole
            // (name + location) so the summary can DISCLOSE EVERY hole site. The default-mode
            // REJECT (a hole-reaching result isn't complete) and the --draft ALLOW happen at the
            // summary — publishing here lets us reach + report all hole sites, not just the
            // first. See [[hole-mechanism]].
            const off = try st.prove.pool.reify(st.goal.?, self.interner);
            const fact = try self.facts.publish(self.io, key, .axiom, off, st.goal_loc);
            try self.holes_reached.append(self.arena, .{ .name = hh.name, .file = task.file, .loc = st.goal_loc });
            // the hole rests on ITSELF (the taint seed) — so any dependent inheriting this fact's
            // taint records this hole in its blast-radius.
            try self.hole_taint.put(self.arena, fact, try self.arena.dupe(InternPool.StrId, &.{hh.name}));
        },
    }
}

/// The stated formula's read pass + elaboration into `st.prove.pool` (the goal phase).
/// Returns `.suspended` (a ref wasn't ready — `h.suspendOn` was called; `run` returns) or
/// `.done`. On a diagnosed Recover it leaves `st.goal` null and returns `.done` (the caller
/// treats null-goal as a no-publish return). Behaviour is IDENTICAL to the former inline
/// block; it is a function so `Prove.elaborateFactStatement` shares the relativization.
fn elaborateGoalInto(self: *Context, task: *ProveTask, h: *Engine.Handle, st: *State) std.mem.Allocator.Error!enum { done, suspended } {
    const formula = switch (st.decl) {
        inline else => |d| d.formula,
    };
    var scanner = RefScan.init(self.arena, self.interner, st.source, st.walk);
    scanner.schema_params = st.prove.schema_params;
    const refs = try scanner.scanFormula(formula);
    // resolve in the RESOLUTION ns (st.prove.ns = universe-of-file), not the identity
    // ns — a model transfer's source names resolve there + get overlay-redirected.
    if (try Prove.resolveRefs(self, h, task.file, st.prove.ns, st.prove.model, refs)) |blocker| {
        h.suspendOn(blocker);
        return .suspended;
    }
    // the goal elaborates into the PROOF's scratchpad (st.prove.pool) — the same pool
    // its steps and the kernel check use, and that it reifies back from at publish.
    var e = Elab.init(self.arena, self.io, self, self.interner, &self.idents, st.prove.pool, self.sink, st.source, st.walk, st.prove.ns, &st.prove.fresh_counter);
    e.schema_args = st.prove.schema_args; // resolve schema params (null in ordinary proofs)
    e.model = st.prove.model; // remap source globals for a model transfer (identity else)
    e.no_relativize = st.prove.pre_relativized; // synthetic instance: no guard re-injection
    // a guarded/refined application in the STATEMENT owes its obligation just as one in a step
    // does — wire the same sinks so `dischargeGoalTccs` (below) proves them against the empty
    // statement context (a self-relativized `forall d; d != ZERO -> …` discharges; a bare
    // `div(ONE, ZERO)` does not).
    e.tccs = &st.prove.pending_tccs;
    e.result_facts = &st.prove.result_facts;
    e.in_statement = true; // suppress refined-sort arg obligations in the statement (guard-func only)
    const typed = e.requireProp(e.elaborateExpr(formula) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .done, // diagnosed; no publish (st.goal stays null)
    }, formula) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .done,
    };
    st.prove.dischargeGoalTccs() catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return .done, // an undischarged statement obligation — diagnosed; no publish
    };
    st.goal = typed.id;
    return .done;
}

/// Drive the Walk over `steps` proving `st.goal`; on success reify + publish the fact.
/// Shared by ordinary theorems and proof-carrying schema instances.
fn proveSteps(self: *Context, task: *ProveTask, h: *Engine.Handle, st: *State, key: FactKV.Key, steps: []const ast.Step) std.mem.Allocator.Error!void {
    _ = task;
    switch (try st.walk.drive(steps, st.prove)) {
        .blocked => |blocker| {
            h.suspendOn(blocker);
            return;
        },
        .failed => return, // diagnosed; no publish
        .done => {
            if (!try st.prove.finish(st.goal.?, st.goal_loc)) return; // no publish
            const off = try st.prove.pool.reify(st.goal.?, self.interner);
            const fact = try self.facts.publish(self.io, key, .theorem, off, st.goal_loc);
            // record any `using` words this proof ADMITTED (`--fast`) against the fact, for the
            // summary's trust disclosure. Empty in strict mode (nothing admitted).
            if (st.prove.admitted.count() > 0) try self.accelerated.put(self.arena, fact, st.prove.admitted);
            // record the HOLES this proof transitively rests on (blast-radius report only).
            if (st.prove.holes_used.items.len > 0)
                try self.hole_taint.put(self.arena, fact, st.prove.holes_used.items);
        },
    }
}

/// Point the sink at the file `task.loc` is relative to (the DEMANDER, `loc_file`, or
/// `file` for a same-file / root demand), then record a demand-site diagnostic. Must
/// precede any `sink.add(task.loc, …)` so the offset renders against the right source.
fn demandDiag(self: *Context, task: *ProveTask, comptime fmt: []const u8, args: anytype) std.mem.Allocator.Error!void {
    const loc_file = task.loc_file orelse task.file;
    if (self.pool_file.get(loc_file)) |lf| self.sink.current_file = @intFromEnum(lf);
    self.sink.add(task.loc, fmt, args) catch return error.OutOfMemory;
}

/// Find the fact's declaration in its file's parsed AST and build the production state.
/// Null = diagnosed (missing / not-a-fact / unsupported kind); the task completes
/// without publishing.
const AliasOutcome = enum { handled, not_alias };

/// FACT ALIAS resolution (`axiom/theorem LOCAL = TARGET`). `handled` = published (bound
/// LOCAL to the origin fact), SUSPENDED (blocked on the origin's ProveTask; resume re-runs),
/// or DIAGNOSED (no publish). `not_alias` = the decl is not a fact alias (fall through to the
/// normal locate/prove path). Mirrors resolveRefs' `.fact` path: qualifier → import → target
/// file/ns, then FactKV demand.
fn factAlias(self: *Context, task: *ProveTask, h: *Engine.Handle, key: FactKV.Key) std.mem.Allocator.Error!AliasOutcome {
    const fid = self.pool_file.get(task.file) orelse return .not_alias; // locate reports it
    const decl = self.declOf(fid, task.name) orelse return .not_alias; // locate reports "not found"
    const alias: ast.Alias = switch (decl.*) {
        .axiom => |a| switch (a) {
            .alias => |x| x,
            .local => return .not_alias,
        },
        .theorem => |t| switch (t) {
            .alias => |x| x,
            .local => return .not_alias,
        },
        else => return .not_alias,
    };
    const origin = (try demandFactTarget(self, task, h, alias.target)) orelse return .handled; // suspended/diagnosed
    try self.facts.publishExisting(self.io, key, origin);
    return .handled;
}

/// SCHEMA LOCATOR: a params-carrying axiom/theorem/hole is a fact whose "content at rest" is
/// a LOCATOR back to its AST decl (name/file/loc) — not a ground formula. Publish that locator
/// into FactKV (State-less, like a fact alias) so the name resolves through the fact table; the
/// instantiation path reads the locator + re-reads params/body/steps from the by-name registry.
/// `not_alias` = the decl is not a schema (fall through to the normal locate/prove path).
fn schemaLocator(self: *Context, task: *ProveTask, h: *Engine.Handle, key: FactKV.Key) std.mem.Allocator.Error!AliasOutcome {
    _ = h;
    const fid = self.pool_file.get(task.file) orelse return .not_alias; // locate reports it
    const decl = self.declOf(fid, task.name) orelse return .not_alias; // locate reports "not found"
    const fact = ast.factOf(decl) orelse return .not_alias; // an alias / non-fact → not us
    if (fact.params == null) return .not_alias; // a plain (ground) fact → normal prove path
    const name_tok = ast.declName(decl);
    _ = try self.facts.publishSchema(self.io, key, .{ .name = task.name, .file = task.file, .loc = name_tok.start });
    return .handled;
}

/// Resolve a fact-reference token (possibly `ns.name`-qualified) to its PROVEN fact Index,
/// demanding the import and/or the origin fact's ProveTask. Returns null if it SUSPENDED (a
/// blocker was set) or DIAGNOSED. Diagnostics point at the alias's target token in
/// `task.file` (where `sink.current_file` already points from `run`'s top).
fn demandFactTarget(self: *Context, task: *ProveTask, h: *Engine.Handle, tok: lexer.Token) std.mem.Allocator.Error!?InternPool.Index {
    var target_file = task.file;
    var target_ns = try self.interner.namespace(.universe, task.file);
    if (tok.qualifier != InternPool.Index.none) {
        const self_ns = try self.interner.namespace(.universe, task.file);
        const state = self.idents.lookup(self.io, .{ .namespace = self_ns, .name = tok.qualifier }) orelse {
            h.suspendOn(try h.rackIndexed(try FetchTask.new(self.arena, .{ .file = task.file, .name = tok.qualifier, .loc = tok.start })));
            return null;
        };
        switch (state) {
            .in_flight => |owner| {
                if (owner != h.self_index) h.suspendOn(owner);
                return null;
            },
            .done => |ix| switch (self.interner.keyOf(ix)) {
                .import => |m| {
                    target_ns = m.namespace;
                    target_file = self.interner.keyOf(m.namespace).namespace.file;
                },
                else => {
                    self.sink.add(tok.start, "'{s}' is not a namespace", .{self.interner.stringBytes(tok.qualifier)}) catch return error.OutOfMemory;
                    return null;
                },
            },
        }
    }
    // PLAIN lookup (not claimOrLookup): we are NOT proving the origin — we bind to it once
    // its own ProveTask proves it. Absent → rack that prover + suspend.
    const origin_key = FactKV.Key{ .namespace = target_ns, .name = tok.name };
    if (self.facts.lookup(self.io, origin_key)) |state| switch (state) {
        .proven => |ix| return ix,
        .in_flight => |owner| {
            h.suspendOn(owner); // the origin's own prover is running — wait for it
            return null;
        },
    };
    h.suspendOn(try h.rackIndexed(try ProveTask.new(self.arena, .{ .file = target_file, .name = tok.name, .loc = tok.start, .loc_file = task.file })));
    return null;
}

fn locate(self: *Context, task: *ProveTask, h: *Engine.Handle, ns: InternPool.Index) std.mem.Allocator.Error!?*State {
    const fid = self.pool_file.get(task.file) orelse {
        try demandDiag(self, task, "internal: prove into an undiscovered file", .{});
        return null;
    };
    const source = self.files.items[@intFromEnum(fid)].source;

    // resolve the fact's decl by name (O(1) registry lookup); a miss is "reference not found".
    const decl = self.declOf(fid, task.name) orelse {
        try demandDiag(self, task, "reference not found: '{s}'", .{self.interner.stringBytes(task.name)});
        return null;
    };
    const name_tok = ast.declName(decl);
    const raw: State.Decl = switch (decl.*) {
        .axiom => |a| switch (a) {
            .local => |f| blk: {
                // a bare axiom is a leaf; a SCHEMA (params != null) cited as a fact is misuse.
                if (f.params != null) {
                    try demandDiag(self, task, "'{s}' is a schema; use `[using instantiation {s}(...)]`, not a fact citation", .{ self.interner.stringBytes(task.name), self.interner.stringBytes(task.name) });
                    return null;
                }
                break :blk .{ .axiom = .{ .formula = f.formula } };
            },
            .alias => {
                try demandDiag(self, task, "fact aliases are not yet supported by the demand prover", .{});
                return null;
            },
        },
        .theorem => |t| switch (t) {
            .local => |l| blk: {
                if (l.fact.params != null) {
                    try demandDiag(self, task, "'{s}' is a schema; use `[using instantiation {s}(...)]`, not a fact citation", .{ self.interner.stringBytes(task.name), self.interner.stringBytes(task.name) });
                    return null;
                }
                break :blk .{ .theorem = .{ .formula = l.fact.formula, .steps = l.steps } };
            },
            .alias => {
                try demandDiag(self, task, "fact aliases are not yet supported by the demand prover", .{});
                return null;
            },
        },
        .hole => |a| switch (a) {
            .local => |f| blk: {
                // a hole is axiom-shaped — a LEAF whose assertion IS the fact (its own name is
                // the taint seed). A params-carrying hole (a hole-SCHEMA) is misuse here.
                if (f.params != null) {
                    try demandDiag(self, task, "'{s}' is a schema; use `[using instantiation {s}(...)]`, not a fact citation", .{ self.interner.stringBytes(task.name), self.interner.stringBytes(task.name) });
                    return null;
                }
                break :blk .{ .hole = .{ .formula = f.formula, .name = task.name } };
            },
            .alias => {
                try demandDiag(self, task, "fact aliases are not yet supported by the demand prover", .{});
                return null;
            },
        },
        else => {
            try demandDiag(self, task, "'{s}' names an identifier, not an axiom/theorem", .{self.interner.stringBytes(task.name)});
            return null;
        },
    };
    // DEFINE EXPANSION (the lifecycle's first step — see Engine/Expand): the decl's AST is made
    // define-free BEFORE its read pass or elaboration ever sees it. A suspend returns null with
    // `task.st` unset, so the resume re-locates and re-expands (idempotent).
    self.sink.current_file = @intFromEnum(fid);
    const d: State.Decl = switch (raw) {
        .axiom => |a| switch (try Expand.expandFormula(self, h, task.file, a.formula, .{ .model = task.model })) {
            .ready => |f| .{ .axiom = .{ .formula = f } },
            .suspended, .failed => return null,
        },
        .hole => |hh| switch (try Expand.expandFormula(self, h, task.file, hh.formula, .{ .model = task.model })) {
            .ready => |f| .{ .hole = .{ .formula = f, .name = hh.name } },
            .suspended, .failed => return null,
        },
        .theorem => |t| switch (try Expand.expandProof(self, h, task.file, t.formula, t.steps, .{ .model = task.model })) {
            .ready => |pr| .{ .theorem = .{ .formula = pr.formula, .steps = pr.steps } },
            .suspended, .failed => return null,
        },
        .instance => unreachable, // built by buildInstanceState
    };
    // a TRANSFER also keeps the SOURCE-space AST (expanded with the model off) paired per step,
    // for the accelerant producers' source twins (see Prove.source_ast).
    const source_ast: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, *const ast.Expr) = if (task.model != .universe and task.model != InternPool.Index.none and d == .theorem)
        switch (try Expand.expandProof(self, h, task.file, raw.theorem.formula, raw.theorem.steps, .{})) {
            .ready => |src| try Expand.pairSource(self, .{ .formula = d.theorem.formula, .steps = d.theorem.steps }, src),
            .suspended, .failed => return null,
        }
    else
        null;
    const st = try self.arena.create(State);
    const walk = try self.arena.create(Walk);
    walk.* = Walk.init(self.arena, self.interner, source, self.sink);
    // RESOLUTION ns is the UNIVERSE ns of the file — the proof's source names resolve
    // there, then `applyModel(prove.model)` redirects for a transfer. (The fact's
    // IDENTITY ns `(model, file)` = `ns`, used only for the FactKV key/publish.)
    const resolve_ns = try self.interner.namespace(.universe, task.file);
    const prove = try Prove.init(self, h, source, task.file, resolve_ns);
    prove.model = task.model;
    prove.source_ast = source_ast;
    st.* = .{
        .source = source,
        .ns = ns,
        .decl = d,
        .walk = walk,
        .prove = prove,
        .goal_loc = name_tok.start,
    };
    return st;
}

/// Build the production State for a schema INSTANCE from its payload: copyIn the durable
/// args into the task's fresh scratchpad, install them as `schema_args` on the Prove, and
/// read the schema's body+steps from its decl AST. `task.file` is the SCHEMA's file, so
/// `ns` is the schema namespace and the body/steps resolve there. Never diagnoses (the
/// citer validated arity/binding); returns the ready State.
fn buildInstanceState(self: *Context, task: *ProveTask, h: *Engine.Handle, ns: InternPool.Index, inst: Instance) std.mem.Allocator.Error!?*State {
    // `ns` (the identity ns (model, file)) is stored as st.ns for the FactKV publish key;
    // resolution uses the schema file's universe ns + prove.model (below).
    const fid = self.pool_file.get(task.file).?; // demandParse ensured it's parsed
    const source = self.files.items[@intFromEnum(fid)].source;
    // the schema decl (parsed or synthetic) from the by-name registry: an axiom/theorem/hole
    // WITH params. Its formula is the schema body; a proof-carrying schema (a theorem) also
    // has steps (re-checked at this instance); an axiom-schema has none (trusted monomorph).
    const schema_decl = self.declOf(fid, inst.schema_name).?;
    const schema_fact = ast.factOf(schema_decl).?;
    // DEFINE EXPANSION of the schema's body + steps in the SCHEMA's file (its params shadow).
    self.sink.current_file = @intFromEnum(fid);
    const schema_formula: *const ast.Expr, const schema_steps: ?[]const ast.Step = if (schema_decl.* == .theorem)
        switch (try Expand.expandProof(self, h, task.file, schema_fact.formula, schema_decl.theorem.local.steps, .{ .scope = inst.params, .model = task.model })) {
            .ready => |pr| .{ pr.formula, pr.steps },
            .suspended, .failed => return null,
        }
    else switch (try Expand.expandFormula(self, h, task.file, schema_fact.formula, .{ .scope = inst.params, .model = task.model })) {
        .ready => |f| .{ f, null },
        .suspended, .failed => return null,
    };
    // a proof-carrying schema under a TRANSFER keeps its source-space AST twin (Prove.source_ast).
    const inst_source_ast: ?*const std.AutoHashMapUnmanaged(*const ast.Expr, *const ast.Expr) = if (task.model != .universe and task.model != InternPool.Index.none and schema_steps != null)
        switch (try Expand.expandProof(self, h, task.file, schema_fact.formula, schema_decl.theorem.local.steps, .{ .scope = inst.params })) {
            .ready => |src| try Expand.pairSource(self, .{ .formula = schema_formula, .steps = schema_steps.? }, src),
            .suspended, .failed => return null,
        }
    else
        null;

    // RESOLUTION ns is the schema file's UNIVERSE ns; a model instance remaps source syms
    // via prove.model + applyModel (so the monomorphized body is in target terms).
    const resolve_ns = try self.interner.namespace(.universe, task.file);
    const prove = try Prove.init(self, h, source, task.file, resolve_ns);
    prove.model = task.model;
    prove.source_ast = inst_source_ast;
    prove.pre_relativized = inst.synthetic; // delaborated formulas: no guard re-injection

    // rebuild the live SchemaArgs by copying each durable arg into the task's scratchpad.
    const args = try self.arena.create(Schema.SchemaArgs);
    args.* = .empty;
    for (inst.params, inst.args) |pname, darg| {
        const live: Schema.SchemaArg = switch (darg) {
            .value => |v| .{ .value = .{ .id = try prove.pool.copyIn(self.interner, v.off), .sort = v.sort } },
            .lambda => |l| .{ .lambda = .{
                .body = try prove.pool.copyIn(self.interner, l.off),
                .params = l.params,
                .arg_sorts = l.arg_sorts,
                .result_sort = l.result_sort,
            } },
        };
        try args.put(self.arena, pname, live);
    }
    prove.schema_args = args;
    // the SOURCE-space twins (the same map when they are the same slice — no model transfer).
    if (inst.args_source.ptr == inst.args.ptr) {
        prove.schema_args_source = args;
    } else {
        const args_source = try self.arena.create(Schema.SchemaArgs);
        args_source.* = .empty;
        for (inst.params, inst.args_source) |pname, darg| {
            const live: Schema.SchemaArg = switch (darg) {
                .value => |v| .{ .value = .{ .id = try prove.pool.copyIn(self.interner, v.off), .sort = v.sort } },
                .lambda => |l| .{ .lambda = .{
                    .body = try prove.pool.copyIn(self.interner, l.off),
                    .params = l.params,
                    .arg_sorts = l.arg_sorts,
                    .result_sort = l.result_sort,
                } },
            };
            try args_source.put(self.arena, pname, live);
        }
        prove.schema_args_source = args_source;
    }
    prove.schema_params = inst.params;

    // VALUE-PARAM GUARDS — the model's business, not the schema's. Under a model transfer a
    // value param whose image sort is REFINED (`p: Src` with `Src → Tgt where good`) is
    // relativized exactly like a `∀p` binder: the instance's stated formula leads with
    // `good(p) ->`, its proof ASSUMES it (so the guard is in scope for the body's own
    // discharges), and the CALL SITE discharges it (Prove.withGuardPremises). The guard
    // predicate is the refined sort's declared qualifier: the r-values of a model live in its
    // PARENT space, so this is the parent's `good`, never re-interpreted through the model (a
    // model that also remaps a symbol named `good` remaps the SOURCE's `good`, not the target
    // sort's refinement). The schema itself (parsed or a source-space synthetic) says nothing
    // about guards. Nothing is injected outside a model transfer.
    var inst_formula: *const ast.Expr = schema_formula;
    var inst_steps: ?[]const ast.Step = schema_steps;
    if (task.model != InternPool.Index.none and task.model != .universe) {
        var b: Accelerant.Builder = .{ .arena = self.arena, .interner = self.interner, .pool = prove.pool, .loc = schema_fact.name.start };
        // a schema-scoped, model-aware Elab to resolve each param's sort token to its image.
        var sort_walk = Walk.init(self.arena, self.interner, source, self.sink);
        var se = Elab.init(self.arena, self.io, self, self.interner, &self.idents, prove.pool, self.sink, source, &sort_walk, resolve_ns, &prove.fresh_counter);
        se.model = task.model;
        var guards: std.ArrayList(*const ast.Expr) = .empty; // in param order (outermost first)
        for (schema_fact.params.?) |p| {
            if (p.arg_sorts.len != 0) continue; // a generator param has no element to guard
            const image = se.resolveSortTok(p.result) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => break, // diagnosed into the sink; the instance proof reports it
            };
            const image_ix: InternPool.Index = @enumFromInt(@intFromEnum(image));
            if (!self.interner.isRefined(image_ix)) continue;
            const quals = try self.interner.qualifiersOf(self.arena, image_ix);
            for (quals) |q| {
                const arg1 = try self.arena.alloc(*const ast.Expr, 1);
                arg1[0] = try b.nameExpr(p.name.name);
                const call = try self.arena.create(ast.Expr);
                call.* = .{ .call = .{ .callee = b.symTok(q, true), .args = arg1 } };
                try guards.append(self.arena, call);
            }
        }
        if (guards.items.len > 0) {
            // stated formula: g1 -> g2 -> … -> body.
            var f = inst_formula;
            var i = guards.items.len;
            while (i > 0) {
                i -= 1;
                f = try b.implies(guards.items[i], f);
            }
            inst_formula = f;
            // proof (a proof-carrying schema): nest `assume g_i { … }` innermost-last, exporting
            // `g_i -> …` by implies_intro; the outermost export is the instance's conclusion.
            if (inst_steps) |steps| {
                var body = steps;
                var j = guards.items.len;
                while (j > 0) {
                    j -= 1;
                    const blk_label = prove.freshNamed("guard-assume") catch return error.OutOfMemory;
                    var lvl: std.ArrayList(ast.Step) = .empty;
                    try lvl.append(self.arena, try b.assumeStep(blk_label, guards.items[j], body));
                    var exported = schema_formula;
                    var k = guards.items.len;
                    while (k > j) {
                        k -= 1;
                        exported = try b.implies(guards.items[k], exported);
                    }
                    const refs = try self.arena.alloc(lexer.Token, 1);
                    refs[0] = b.tok(blk_label);
                    try lvl.append(self.arena, try b.claimStep(
                        if (j == 0) try b.intern("conclusion") else prove.freshNamed("guard-export") catch return error.OutOfMemory,
                        exported,
                        .by,
                        try b.intern("implies_intro"),
                        &.{},
                        refs,
                    ));
                    body = try lvl.toOwnedSlice(self.arena);
                }
                inst_steps = body;
                prove.guard_wrappers = @intCast(guards.items.len);
            }
        }
    }

    const st = try self.arena.create(State);
    const walk = try self.arena.create(Walk);
    walk.* = Walk.init(self.arena, self.interner, source, self.sink);
    st.* = .{
        .source = source,
        .ns = ns,
        .decl = .{ .instance = .{ .formula = inst_formula, .steps = inst_steps } },
        .walk = walk,
        .prove = prove,
        .goal_loc = schema_fact.name.start,
    };
    return st;
}
