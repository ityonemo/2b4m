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
const InternPool = @import("../InternPool.zig");
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
    decl_index: u32, // the schema decl in parsed[file].decls
    params: []const StrId, // param names, in order (for schema_args keys + read-pass skip)
    args: []const DurableArg, // one per param, in order
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
    const ns = try self.interner.namespace(.universe, task.file);
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

    const st = task.st orelse blk: {
        const st = if (task.instance) |inst|
            (try buildInstanceState(self, task, h, ns, inst)) orelse return // diagnosed
        else
            (try locate(self, task, h, ns)) orelse return; // diagnosed; no publish
        task.st = st;
        break :blk st;
    };
    st.prove.h = h; // each (re)entry gets a fresh handle; racking goes through it

    // GOAL PHASE: the stated formula's own read pass + elaboration ("step -1"). For a
    // schema instance the formula is the schema BODY (elaborated with schema_args resolving
    // the params); the read pass skips param names via prove.schema_params.
    if (st.goal == null) {
        const formula = switch (st.decl) {
            inline else => |d| d.formula,
        };
        var scanner = RefScan.init(self.arena, self.interner, st.source, st.walk);
        scanner.schema_params = st.prove.schema_params;
        const refs = try scanner.scanFormula(formula);
        if (try Prove.resolveRefs(self, h, task.file, ns, refs)) |blocker| {
            h.suspendOn(blocker);
            return;
        }
        // the goal elaborates into the PROOF's scratchpad (st.prove.pool) — the same pool
        // its steps and the kernel check use, and that it reifies back from at publish.
        var e = Elab.init(self.arena, self.io, self.interner, &self.idents, st.prove.pool, self.sink, st.source, st.walk, ns, &st.prove.fresh_counter);
        e.schema_args = st.prove.schema_args; // resolve schema params (null in ordinary proofs)
        const typed = e.requireProp(e.elaborateExpr(formula) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return, // diagnosed; no publish
        }, formula) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Recover => return,
        };
        st.goal = typed.id;
    }

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
            // non-proof-carrying schema (or !recheck_schemas) trusts the monomorphization
            // and publishes a leaf fact.
            if (i.steps) |steps| {
                if (self.verify.recheck_schemas) return proveSteps(self, task, h, st, key, steps);
            }
            const off = try st.prove.pool.reify(st.goal.?, self.interner);
            _ = try self.facts.publish(self.io, key, .theorem, off, st.goal_loc);
        },
    }
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
            _ = try self.facts.publish(self.io, key, .theorem, off, st.goal_loc);
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
fn locate(self: *Context, task: *ProveTask, h: *Engine.Handle, ns: InternPool.Index) std.mem.Allocator.Error!?*State {
    const fid = self.pool_file.get(task.file) orelse {
        try demandDiag(self, task, "internal: prove into an undiscovered file", .{});
        return null;
    };
    const parsed = self.parsed.items[@intFromEnum(fid)];
    const source = self.files.items[@intFromEnum(fid)].source;

    for (parsed.decls) |*decl| {
        const name_tok = switch (decl.*) {
            .axiom => |d| d.name,
            .theorem => |d| d.name,
            .hole => |d| d.name,
            .schema => |d| d.name,
            .sort => |d| d.name,
            .import => |d| d.ns,
            .constant => |d| d.name,
            .func => |d| d.name,
            .pred => |d| d.name,
            .define => |d| d.name,
            .alias => |d| d.name,
            .forward, .model => continue,
        };
        const decl_name = self.interner.internString(source[name_tok.start..name_tok.end]) catch return error.OutOfMemory;
        if (decl_name != task.name) continue;

        const d: State.Decl = switch (decl.*) {
            .axiom => |d| .{ .axiom = .{ .formula = d.formula } },
            .theorem => |d| .{ .theorem = .{ .formula = d.formula, .steps = d.steps } },
            .hole => {
                self.sink.add(name_tok.start, "holes are not yet supported by the demand prover", .{}) catch return error.OutOfMemory;
                return null;
            },
            .schema => {
                // a schema is not a fact — it cannot be cited as an axiom/theorem; it is
                // used via `[by instantiate <schema>(args)]`. (Reached only on a misuse.)
                try demandDiag(self, task, "'{s}' is a schema; use `[by instantiate {s}(...)]`, not a fact citation", .{ self.interner.stringBytes(task.name), self.interner.stringBytes(task.name) });
                return null;
            },
            else => {
                try demandDiag(self, task, "'{s}' names an identifier, not an axiom/theorem", .{self.interner.stringBytes(task.name)});
                return null;
            },
        };
        const st = try self.arena.create(State);
        const walk = try self.arena.create(Walk);
        walk.* = Walk.init(self.arena, self.interner, source, self.sink);
        st.* = .{
            .source = source,
            .ns = ns,
            .decl = d,
            .walk = walk,
            .prove = try Prove.init(self, h, source, task.file, ns),
            .goal_loc = name_tok.start,
        };
        return st;
    }
    try demandDiag(self, task, "reference not found: '{s}'", .{self.interner.stringBytes(task.name)});
    return null;
}

/// Build the production State for a schema INSTANCE from its payload: copyIn the durable
/// args into the task's fresh scratchpad, install them as `schema_args` on the Prove, and
/// read the schema's body+steps from its decl AST. `task.file` is the SCHEMA's file, so
/// `ns` is the schema namespace and the body/steps resolve there. Never diagnoses (the
/// citer validated arity/binding); returns the ready State.
fn buildInstanceState(self: *Context, task: *ProveTask, h: *Engine.Handle, ns: InternPool.Index, inst: Instance) std.mem.Allocator.Error!?*State {
    const fid = self.pool_file.get(task.file).?; // demandParse ensured it's parsed
    const source = self.files.items[@intFromEnum(fid)].source;
    const decl = self.parsed.items[@intFromEnum(fid)].decls[inst.decl_index].schema;

    const prove = try Prove.init(self, h, source, task.file, ns);

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
    prove.schema_params = inst.params;

    const st = try self.arena.create(State);
    const walk = try self.arena.create(Walk);
    walk.* = Walk.init(self.arena, self.interner, source, self.sink);
    st.* = .{
        .source = source,
        .ns = ns,
        .decl = .{ .instance = .{ .formula = decl.formula, .steps = decl.steps } },
        .walk = walk,
        .prove = prove,
        .goal_loc = decl.name.start,
    };
    return st;
}
