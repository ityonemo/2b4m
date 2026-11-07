//! Demand — the STATIC demand helpers shared by the proof driver (`Prove`), the ProveTask's
//! formula pass and the accelerated tactics' read hooks: resolve a read-pass candidate set
//! against the KV tables (racking Fetch/Prove tasks for absent names), and elaborate a cited
//! fact's STATEMENT without demanding its proof. Everything here takes the Context + engine
//! handle explicitly — nothing holds a driver.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const tokName = lexer.tokName;
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const Engine = @import("../../Engine.zig");
const Context = @import("../../Context.zig");
const FactKV = @import("../../FactKV.zig");
const FetchTask = @import("../FetchTask.zig");
const ModelTask = @import("../ModelTask.zig");
const ProveTask = @import("../ProveTask.zig");
const Walk = @import("Walk.zig");
const RefScan = @import("RefScan.zig");
const Elab = @import("Elab.zig");
const Expand = @import("../Expand.zig");

const Error = error{ Recover, OutOfMemory };

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
