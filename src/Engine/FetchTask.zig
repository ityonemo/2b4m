//! The fetch task — the task type that produces an IDENTIFIER (sort/const/func/pred/
//! define/import), the non-fact sibling of ProveTask. Racked ON DEMAND when a read pass
//! finds a name absent from IdentKV; it finds the name's DECLARATION in its file's parsed
//! AST, assembles the identifier's pool content, mints it, and publishes the `Index` into
//! IdentKV — waking everything suspended on it. See memory `provetask-step-walk-design`.
//!
//! ENTRY PROTOCOL (IdentKV.claimOrLookup):
//!   - done                 -> someone already produced it; complete.
//!   - in_flight (another)  -> SUSPEND blocked on that task.
//!   - in_flight (SELF)     -> we own it and were RESUMED mid-production (a sub-fetch we
//!                             suspended on has completed) — continue producing.
//!   - claimed              -> we own it; produce.
//!
//! PRODUCTION (layer 1 — Step 8 W3): plain `sort` decls (root sorts) and `import` decls
//! (the target file was resolved at parse time via the import map). LAYER 2 (W4.5):
//! constants, funcs and preds — their referenced SORTS are themselves DEMANDED (IdentKV
//! lookup; a miss racks a sub-FetchTask and SUSPENDS; resume re-runs `produce`, which is
//! idempotent — earlier demands now hit `done`). A GUARDED func (`requires`) additionally
//! REIFIES its precondition into the func Item's `.guard` term (`reifyGuard`): the closure of
//! the precondition's refs is demanded first (it must resolve before elaboration), then a
//! throwaway Elab elaborates it over the params (bound to `#gN` fvars) and it is reified durably.
//! Still unsupported (diagnosed, no publish): predicated params (`where` on a param).
//!
//! FAILURE ("reference not found" — the UndefinedError terminal): if no declaration
//! produces the name, a diagnostic is recorded and the task completes WITHOUT publishing.
//! The IdentKV entry stays in_flight-ours, so other demanders of the same name stay
//! parked (a wedge — the engine still terminates; wedge REPORTING is deferred, and the
//! demanding proof correctly never completes).

const std = @import("std");
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const InternPool = @import("../InternPool.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const IdentKV = @import("../IdentKV.zig");
const term = @import("../term.zig");
const Elab = @import("ProveTask/Elab.zig");
const Expand = @import("Expand.zig");
const Walk = @import("ProveTask/Walk.zig");

const FetchTask = @This();

/// the pool `.file` Index of the file in whose NAMESPACE the identifier is declared
/// (the demander resolves qualifiers first, so this is always the declaring file).
file: InternPool.Index,
name: InternPool.StrId,
/// the DEMANDING reference's source offset — where a demand-site diagnostic ("reference
/// not found", kind mismatch, unsupported kind) points. Relative to `loc_file`, NOT to
/// `file` (a cross-file citation demands into an imported `file` but the offset lives in
/// the citing file). `null` `loc_file` means "relative to `file`" (a same-file demand).
loc: u32,
loc_file: ?InternPool.Index = null,

/// Package a payload into a rack-ready `Engine.Task` (arena-allocated payload + typed
/// erased run), mirroring `ParseTask.new` / `ProveTask.new`.
pub fn new(arena: std.mem.Allocator, payload: FetchTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(FetchTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *FetchTask = @ptrCast(@alignCast(payload));
    return run(self, task.*, h);
}

pub fn run(self: *Context, task: FetchTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    if (self.verify.trace_facts) {
        const line = std.fmt.allocPrint(self.arena, "[fetch] task#{d} = ident {s} in file#{d}\n", .{ @intFromEnum(h.self_index), self.interner.stringBytes(task.name), @intFromEnum(task.file) }) catch "";
        self.fact_trace.append(self.arena, line) catch {};
    }
    // point the sink at THIS task's file (see the same note in ProveTask.run): a fetch's
    // "reference not found" / kind-mismatch offset is relative to its own file's source.
    if (self.pool_file.get(task.file)) |fid| self.sink.current_file = @intFromEnum(fid);
    const ns = try self.interner.namespace(.universe, task.file);
    const key = IdentKV.Key{ .namespace = ns, .name = task.name };
    switch (try self.idents.claimOrLookup(self.io, key, h.self_index)) {
        .done => return,
        .in_flight => |owner| {
            if (owner != h.self_index) {
                h.suspendOn(owner);
                return;
            }
            // ours — resumed mid-production; fall through and produce.
        },
        .claimed => {},
    }
    // the declaring file must be PARSED before we can scan its decls (lazy parsing,
    // Step 11): demand its parse and suspend if it isn't ready. Idempotent across resumes.
    switch (try self.demandParse(h, task.file)) {
        .parsed => {},
        .parsing => |t| return h.suspendOn(t),
        .unparsed => {}, // undiscovered — produce() reports the internal wiring error
    }
    try produce(self, task, h, key);
}

/// Find the declaration and assemble/publish the identifier. Layer 1: root sorts +
/// imports (no identifier references — never suspends). Layer 2: constants/funcs/preds
/// — referenced sorts are demanded via `resolveSortDemand`, which may rack sub-fetches
/// and SUSPEND; each resume re-enters here idempotently (earlier demands hit `done`).
/// Point the sink at the file `task.loc` is relative to (the DEMANDER, `loc_file`, or
/// `file` for a same-file demand), then record a demand-site diagnostic. Must precede
/// any such `sink.add(task.loc, …)` so the offset renders against the right source.
fn demandDiag(self: *Context, task: FetchTask, comptime fmt: []const u8, args: anytype) std.mem.Allocator.Error!void {
    const loc_file = task.loc_file orelse task.file;
    if (self.pool_file.get(loc_file)) |lf| self.sink.current_file = @intFromEnum(lf);
    self.sink.add(task.loc, fmt, args) catch return error.OutOfMemory;
}

fn produce(self: *Context, task: FetchTask, h: *Engine.Handle, key: IdentKV.Key) std.mem.Allocator.Error!void {
    const fid = self.pool_file.get(task.file) orelse {
        // the namespace's file was never discovered — an internal wiring error
        try demandDiag(self, task, "internal: fetch into an undiscovered file", .{});
        return;
    };
    const source = self.files.items[@intFromEnum(fid)].source;

    // resolve the decl by name (O(1) registry lookup); a miss is "reference not found".
    const decl = self.declOf(fid, task.name) orelse {
        try demandDiag(self, task, "reference not found: '{s}'", .{self.interner.stringBytes(task.name)});
        return;
    };
    const name_tok = ast.declName(decl);
    {
        switch (decl.*) {
            .forward => {
                // a promise / a model decl — not identifiers this fetch produces.
                try demandDiag(self, task, "'{s}' is not an identifier", .{self.interner.stringBytes(task.name)});
                return;
            },
            .model => {
                try demandDiag(self, task, "'{s}' is not an identifier", .{self.interner.stringBytes(task.name)});
                return;
            },
            .sort => |s| switch (s) {
                // `sort X` → a ROOT sort.
                .local => {
                    _ = try self.idents.publish(self.io, key, .{ .sort = .{
                        .name = task.name,
                        .loc = name_tok.start,
                        .refinement = null,
                    } });
                    return;
                },
                // `sort A = G` → ALIAS-COLLAPSE: bind A to G's EXISTING Index (identity by
                // origin, mints nothing), so A and G are the SAME sort everywhere — kernel
                // terms + every func/const/pred sig referencing either coincide. (A plain
                // re-export is definitionally G; collapsing keeps sorts consistent with the
                // const/func/pred aliases, which also collapse — otherwise a local `Int` and
                // an aliased `mul`'s `integer.Int` sig would be distinct Indexes.) The GUARDED
                // form below is the only sort alias that mints a new (refined) sort.
                .alias => |a| {
                    const target = resolveSortDemand(self, h, task.file, source, a.target) catch |e| switch (e) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.Unresolved => return,
                    };
                    _ = try self.idents.publish(self.io, key, .{ .existing = target });
                    return;
                },
                // `sort H = G where inH [and inK …]` → a REFINED sort
                // {parent: G, qualifiers: [inH, inK, …]} (one per `and`-chained predicate).
                .guarded => |g| {
                    const parent = resolveSortDemand(self, h, task.file, source, g.parent) catch |e| switch (e) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.Unresolved => return,
                    };
                    const quals = try self.arena.alloc(InternPool.Index, g.guards.len);
                    for (g.guards, quals) |gt, *q| {
                        q.* = resolveGuard(self, h, task.file, source, gt, parent) catch |e| switch (e) {
                            error.OutOfMemory => return error.OutOfMemory,
                            error.Unresolved => return,
                        };
                    }
                    _ = try self.idents.publish(self.io, key, .{ .sort = .{
                        .name = task.name,
                        .loc = name_tok.start,
                        .refinement = .{ .parent = parent, .qualifiers = quals },
                    } });
                    return;
                },
            },
            .import => |d| {
                // the parse phase resolved the raw path -> child FileId; map it to the
                // child's pool `.file` Index and bind the import to its namespace.
                const raw = d.path.name; // the parser stamped the quote-stripped path
                const target_fid = self.import_maps.items[@intFromEnum(fid)].get(raw) orelse {
                    self.sink.add(d.path.start, "import '{s}' was not resolved at parse time", .{source[d.path.start..d.path.end]}) catch return error.OutOfMemory;
                    return; // no publish — demanders of this import stay parked
                };
                const target_file = try self.fileIndex(self.files.items[@intFromEnum(target_fid)].path);
                const target_ns = try self.interner.namespace(.universe, target_file);
                _ = try self.idents.publish(self.io, key, .{ .import = .{
                    .namespace = target_ns,
                    .name = task.name,
                    .loc = name_tok.start,
                } });
                return;
            },
            .constant => |c| switch (c) {
                .local => |d| {
                    const sort_ix = resolveSortDemand(self, h, task.file, source, d.sort) catch |e| switch (e) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.Unresolved => return, // suspended or diagnosed — yield either way
                    };
                    _ = try self.idents.publish(self.io, key, .{ .constant = .{
                        .sort = sort_ix,
                        .name = task.name,
                        .loc = name_tok.start,
                    } });
                    return;
                },
                .alias => |a| return publishAlias(self, h, task, key, a, .constant),
            },
            .func => |fu| switch (fu) {
                .local => |d| {
                    const parts = assembleSig(self, h, task.file, source, d.params, d.result) catch |e| switch (e) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.Unresolved => return,
                    };
                    // A GUARDED func (`requires`): reify its precondition into the Item's guard
                    // term (params as hygienic `#gN` fvars — see `reifyGuard`), so every call site
                    // substitutes the actuals and owes the resulting obligation (mirrors the
                    // refined-sort TCC path). Unguarded funcs store `no_term`.
                    const guard: InternPool.TermOff = if (d.requires) |req|
                        reifyGuard(self, h, task.file, source, task.name, d.params, parts.sig, req) catch |e| switch (e) {
                            error.OutOfMemory => return error.OutOfMemory,
                            error.Unresolved => return, // suspended on a guard ref, or diagnosed
                        }
                    else
                        InternPool.no_term;
                    _ = try self.idents.publish(self.io, key, .{ .func = .{
                        .sig = parts.sig,
                        .guard = guard,
                        .param_names = parts.param_names,
                        .name = task.name,
                        .loc = name_tok.start,
                    } });
                    return;
                },
                .alias => |a| return publishAlias(self, h, task, key, a, .func),
            },
            .pred => |pr| switch (pr) {
                .local => |d| {
                    const parts = assembleSig(self, h, task.file, source, d.params, null) catch |e| switch (e) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.Unresolved => return,
                    };
                    _ = try self.idents.publish(self.io, key, .{ .pred = .{
                        .sig = parts.sig,
                        .guard = InternPool.no_term,
                        .param_names = parts.param_names,
                        .name = task.name,
                        .loc = name_tok.start,
                    } });
                    return;
                },
                .alias => |a| return publishAlias(self, h, task, key, a, .pred),
            },
            // a FACT decl (axiom/theorem/hole, schema or ground). FetchTask produces only
            // IDENTIFIERS — facts (including schemas) resolve through the FACT table via a
            // ProveTask. A fact reaching here means the demand was routed to the wrong table;
            // diagnose it (the citer used a name in an identifier position).
            .axiom, .hole, .theorem => {
                try demandDiag(self, task, "'{s}' names a fact, not a sort/constant/function/predicate", .{self.interner.stringBytes(task.name)});
                return; // no publish
            },
            // a DEFINE is a MACRO, never an identifier: the expansion pass (Engine/Expand)
            // substitutes it away before any AST reaches a read pass, so no demand for its
            // NAME can arise from an expression. One reaching here came from a position where
            // a define cannot stand (a model mapping, an alias target of a non-expression
            // walk) — diagnose the misuse at the demand site. No publish, ever.
            .define => {
                try demandDiag(self, task, "'{s}' is a define — it expands where it is used and cannot be named here", .{self.interner.stringBytes(task.name)});
                return;
            },
        }
    }
}

/// The identifier kind an alias must resolve to (const/func/pred). Sort aliases take the
/// refined-re-export path (they carry a carrier walk), not alias-collapse.
const AliasKind = enum {
    constant,
    func,
    pred,

    fn matches(self: AliasKind, tag: std.meta.Tag(InternPool.Key)) bool {
        return switch (self) {
            .constant => tag == .constant,
            .func => tag == .func,
            .pred => tag == .pred,
        };
    }

    fn label(self: AliasKind) []const u8 {
        return switch (self) {
            .constant => "constant",
            .func => "function",
            .pred => "predicate",
        };
    }
};

/// ALIAS-COLLAPSE (Foundation C): `const/func/pred LOCAL = TARGET` binds LOCAL to TARGET's
/// EXISTING pool Index — mints nothing (identity by origin). Resolve TARGET (demanding it +
/// following qualifiers; transitive through a chain of aliases for free, since each aliased
/// target already resolved to its origin Index), check its kind, then publish `Mint.existing`.
/// A diagnostic points at the alias's TARGET token (in `task.file`, where `sink.current_file`
/// already points) — the local name has no meaning apart from its target.
fn publishAlias(self: *Context, h: *Engine.Handle, task: FetchTask, key: IdentKV.Key, a: ast.Alias, kind: AliasKind) std.mem.Allocator.Error!void {
    const target = demandTok(self, h, task.file, a.target) catch |e| switch (e) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Unresolved => return, // suspended (resume re-runs) or diagnosed by demandTok
    };
    if (!kind.matches(self.interner.keyOf(target))) {
        self.sink.add(a.target.start, "'{s}' is not a {s}", .{ self.interner.stringBytes(a.target.name), kind.label() }) catch return error.OutOfMemory;
        return; // no publish
    }
    _ = try self.idents.publish(self.io, key, .{ .existing = target });
}

// --- layer-2 sub-demand resolution ----------------------------------------------------

/// `Unresolved` = "this production cannot finish THIS run" — either SUSPENDED (a
/// sub-fetch was racked and `h.suspendOn` set; resume re-runs `produce`) or DIAGNOSED
/// (a kind mismatch / unsupported form was reported; no publish, demanders wedge — the
/// red-phase failure mode). Callers yield identically for both.
const ResolveError = std.mem.Allocator.Error || error{Unresolved};

/// One sub-demand: `name` in `file`'s universe namespace. `done` = the Index; `pending`
/// = the TaskIndex to suspend on (an in-flight fetch, or a sub-fetch just racked here).
const Demand = union(enum) { done: InternPool.Index, pending: Engine.TaskIndex };

fn demandIdent(self: *Context, h: *Engine.Handle, file: InternPool.Index, name: InternPool.StrId, loc: u32) std.mem.Allocator.Error!Demand {
    const ns = try self.interner.namespace(.universe, file);
    if (self.idents.lookup(self.io, .{ .namespace = ns, .name = name })) |state| switch (state) {
        .done => |ix| return .{ .done = ix },
        .in_flight => |owner| return .{ .pending = owner },
    };
    // absent: rack the sub-fetch ourselves. (A racing demander racks a duplicate — the
    // sub-fetch's own claimOrLookup dedups; the loser becomes a waiter.)
    const t = try h.rackIndexed(try new(self.arena, .{ .file = file, .name = name, .loc = loc }));
    return .{ .pending = t };
}

/// Resolve a SORT-position token (possibly `ns.Name`-qualified) to a pool sort `Index`,
/// demanding the import and/or sort as needed. Suspends on the FIRST miss (no batching
/// — each resume re-runs `produce` cheaply and gets one name further; simplicity wins
/// while single-threaded).
fn resolveSortDemand(self: *Context, h: *Engine.Handle, file: InternPool.Index, source: []const u8, tok: lexer.Token) ResolveError!InternPool.Index {
    const text = source[tok.start..tok.end]; // diagnostics only
    var target_file = file;
    if (tok.qualifier != InternPool.Index.none) {
        const imp_ix = switch (try demandIdent(self, h, file, tok.qualifier, tok.start)) {
            .done => |ix| ix,
            .pending => |t| {
                h.suspendOn(t);
                return error.Unresolved;
            },
        };
        const imp = self.interner.keyOf(imp_ix);
        if (imp != .import) {
            self.sink.add(tok.start, "'{s}' is not a namespace", .{self.interner.stringBytes(tok.qualifier)}) catch return error.OutOfMemory;
            return error.Unresolved;
        }
        // the sort lives in the imported namespace's FILE
        target_file = self.interner.keyOf(imp.import.namespace).namespace.file;
    }
    const ix = switch (try demandIdent(self, h, target_file, tok.name, tok.start)) {
        .done => |x| x,
        .pending => |t| {
            h.suspendOn(t);
            return error.Unresolved;
        },
    };
    if (self.interner.keyOf(ix) != .sort) {
        self.sink.add(tok.start, "'{s}' is not a sort", .{text}) catch return error.OutOfMemory;
        return error.Unresolved;
    }
    return ix;
}

/// Resolve a refinement GUARD token (`g` in `sort H = G where g`) to a QUALIFIER Index. The
/// guard is walked like any AST: the expansion pass is run over the synthetic call `g(#g0)`
/// (`#g0` = the guarded element, a root local). An OPAQUE predicate survives as a resolved
/// call: check it is unary over the parent's carrier and use its `.pred` Index. A DEFINE'd
/// guard was substituted away: elaborate the expanded body with `#g0` bound at the carrier,
/// reify it, and mint an anonymous `.guard` TERM Item (applied later by substituting `#g0` —
/// Elab.qualifierApp). Suspends (Unresolved) while the pass has demands outstanding.
fn resolveGuard(self: *Context, h: *Engine.Handle, file: InternPool.Index, source: []const u8, tok: lexer.Token, parent: InternPool.Index) ResolveError!InternPool.Index {
    const g0 = try guardParamName(self, 0);
    const arg = try self.arena.create(ast.Expr);
    arg.* = .{ .name = .{ .tag = .identifier, .start = tok.start, .end = tok.start, .name = g0 } };
    const args = try self.arena.alloc(*const ast.Expr, 1);
    args[0] = arg;
    const call = try self.arena.create(ast.Expr);
    call.* = .{ .call = .{ .callee = tok, .args = args } };
    const scope_names = [_]InternPool.StrId{g0};
    const expanded = switch (try Expand.expandFormula(self, h, file, call, .{ .scope = &scope_names, .symbolize_root = true })) {
        .ready => |x| x,
        .suspended, .failed => return error.Unresolved,
    };
    const carrier = self.interner.carrierOf(parent);
    if (expanded.* == .call and expanded.call.callee.tag == .symbol) {
        // an opaque predicate (resolved to its identity by the pass): unary over the carrier.
        const ix = expanded.call.callee.name;
        const cb = switch (self.interner.keyOf(ix)) {
            .pred => |c| c,
            else => {
                self.sink.add(tok.start, "sort refinement '{s}' is not a predicate in scope", .{source[tok.start..tok.end]}) catch return error.OutOfMemory;
                return error.Unresolved;
            },
        };
        const sig = self.interner.keyOf(cb.sig).sig;
        if (sig.args.len != 1 or self.interner.carrierOf(sig.args[0]) != carrier) {
            self.sink.add(tok.start, "sort refinement '{s}' must be a unary predicate over the base sort", .{source[tok.start..tok.end]}) catch return error.OutOfMemory;
            return error.Unresolved;
        }
        return ix;
    }
    // a define'd guard: its expanded body over `#g0` at the carrier, reified as a guard term.
    const ns = try self.interner.namespace(.universe, file);
    var scratch: term.Pool = .init(self.arena, self.gpa);
    var walk: Walk = Walk.init(self.arena, self.interner, source, self.sink);
    var fresh: u32 = 0;
    var e = Elab.init(self.arena, self.io, self, self.interner, &self.idents, &scratch, self.sink, source, &walk, ns, &fresh);
    e.pushBinder(g0, @enumFromInt(@intFromEnum(carrier)), g0) catch return error.OutOfMemory;
    const typed = e.elaborateExpr(expanded) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return error.Unresolved, // diagnosed by Elab
    };
    if (typed.sort != Elab.prop_sort) {
        self.sink.add(tok.start, "sort refinement '{s}' must be a proposition over the base sort", .{source[tok.start..tok.end]}) catch return error.OutOfMemory;
        return error.Unresolved;
    }
    self.interner.lockWrite(self.io);
    defer self.interner.unlockWrite(self.io);
    const off = scratch.reify(typed.id, self.interner) catch return error.OutOfMemory;
    return self.interner.mintGuard(.{ .term = off, .carrier = carrier }) catch return error.OutOfMemory;
}

/// Resolve a (possibly `ns.`-qualified) token to its pool Index, demanding the import +
/// (if qualified) parsing the target file. Suspends on the first miss. Kind-AGNOSTIC — the
/// caller inspects the returned Index (a define recurses; anything else is just demanded).
fn demandTok(self: *Context, h: *Engine.Handle, file: InternPool.Index, tok: lexer.Token) ResolveError!InternPool.Index {
    var target_file = file;
    if (tok.qualifier != InternPool.Index.none) {
        const imp_ix = switch (try demandIdent(self, h, file, tok.qualifier, tok.start)) {
            .done => |ix| ix,
            .pending => |t| {
                h.suspendOn(t);
                return error.Unresolved;
            },
        };
        if (self.interner.keyOf(imp_ix) != .import) {
            self.sink.add(tok.start, "'{s}' is not a namespace", .{self.interner.stringBytes(tok.qualifier)}) catch return error.OutOfMemory;
            return error.Unresolved;
        }
        target_file = self.interner.keyOf(imp_ix).import.namespace;
        target_file = self.interner.keyOf(target_file).namespace.file;
        // the target file must be parsed before we can recurse into a define it declares.
        switch (try self.demandParse(h, target_file)) {
            .parsed => {},
            .parsing => |t| {
                h.suspendOn(t);
                return error.Unresolved;
            },
            .unparsed => {},
        }
    }
    return switch (try demandIdent(self, h, target_file, tok.name, tok.start)) {
        .done => |ix| ix,
        .pending => |t| {
            h.suspendOn(t);
            return error.Unresolved;
        },
    };
}

const SigParts = struct { sig: InternPool.Index, param_names: []const InternPool.StrId };

/// Assemble a callable's deduped Sig + param names from its binder params and optional
/// result token (null = predicate, result Prop). Static rejections (predicated params)
/// fire before any demand so a diagnostic can't repeat across resumes.
fn assembleSig(self: *Context, h: *Engine.Handle, file: InternPool.Index, source: []const u8, params: []const ast.Binder, result_tok: ?lexer.Token) ResolveError!SigParts {
    for (params) |b| {
        if (b.guard != null) {
            self.sink.add(b.name.start, "predicated parameters ('where') are not yet supported by the demand prover", .{}) catch return error.OutOfMemory;
            return error.Unresolved;
        }
    }
    const args = try self.arena.alloc(InternPool.Index, params.len);
    const names = try self.arena.alloc(InternPool.StrId, params.len);
    for (params, args, names) |b, *a, *n| {
        a.* = try resolveSortDemand(self, h, file, source, b.sort);
        n.* = b.name.name; // stamped at parse
    }
    const result: InternPool.Index = if (result_tok) |rt|
        try resolveSortDemand(self, h, file, source, rt)
    else
        .prop;
    const sig = self.interner.get(.{ .sig = .{ .result = result, .result_refined = .none, .args = args } }) catch return error.OutOfMemory;
    return .{ .sig = sig, .param_names = names };
}

/// The hygienic fvar name for a guard's parameter at position `i` — `#gN`. '#' cannot lex, so
/// these never collide with a userland arg term's free variables (the capture-safety `substFvar`
/// relies on at the call site). Position-based is enough: a guard is copied in + FULLY
/// substituted at each call before it enters the surrounding term, so two funcs may reuse `#g0`.
fn guardParamName(self: *Context, i: usize) std.mem.Allocator.Error!InternPool.StrId {
    const bytes = try std.fmt.allocPrint(self.arena, "#g{d}", .{i});
    return self.interner.internString(bytes);
}

/// Reify a guarded func's `requires` precondition into a durable guard TERM over its PARAMS,
/// returning the `extra` offset (an `InternPool.TermOff`) stored in the func Item. The params
/// bind to hygienic `#gN` fvars (`guardParamName`); a call site substitutes the actual arg
/// terms for these fvars and owes the resulting obligation (`Elab.elaborateCall`).
///
/// LAYERING: the precondition may reference other identifiers (`ZERO`, guard predicates, …).
/// Elab CANNOT suspend, so their transitive reference closure is demanded FIRST (reusing the
/// define-closure walk over `requires` as the "body" with the params as locals); a miss suspends
/// this FetchTask (resume re-runs `produce`, idempotent). Once resolved, a throwaway scratchpad
/// Elab elaborates the precondition — the params pushed as expression-local binders at their
/// carrier sorts — and `reify` serializes it under the InternPool write-mutex.
fn reifyGuard(self: *Context, h: *Engine.Handle, file: InternPool.Index, source: []const u8, name: InternPool.StrId, params: []const ast.Binder, sig: InternPool.Index, requires: *const ast.Expr) ResolveError!InternPool.TermOff {
    // (a) DEFINE-EXPAND the precondition with every free global SYMBOLIZED (resolved to its
    // identity, demanded — a miss suspends this FetchTask; resume re-runs `produce`), so the
    // throwaway Elab below needs no read pass of its own.
    _ = name;
    const pnames = try self.arena.alloc(InternPool.StrId, params.len);
    for (params, pnames) |b, *o| o.* = b.name.name;
    const body = switch (try Expand.expandFormula(self, h, file, requires, .{ .scope = pnames, .symbolize_root = true })) {
        .ready => |x| x,
        .suspended, .failed => return error.Unresolved,
    };

    // (b) elaborate the precondition to a scratchpad term with the params bound to `#gN` fvars.
    const ns = try self.interner.namespace(.universe, file);
    var scratch: term.Pool = .init(self.arena, self.gpa);
    var walk: Walk = Walk.init(self.arena, self.interner, source, self.sink);
    var fresh: u32 = 0;
    var e = Elab.init(self.arena, self.io, self, self.interner, &self.idents, &scratch, self.sink, source, &walk, ns, &fresh);
    // COPY the sig's arg slice: it aliases `extra`, which `guardParamName`'s interning below can
    // reallocate mid-loop (the stale-slice trap).
    const arg_ixs = try self.arena.dupe(InternPool.Index, self.interner.keyOf(sig).sig.args);
    for (params, arg_ixs, 0..) |b, arg_ix, i| {
        const carrier: term.SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(arg_ix)));
        const fv = try guardParamName(self, i);
        e.pushBinder(b.name.name, carrier, fv) catch return error.OutOfMemory;
    }
    const typed = e.elaborateExpr(body) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        // a malformed precondition (bad sort, unknown name) is DIAGNOSED into the sink by Elab;
        // yield without publishing (demanders wedge — same red-phase mode as any diagnosed miss).
        error.Recover => return error.Unresolved,
    };
    if (typed.sort != Elab.prop_sort) {
        self.sink.add(exprLocOf(requires), "a function's 'requires' precondition must be a proposition", .{}) catch return error.OutOfMemory;
        return error.Unresolved;
    }

    // (c) serialize the guard durably (params live as `#gN` fvars in the reified term).
    self.interner.lockWrite(self.io);
    defer self.interner.unlockWrite(self.io);
    return scratch.reify(typed.id, self.interner) catch return error.OutOfMemory;
}

fn exprLocOf(e: *const ast.Expr) u32 {
    return Elab.exprLoc(e);
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");
const FactKV = @import("../FactKV.zig");

/// A read_fn stub for single-file tests (no imports followed) — never called.
fn readNothing(_: ?*anyopaque, _: std.mem.Allocator, _: []const u8) anyerror![]const u8 {
    return error.FileNotFound;
}

/// Build a REAL Context around one discovered + parsed fixture file. `pub` for the other
/// engine modules' unit tests (Polynomial/Prove rigs build on it).
pub fn fixtureCtx(arena: std.mem.Allocator, io: std.Io, path: []const u8, source: []const u8) !*Context {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);

    const ctx = try arena.create(Context);
    ctx.* = .{
        .arena = arena,
        .gpa = arena, // test fixture: arena doubles as the scratch GPA
        .io = io,
        .sink = sink,
        .interner = interner,
        .facts = FactKV.init(interner),
        .idents = IdentKV.init(interner),
        .read_ctx = null,
        .read_fn = &readNothing,
        .verify = .{},
        .std_root = "",
    };
    const fid = try ctx.preload(path, source);
    var p: parser.Parser = .initInterning(arena, source, sink, interner);
    ctx.parsed.items[@intFromEnum(fid)] = try p.parseFile();
    for (ctx.parsed.items[@intFromEnum(fid)].decls) |*decl| _ = try ctx.registerDecl(fid, decl);
    // this fixture registers the root file's decls DIRECTLY (bypassing ParseTask); mark it
    // `.parsed` so a later `demandParse` doesn't re-rack a ParseTask that would re-register
    // every decl and (now) diagnose each as a duplicate.
    ctx.parse_state.items[@intFromEnum(fid)] = .parsed;
    try testing.expectEqual(@as(usize, 0), sink.list.items.len);
    return ctx;
}

test "ast registry: declOf resolves parsed decls by name; a miss is null; a synthetic inserts" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort Nat
        \\func succ(n: Nat): Nat
        \\axiom refl: forall n: Nat; n = n
    );
    const fid = (try ctx.lookupFile("/t/a.bpa")).?;

    // each named decl resolves by its stamped name, to the right kind.
    try testing.expect(ctx.declOf(fid, try ctx.interner.internString("Nat")).?.* == .sort);
    try testing.expect(ctx.declOf(fid, try ctx.interner.internString("succ")).?.* == .func);
    try testing.expect(ctx.declOf(fid, try ctx.interner.internString("refl")).?.* == .axiom);
    // an undeclared name misses cleanly.
    try testing.expect(ctx.declOf(fid, try ctx.interner.internString("Missing")) == null);

    // a SYNTHETIC decl (no positional slot) inserts under a mangled name and resolves the
    // same way — the mechanism accelerant generators rely on.
    const synth = try arena.create(ast.Decl);
    synth.* = .{ .sort = .{ .local = .{ .tag = .identifier, .start = 0, .end = 0, .name = try ctx.interner.internString("foo[3]") } } };
    _ = try ctx.registerDecl(fid, synth);
    try testing.expectEqual(synth, ctx.declOf(fid, try ctx.interner.internString("foo[3]")).?);
}

test "fetch: a root sort is produced from its declaration and published (demanders dedup)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort Nat
        \\sort Bool
    );
    const f = try ctx.fileIndex("/t/a.bpa");
    const nat = try ctx.interner.internString("Nat");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    // two demanders of the same sort: the second dedups to a suspended waiter.
    _ = try eng.rack(try new(arena, .{ .file = f, .name = nat, .loc = 0 }));
    _ = try eng.rack(try new(arena, .{ .file = f, .name = nat, .loc = 0 }));
    try eng.run();
    try testing.expectEqual(eng.racked, eng.completed); // quiescent, no wedge

    const ns = try ctx.interner.namespace(.universe, f);
    const outcome = try ctx.idents.claimOrLookup(io, .{ .namespace = ns, .name = nat }, @enumFromInt(99));
    try testing.expect(outcome == .done);
    const key = ctx.interner.keyOf(outcome.done);
    try testing.expect(key == .sort);
    try testing.expect(key.sort.refinement == null); // a root sort
    try testing.expectEqual(nat, key.sort.name);
    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);
}

test "fetch: a `where`-alias produces a refined sort {parent, [guard]}" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort Nat
        \\pred nonzero(n: Nat)
        \\sort Pos = Nat where nonzero
    );
    const f = try ctx.fileIndex("/t/a.bpa");
    const pos = try ctx.interner.internString("Pos");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = f, .name = pos, .loc = 0 }));
    try eng.run();
    try testing.expectEqual(eng.racked, eng.completed);
    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);

    const ns = try ctx.interner.namespace(.universe, f);
    const pos_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = pos }).?.done;
    const key = ctx.interner.keyOf(pos_ix).sort;
    try testing.expect(key.refinement != null); // a refined sort
    const nat_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("Nat") }).?.done;
    const nz_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("nonzero") }).?.done;
    try testing.expectEqual(nat_ix, key.refinement.?.parent);
    try testing.expectEqual(@as(usize, 1), key.refinement.?.qualifiers.len);
    try testing.expectEqual(nz_ix, key.refinement.?.qualifiers[0]);
    // carrierOf walks the refinement to the root Nat
    try testing.expectEqual(nat_ix, ctx.interner.carrierOf(pos_ix));
}

test "fetch: an import binds to the target file's namespace" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    // parent imports child; simulate the parse phase's import resolution by
    // discovering both files and recording the raw-path -> child mapping.
    const ctx = try fixtureCtx(arena, io, "/t/parent.bpa",
        \\import peano <<< "child.bpa"
    );
    const child_fid = try ctx.preload("/t/child.bpa", "sort Nat");
    {
        var p: parser.Parser = .initInterning(arena, "sort Nat", ctx.sink, ctx.interner);
        ctx.parsed.items[@intFromEnum(child_fid)] = try p.parseFile();
        for (ctx.parsed.items[@intFromEnum(child_fid)].decls) |*decl| _ = try ctx.registerDecl(child_fid, decl);
        ctx.parse_state.items[@intFromEnum(child_fid)] = .parsed; // registered directly; don't re-parse
    }
    const parent_fid = (try ctx.lookupFile("/t/parent.bpa")).?;
    const raw = try ctx.interner.internString("child.bpa");
    try ctx.import_maps.items[@intFromEnum(parent_fid)].put(arena, raw, child_fid);

    const parent = try ctx.fileIndex("/t/parent.bpa");
    const peano = try ctx.interner.internString("peano");
    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = parent, .name = peano, .loc = 0 }));
    try eng.run();

    const ns = try ctx.interner.namespace(.universe, parent);
    const outcome = try ctx.idents.claimOrLookup(io, .{ .namespace = ns, .name = peano }, @enumFromInt(99));
    try testing.expect(outcome == .done);
    const key = ctx.interner.keyOf(outcome.done);
    try testing.expect(key == .import);
    // the import's namespace IS the child's universe-namespace
    const child_file = try ctx.fileIndex("/t/child.bpa");
    try testing.expectEqual(try ctx.interner.namespace(.universe, child_file), key.import.namespace);
    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);
}

test "fetch: an undeclared name diagnoses 'reference not found' and publishes nothing" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa", "sort Nat");
    const f = try ctx.fileIndex("/t/a.bpa");
    const missing = try ctx.interner.internString("Missing");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = f, .name = missing, .loc = 3 }));
    try eng.run();

    try testing.expectEqual(@as(usize, 1), ctx.sink.list.items.len);
    try testing.expect(std.mem.indexOf(u8, ctx.sink.list.items[0].message, "reference not found") != null);
    // never published: a fresh lookup CLAIMS (the failed fetch's in_flight entry is its
    // own; a later demander... would wedge — here we assert the entry is not done).
    const ns = try ctx.interner.namespace(.universe, f);
    const outcome = try ctx.idents.claimOrLookup(io, .{ .namespace = ns, .name = missing }, @enumFromInt(99));
    try testing.expect(outcome != .done);
}

test "fetch layer 2: a func's sorts are sub-demanded; sig + param names assemble" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort Nat
        \\func add(a: Nat, b: Nat): Nat
        \\pred le(a: Nat, b: Nat)
        \\const ZERO: Nat
    );
    const f = try ctx.fileIndex("/t/a.bpa");
    const add = try ctx.interner.internString("add");
    const le = try ctx.interner.internString("le");
    const zero = try ctx.interner.internString("ZERO");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    // demand ONLY the callables/constant — the sort Nat is sub-demanded automatically.
    _ = try eng.rack(try new(arena, .{ .file = f, .name = add, .loc = 0 }));
    _ = try eng.rack(try new(arena, .{ .file = f, .name = le, .loc = 0 }));
    _ = try eng.rack(try new(arena, .{ .file = f, .name = zero, .loc = 0 }));
    try eng.run();
    try testing.expectEqual(eng.racked, eng.completed); // quiescent, no wedge
    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);

    const ns = try ctx.interner.namespace(.universe, f);
    const nat_state = ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("Nat") }).?;
    const nat = nat_state.done; // the sub-demanded sort published

    { // func add: sig (Nat,Nat)->Nat, unguarded, param names [a,b]
        const add_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = add }).?.done;
        const c = ctx.interner.keyOf(add_ix).func;
        try testing.expectEqual(InternPool.no_term, c.guard);
        const sig = ctx.interner.keyOf(c.sig).sig;
        try testing.expectEqual(nat, sig.result);
        try testing.expectEqual(@as(usize, 2), sig.args.len);
        try testing.expectEqual(nat, sig.args[0]);
        try testing.expectEqual(nat, sig.args[1]);
        try testing.expectEqual(try ctx.interner.internString("a"), c.param_names[0]);
        try testing.expectEqual(try ctx.interner.internString("b"), c.param_names[1]);
    }
    { // pred le: result is the reserved Prop
        const le_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = le }).?.done;
        const sig = ctx.interner.keyOf(ctx.interner.keyOf(le_ix).pred.sig).sig;
        try testing.expectEqual(InternPool.Index.prop, sig.result);
        try testing.expectEqual(@as(usize, 2), sig.args.len);
    }
    { // const ZERO: sort Nat
        const zero_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = zero }).?.done;
        try testing.expectEqual(nat, ctx.interner.keyOf(zero_ix).constant.sort);
    }
}

test "fetch layer 2: a qualified param sort walks import -> child file's sort" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/parent.bpa",
        \\import peano <<< "child.bpa"
        \\func double(n: peano.Nat): peano.Nat
    );
    const child_fid = try ctx.preload("/t/child.bpa", "sort Nat");
    {
        var p: parser.Parser = .initInterning(arena, "sort Nat", ctx.sink, ctx.interner);
        ctx.parsed.items[@intFromEnum(child_fid)] = try p.parseFile();
        for (ctx.parsed.items[@intFromEnum(child_fid)].decls) |*decl| _ = try ctx.registerDecl(child_fid, decl);
        ctx.parse_state.items[@intFromEnum(child_fid)] = .parsed; // registered directly; don't re-parse
    }
    const parent_fid = (try ctx.lookupFile("/t/parent.bpa")).?;
    const raw = try ctx.interner.internString("child.bpa");
    try ctx.import_maps.items[@intFromEnum(parent_fid)].put(arena, raw, child_fid);

    const parent = try ctx.fileIndex("/t/parent.bpa");
    const double = try ctx.interner.internString("double");
    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = parent, .name = double, .loc = 0 }));
    try eng.run();
    try testing.expectEqual(eng.racked, eng.completed);
    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);

    // the func's arg/result sort is the CHILD file's Nat
    const parent_ns = try ctx.interner.namespace(.universe, parent);
    const child_file = try ctx.fileIndex("/t/child.bpa");
    const child_ns = try ctx.interner.namespace(.universe, child_file);
    const nat = ctx.idents.lookup(io, .{ .namespace = child_ns, .name = try ctx.interner.internString("Nat") }).?.done;
    const dbl = ctx.idents.lookup(io, .{ .namespace = parent_ns, .name = double }).?.done;
    const sig = ctx.interner.keyOf(ctx.interner.keyOf(dbl).func.sig).sig;
    try testing.expectEqual(nat, sig.result);
    try testing.expectEqual(nat, sig.args[0]);
}

test "fetch layer 2: a guarded func ('requires') reifies its precondition into the Item's guard" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort Nat
        \\pred pos(n: Nat)
        \\func dec(n: Nat): Nat requires pos(n)
    );
    const f = try ctx.fileIndex("/t/a.bpa");
    const dec = try ctx.interner.internString("dec");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = f, .name = dec, .loc = 0 }));
    try eng.run();

    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);
    const ns = try ctx.interner.namespace(.universe, f);
    const dec_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = dec }).?.done;
    const c = ctx.interner.keyOf(dec_ix).func;
    // a guard was reified (not `no_term`); rebuild it and check it is `pos(#g0)` — the
    // precondition over the param-0 fvar, ready for a call site to substitute the actual arg.
    try testing.expect(c.guard != InternPool.no_term);
    var scratch: term.Pool = .init(arena, arena);
    const g = try scratch.copyIn(ctx.interner, c.guard);
    const pos_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("pos") }).?.done;
    const nat_ix = ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("Nat") }).?.done;
    const fv = try scratch.add(.{ .fvar = .{ .name = try ctx.interner.internString("#g0"), .sort = @enumFromInt(@intFromEnum(nat_ix)) } });
    const want = try scratch.addApp(.pred, @enumFromInt(@intFromEnum(pos_ix)), &.{fv});
    try testing.expect(scratch.alphaEq(g, want));
}

test "fetch: a fact name demanded as an identifier is a kind mismatch" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort Nat
        \\axiom axP: P
    );
    const f = try ctx.fileIndex("/t/a.bpa");
    const axp = try ctx.interner.internString("axP");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = f, .name = axp, .loc = 0 }));
    try eng.run();

    try testing.expectEqual(@as(usize, 1), ctx.sink.list.items.len);
    try testing.expect(std.mem.indexOf(u8, ctx.sink.list.items[0].message, "names a fact") != null);
}

test "fetch: a schema (a params-carrying fact) is REJECTED — facts resolve via the fact table" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    // FetchTask produces only IDENTIFIERS; a schema is a fact-with-params → it belongs to the
    // FACT table (a ProveTask publishes its `.schema` locator). Reaching FetchTask is misuse.
    const ctx = try fixtureCtx(arena, io, "/t/a.bpa",
        \\sort T
        \\theorem everywhereGoal(prop: T -> Prop): forall x: T; goal(x)
        \\proof
        \\  @c | forall x: T; goal(x) [by cite ax]
        \\qed
    );
    const f = try ctx.fileIndex("/t/a.bpa");
    const name = try ctx.interner.internString("everywhereGoal");

    var eng = Engine.init(arena, ctx);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = f, .name = name, .loc = 0 }));
    try eng.run();

    try testing.expectEqual(@as(usize, 1), ctx.sink.list.items.len);
    try testing.expect(std.mem.indexOf(u8, ctx.sink.list.items[0].message, "names a fact") != null);
}
