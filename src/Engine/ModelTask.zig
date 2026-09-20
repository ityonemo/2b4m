//! ModelTask — produces a MODEL (`.model` Item), the fourth demand-produced entity kind:
//!   ModelTask : model  ::  FetchTask : identifier  ::  ProveTask : fact.
//! Racked when `[by model(M) …]` (or any model reference) hits an un-interned model M.
//!
//! A `model M { src: tgt, … }` decl is an INTERPRETATION: an overlay mapping each source
//! entity Index → the local target Index that plays it. `[by model(M) src.thm]` then proves
//! `src.thm` in the namespace `(M, src_file)`, where resolving a source name consults M's
//! overlay (Step 13b/c) — so the remapping falls out of WHICH NAMESPACE you resolve in, no
//! bespoke formula rewrite. This task just BUILDS the overlay + mints the `.model`.
//!
//! Each mapping line references entities that may not be interned yet, so ModelTask is a
//! RESUMABLE, SUSPENDING task (like FetchTask sub-demanding sorts): it racks a Fetch/Prove
//! for each mapping's src + tgt, suspends on any absent one, and re-runs (idempotently) on
//! each wake until the whole closure is resolved — then assembles the overlay and publishes.
//!   - `.symbol`   (`cite.op: combine`)         — src + tgt are IDENTIFIERS (FetchTask).
//!   - `.obligation` (`cite.ax <- localThm`)    — src + tgt are FACTS (ProveTask/FactKV).
//! Both become one overlay entry `src Index → tgt Index`; the model publishes into IdentKV
//! under M's name (a model is a named entity in its declaring file's namespace).

const std = @import("std");
const ast = @import("../ast.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const IdentKV = @import("../IdentKV.zig");
const FactKV = @import("../FactKV.zig");
const FetchTask = @import("FetchTask.zig");
const ProveTask = @import("ProveTask.zig");
const Token = @import("../lexer.zig").Token;

const ModelTask = @This();

/// the `.file` Index the `model M {…}` decl lives in (the LOCAL/declaring file — sources
/// are `cite.`-qualified into imports of THIS file; targets are bare names in THIS file).
file: InternPool.Index,
name: StrId,
/// the demanding reference's offset + file (for diagnostics), like FetchTask.
loc: u32,
loc_file: ?InternPool.Index = null,

pub fn new(arena: std.mem.Allocator, payload: ModelTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(ModelTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *ModelTask = @ptrCast(@alignCast(payload));
    return run(self, task.*, h);
}

pub fn run(self: *Context, task: ModelTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    if (self.verify.trace_facts) {
        const line = std.fmt.allocPrint(self.arena, "[model] task#{d} = model {s} in file#{d}\n", .{ @intFromEnum(h.self_index), self.interner.stringBytes(task.name), @intFromEnum(task.file) }) catch "";
        self.traceLine(line);
    }
    const ns = try self.interner.namespace(.universe, task.file);
    const key = IdentKV.Key{ .namespace = ns, .name = task.name };
    switch (try self.idents.claimOrLookup(self.io, key, h.self_index)) {
        .done => return,
        .in_flight => |owner| {
            if (owner != h.self_index) {
                h.suspendOn(owner);
                return;
            }
            // ours — resumed mid-production; fall through and re-run the resolve pass.
        },
        .claimed => {},
    }
    // the declaring file must be parsed to read the model decl (lazy parsing).
    switch (try self.demandParse(h, task.file)) {
        .parsed => {},
        .parsing => |t| return h.suspendOn(t),
        .unparsed => {},
    }
    try produce(self, task, h, key);
}

/// Find the `model M` decl, resolve every mapping's src+tgt (racking sub-demands and
/// suspending on any absent), and — once the whole closure is resolved — assemble the
/// overlay + publish the `.model`. Idempotent across resumes.
fn produce(self: *Context, task: ModelTask, h: *Engine.Handle, key: IdentKV.Key) std.mem.Allocator.Error!void {
    const fid = self.fileOf(task.file) orelse {
        self.sink.add(self.diagFile(task.file), task.loc, "internal: model into an undiscovered file", .{}) catch return error.OutOfMemory;
        return;
    };
    const source = self.files.get(@intFromEnum(fid)).source;

    // resolve the model decl by name (registry); require it actually be a `model`.
    const found = self.declOf(fid, task.name);
    if (found == null or found.?.* != .model) {
        try demandDiag(self, task, "reference not found: model '{s}'", .{self.interner.stringBytes(task.name)});
        return;
    }
    const m = found.?.model;

    // resolve all mapping src+tgt; collect overlay entries. Rack + suspend on the FIRST
    // unresolved (re-run resolves one more each wake; the ones already done are cheap). The
    // `:` identifier maps and the `<-` obligation discharges are two lists; the overlay is
    // uniform (src Index → tgt Index). A `:` map may also carry GUARD-DISCHARGER witnesses
    // (`tgt(f…)` for a const→refined sort, `tgt -| f` for a func→refined result) — validated
    // here (const-vs-func kind check) since the target's KIND is resolved at this point.
    var overlay: std.ArrayList(InternPool.Key.Mapping) = .empty;
    var dischargers: std.ArrayList(InternPool.Key.Mapping) = .empty; // (target-symbol, establishing-fact)
    // `src: D` with D a DEFINE (a macro, no Index): not an overlay entry — recorded on the
    // Context at publish so the expansion pass substitutes D's body for `src` in a transfer.
    var define_targets: std.ArrayList(struct { src: InternPool.Index, def: Context.DefineKey }) = .empty;
    var blocker: ?Engine.TaskIndex = null;
    for (m.identifiers) |im| {
        const mapping = identMapping(im);
        // the SHAPE of a `:` map, read off the source's own declaration before any demand
        // resolves it (the demand tables would only say "names a fact, not a symbol", twice).
        if (try mappingDecl(self, h, task.file, mapping.source, &blocker)) |sd| {
            const t = try tokText(self, mapping.source);
            switch (sd.decl.*) {
                .define => return diagAt(self, task, mapping.source.start, "'{s}' is a transparent (`define`d) symbol — it rides along on the primitives in its body and cannot be a model mapping source; map those primitives instead", .{t}),
                .axiom => return diagAt(self, task, mapping.source.start, "'{s}' is an axiom obligation, not a sort/symbol — discharge it with `<-` (`{s} <- <local fact>`), not `:`", .{ t, t }),
                .theorem => return diagAt(self, task, mapping.source.start, "model maps only axioms; '{s}' is a theorem — it materializes through the mapped axioms, so drop this mapping", .{t}),
                else => {},
            }
        } else if (blocker) |b| return h.suspendOn(b);
        const src = try resolveEntity(self, h, task.file, source, mapping.source, .ident, &blocker);
        if (try defineTargetOf(self, h, task.file, mapping.target, &blocker)) |def| {
            if (im != .basic) {
                try demandDiag(self, task, "'{s}' is a define; a define target takes no guard-witness clause", .{self.interner.stringBytes(mapping.target.name)});
                return;
            }
            if (src) |s| try define_targets.append(self.arena, .{ .src = s, .def = def });
            continue;
        }
        const tgt = try resolveEntity(self, h, task.file, source, mapping.target, .ident, &blocker);
        if (src) |s| if (tgt) |t| {
            try overlay.append(self.arena, .{ .src = s, .tgt = t });
            // witness clauses: kind-check against the resolved TARGET, resolve each discharger
            // fact, and record `(target-symbol, fact)` into the model's discharger table (keyed
            // by the target symbol so the transfer's discharge walk finds it in target space).
            if (try checkWitnesses(self, h, task, source, im, t, &dischargers, &blocker)) return; // diagnosed
        };
    }
    for (m.obligations) |mapping| {
        // the SHAPE of a `<-` discharge, likewise read off the declarations.
        if (try mappingDecl(self, h, task.file, mapping.source, &blocker)) |sd| {
            const t = try tokText(self, mapping.source);
            switch (sd.decl.*) {
                .sort, .constant, .func, .pred => return diagAt(self, task, mapping.source.start, "'{s}' is a sort or symbol, not an axiom — map it with `:` (`{s}: <target>`), not `<-`", .{ t, t }),
                .define => return diagAt(self, task, mapping.source.start, "'{s}' is a transparent (`define`d) symbol — it rides along on the primitives in its body and cannot be a model mapping source; map those primitives instead", .{t}),
                .theorem => return diagAt(self, task, mapping.source.start, "model maps only axioms; '{s}' is a theorem — it materializes through the mapped axioms, so drop this mapping", .{t}),
                // a SCHEMA obligation is discharged by a schema (a matching predicate parameter).
                .axiom => if (mapping.projection == null) if (ast.factOf(sd.decl)) |sf| if (sf.params != null) {
                    if (try mappingDecl(self, h, task.file, mapping.target, &blocker)) |td| {
                        const tf = ast.factOf(td.decl);
                        if (tf == null or tf.?.params == null)
                            return diagAt(self, task, mapping.target.start, "'{s}' discharges a schema, so it must itself be a schema (with a matching predicate parameter)", .{try tokText(self, mapping.target)});
                    } else if (blocker) |b| return h.suspendOn(b);
                },
                else => {},
            }
        } else if (blocker) |b| return h.suspendOn(b);
        const src = try resolveEntity(self, h, task.file, source, mapping.source, .fact, &blocker);
        if (mapping.projection) |proj| {
            // `srcAxiom <- NamedModel@proj.thm` — discharge srcAxiom by transferring the theorem
            // `proj.thm` THROUGH the model `NamedModel` (the inverted-dependency composition, e.g.
            // group axioms on a subgroup routed through the subgroup model). The discharging fact
            // is the TRANSFERRED `(NamedModel, proj-file).thm`.
            const tgt = try resolveProjection(self, h, task.file, source, mapping.target, proj, &blocker);
            if (src) |s| if (tgt) |t| {
                try overlay.append(self.arena, .{ .src = s, .tgt = t });
                try self.recordModelDischarged(t);
            };
            continue;
        }
        const tgt = try resolveEntity(self, h, task.file, source, mapping.target, .fact, &blocker);
        if (src) |s| if (tgt) |t| {
            try overlay.append(self.arena, .{ .src = s, .tgt = t });
            try self.recordModelDischarged(t); // the local fact is USED
        };
    }
    if (blocker) |b| return h.suspendOn(b);

    // everything resolved — build the model (deduped via get, under the write lock) and
    // publish its Index into IdentKV under M's name; then record its define targets.
    const model_ix = try self.idents.publish(self.io, key, .{ .model = .{ .parent = .universe, .overlay = try overlay.toOwnedSlice(self.arena), .dischargers = try dischargers.toOwnedSlice(self.arena), .home = task.file } });
    for (define_targets.items) |dt| try self.model_define_targets.put(self.arena, .{ .model = model_ix, .src = dt.src }, dt.def);
}

/// Is a `:` mapping's TARGET token a define (in the model's file, or an imported file)? A
/// define never enters IdentKV, so it is answered from the by-name AST registry — demanding
/// the import + the target file's parse as needed (blocker recorded).
fn defineTargetOf(self: *Context, h: *Engine.Handle, file: InternPool.Index, tok: Token, blocker: *?Engine.TaskIndex) std.mem.Allocator.Error!?Context.DefineKey {
    const md = (try mappingDecl(self, h, file, tok, blocker)) orelse return null;
    if (md.decl.* != .define) return null;
    return .{ .file = md.file, .name = tok.name };
}

/// The declaration a mapping token names — in the model's file for a bare token, in the
/// import's file for a qualified one (demanding the import + that file's parse as needed;
/// blocker recorded). Answered from the by-name AST registry, so it reads a define (which never
/// enters IdentKV) and a fact alike. Null = unresolved (blocked) or undeclared.
const MappingDecl = struct { decl: *const ast.Decl, file: InternPool.Index };
fn mappingDecl(self: *Context, h: *Engine.Handle, file: InternPool.Index, tok: Token, blocker: *?Engine.TaskIndex) std.mem.Allocator.Error!?MappingDecl {
    var target_file = file;
    if (tok.qualifier != InternPool.Index.none) {
        const ns = try self.interner.namespace(.universe, file);
        const st = self.idents.lookup(self.io, .{ .namespace = ns, .name = tok.qualifier }) orelse {
            blocker.* = try h.rackIndexed(try FetchTask.new(self.arena, .{ .file = file, .name = tok.qualifier, .loc = tok.start, .loc_file = file }));
            return null;
        };
        switch (st) {
            .in_flight => |owner| {
                if (owner != h.self_index) blocker.* = owner;
                return null;
            },
            .done => |ix| switch (self.interner.keyOf(ix)) {
                .import => |imp| target_file = self.interner.keyOf(imp.namespace).namespace.file,
                else => return null,
            },
        }
        switch (try self.demandParse(h, target_file)) {
            .parsed => {},
            .parsing => |t| {
                blocker.* = t;
                return null;
            },
            .unparsed => return null,
        }
    }
    const fid = self.fileOf(target_file) orelse return null;
    const decl = self.declOf(fid, tok.name) orelse return null;
    return .{ .decl = decl, .file = target_file };
}

/// A mapping token as the writer spelled it (`ns.name` or `name`).
fn tokText(self: *Context, tok: Token) std.mem.Allocator.Error![]const u8 {
    const name = self.interner.stringBytes(tok.name);
    if (tok.qualifier == InternPool.Index.none) return name;
    return std.fmt.allocPrint(self.arena, "{s}.{s}", .{ self.interner.stringBytes(tok.qualifier), name });
}

/// A diagnostic at a token of the model's OWN declaration (not the citing site).
fn diagAt(self: *Context, task: ModelTask, loc: u32, comptime fmt: []const u8, args: anytype) std.mem.Allocator.Error!void {
    self.sink.add(self.diagFile(task.file), loc, fmt, args) catch return error.OutOfMemory;
}

/// Which demand table a mapping token resolves against.
const Table = enum { ident, fact };

/// The `Mapping` inside an `IdentMapping`, regardless of variant.
fn identMapping(im: ast.IdentMapping) ast.Mapping {
    return switch (im) {
        .basic => |b| b,
        .refined_sort => |r| r.mapping,
        .closed_operation => |c| c.mapping,
    };
}

/// Validate + resolve a `:` symbol map's guard-discharger witness clause. Returns `true` if a
/// diagnostic was recorded (the caller aborts). The KIND rule: the PARENS form `tgt(f…)` is
/// legal ONLY for a CONST target whose sort is refined; the `-|` form `tgt -| f` ONLY for a
/// FUNC target whose result is refined. Wrong pairing = a hard error. Each resolved discharger
/// fact is appended to `dischargers` as `(tgt-symbol, fact)` (only once fully resolved; a
/// not-yet-resolved fact racks a blocker and is picked up on the resume re-run, which rebuilds
/// the list from scratch — no cross-resume duplication).
fn checkWitnesses(self: *Context, h: *Engine.Handle, task: ModelTask, source: []const u8, im: ast.IdentMapping, tgt: InternPool.Index, dischargers: *std.ArrayList(InternPool.Key.Mapping), blocker: *?Engine.TaskIndex) std.mem.Allocator.Error!bool {
    const tgt_key = self.interner.keyOf(tgt);
    switch (im) {
        .basic => return false, // no witness clause
        .refined_sort => |r| {
            // PARENS: base facts for a CONST witness. The refinement is contributed by the MODEL
            // (the const's SOURCE sort maps to a refined target); the const's OWN declared sort is
            // typically the unrefined carrier — so we only check it is a const, not that its sort
            // is refined. Whether the facts are NEEDED is decided at discharge time.
            if (tgt_key != .constant) {
                try demandDiag(self, task, "the `(…)` guard-witness form is only valid mapping to a CONST; '{s}' is not a constant", .{self.interner.stringBytes(self.interner.nameOf(tgt))});
                return true;
            }
            for (r.dischargers) |d| {
                if (try resolveEntity(self, h, task.file, source, d, .fact, blocker)) |fact| {
                    try dischargers.append(self.arena, .{ .src = tgt, .tgt = fact });
                    try self.recordModelDischarged(fact);
                }
            }
            return false;
        },
        .closed_operation => |c| {
            // `-|`: a closure fact for a FUNC witness. (As above, refinement is model-contributed,
            // so only the func-kind is checked here.)
            if (tgt_key != .func) {
                try demandDiag(self, task, "the `-|` closure-witness form is only valid mapping to a FUNC; '{s}' is not a function", .{self.interner.stringBytes(self.interner.nameOf(tgt))});
                return true;
            }
            for (c.closure_facts) |cf| {
                if (try resolveEntity(self, h, task.file, source, cf, .fact, blocker)) |fact| {
                    try dischargers.append(self.arena, .{ .src = tgt, .tgt = fact });
                    try self.recordModelDischarged(fact);
                }
            }
            return false;
        },
    }
}

/// Resolve one mapping token to its entity Index. `.ident` → IdentKV (a FetchTask);
/// `.fact` → FactKV (a ProveTask). Handles a `cite.`-qualified SOURCE (import-walk),
/// or a bare LOCAL target. Returns the Index if `done`/`proven`; else racks the producer,
/// sets `blocker`, returns null (the caller suspends after the whole pass).
fn resolveEntity(self: *Context, h: *Engine.Handle, file: InternPool.Index, source: []const u8, tok: @import("../lexer.zig").Token, kind: Table, blocker: *?Engine.TaskIndex) std.mem.Allocator.Error!?InternPool.Index {
    _ = source;
    var target_file = file;
    var target_ns = try self.interner.namespace(.universe, file);
    if (tok.qualifier != InternPool.Index.none) {
        const st = self.idents.lookup(self.io, .{ .namespace = target_ns, .name = tok.qualifier }) orelse {
            blocker.* = try h.rackIndexed(try FetchTask.new(self.arena, .{ .file = file, .name = tok.qualifier, .loc = tok.start, .loc_file = file }));
            return null;
        };
        switch (st) {
            .in_flight => |owner| {
                if (owner != h.self_index) blocker.* = owner;
                return null;
            },
            .done => |ix| switch (self.interner.keyOf(ix)) {
                .import => |imp| {
                    target_ns = imp.namespace;
                    target_file = self.interner.keyOf(imp.namespace).namespace.file;
                },
                else => return null, // not a namespace — leave unresolved (diagnosed elsewhere)
            },
        }
    }
    const name = tok.name;
    switch (kind) {
        .ident => {
            const st = self.idents.lookup(self.io, .{ .namespace = target_ns, .name = name }) orelse {
                blocker.* = try h.rackIndexed(try FetchTask.new(self.arena, .{ .file = target_file, .name = name, .loc = tok.start, .loc_file = file }));
                return null;
            };
            return switch (st) {
                .done => |ix| ix,
                .in_flight => |owner| blk: {
                    if (owner != h.self_index) blocker.* = owner;
                    break :blk null;
                },
            };
        },
        .fact => {
            const st = self.facts.lookup(self.io, .{ .namespace = target_ns, .name = name }) orelse {
                blocker.* = try h.rackIndexed(try ProveTask.new(self.arena, .{ .file = target_file, .name = name, .loc = tok.start, .loc_file = file }));
                return null;
            };
            return switch (st) {
                .proven => |ix| ix,
                .in_flight => |owner| blk: {
                    if (owner != h.self_index) blocker.* = owner;
                    break :blk null;
                },
            };
        },
    }
}

/// Resolve a `<- NamedModel@proj` projected obligation to its discharging fact Index: the
/// theorem `proj` TRANSFERRED through the model `mtok` names. Resolves `mtok` (must be a
/// `.model`), finds `proj`'s source file (its qualifier's import, or this file if unqualified),
/// and demands the transferred fact `proj.name` in namespace `(model, proj_file)` — racking a
/// transferred ProveTask (`.model = model`) on a miss, exactly as an inline `[using model] cite`
/// does. Returns the fact Index if proven, else sets `blocker` and returns null.
fn resolveProjection(self: *Context, h: *Engine.Handle, file: InternPool.Index, source: []const u8, mtok: @import("../lexer.zig").Token, proj: @import("../lexer.zig").Token, blocker: *?Engine.TaskIndex) std.mem.Allocator.Error!?InternPool.Index {
    _ = source;
    // the model the projection routes through. A model name lives in IdentKV but is PRODUCED by
    // a ModelTask (not a FetchTask), so demand it that way — rack a ModelTask on a miss.
    const self_ns = try self.interner.namespace(.universe, file);
    const mstate = self.idents.lookup(self.io, .{ .namespace = self_ns, .name = mtok.name }) orelse {
        blocker.* = try h.rackIndexed(try ModelTask.new(self.arena, .{ .file = file, .name = mtok.name, .loc = mtok.start, .loc_file = file }));
        return null;
    };
    const model_ix = switch (mstate) {
        .done => |ix| ix,
        .in_flight => |owner| {
            if (owner != h.self_index) blocker.* = owner;
            return null;
        },
    };
    if (self.interner.keyOf(model_ix) != .model) return null; // diagnosed by the transferred fact's absence

    // the projected theorem's file: its qualifier's import (or this file if unqualified).
    var proj_file = file;
    if (proj.qualifier != InternPool.Index.none) {
        const st = self.idents.lookup(self.io, .{ .namespace = self_ns, .name = proj.qualifier }) orelse {
            blocker.* = try h.rackIndexed(try FetchTask.new(self.arena, .{ .file = file, .name = proj.qualifier, .loc = proj.start, .loc_file = file }));
            return null;
        };
        switch (st) {
            .in_flight => |owner| {
                if (owner != h.self_index) blocker.* = owner;
                return null;
            },
            .done => |ix| switch (self.interner.keyOf(ix)) {
                .import => |imp| proj_file = self.interner.keyOf(imp.namespace).namespace.file,
                else => return null,
            },
        }
    }

    // demand the TRANSFERRED fact `(model, proj_file).name`.
    const tns = try self.interner.namespace(model_ix, proj_file);
    if (self.facts.lookup(self.io, .{ .namespace = tns, .name = proj.name })) |st| switch (st) {
        .proven => |ix| return ix,
        .in_flight => |owner| {
            if (owner != h.self_index) blocker.* = owner;
            return null;
        },
    };
    blocker.* = try h.rackIndexed(try ProveTask.new(self.arena, .{ .file = proj_file, .name = proj.name, .loc = proj.start, .loc_file = file, .model = model_ix }));
    return null;
}

fn demandDiag(self: *Context, task: ModelTask, comptime fmt: []const u8, args: anytype) std.mem.Allocator.Error!void {
    const loc_file = task.loc_file orelse task.file;
    const fid = self.fileOf(loc_file) orelse return; // undiscovered: nowhere to anchor
    self.sink.add(@intFromEnum(fid), task.loc, fmt, args) catch return error.OutOfMemory;
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");

fn readNothing(_: ?*anyopaque, _: std.mem.Allocator, _: []const u8) anyerror![]const u8 {
    return error.FileNotFound;
}

fn fixtureCtx(arena: std.mem.Allocator, io: std.Io, path: []const u8, src: []const u8) !*Context {
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
    const fid = try ctx.preload(path, src);
    var p: parser.Parser = .initInterning(arena, src, sink, interner);
    ctx.parsed.set(@intFromEnum(fid), try p.parseFile());
    for (ctx.parsed.get(@intFromEnum(fid)).decls) |*decl| _ = try ctx.registerDecl(fid, decl);
    ctx.parse_state.set(@intFromEnum(fid), .parsed);
    try testing.expectEqual(@as(usize, 0), sink.list.items.len);
    return ctx;
}

test "model: overlay populated from same-file symbol + obligation mappings; deduped publish" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    // a self-contained model: a `.symbol` map (func srcF -> tgtF) and an `.obligation`
    // (axiom srcAx <- tgtAx). All same-file so no import qualifier is needed.
    const ctx = try fixtureCtx(arena, io, "/t/m.bpa",
        \\sort T
        \\func srcF(a: T): T
        \\func tgtF(a: T): T
        \\axiom srcAx: forall a: T; srcF(a) = a
        \\axiom tgtAx: forall a: T; tgtF(a) = a
        \\model M {
        \\  srcF: tgtF
        \\  srcAx <- tgtAx
        \\  }
    );
    const f = try ctx.fileIndex("/t/m.bpa");
    const mname = try ctx.interner.internString("M");

    var eng = Engine.init(arena, ctx, ctx.io);
    defer eng.deinit();
    _ = try eng.rack(try new(arena, .{ .file = f, .name = mname, .loc = 0 }));
    try eng.run();
    try testing.expectEqual(eng.racked, eng.completed); // quiescent, no wedge
    try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);

    const ns = try ctx.interner.namespace(.universe, f);
    const outcome = try ctx.idents.claimOrLookup(io, .{ .namespace = ns, .name = mname }, @enumFromInt(99));
    try testing.expect(outcome == .done);
    const model = ctx.interner.keyOf(outcome.done);
    try testing.expect(model == .model);
    try testing.expectEqual(InternPool.Index.universe, model.model.parent);
    try testing.expectEqual(@as(usize, 2), model.model.overlay.len);

    // resolve the four entities independently to check the overlay maps src->tgt correctly.
    const srcF = (ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("srcF") }).?).done;
    const tgtF = (ctx.idents.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("tgtF") }).?).done;
    const srcAx = (ctx.facts.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("srcAx") }).?).proven;
    const tgtAx = (ctx.facts.lookup(io, .{ .namespace = ns, .name = try ctx.interner.internString("tgtAx") }).?).proven;

    var saw_sym = false;
    var saw_obl = false;
    for (model.model.overlay) |e| {
        if (e.src == srcF) {
            try testing.expectEqual(tgtF, e.tgt);
            saw_sym = true;
        } else if (e.src == srcAx) {
            try testing.expectEqual(tgtAx, e.tgt);
            saw_obl = true;
        }
    }
    try testing.expect(saw_sym and saw_obl);
}
