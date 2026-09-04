//! SchemaCheckTask — STRICT well-formedness for a proof-carrying schema (Step 12h).
//!
//! A schema's proof body is checked at DECLARATION by instantiating it at OPAQUE arguments
//! (one fresh uninterpreted entity per param), so a structurally-broken or over-general
//! body is rejected at its own line even if nothing instantiates it (the historical
//! soundness footgun — see memory `schema-wellformedness-check`). Racked by the root
//! ParseTask per proof-carrying schema in the root file when `verify.recheck_schemas`.
//!
//! MECHANISM (reuse, not reinvent): opaque args ARE a `Schema.SchemaArgs` — a value param
//! → a fresh FVAR of the param sort (an fvar is an opaque term); an N-ary generator param
//! → `fun x.. => opaqueSym(x..)` over a freshly-MINTED pred/func + fresh fvars. Those args
//! are reified durably and handed to an ordinary INSTANCE ProveTask (the same machinery
//! `instantiate` uses), racked under a private `<schema>{opaque}` name; this task SUSPENDS
//! on it. If that instance proof checks, the schema is well-formed; if it fails, the
//! instance ProveTask already recorded the diagnostic. This task publishes NOTHING.

const std = @import("std");
const ast = @import("../ast.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const SortId = term.SortId;
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const ProveTask = @import("ProveTask.zig");
const Schema = @import("ProveTask/Schema.zig");
const Elab = @import("ProveTask/Elab.zig");

const SchemaCheckTask = @This();

/// the `.file` Index the schema is declared in, and its name (for dedup + diagnostics).
file: InternPool.Index,
name: StrId,
loc: u32,
/// set once we've racked the opaque instance and are waiting on it.
racked: bool = false,

pub fn new(arena: std.mem.Allocator, payload: SchemaCheckTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(SchemaCheckTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *SchemaCheckTask = @ptrCast(@alignCast(payload));
    return run(self, task, h);
}

pub fn run(self: *Context, task: *SchemaCheckTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    if (self.pool_file.get(task.file)) |fid| self.sink.current_file = @intFromEnum(fid);
    if (self.schema_checked.contains(task.name)) return; // already checked (dedup)

    if (task.racked) {
        // resumed after the opaque instance ran — well-formed iff it published. Either way
        // this check is done (a failure already recorded its own diagnostic).
        try self.schema_checked.put(self.arena, task.name, {});
        return;
    }

    // find the schema's decl in its (root) file's AST directly — the root scan racked us
    // for a decl it just saw, and the file is parsed. (No IdentKV round-trip needed: the
    // instance ProveTask we rack carries the decl_index in its payload.)
    const ns = try self.interner.namespace(.universe, task.file);
    const fid = self.pool_file.get(task.file).?;
    const source = self.files.items[@intFromEnum(fid)].source;
    const decls = self.parsed.items[@intFromEnum(fid)].decls;
    var decl_index: u32 = 0;
    const decl: ast.Decl = for (decls, 0..) |d, i| {
        if (d != .schema) continue;
        if (d.schema.name.name == task.name) { // stamped at parse — integer compare
            decl_index = @intCast(i);
            break d;
        }
    } else return; // no such schema (shouldn't happen)
    if (decl.schema.steps == null) return; // not proof-carrying — nothing to check

    // build OPAQUE args in a throwaway scratchpad, reify them durably for the instance task.
    var pool = term.Pool.init(self.arena);
    var counter: u32 = 0;
    const pnames = try self.arena.alloc(StrId, decl.schema.params.len);
    const durable = try self.arena.alloc(ProveTask.DurableArg, decl.schema.params.len);
    for (decl.schema.params, pnames, durable) |p, *pn, *dout| {
        pn.* = p.name.name; // stamped at parse
        const brand = try std.fmt.allocPrint(self.arena, "opaque-schema-param#{s}", .{source[p.name.start..p.name.end]});
        if (p.arg_sorts.len == 0) {
            // a VALUE param: a fresh fvar of the param's result sort (opaque term).
            const sort = try resolveSort(self, ns, source, p.result);
            const fv = try pool.add(.{ .fvar = .{ .name = try fresh(self, brand, &counter), .sort = sort } });
            dout.* = .{ .value = .{ .off = try pool.reify(fv, self.interner), .sort = sort } };
        } else {
            // an N-ary GENERATOR param: `fun x.. => opaqueSym(x..)`; mint the opaque sym.
            const arg_sorts = try self.arena.alloc(SortId, p.arg_sorts.len);
            for (p.arg_sorts, arg_sorts) |stok, *so| so.* = try resolveSort(self, ns, source, stok);
            const result_sort = try resolveSort(self, ns, source, p.result);
            const sym = try mintOpaqueSym(self, brand, arg_sorts, result_sort);
            const params = try self.arena.alloc(StrId, arg_sorts.len);
            const fvars = try self.arena.alloc(term.TermId, arg_sorts.len);
            for (arg_sorts, params, fvars) |so, *pm, *fv| {
                pm.* = try fresh(self, "eta", &counter);
                fv.* = try pool.add(.{ .fvar = .{ .name = pm.*, .sort = so } });
            }
            const kind: term.AppKind = if (result_sort == Elab.prop_sort) .pred else .app;
            const body = try pool.addApp(kind, @enumFromInt(@intFromEnum(sym)), fvars);
            dout.* = .{ .lambda = .{ .off = try pool.reify(body, self.interner), .params = params, .arg_sorts = arg_sorts, .result_sort = result_sort } };
        }
    }

    // rack the opaque INSTANCE (a normal instance ProveTask) under a private name; suspend.
    const inst_name_bytes = try std.fmt.allocPrint(self.arena, "{s}{{opaque}}", .{self.interner.stringBytes(task.name)});
    const inst_name = try self.interner.internString(inst_name_bytes);
    const t = try h.rackIndexed(try ProveTask.new(self.arena, .{
        .file = task.file,
        .name = inst_name,
        .loc = task.loc,
        .loc_file = task.file,
        .instance = .{ .decl_index = decl_index, .params = pnames, .args = durable },
    }));
    task.racked = true;
    h.suspendOn(t);
}

/// Resolve a param sort token in the schema's namespace (handles the reserved `Prop`).
fn resolveSort(self: *Context, ns: InternPool.Index, source: []const u8, tok: anytype) std.mem.Allocator.Error!SortId {
    _ = source;
    if (tok.name == InternPool.Index.prop_name) return Elab.prop_sort;
    if (self.idents.lookup(self.io, .{ .namespace = ns, .name = tok.name })) |state| switch (state) {
        .done => |ix| return @enumFromInt(@intFromEnum(ix)),
        .in_flight => {},
    };
    // a param sort that isn't fetched yet: fall back to Prop (the opaque check will still
    // exercise structure; a genuinely unknown sort surfaces at real instantiation). Rare.
    return Elab.prop_sort;
}

fn fresh(self: *Context, brand: []const u8, counter: *u32) std.mem.Allocator.Error!StrId {
    counter.* += 1;
    const s = try std.fmt.allocPrint(self.arena, "{s}#{d}", .{ brand, counter.* });
    return self.interner.internString(s);
}

/// Mint a fresh opaque func/pred Item (an uninterpreted symbol of the given signature).
fn mintOpaqueSym(self: *Context, brand: []const u8, arg_sorts: []const SortId, result_sort: SortId) std.mem.Allocator.Error!InternPool.Index {
    const args = try self.arena.alloc(InternPool.Index, arg_sorts.len);
    for (arg_sorts, args) |so, *a| a.* = @enumFromInt(@intFromEnum(so));
    const result: InternPool.Index = @enumFromInt(@intFromEnum(result_sort));
    self.interner.lockWrite(self.io);
    defer self.interner.unlockWrite(self.io);
    const sig = try self.interner.get(.{ .sig = .{ .result = result, .result_refined = .none, .args = args } });
    const name = try self.interner.internString(brand);
    const c = InternPool.Key.Callable{ .sig = sig, .guard = InternPool.no_term, .param_names = &.{}, .name = name, .loc = 0 };
    return if (result_sort == Elab.prop_sort) self.interner.mintPred(c) else self.interner.mintFunc(c);
}
