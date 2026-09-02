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
//! (the target file was resolved at parse time via the import map). Later layers add
//! funcs/preds/consts/defines (need expression elaboration for guards, W4.5) and aliases
//! (incl. predicated sorts). A decl kind not yet supported diagnoses "not yet supported".
//!
//! FAILURE ("reference not found" — the UndefinedError terminal): if no declaration
//! produces the name, a diagnostic is recorded and the task completes WITHOUT publishing.
//! The IdentKV entry stays in_flight-ours, so other demanders of the same name stay
//! parked (a wedge — the engine still terminates; wedge REPORTING is deferred, and the
//! demanding proof correctly never completes).

const std = @import("std");
const ast = @import("../ast.zig");
const InternPool = @import("../InternPool.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");
const IdentKV = @import("../IdentKV.zig");

const FetchTask = @This();

/// the pool `.file` Index of the file in whose NAMESPACE the identifier is declared
/// (the demander resolves qualifiers first, so this is always the declaring file).
file: InternPool.Index,
name: InternPool.StrId,
/// the demanding reference's source offset — where "reference not found" points.
loc: u32,

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
    try produce(self, task, h, key);
}

/// Find the declaration and assemble/publish the identifier. Layer 1: root sorts +
/// imports (neither references other identifiers, so production never suspends yet;
/// the read-pass-then-produce suspension pattern arrives with funcs/preds in W4.5).
fn produce(self: *Context, task: FetchTask, h: *Engine.Handle, key: IdentKV.Key) std.mem.Allocator.Error!void {
    _ = h; // layer 1 production has no sub-fetches to suspend on yet
    const fid = self.pool_file.get(task.file) orelse {
        // the namespace's file was never discovered — an internal wiring error
        self.sink.add(task.loc, "internal: fetch into an undiscovered file", .{}) catch return error.OutOfMemory;
        return;
    };
    const parsed = self.parsed.items[@intFromEnum(fid)];
    const source = self.files.items[@intFromEnum(fid)].source;

    for (parsed.decls) |*decl| {
        const name_tok = switch (decl.*) {
            .sort => |d| d.name,
            .import => |d| d.ns,
            .constant => |d| d.name,
            .func => |d| d.name,
            .pred => |d| d.name,
            .define => |d| d.name,
            .alias => |d| d.name,
            .axiom => |d| d.name,
            .hole => |d| d.name,
            .schema => |d| d.name,
            .theorem => |d| d.name,
            .forward, .model => continue, // a promise / a model decl — not identifiers
        };
        const decl_name = self.interner.internString(source[name_tok.start..name_tok.end]) catch return error.OutOfMemory;
        if (decl_name != task.name) continue;

        switch (decl.*) {
            .sort => {
                // a plain `sort X` declaration is always a ROOT sort (predicated sorts
                // arrive as aliases with a guard — a later layer).
                _ = try self.idents.publish(self.io, key, .{ .sort = .{
                    .name = task.name,
                    .loc = name_tok.start,
                    .refinement = null,
                } });
                return;
            },
            .import => |d| {
                // the parse phase resolved the raw path -> child FileId; map it to the
                // child's pool `.file` Index and bind the import to its namespace.
                const raw_quoted = source[d.path.start..d.path.end];
                const raw = self.interner.internString(raw_quoted[1 .. raw_quoted.len - 1]) catch return error.OutOfMemory;
                const target_fid = self.import_maps.items[@intFromEnum(fid)].get(raw) orelse {
                    self.sink.add(d.path.start, "import '{s}' was not resolved at parse time", .{raw_quoted}) catch return error.OutOfMemory;
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
            .axiom, .hole, .schema, .theorem => {
                self.sink.add(task.loc, "'{s}' names a fact, not a sort/constant/function/predicate", .{self.interner.stringBytes(task.name)}) catch return error.OutOfMemory;
                return; // no publish
            },
            else => {
                // constant/func/pred/define/alias: need expression elaboration /
                // reference resolution — the next fetch layer (W4.5).
                self.sink.add(task.loc, "identifier kind of '{s}' is not yet supported by the demand prover", .{self.interner.stringBytes(task.name)}) catch return error.OutOfMemory;
                return; // no publish
            },
        }
    }
    // the UndefinedError terminal: nothing in the file declares this name.
    self.sink.add(task.loc, "reference not found: '{s}'", .{self.interner.stringBytes(task.name)}) catch return error.OutOfMemory;
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../parser.zig");
const term = @import("../term.zig");
const env_mod = @import("../env.zig");
const diagnostics = @import("../diagnostics.zig");
const FactKV = @import("../FactKV.zig");

/// A read_fn stub for single-file tests (no imports followed) — never called.
fn readNothing(_: ?*anyopaque, _: std.mem.Allocator, _: []const u8) anyerror![]const u8 {
    return error.FileNotFound;
}

/// Build a REAL Context around one discovered + parsed fixture file.
fn fixtureCtx(arena: std.mem.Allocator, io: std.Io, path: []const u8, source: []const u8) !*Context {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const environment = try arena.create(env_mod.Env);
    environment.* = try .init(arena, interner);

    const ctx = try arena.create(Context);
    ctx.* = .{
        .arena = arena,
        .io = io,
        .sink = sink,
        .interner = interner,
        .facts = FactKV.init(interner),
        .idents = IdentKV.init(interner),
        .pool = pool,
        .environment = environment,
        .read_ctx = null,
        .read_fn = &readNothing,
        .verify = .{},
        .std_root = "",
    };
    const fid = try ctx.discover(path, source);
    var p: parser.Parser = .init(arena, source, sink);
    ctx.parsed.items[@intFromEnum(fid)] = try p.parseFile();
    try testing.expectEqual(@as(usize, 0), sink.list.items.len);
    return ctx;
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
    const child_fid = try ctx.discover("/t/child.bpa", "sort Nat");
    {
        var p: parser.Parser = .init(arena, "sort Nat", ctx.sink);
        ctx.parsed.items[@intFromEnum(child_fid)] = try p.parseFile();
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
