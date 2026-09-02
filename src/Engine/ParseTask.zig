//! The parse task: payload + behavior. `src/Engine/` is where all engine task payloads
//! live (ParseTask now; ProveTask and friends alongside it later).
//!
//! This FILE IS the payload struct (capitalized-file = top-level-struct convention):
//! `const ParseTask = @import("Engine/ParseTask.zig")` yields the type directly. It is
//! self-contained: `new()` packages a payload into a rack-ready `Engine.Task` (bundling
//! the run-fn), and `run` IS that run-fn — the parse-task body.
//!
//! FileId + source are assigned/read at DISCOVERY time (so a child's id exists before its
//! parse runs — cyclic-import safe); parse is the ONE task type that never suspends.
//!
//! LAZY PARSING (Step 11): a ParseTask parses ONE file. It discovers + resolves that
//! file's imports (populating `import_maps` so a qualified `ns.name` can find the child's
//! FileId) but does NOT rack the children's ParseTasks — a child is parsed only when a
//! Fetch/Prove task first cites into it (via `Context.demandParse`, which racks the
//! ParseTask and suspends on it). At completion this task marks its file `parsed`
//! (waking anyone suspended on it). The ROOT ParseTask additionally scans its theorems
//! and racks the ProveTasks that seed demand.

const std = @import("std");
const parser = @import("../parser.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");

const ParseTask = @This();

file_id: Context.FileId,
source: []const u8,
path: []const u8,

/// Package a payload into a rack-ready `Engine.Task`. Arena-allocates the payload (so it
/// outlives the queue slot behind the engine's type-erased `*anyopaque`) and bundles the
/// typed `runErased`. Call sites just `try h.rack(ParseTask.new(arena, .{…}))`.
pub fn new(arena: std.mem.Allocator, payload: ParseTask) std.mem.Allocator.Error!Engine.Task {
    const p = try arena.create(ParseTask);
    p.* = payload;
    return .{ .payload = p, .run = &runErased };
}

/// The engine calls this with the type-erased payload; cast back and dispatch to `run`.
fn runErased(self: *Context, payload: *anyopaque, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const task: *ParseTask = @ptrCast(@alignCast(payload));
    return run(self, task.*, h);
}

/// The parse-task body: parse ONE file, resolve its imports (DISCOVER each child + record
/// the raw-path -> child-FileId map, so citations can find it — but do NOT rack the
/// child's ParseTask; that happens on demand when something cites into it). Mark the file
/// `parsed` at the end (the completion wakes anyone suspended in `demandParse`). If this
/// is the root file, scan its theorems and rack the seed ProveTasks.
pub fn run(self: *Context, task: ParseTask, h: *Engine.Handle) std.mem.Allocator.Error!void {
    const idx = @intFromEnum(task.file_id);
    self.sink.current_file = idx;
    var p: parser.Parser = .init(self.arena, task.source, self.sink);
    const parsed = try p.parseFile();
    self.parsed.items[idx] = parsed;
    self.declarations += parsed.decls.len;

    for (parsed.decls) |decl| {
        if (decl != .import) continue;
        const d = decl.import;
        const raw_quoted = task.source[d.path.start..d.path.end];
        const raw = raw_quoted[1 .. raw_quoted.len - 1];
        const resolved = if (std.mem.startsWith(u8, raw, "std/"))
            try std.fs.path.resolve(self.arena, &.{ self.std_root, raw["std/".len..] })
        else
            try std.fs.path.resolve(self.arena, &.{ std.fs.path.dirname(task.path) orelse ".", raw });

        const child: Context.FileId = if (try self.lookupFile(resolved)) |existing|
            existing // already discovered (incl. a cyclic re-reference) — reuse id
        else child: {
            // DISCOVER the child (read its source, reserve its FileId + table slots) so
            // the import resolves — but leave it `unparsed`; a citation triggers its
            // parse lazily. Import resolution only needs the child's identity, not its AST.
            const src = self.read_fn(self.read_ctx, self.arena, resolved) catch {
                self.sink.current_file = idx;
                try self.sink.add(d.path.start, "cannot open '{s}': file not found", .{resolved});
                continue;
            };
            break :child try self.discover(resolved, src);
        };
        const raw_id = try self.interner.internString(raw);
        try self.import_maps.items[idx].put(self.arena, raw_id, child);
    }

    // this file's AST is now populated — mark it parsed so `demandParse` waiters wake.
    self.parse_state.items[idx] = .parsed;

    // the ROOT file's theorems are the roots of demand: scan + rack a ProveTask each.
    // (Only the root — imported files' theorems are demanded by citations, not proved
    // just for being imported.)
    if (task.file_id == self.root_file) {
        const file_index = try self.fileIndex(task.path);
        for (parsed.decls) |decl| {
            if (decl != .theorem) continue;
            const name = decl.theorem.name;
            const name_id = try self.interner.internString(task.source[name.start..name.end]);
            try h.rack(try Engine.ProveTask.new(self.arena, .{ .file = file_index, .name = name_id }));
        }
    }
}
