//! The parse task: payload + behavior. `src/Engine/` is where all engine task payloads
//! live (ParseTask now; ProveTask and friends alongside it later).
//!
//! This FILE IS the payload struct (capitalized-file = top-level-struct convention):
//! `const ParseTask = @import("Engine/ParseTask.zig")` yields the type directly. It is
//! self-contained: `new()` packages a payload into a rack-ready `Engine.Task` (bundling
//! the run-fn), and `run` IS that run-fn — the parse-task body.
//!
//! FileId + source are assigned/read at discovery time (so a child's id exists before
//! its parse runs — cyclic-import safe); parse is the ONE task type that never suspends.

const std = @import("std");
const env = @import("../env.zig");
const parser = @import("../parser.zig");
const Engine = @import("../Engine.zig");
const Context = @import("../Context.zig");

const ParseTask = @This();

file_id: env.FileId,
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

/// The parse-task body: parse the file, resolve its imports (discovering + racking
/// child parse tasks), and record its import map. TRANSITIONAL: parse follows imports
/// here only because the eager elaborator back-end (Context phase B) needs the whole
/// transitive file set present. In the target demand-driven design, the PROVER pulls a
/// file in when it cites into it; this import-following goes away then.
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

        const child: env.FileId = if (try self.lookupFile(resolved)) |existing|
            existing // already discovered (incl. a cyclic re-reference) — reuse id
        else child: {
            const src = self.read_fn(self.read_ctx, self.arena, resolved) catch {
                self.sink.current_file = idx;
                try self.sink.add(d.path.start, "cannot open '{s}': file not found", .{resolved});
                continue;
            };
            const cid = try self.discover(resolved, src);
            try h.rack(try new(self.arena, .{ .file_id = cid, .source = src, .path = resolved }));
            break :child cid;
        };
        const raw_id = try self.interner.internString(raw);
        try self.import_maps.items[idx].put(self.arena, raw_id, child);
    }

    // SCAN (tail of parse): the requested (root) file's theorems are the roots of demand.
    // Rack a ProveTask per theorem. Whole-file request => all theorems (the only filter
    // today). Only the root file is scanned — imported files' theorems are demanded by
    // citations later, not proved just for being imported. ProveTask is a NO-OP for now,
    // so this is behavior-neutral wiring: it proves scan -> rack -> prove runs to
    // quiescence alongside the still-authoritative eager back-end.
    if (task.file_id == self.root_file) {
        const file_index = try self.fileIndex(task.path); // the pool .file identity
        for (parsed.decls) |decl| {
            if (decl != .theorem) continue;
            const name = decl.theorem.name;
            const name_id = try self.interner.internString(task.source[name.start..name.end]);
            try h.rack(try Engine.ProveTask.new(self.arena, .{ .file = file_index, .name = name_id }));
        }
    }
}
