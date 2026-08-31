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

/// Package this payload into a rack-ready `Engine.Task` — bundles it with the parse
/// run-fn so call sites just `try h.rack(ParseTask.new(...))` (or seed the same on the
/// engine) instead of hand-assembling `.{ .payload = …, .run = … }`.
pub fn new(payload: ParseTask) Engine.Task {
    return .{ .payload = payload, .run = &run };
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

        const child: env.FileId = if (self.by_path.get(resolved)) |existing|
            existing // already discovered (incl. a cyclic re-reference) — reuse id
        else child: {
            const src = self.read_fn(self.read_ctx, self.arena, resolved) catch {
                self.sink.current_file = idx;
                try self.sink.add(d.path.start, "cannot open '{s}': file not found", .{resolved});
                continue;
            };
            const cid = try self.discover(resolved, src);
            try h.rack(new(.{ .file_id = cid, .source = src, .path = resolved }));
            break :child cid;
        };
        const raw_id = try self.interner.internString(raw);
        try self.import_maps.items[idx].put(self.arena, raw_id, child);
    }
}
