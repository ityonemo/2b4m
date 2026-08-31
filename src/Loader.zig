//! The project loader: reads a root file and everything it transitively imports, then
//! elaborates them. Two engine-driven phases (see Engine.zig): PHASE A parses the whole
//! transitive file set on the task engine (filling the FileId-indexed tables); PHASE B
//! elaborates every file in dependency order with the (unchanged) eager back-end.
//!
//! This FILE IS the loader struct (capitalized-file = top-level-struct convention):
//! `const Loader = @import("Loader.zig")` yields the type directly. It owns the
//! parse-task body and the FileId-indexed results tables the engine populates — the
//! loader is the engine's sole caller today.

const std = @import("std");
const ast = @import("ast.zig");
const diagnostics = @import("diagnostics.zig");
const intern = @import("intern.zig");
const term = @import("term.zig");
const env = @import("env.zig");
const elaborate = @import("elaborate.zig");
const Engine = @import("Engine.zig");

const Loader = @This();

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8;

/// raw-import-path StrId -> resolved child FileId, for one file.
const ImportMap = std.AutoHashMapUnmanaged(intern.StrId, env.FileId);

arena: std.mem.Allocator,
sink: *diagnostics.Sink,
interner: *intern.Interner,
pool: *term.Pool,
environment: *env.Env,
files: std.ArrayList(diagnostics.FileSrc) = .empty,
/// resolved path -> FileId. A file gets its FileId when first DISCOVERED (racked),
/// before it is parsed — so a second reference resolves to the same id (and cyclic
/// file imports are naturally fine: the id exists before parsing completes).
by_path: std.StringHashMapUnmanaged(env.FileId) = .empty,
read_ctx: ?*anyopaque,
read_fn: ReadFileFn,
/// which verification layers are active (see elaborate.Verify). When
/// `recheck_imports` is false, imported files are TRUSTED: declarations
/// load, proofs are not re-checked.
verify: elaborate.Verify,
/// the standard library root: import paths beginning "std/" resolve here
/// (the prefix is reserved) instead of relative to the importing file
std_root: []const u8,
declarations: usize = 0,

/// FILL-ON-PARSE tables, indexed by FileId (grown in lockstep with `files`, so
/// `@intFromEnum(fid)` is the index). The engine's parse tasks populate these; the
/// second (elaborate) phase reads them. `import_maps[fid]` is that file's raw->child
/// import resolution; `parsed[fid]` its AST.
parsed: std.ArrayList(ast.File) = .empty,
import_maps: std.ArrayList(ImportMap) = .empty,
/// the root FileId (elaborated with is_root = true; not trusted).
root_file: env.FileId = undefined,

/// Register a newly-discovered file: assign its FileId, reserve its table slots.
/// FileId order == `files`/`parsed`/`import_maps` index order (the newFile assert).
/// Pub: the parse task (Engine/ParseTask.zig) discovers a file's imports.
pub fn discover(self: *Loader, resolved_path: []const u8, source: []const u8) !env.FileId {
    const file_id = try self.environment.newFile();
    std.debug.assert(@intFromEnum(file_id) == self.files.items.len);
    try self.files.append(self.arena, .{ .path = resolved_path, .source = source });
    try self.parsed.append(self.arena, .{ .decls = &.{} });
    try self.import_maps.append(self.arena, .{});
    try self.by_path.put(self.arena, resolved_path, file_id);
    return file_id;
}

// -- PHASE A lives in Engine/ParseTask.zig (the self-contained parse task) ----

// -- PHASE B: dependency-order elaborate --------------------------------------
// Any topological order of the import DAG works (a file's imports must be elaborated
// before it, so its qualified names resolve into populated scopes). We emit a
// post-order DFS over the import edges from the root — the same order the old
// depth-first loader produced. A cyclic file-import (allowed now) is simply visited
// in whatever order the DFS reaches it; the old cycle-error is dropped (the target
// design permits cyclic file imports — acyclicity is a PROOF-graph concern).
fn elaborateAll(self: *Loader) !void {
    const visited = try self.arena.alloc(bool, self.files.items.len);
    @memset(visited, false);
    var order: std.ArrayList(env.FileId) = .empty;
    try self.emitPostOrder(self.root_file, visited, &order);
    // any file the root doesn't transitively import (shouldn't happen — all files
    // are discovered via imports from the root) still gets elaborated, in id order.
    for (0..self.files.items.len) |i| {
        if (!visited[i]) try self.emitPostOrder(@enumFromInt(i), visited, &order);
    }
    for (order.items) |fid| {
        const idx = @intFromEnum(fid);
        self.sink.current_file = idx;
        var elab: elaborate.Elaborator = .init(self.arena, self.files.items[idx].source, self.interner, self.pool, self.environment, self.sink, fid);
        elab.imports = &self.import_maps.items[idx];
        elab.trusted = fid != self.root_file and !self.verify.recheck_imports;
        elab.verify = self.verify;
        try elab.elaborateFile(self.parsed.items[idx]);
    }
}

fn emitPostOrder(self: *Loader, fid: env.FileId, visited: []bool, order: *std.ArrayList(env.FileId)) !void {
    const idx = @intFromEnum(fid);
    if (visited[idx]) return;
    visited[idx] = true; // mark BEFORE recursing so a cycle doesn't loop forever
    var it = self.import_maps.items[idx].valueIterator();
    while (it.next()) |child| try self.emitPostOrder(child.*, visited, order);
    try order.append(self.arena, fid);
}

/// The two-phase entry: discover + parse the whole transitive file set via the
/// engine, then elaborate every file in dependency order.
pub fn run(self: *Loader, root_path: []const u8, root_source: []const u8) !env.FileId {
    self.root_file = try self.discover(root_path, root_source);
    var eng = Engine.init(self.arena, self);
    try eng.rack(Engine.ParseTask.new(.{ .file_id = self.root_file, .source = root_source, .path = root_path }));
    try eng.run(); // parse phase to quiescence
    try self.elaborateAll(); // elaborate phase in dependency order
    return self.root_file;
}
