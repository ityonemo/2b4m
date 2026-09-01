//! The checker's shared world — the CONTEXT everything operates against: the interner,
//! term pool, environment, diagnostics sink, verify config, and the per-file tables
//! (files/parsed/import_maps) keyed by FileId. It is threaded to every engine task (the
//! engine's `ctx`). LOADING is a thing you DO with a context (`loadProject`), not a
//! separate abstraction — hence Context, not "Loader".
//!
//! `loadProject` runs two engine-driven phases (see Engine.zig): PHASE A parses the whole
//! transitive file set on the task engine (filling the FileId-indexed tables); PHASE B
//! elaborates every file in dependency order with the (unchanged) eager back-end.
//!
//! This FILE IS the context struct (capitalized-file = top-level-struct convention):
//! `const Context = @import("Context.zig")` yields the type directly.
//!
//! File identity is context-global and IS the namespace's file component: the InternPool
//! does the file DEDUP (intern the resolved path -> a `.file` entity Index; the same path
//! collapses to the same Index), and `pool_file` maps that Index -> the dense `FileId`
//! that cursors the per-file tables. `discover` mints a FileId only on a pool-file MISS.

const std = @import("std");
const ast = @import("ast.zig");
const diagnostics = @import("diagnostics.zig");
const InternPool = @import("InternPool.zig");
const term = @import("term.zig");
const env = @import("env.zig");
const elaborate = @import("elaborate.zig");
const Engine = @import("Engine.zig");
const FactKV = @import("FactKV.zig");
const IdentKV = @import("IdentKV.zig");

const Context = @This();

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8;

/// raw-import-path StrId -> resolved child FileId, for one file.
const ImportMap = std.AutoHashMapUnmanaged(InternPool.StrId, env.FileId);

arena: std.mem.Allocator,
/// The Io handle (from Zig 0.16 "juicy main" `init.io`), threaded through the entry
/// points. Writers use it to take the InternPool write-mutex / FactKV RwLock. Reads are
/// lock-free and never need it. Single-threaded today, so locks are uncontended.
io: std.Io,
sink: *diagnostics.Sink,
interner: *InternPool,
/// The fact resolution/coordination table over `interner` (see FactKV). Populated by the
/// prove scan (a fact per theorem) and, later, by citation resolution.
facts: FactKV,
/// The identifier resolution/coordination table over `interner` (see IdentKV). Filled by
/// FetchTask. Sibling of `facts`; not wired into resolution yet.
idents: IdentKV,
pool: *term.Pool,
environment: *env.Env,
files: std.ArrayList(diagnostics.FileSrc) = .empty,
/// resolved path -> FileId. A file gets its FileId when first DISCOVERED (racked),
/// before it is parsed — so a second reference resolves to the same id (and cyclic
/// file imports are naturally fine: the id exists before parsing completes).
/// pool `.file` entity Index -> the dense FileId cursoring the per-file tables. The
/// InternPool does the path dedup (same resolved path -> same file Index); this maps that
/// interned identity onto the FileId used to index files/parsed/import_maps/scopes. A
/// second reference to a file resolves through the pool to the same Index -> same FileId
/// (so cyclic file imports are naturally fine: the id exists before parsing completes).
pool_file: std.AutoHashMapUnmanaged(InternPool.Index, env.FileId) = .empty,
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

/// Intern a resolved path to its `.file` entity Index — the context-global file
/// identity. The InternPool dedups: the same path always yields the same Index.
pub fn fileIndex(self: *Context, resolved_path: []const u8) !InternPool.Index {
    const path_id = try self.interner.internString(resolved_path);
    return self.interner.get(.{ .file = .{ .path = path_id } });
}

/// The FileId already assigned to a resolved path, or null if not yet discovered. Reads
/// through the pool (interns the path -> file Index -> the pool_file map).
pub fn lookupFile(self: *Context, resolved_path: []const u8) !?env.FileId {
    return self.pool_file.get(try self.fileIndex(resolved_path));
}

/// Register a newly-discovered file: intern its path (the file entity), assign a FileId,
/// reserve its table slots. IDEMPOTENT — a repeat path returns the existing FileId
/// (the pool dedups the path to one file Index, and pool_file maps it to one FileId).
/// FileId order == `files`/`parsed`/`import_maps` index order (the newFile assert).
/// Pub: the parse task (Engine/ParseTask.zig) discovers a file's imports.
pub fn discover(self: *Context, resolved_path: []const u8, source: []const u8) !env.FileId {
    const file_index = try self.fileIndex(resolved_path);
    if (self.pool_file.get(file_index)) |existing| return existing;

    const file_id = try self.environment.newFile();
    std.debug.assert(@intFromEnum(file_id) == self.files.items.len);
    try self.files.append(self.arena, .{ .path = resolved_path, .source = source });
    try self.parsed.append(self.arena, .{ .decls = &.{} });
    try self.import_maps.append(self.arena, .{});
    try self.pool_file.put(self.arena, file_index, file_id);
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
fn elaborateAll(self: *Context) !void {
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

fn emitPostOrder(self: *Context, fid: env.FileId, visited: []bool, order: *std.ArrayList(env.FileId)) !void {
    const idx = @intFromEnum(fid);
    if (visited[idx]) return;
    visited[idx] = true; // mark BEFORE recursing so a cycle doesn't loop forever
    var it = self.import_maps.items[idx].valueIterator();
    while (it.next()) |child| try self.emitPostOrder(child.*, visited, order);
    try order.append(self.arena, fid);
}

/// The two-phase entry: discover + parse the whole transitive file set via the
/// engine, then elaborate every file in dependency order. (Loading is a thing you DO
/// with a context.)
pub fn loadProject(self: *Context, root_path: []const u8, root_source: []const u8) !env.FileId {
    self.root_file = try self.discover(root_path, root_source);
    var eng = Engine.init(self.arena, self);
    _ = try eng.rack(try Engine.ParseTask.new(self.arena, .{ .file_id = self.root_file, .source = root_source, .path = root_path }));
    try eng.run(); // parse phase to quiescence
    try self.elaborateAll(); // elaborate phase in dependency order
    return self.root_file;
}
