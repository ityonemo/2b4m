//! The checker's shared world — the CONTEXT everything operates against: the interner,
//! the demand tables (FactKV/IdentKV), the shared term scratchpad, diagnostics sink,
//! verify config, and the per-file tables (files/parsed/import_maps) keyed by FileId. It
//! is threaded to every engine task (the engine's `ctx`). LOADING is a thing you DO with
//! a context (`loadProject`), not a separate abstraction — hence Context, not "Loader".
//!
//! `loadProject` racks the root ParseTask and runs the engine to quiescence: parsing
//! discovers + parses the transitive file set, the root scan racks a ProveTask per
//! requested theorem, and DEMAND does the rest (ProveTasks pull FetchTasks/ProveTasks
//! for what they cite; everything suspends/resumes on the KV protocols). There is no
//! eager elaborate phase — the demand pipeline IS the checker.
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
const Engine = @import("Engine.zig");
const FactKV = @import("FactKV.zig");
const IdentKV = @import("IdentKV.zig");
const Verify = @import("Verify.zig");

const Context = @This();

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8;

/// Dense per-context file id, cursoring the per-file tables (files/parsed/import_maps).
/// (Formerly env.FileId; env is gone — the dense id is a Context concern.)
pub const FileId = enum(u32) { _ };

/// raw-import-path StrId -> resolved child FileId, for one file.
const ImportMap = std.AutoHashMapUnmanaged(InternPool.StrId, FileId);

arena: std.mem.Allocator,
/// The Io handle (from Zig 0.16 "juicy main" `init.io`), threaded through the entry
/// points. Writers use it to take the InternPool write-mutex / KV RwLocks. Reads are
/// lock-free and never need it. Single-threaded today, so locks are uncontended.
io: std.Io,
sink: *diagnostics.Sink,
interner: *InternPool,
/// The fact resolution/coordination table over `interner` (see FactKV). Filled by
/// ProveTask (the scan's roots + every demanded citation).
facts: FactKV,
/// The identifier resolution/coordination table over `interner` (see IdentKV). Filled
/// by FetchTask on demand.
idents: IdentKV,
/// the SHARED term scratchpad (Step 10 makes this per-ProveTask; one pool for now)
pool: *term.Pool,
files: std.ArrayList(diagnostics.FileSrc) = .empty,
/// pool `.file` entity Index -> the dense FileId cursoring the per-file tables. The
/// InternPool does the path dedup (same resolved path -> same file Index); this maps that
/// interned identity onto the FileId used to index files/parsed/import_maps. A second
/// reference to a file resolves through the pool to the same Index -> same FileId (so
/// cyclic file imports are naturally fine: the id exists before parsing completes).
pool_file: std.AutoHashMapUnmanaged(InternPool.Index, FileId) = .empty,
read_ctx: ?*anyopaque,
read_fn: ReadFileFn,
/// which verification layers are active (see Verify).
verify: Verify,
/// the standard library root: import paths beginning "std/" resolve here
/// (the prefix is reserved) instead of relative to the importing file
std_root: []const u8,
declarations: usize = 0,

/// FILL-ON-PARSE tables, indexed by FileId (grown in lockstep with `files`, so
/// `@intFromEnum(fid)` is the index). The engine's parse tasks populate these; the
/// demand tasks read them. `import_maps[fid]` is that file's raw->child import
/// resolution; `parsed[fid]` its AST.
parsed: std.ArrayList(ast.File) = .empty,
import_maps: std.ArrayList(ImportMap) = .empty,
/// the root FileId (its theorems are the roots of demand).
root_file: FileId = undefined,

/// Intern a resolved path to its `.file` entity Index — the context-global file
/// identity. The InternPool dedups: the same path always yields the same Index.
pub fn fileIndex(self: *Context, resolved_path: []const u8) !InternPool.Index {
    const path_id = try self.interner.internString(resolved_path);
    return self.interner.get(.{ .file = .{ .path = path_id } });
}

/// The FileId already assigned to a resolved path, or null if not yet discovered. Reads
/// through the pool (interns the path -> file Index -> the pool_file map).
pub fn lookupFile(self: *Context, resolved_path: []const u8) !?FileId {
    return self.pool_file.get(try self.fileIndex(resolved_path));
}

/// Register a newly-discovered file: intern its path (the file entity), assign a FileId,
/// reserve its table slots. IDEMPOTENT — a repeat path returns the existing FileId
/// (the pool dedups the path to one file Index, and pool_file maps it to one FileId).
/// Pub: the parse task (Engine/ParseTask.zig) discovers a file's imports.
pub fn discover(self: *Context, resolved_path: []const u8, source: []const u8) !FileId {
    const file_index = try self.fileIndex(resolved_path);
    if (self.pool_file.get(file_index)) |existing| return existing;

    const file_id: FileId = @enumFromInt(self.files.items.len);
    try self.files.append(self.arena, .{ .path = resolved_path, .source = source });
    try self.parsed.append(self.arena, .{ .decls = &.{} });
    try self.import_maps.append(self.arena, .{});
    try self.pool_file.put(self.arena, file_index, file_id);
    return file_id;
}

/// The demand entry, two engine-driven phases (both to quiescence). PHASE A: parse the
/// transitive file set (the root ParseTask fans out over imports). PHASE B: scan the
/// root file's theorems, rack a ProveTask each, and let demand pull everything cited
/// (Fetch/Prove, suspending/resuming on the KV protocols). A is separate from B because
/// a ProveTask reads a CITED file's parsed AST — every file must be parsed first.
/// (Loading is a thing you DO with a context.)
pub fn loadProject(self: *Context, root_path: []const u8, root_source: []const u8) !FileId {
    self.root_file = try self.discover(root_path, root_source);

    var parse_eng = Engine.init(self.arena, self);
    _ = try parse_eng.rack(try Engine.ParseTask.new(self.arena, .{ .file_id = self.root_file, .source = root_source, .path = root_path }));
    try parse_eng.run();

    var prove_eng = Engine.init(self.arena, self);
    const root_idx = @intFromEnum(self.root_file);
    const root_parsed = self.parsed.items[root_idx];
    const root_source_text = self.files.items[root_idx].source;
    const file_index = try self.fileIndex(self.files.items[root_idx].path);
    for (root_parsed.decls) |decl| {
        if (decl != .theorem) continue;
        const name = decl.theorem.name;
        const name_id = try self.interner.internString(root_source_text[name.start..name.end]);
        _ = try prove_eng.rack(try Engine.ProveTask.new(self.arena, .{ .file = file_index, .name = name_id }));
    }
    try prove_eng.run();
    return self.root_file;
}
