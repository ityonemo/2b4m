//! The checker's shared world — the CONTEXT everything operates against: the interner,
//! the demand tables (FactKV/IdentKV), diagnostics sink, verify config, and the per-file
//! tables (files/parsed/import_maps) keyed by FileId. It is threaded to every engine task
//! (the engine's `ctx`). Term scratchpads are PER-PROOF (each ProveTask's `Prove` owns
//! one), not shared here — the substitution calculus is per-proof construction work.
//! LOADING is a thing you DO with a context (`loadProject`), not a separate abstraction —
//! hence Context, not "Loader".
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

/// Key into the by-name AST registry: a decl is addressed by its file + stamped name.
pub const DeclKey = struct { file: FileId, name: InternPool.StrId };

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
/// resolution; `parsed[fid]` its AST; `parse_state[fid]` its demand-parse lifecycle.
parsed: std.ArrayList(ast.File) = .empty,
/// BY-NAME AST registry: `(FileId, name StrId) -> the decl`. Populated by ParseTask
/// alongside `parsed[fid]` (one entry per named decl, keyed by its stamped name). The
/// demand tasks resolve a decl by NAME through this (O(1)) instead of linear-scanning
/// `parsed[fid].decls`. SYNTHETIC decls (accelerant-generated schemas, e.g. specialize's
/// `head[N]`) are inserted here under their mangled StrId with no positional slot — the
/// instance/schema path finds them by name identically. `parsed[fid].decls` (the ordered
/// slice) stays for the order/iteration consumers (root scan, queries, lint).
ast_index: std.AutoHashMapUnmanaged(DeclKey, *const ast.Decl) = .empty,
import_maps: std.ArrayList(ImportMap) = .empty,
/// LAZY-PARSE state per FileId (Step 11): a file is discovered (source read, FileId +
/// table slots reserved) LONG before it is parsed — parsing is on demand, when a
/// Fetch/Prove task first needs the file's AST. `unparsed` = discovered only;
/// `parsing` = a ParseTask (this TaskIndex) is parsing it, suspend blocked-on it;
/// `parsed` = `parsed[fid]` is populated, proceed. Mirrors the FactKV/IdentKV protocol
/// but keyed by the dense FileId (a plain array, not a hashmap).
parse_state: std.ArrayList(ParseState) = .empty,
/// the root FileId (its theorems are the roots of demand).
root_file: FileId = undefined,
/// schema names already well-formedness-checked (strict mode), for SchemaCheckTask dedup
/// (a check is racked once per proof-carrying schema; a re-entry is a no-op).
schema_checked: std.AutoHashMapUnmanaged(InternPool.StrId, void) = .empty,

pub const ParseState = union(enum) {
    unparsed,
    parsing: Engine.TaskIndex,
    parsed,
};

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
    try self.parse_state.append(self.arena, .unparsed);
    try self.pool_file.put(self.arena, file_index, file_id);
    return file_id;
}

/// Register one decl in the by-name AST registry under (file, its stamped name). A
/// duplicate name in a file leaves the FIRST winning (later decls don't overwrite) — a
/// name-collision is a separate diagnostic concern, not the registry's job. Called by
/// ParseTask for each parsed decl, and by accelerant generators for synthetic decls.
/// A `forward` (`intheory`) decl is SKIPPED: it is a manifest PROMISE, not a definition —
/// it must never occupy a name's registry slot (else it shadows the real theorem/axiom the
/// promise refers to). ParseTask separately checks every forward is fulfilled.
pub fn registerDecl(self: *Context, file: FileId, decl: *const ast.Decl) std.mem.Allocator.Error!void {
    if (decl.* == .forward) return;
    const gop = try self.ast_index.getOrPut(self.arena, .{ .file = file, .name = ast.declName(decl).name });
    if (!gop.found_existing) gop.value_ptr.* = decl;
}

/// Resolve a decl by NAME in a file (registry lookup; null = no such decl). Replaces the
/// linear `parsed[fid].decls` name-scans, and transparently serves synthetic decls.
pub fn declOf(self: *const Context, file: FileId, name: InternPool.StrId) ?*const ast.Decl {
    return self.ast_index.get(.{ .file = file, .name = name });
}

/// Ensure `file`'s AST is available, the LAZY-PARSE demand step. Returns:
///   - `.parsed`  → `parsed[fid]` is populated; the caller proceeds.
///   - `.parsing` → a ParseTask is producing it; the caller SUSPENDS on that TaskIndex.
/// On the first (`unparsed`) call it racks the file's ParseTask (claiming `parsing` with
/// that task's index) and returns `.parsing`. Idempotent: a second demander sees the
/// live `parsing` and suspends on the same task. `h` racks; single-threaded so the
/// discover→check→rack window is uncontended.
pub fn demandParse(self: *Context, h: *Engine.Handle, file: InternPool.Index) std.mem.Allocator.Error!ParseState {
    const fid = self.pool_file.get(file) orelse return .unparsed; // undiscovered — caller errors
    const idx = @intFromEnum(fid);
    switch (self.parse_state.items[idx]) {
        .parsed => return .parsed,
        .parsing => |t| return .{ .parsing = t },
        .unparsed => {
            const src = self.files.items[idx].source;
            const path = self.files.items[idx].path;
            const t = try h.rackIndexed(try Engine.ParseTask.new(self.arena, .{ .file_id = fid, .source = src, .path = path }));
            self.parse_state.items[idx] = .{ .parsing = t };
            return .{ .parsing = t };
        },
    }
}

/// The demand entry — ONE engine pass to quiescence (Step 11: parsing is itself lazy).
/// Rack the root ParseTask; it parses the root and, being the root, scans its theorems
/// and racks a ProveTask each. From there DEMAND drives everything: a Prove/Fetch task
/// that needs a not-yet-parsed cited file racks that file's ParseTask (`demandParse`) and
/// suspends until it completes. Imported files are parsed only when cited into — no eager
/// transitive parse. (Loading is a thing you DO with a context.)
pub fn loadProject(self: *Context, root_path: []const u8, root_source: []const u8) !FileId {
    self.root_file = try self.discover(root_path, root_source);
    var eng = Engine.init(self.arena, self);
    const t = try eng.rack(try Engine.ParseTask.new(self.arena, .{ .file_id = self.root_file, .source = root_source, .path = root_path }));
    self.parse_state.items[@intFromEnum(self.root_file)] = .{ .parsing = t };
    try eng.run();
    return self.root_file;
}
