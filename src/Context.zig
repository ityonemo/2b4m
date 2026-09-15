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

/// Key into the synthetic-by-step map: the file + the byte offset of the citing step's rule
/// token (the `loc` every accelerant stamps on its synthetic).
pub const SyntheticKey = struct { file: FileId, loc: u32 };

/// DURABLE allocator — the process-lifetime main arena (never reset). Holds the AST, InternPool,
/// facts, task payloads, per-Pool nodes — everything read by pointer/Index after a task returns.
arena: std.mem.Allocator,
/// THREAD-SAFE program-wide GPA (see `root.gpa`) for TRANSIENT scratch that must be RECLAIMED:
/// recursion work-stacks + throwaway pools spin up `ArenaAllocator.init(ctx.gpa)` + `defer deinit`
/// rather than leaking into the never-reset main arena. Distinct from `arena` by lifetime.
gpa: std.mem.Allocator,
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
/// SYNTHETIC decl by STEP: `(FileId, the citing step's rule-token offset) -> the registry key
/// of the accelerant-generated decl that step produced` (filled by `Prove.demandUsing` beside
/// `registerDecl`, keep-first). The debug reprint (`bpa debug accelerant`) locates a step's
/// synthetic through this; the engine itself resolves synthetics by NAME via `ast_index`.
synthetic_at: std.AutoHashMapUnmanaged(SyntheticKey, DeclKey) = .empty,
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
/// A SINGLE-THEOREM check (`bpa check <file> <theorem>`): only this root-file theorem is a
/// root of demand — what it cites is demanded from there; the file's other theorems and
/// axioms are not proved. Null = every root theorem (and axiom statement) is a root.
root_theorem: ?InternPool.StrId = null,
/// ACCELERATED facts (`--fast`): a published fact Index -> the set of `using` words its proof
/// ADMITTED (trusted, not proved). Populated at publish from the ProveTask's `prove.admitted`;
/// read by the summary to disclose which theorems accelerated + under which words.
accelerated: std.AutoHashMapUnmanaged(InternPool.Index, Verify.Word.Set) = .empty,
/// HOLES REACHED during the run: a `hole` decl is treated as an AXIOM everywhere except that
/// ProveTask records it here when it publishes (i.e. when something DEMANDED it). The summary
/// reports these (default mode rejects a hole-reaching result; --draft allows). See
/// [[hole-mechanism]].
holes_reached: std.ArrayList(HoleDecl) = .empty,
/// HOLE TAINT (for the summary's blast-radius): a published fact Index -> the hole NAMES it
/// transitively rests on. A `hole` maps to `&.{its own name}`; a theorem citing a hole-tainted
/// fact INHERITS that list (via `resolveFactRef`, accumulated in `Prove.holes_used`). Read to
/// report, per hole, which theorems rest on it ("rested on by: …"). Hole = axiom everywhere
/// else; this is a pure reporting side-channel, never consulted for the proof verdict.
hole_taint: std.AutoHashMapUnmanaged(InternPool.Index, []const InternPool.StrId) = .empty,
/// DEFINE EXPANSION (Engine/Expand): the hygienic-binder counter (`name#N` — program-wide, so
/// two expansions nested by substitution never rename to the same binder) and the set of
/// defines already diagnosed as an alias-in-disguise (once each).
expand_fresh: u32 = 0,
expand_linted: std.AutoHashMapUnmanaged(DefineKey, void) = .empty,
/// MODEL MAPPINGS ONTO DEFINES: `model M { src.UNIT: DOUBLED }` where `DOUBLED` is a define. A
/// define has no pool Index, so it cannot sit in M's overlay; instead the mapping is recorded
/// here — (M, source symbol) → the define — and the expansion pass, expanding a source proof
/// under M, treats that source symbol AS the define (substituting its body, in the parent
/// space). Filled by ModelTask at publish; composed models copy their inner's entries
/// (`copyModelDefineTargets`), and the pass walks a model's parent chain for the rest.
model_define_targets: std.AutoHashMapUnmanaged(ModelDefineKey, DefineKey) = .empty,

pub const ModelDefineKey = struct { model: InternPool.Index, src: InternPool.Index };

pub const HoleDecl = struct { name: InternPool.StrId, file: InternPool.Index, loc: u32 };

/// A define's identity (its home file + name) — the key of the expansion pass's per-define
/// "alias written as a macro" lint (diagnosed once, at the first use).
pub const DefineKey = struct { file: InternPool.Index, name: InternPool.StrId };

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
/// duplicate name in a file leaves the FIRST winning (later decls don't overwrite): this is
/// LOAD-BEARING — the re-entrant demand tasks (Model/Fetch materialization) re-register a
/// file's decls idempotently and rely on keep-first silence. Returns `true` if this was a
/// FRESH insert, `false` if the name was already registered. Only ParseTask's first,
/// authoritative pass acts on `false` (a genuine intra-file duplicate declaration); the
/// re-registration callers ignore it. A `forward` (`intheory`) decl is SKIPPED (returns
/// true): it is a manifest PROMISE, not a definition — it must never occupy a name's slot
/// (else it shadows the real theorem the promise refers to); ParseTask checks fulfilment
/// separately.
pub fn registerDecl(self: *Context, file: FileId, decl: *const ast.Decl) std.mem.Allocator.Error!bool {
    if (decl.* == .forward) return true;
    const gop = try self.ast_index.getOrPut(self.arena, .{ .file = file, .name = ast.declName(decl).name });
    if (!gop.found_existing) gop.value_ptr.* = decl;
    return !gop.found_existing;
}

/// The define a source symbol maps onto under `model` (or a model up its parent chain — a
/// composed model's parent is its outer model, whose entries apply to every symbol the inner
/// leaves alone). Null = no define mapping.
pub fn modelDefineTarget(self: *const Context, model: InternPool.Index, src: InternPool.Index) ?DefineKey {
    var cur = model;
    while (cur != InternPool.Index.none and cur != .universe) {
        if (self.model_define_targets.get(.{ .model = cur, .src = src })) |d| return d;
        const m = self.interner.keyOf(cur).model;
        if (m.parent == cur) break;
        cur = m.parent;
    }
    return null;
}

/// After `composed = outer ∘ inner`: the inner's define mappings apply to the composed model
/// as-is (its sources are the composed model's sources); an outer define mapping of a symbol
/// the inner maps ONTO (`inner: s → t`, `outer: t → D`) applies to `s`. Outer mappings of
/// symbols the inner leaves alone are found through the parent chain (composed.parent = outer).
pub fn copyModelDefineTargets(self: *Context, composed: InternPool.Index, outer: InternPool.Index, inner: InternPool.Index) std.mem.Allocator.Error!void {
    var it = self.model_define_targets.iterator();
    var pending: std.ArrayList(struct { key: ModelDefineKey, def: DefineKey }) = .empty;
    while (it.next()) |e| {
        if (e.key_ptr.model == inner) try pending.append(self.arena, .{ .key = .{ .model = composed, .src = e.key_ptr.src }, .def = e.value_ptr.* });
    }
    for (self.interner.keyOf(inner).model.overlay) |m| {
        if (self.modelDefineTarget(outer, m.tgt)) |d| try pending.append(self.arena, .{ .key = .{ .model = composed, .src = m.src }, .def = d });
    }
    for (pending.items) |p| try self.model_define_targets.put(self.arena, p.key, p.def);
}

/// Resolve a decl by NAME in a file (registry lookup; null = no such decl). Replaces the
/// linear `parsed[fid].decls` name-scans, and transparently serves synthetic decls.
pub fn declOf(self: *const Context, file: FileId, name: InternPool.StrId) ?*const ast.Decl {
    return self.ast_index.get(.{ .file = file, .name = name });
}

/// Record that the step at `loc` in `file` produced the synthetic decl registered as `name`
/// (keep-first: a step's synthetic is produced once per space; the first stays the answer).
pub fn registerSynthetic(self: *Context, file: FileId, loc: u32, name: InternPool.StrId) std.mem.Allocator.Error!void {
    const gop = try self.synthetic_at.getOrPut(self.arena, .{ .file = file, .loc = loc });
    if (!gop.found_existing) gop.value_ptr.* = .{ .file = file, .name = name };
}

/// The synthetic decl the step at `loc` in `file` produced, if any.
pub fn syntheticAt(self: *const Context, file: FileId, loc: u32) ?*const ast.Decl {
    const key = self.synthetic_at.get(.{ .file = file, .loc = loc }) orelse return null;
    return self.ast_index.get(key);
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
