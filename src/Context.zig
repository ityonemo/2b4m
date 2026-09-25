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
const Segmented = @import("segmented.zig").Segmented;
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
/// Guards the per-file tables' growth and the parse claim (see `files`/`demandParse`). A
/// self-contained spinlock, like `Engine.mutex` and `InternPool.intern_lock`: uncontended
/// single-threaded, and the critical sections are marked for when workers land.
files_lock: InternPool.Lock = .{},
/// Guards the by-name AST registry (`ast_index`, `synthetic_at`). Unlike the file tables
/// these are written DURING proving — an accelerant producer registers the synthetic decl it
/// generated — so reads take it too: a hashmap rehashes on growth.
ast_lock: InternPool.Lock = .{},
/// Guards the publish-time SIDE TABLES — `accelerated`, `axiom_origin`, `axiom_taint`,
/// `hole_taint`, `model_discharged`, `model_define_targets`, `holes_reached`, `expand_linted`
/// — plus the `declarations` counter and the `fact_trace` buffer. One lock for all of them:
/// they are low-traffic, written only as a task publishes, and never held together, so one
/// lock-order edge beats eight. Most READS happen in reporting, after quiescence, and are
/// unguarded by design; the accessors below cover the writes that race.
side_lock: InternPool.Lock = .{},
interner: *InternPool,
/// The fact resolution/coordination table over `interner` (see FactKV). Filled by
/// ProveTask (the scan's roots + every demanded citation).
facts: FactKV,
/// The identifier resolution/coordination table over `interner` (see IdentKV). Filled
/// by FetchTask on demand.
idents: IdentKV,
files: Segmented(diagnostics.FileSrc) = .empty,
/// Per file: WHERE it was discovered from — the `import` token in the parent that named it —
/// or null for a root. A file's ParseTask READS the file; when the read fails, this is where
/// "cannot open" is reported (the parent's import site), the way an eager reader would have.
origins: Segmented(?Origin) = .empty,
/// pool `.file` entity Index -> the dense FileId cursoring the per-file tables. The
/// InternPool does the path dedup (same resolved path -> same file Index); this maps that
/// interned identity onto the FileId used to index files/parsed/import_maps. A second
/// reference to a file resolves through the pool to the same Index -> same FileId (so
/// cyclic file imports are naturally fine: the id exists before parsing completes).
pool_file: std.AutoHashMapUnmanaged(InternPool.Index, FileId) = .empty,
read_ctx: ?*anyopaque,
read_fn: ReadFileFn,
/// The off-worker file loader (`Engine/Loader.zig`), when the run has one: `root.loadProject`
/// configures it unless `--sync-io`. Null = every read is inline on the demanding worker (the
/// in-process test rigs that call `loadRoots` directly, and `--sync-io`). Valid only for the
/// duration of `loadRoots` — the pool it fronts is owned by the caller's frame.
loader: ?*Engine.Loader = null,
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
///
/// GUARDED BY `files_lock`: these five grow together in `discover`, and `parse_state` also
/// carries the parse CLAIM. Reads of an already-populated slot are safe unguarded (the
/// tables only ever grow, and a slot is written once), but any growth or claim is a
/// transaction.
parsed: Segmented(ast.File) = .empty,
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
/// `registerDecl`, keep-first). The debug reprint (`2b4m debug accelerant`) locates a step's
/// synthetic through this; the engine itself resolves synthetics by NAME via `ast_index`.
synthetic_at: std.AutoHashMapUnmanaged(SyntheticKey, DeclKey) = .empty,
import_maps: Segmented(ImportMap) = .empty,
/// LAZY-PARSE state per FileId (Step 11): a file is discovered (source read, FileId +
/// table slots reserved) LONG before it is parsed — parsing is on demand, when a
/// Fetch/Prove task first needs the file's AST. `unparsed` = discovered only;
/// `parsing` = a ParseTask (this TaskIndex) is parsing it, suspend blocked-on it;
/// `parsed` = `parsed[fid]` is populated, proceed. Mirrors the FactKV/IdentKV protocol
/// but keyed by the dense FileId (a plain array, not a hashmap).
parse_state: Segmented(ParseState) = .empty,
/// the root FileId (its theorems are the roots of demand).
root_file: FileId = undefined,
/// The files this run was ASKED ABOUT — one for a single-file check, N for a directory. Set
/// by whoever racks the roots; the ENGINE never consults it (a file's tasks say what to do).
/// It exists for REPORTING: the summary counts, the axiom report and the hole blast-radius all
/// walk "the files the user named". `root_file` is the first entry.
root_files: std.ArrayList(FileId) = .empty,
/// ACCELERATED facts (`--fast`): a published fact Index -> the set of `using` words its proof
/// ADMITTED (trusted, not proved). Populated at publish from the ProveTask's `prove.admitted`;
/// read by the summary to disclose which theorems accelerated + under which words.
accelerated: std.AutoHashMapUnmanaged(InternPool.Index, Verify.Word.Set) = .empty,
/// HOLES REACHED during the run: a `hole` decl is treated as an AXIOM everywhere except that
/// ProveTask records it here when it publishes (i.e. when something DEMANDED it). The summary
/// reports these (default mode rejects a hole-reaching result; --draft allows). See
/// [[hole-mechanism]].
holes_reached: std.ArrayList(HoleDecl) = .empty,
/// AXIOM ORIGINS: a published AXIOM's fact Index -> where it was declared. Recorded at publish
/// (the only place the declaring file is in hand); read by the `--axioms` report to name each
/// axiom's file:line. A `hole` publishes as an axiom and is recorded here too — the report
/// separates them by asking `holes_reached`.
axiom_origin: std.AutoHashMapUnmanaged(InternPool.Index, HoleDecl) = .empty,
/// `--trace-facts` output, ACCUMULATED rather than written as it happens: the demand engine
/// interleaves tasks, so writing each line to stderr when it is produced shreds them into each
/// other. The driver prints this once the run is quiescent.
fact_trace: std.ArrayList([]const u8) = .empty,
/// MODEL-DISCHARGED facts: every LOCAL fact a `model` names as the thing that discharges a
/// source obligation (`src <- local`, a `@`-projection, or a guard witness on a `:` map).
/// Such a fact is USED — by the model machinery rather than by a proof's citation closure, so
/// it never enters `axiom_taint` — and `--library` must not call it unused. Recorded by
/// ModelTask as each mapping resolves.
model_discharged: std.AutoHashMapUnmanaged(InternPool.Index, void) = .empty,
/// AXIOM TAINT (the `--axioms` report): a published fact Index -> the AXIOM fact Indexes its
/// proof transitively rests on. An axiom maps to `&.{itself}`; a theorem citing it INHERITS
/// that list (via `resolveFactRef`, accumulated in `Prove.axioms_used`) — the same side-channel
/// shape as `hole_taint`, and likewise never consulted for a proof verdict.
axiom_taint: std.AutoHashMapUnmanaged(InternPool.Index, []const InternPool.Index) = .empty,
/// THE PROOF TREE: a published fact Index -> the `(namespace, name)` of the proof that
/// DEMANDED it, or null for a root (a theorem the run was asked to check).
///
/// The parent is a KEY, not an Index, because a fact's Index does not exist until its
/// statement is elaborated (`Key.Fact` includes the formula) — whereas a demanding proof
/// knows its own `(namespace, name)` from the moment it starts. The namespace already
/// encodes `(model, file)`, so a model TRANSFER and its source are distinct parents.
///
/// One node per ProveTask that actually proves something — a `.theorem` or a schema
/// `.instance`. An AXIOM and a HOLE are LEAVES and get no node: their assertion IS the
/// fact, nothing was demanded to establish it (they seed `axiom_taint` with themselves
/// instead).
///
/// The parent pointer IS the demand chain: walk it to a root to recover "why was this
/// proved". A fact is keyed in a namespace and `Key.Namespace = {model, file}`, so a model
/// TRANSFER of `src.thm` and the source `src.thm` are distinct nodes — which is what lets a
/// failed transfer say "model M cannot transfer src.thm" against the citing step rather
/// than against the source theorem's own line (the diagnostic that cost this project two
/// wrong root-cause analyses).
///
/// APPEND-ONLY and keyed by interned identity, so it is insensitive to scheduling: a second
/// demander of an already-proven fact adds nothing (the first proof is the one that
/// happened). Report ORDER must still come from declaration sites, never from task order.
proof_parent: std.AutoHashMapUnmanaged(InternPool.Index, ?FactKV.Key) = .empty,
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

/// Where a file was discovered from: the import token (`loc`, in `file`) that named it.
pub const Origin = struct { file: FileId, loc: u32 };

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
    return self.interner.intern(.{ .file = .{ .path = path_id } });
}

/// The FileId already assigned to a resolved path, or null if not yet discovered. Reads
/// through the pool (interns the path -> file Index -> the pool_file map).
pub fn lookupFile(self: *Context, resolved_path: []const u8) !?FileId {
    return self.fileOf(try self.fileIndex(resolved_path));
}

/// Register a newly-discovered file: intern its path (the file entity), assign a FileId,
/// reserve its table slots. IDEMPOTENT — a repeat path returns the existing FileId
/// (the pool dedups the path to one file Index, and pool_file maps it to one FileId).
/// Pub: the parse task (Engine/ParseTask.zig) discovers a file's imports.
pub fn discover(self: *Context, resolved_path: []const u8, origin: ?Origin) !FileId {
    const file_index = try self.fileIndex(resolved_path);
    // ONE TRANSACTION: check, mint the id, grow the five per-file tables, record the
    // mapping. Two tasks discovering the same path concurrently would otherwise both miss
    // and both mint, giving one file two FileIds — and the appends themselves must not
    // interleave, since the tables are grown in lockstep and indexed by that id.
    self.files_lock.lock();
    defer self.files_lock.unlock();
    // direct map read, NOT `fileOf`: we already hold `files_lock` (it is not reentrant).
    if (self.pool_file.get(file_index)) |existing| return existing;

    const file_id: FileId = @enumFromInt(self.files.len);
    // the SOURCE is not read here: the file's ParseTask reads it (and extracts a literate
    // document's 2b4m blocks) when the file is actually parsed. Until then it is empty.
    _ = try self.files.append(self.arena, .{ .path = resolved_path, .source = "" });
    _ = try self.origins.append(self.arena, origin);
    _ = try self.parsed.append(self.arena, .{ .decls = &.{} });
    _ = try self.import_maps.append(self.arena, .{});
    _ = try self.parse_state.append(self.arena, .unparsed);
    try self.pool_file.put(self.arena, file_index, file_id);
    return file_id;
}

/// TEST RIG entry: discover `path` with its source ALREADY IN HAND (an in-memory fixture that
/// parses + registers the file itself, bypassing ParseTask). Production never preloads — a
/// ParseTask reads its own file.
pub fn preload(self: *Context, path: []const u8, source: []const u8) !FileId {
    const fid = try self.discover(path, null);
    self.files.at(@intFromEnum(fid)).source = source; // in place
    return fid;
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
    self.ast_lock.lock();
    defer self.ast_lock.unlock();
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
    // A read takes the lock too: the map REHASHES on growth, so an unguarded read can race
    // a concurrent `registerDecl` (the accelerant producers register synthetics DURING
    // proving, so this map is not write-once). `@constCast` because the lock is mutable
    // state on an otherwise-read-only view.
    const lock = @constCast(&self.ast_lock);
    lock.lock();
    defer lock.unlock();
    return self.ast_index.get(.{ .file = file, .name = name });
}

/// Record that the step at `loc` in `file` produced the synthetic decl registered as `name`
/// (keep-first: a step's synthetic is produced once per space; the first stays the answer).
pub fn registerSynthetic(self: *Context, file: FileId, loc: u32, name: InternPool.StrId) std.mem.Allocator.Error!void {
    self.ast_lock.lock();
    defer self.ast_lock.unlock();
    const gop = try self.synthetic_at.getOrPut(self.arena, .{ .file = file, .loc = loc });
    if (!gop.found_existing) gop.value_ptr.* = .{ .file = file, .name = name };
}

/// The synthetic decl the step at `loc` in `file` produced, if any.
pub fn syntheticAt(self: *const Context, file: FileId, loc: u32) ?*const ast.Decl {
    const lock = @constCast(&self.ast_lock);
    lock.lock();
    defer lock.unlock();
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
/// PUBLISH a file as parsed. Taken under `files_lock` — the lock `demandParse` READS the
/// state under — so that everything the ParseTask wrote before this point (the decl
/// registrations, the import map) happens-before any reader that observes `.parsed`.
///
/// A plain store here was a real race: nothing ordered it after the writes it announces,
/// so the compiler may hoist it above the preceding `ast_lock` release and a reader on
/// another thread can see `.parsed` while `declOf` still misses. In `Expand.resolveDeclDefine`
/// a miss means "not a define", the guard is left opaque, and a FetchTask later hits the
/// define-misuse arm: `'isBig' is a define — it expands where it is used` on
/// `define_guard_nested.b4m`, 2 runs in 20 at `-j8` and never under `--chaos` (which
/// reorders the schedule without threads — this needs two).
pub fn markParsed(self: *Context, fid: FileId) void {
    self.files_lock.lock();
    defer self.files_lock.unlock();
    self.parse_state.set(@intFromEnum(fid), .parsed);
}

pub fn demandParse(self: *Context, h: *Engine.Handle, file: InternPool.Index) std.mem.Allocator.Error!ParseState {
    const fid = self.fileOf(file) orelse return .unparsed; // undiscovered — caller errors
    const idx = @intFromEnum(fid);
    // The CLAIM (`unparsed` -> rack -> `.parsing`) is one transaction for the same reason
    // `discover` is: two demanders racing it would rack two ParseTasks for one file, which
    // double-registers its decls and double-counts `declarations`.
    self.files_lock.lock();
    defer self.files_lock.unlock();
    switch (self.parse_state.get(idx)) {
        .parsed => return .parsed,
        .parsing => |t| return .{ .parsing = t },
        .unparsed => {
            const t = try h.rackIndexed(try Engine.ParseTask.new(self.arena, .{ .file_id = fid }));
            self.parse_state.set(idx, .{ .parsing = t });
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
pub fn loadProject(self: *Context, root_path: []const u8) !FileId {
    return self.loadRoots(&.{.{ .path = root_path }});
}

/// A root of the run: a file the user asked to check — a PATH; its ParseTask reads it. With
/// `theorem` null, EVERY local theorem (and axiom statement) in it is a proof obligation; with a
/// name, only that theorem is.
pub const Root = struct { path: []const u8, theorem: ?[]const u8 = null };

/// THE ENTRY: rack the tasks the request names, then run the engine once to quiescence.
///   - `check <file>`           → a ParseTask that SEEDS proofs (racks a ProveTask per theorem).
///   - `check <file> <theorem>` → a ParseTask that seeds nothing + the ONE ProveTask, racked
///                                here; it suspends on the parse and resolves the name itself
///                                (a missing/misused name is that task's diagnostic).
///   - `check <dir>`            → a seeding ParseTask per file.
/// The entry only racks; from there DEMAND drives everything (an import is parsed when cited
/// into, a fact proved when cited). Sharing the pass is why a directory is N roots and not N
/// runs: a fact two roots cite is proved once. Returns the first root (`self.root_file`).
/// The dense FileId a diagnostic whose offset indexes `file` renders against. Every
/// `sink.add` takes its file explicitly (see diagnostics.zig — it must never be ambient
/// state), and the demand tasks hold pool `.file` Indexes, so this is the bridge. 0 when
/// the file is undiscovered: an offset with nowhere to anchor, which `render` clamps.
/// Record that `fact` rests on `axioms` (the `--axioms` report's edge). Publish-time.
pub fn recordAxiomTaint(self: *Context, fact: InternPool.Index, axioms: []const InternPool.Index) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    try self.axiom_taint.put(self.arena, fact, axioms);
}

/// Record `fact`'s parent in the proof tree — the fact whose proof demanded it, or
/// `InternPool.Index.none` for a root. Keep-first: a fact is proved once, and the demander
/// that raced to it first is the one whose proof actually caused the work.
pub fn recordProofParent(self: *Context, fact: InternPool.Index, parent: ?FactKV.Key) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    const gop = try self.proof_parent.getOrPut(self.arena, fact);
    if (!gop.found_existing) gop.value_ptr.* = parent;
}

/// The chain of facts that led to `fact` being proved, innermost FIRST (`fact` itself, then
/// its demander, ...) up to a root. Bounded by the table size, so a cycle cannot loop
/// forever. Reads unguarded: callers use it after quiescence, when nothing is still writing.
pub fn proofChain(self: *const Context, arena: std.mem.Allocator, fact: InternPool.Index) std.mem.Allocator.Error![]const FactKV.Key {
    var out: std.ArrayList(FactKV.Key) = .empty;
    var cur: ?FactKV.Key = self.proof_parent.get(fact) orelse null;
    var hops: usize = 0;
    while (hops <= self.proof_parent.count()) : (hops += 1) {
        const key = cur orelse break; // a root: nobody demanded it
        try out.append(arena, key);
        // `lookup` takes the table's lock, so it needs a mutable receiver; this walk is
        // logically read-only (same pattern as `declOf`/`fileOf`).
        const state = @constCast(&self.facts).lookup(self.io, key) orelse break;
        const parent_fact = switch (state) {
            .proven => |ix| ix,
            .in_flight => break, // still being proved: the chain ends here
        };
        cur = self.proof_parent.get(parent_fact) orelse null;
    }
    return out.items;
}

/// Record where the axiom `fact` was declared (its site in the `--axioms` report).
pub fn recordAxiomOrigin(self: *Context, fact: InternPool.Index, decl: HoleDecl) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    try self.axiom_origin.put(self.arena, fact, decl);
}

/// Record that `fact` rests on the named `holes` (the `--draft` blast radius).
pub fn recordHoleTaint(self: *Context, fact: InternPool.Index, holes: []const InternPool.StrId) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    try self.hole_taint.put(self.arena, fact, holes);
}

/// Record that a hole declaration was actually REACHED by a proof.
pub fn recordHoleReached(self: *Context, decl: HoleDecl) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    try self.holes_reached.append(self.arena, decl);
}

/// Record the `using` words `fact`'s proof ADMITTED under `--fast` (the disclosure set).
pub fn recordAccelerated(self: *Context, fact: InternPool.Index, words: Verify.Word.Set) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    try self.accelerated.put(self.arena, fact, words);
}

/// Record that a `model` names `fact` as a discharger — `--library` counts that as USE.
pub fn recordModelDischarged(self: *Context, fact: InternPool.Index) std.mem.Allocator.Error!void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    try self.model_discharged.put(self.arena, fact, {});
}

/// Add to the running declaration count (the summary line's total).
pub fn addDeclarations(self: *Context, n: usize) void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    self.declarations += n;
}

/// Append a `--trace-facts` line. Buffered on the Context because per-task stderr writers
/// interleave into shredded output; printed once, before the verdict.
pub fn traceLine(self: *Context, line: []const u8) void {
    self.side_lock.lock();
    defer self.side_lock.unlock();
    self.fact_trace.append(self.arena, line) catch {};
}

/// The file table as a flat slice, for the diagnostic renderer (which indexes it by the
/// `file` each diagnostic carries). Built on `arena` AFTER the run, when the table has
/// stopped growing — the segmented store exists precisely so the live table need not be
/// contiguous while tasks are appending to it.
/// The dense FileId a pool `.file` Index was discovered as, or null. GUARDED: `discover`
/// inserts into this map, which REHASHES on growth, so an unguarded read can race a
/// concurrent discovery — and every task does this lookup constantly.
pub fn fileOf(self: *const Context, file: InternPool.Index) ?FileId {
    const lock = @constCast(&self.files_lock);
    lock.lock();
    defer lock.unlock();
    return self.pool_file.get(file);
}

pub fn fileList(self: *const Context, arena: std.mem.Allocator) std.mem.Allocator.Error![]const diagnostics.FileSrc {
    const out = try arena.alloc(diagnostics.FileSrc, self.files.len);
    for (out, 0..) |*slot, i| slot.* = self.files.get(@intCast(i));
    return out;
}

pub fn diagFile(self: *const Context, file: InternPool.Index) u32 {
    const fid = self.fileOf(file) orelse return 0;
    return @intFromEnum(fid);
}

pub fn loadRoots(self: *Context, roots: []const Root) !FileId {
    std.debug.assert(roots.len > 0);
    var eng = Engine.init(self.arena, self, self.io);
    // Every off-worker load reports to `eng` (`externalEnd`), so all of them must land before
    // this frame ends — including on the failure path, where `runWorkers` returns with loads
    // still in flight. `runWorkers` joins every worker first, so nothing submits after it
    // returns and the barrier is exact.
    defer if (self.loader) |l| l.drain();
    eng.trace = self.verify.trace_facts;
    if (self.verify.chaos_seed) |seed| eng.chaos = .init(seed); // --chaos: shuffle scheduling
    for (roots) |r| {
        const fid = try self.discover(r.path, null);
        try self.root_files.append(self.arena, fid);
        // a path listed twice (or already discovered as another root's import) parses once —
        // `parse_state` is the guard.
        if (self.parse_state.get(@intFromEnum(fid)) == .unparsed) {
            const t = try eng.rack(try Engine.ParseTask.new(self.arena, .{ .file_id = fid, .seed_proofs = r.theorem == null }));
            self.parse_state.set(@intFromEnum(fid), .{ .parsing = t });
        }
        if (r.theorem) |name| {
            _ = try eng.rack(try Engine.ProveTask.new(self.arena, .{ .file = try self.fileIndex(r.path), .name = try self.interner.internString(name) }));
        }
    }
    self.root_file = self.root_files.items[0];
    try eng.runWorkers(self.verify.workers orelse Verify.defaultWorkers());
    try self.reportWedge(&eng);
    return self.root_file;
}

/// A run that ends with tasks still PARKED abandoned work: nothing could wake them. Report
/// the ones that form a CYCLE — tasks waiting on each other, so no order could have helped.
///
/// The other kind of wedge is a task parked behind a proof that FAILED: that proof published
/// nothing, so its `in_flight` claim stands forever and its citers never wake. Its root cause
/// is already in the sink (the failure's own diagnostic), so re-reporting the consequence
/// would add an error to every failing file. `Engine.Wedged.in_cycle` is exactly that split.
///
/// Why this must exist: without it a citation cycle is SILENT — the theorems are simply never
/// proved, the run looks quiescent, and `2b4m check` prints `OK: 0 theorems proven` and exits
/// 0. Silence must never imply verification.
fn reportWedge(self: *Context, eng: *Engine) !void {
    const stuck = try eng.wedged(self.arena);
    if (stuck.len == 0) return;

    // Name each cycle member by the fact it claimed but never published, ordered by
    // declaration site so the report does not depend on task numbering (which is
    // scheduling, not content — see `Verify.chaos_seed`).
    const Member = struct { file: FileId, loc: u32, name: []const u8 };
    var members: std.ArrayList(Member) = .empty;
    for (stuck) |w| {
        if (!w.in_cycle) continue; // parked behind a failure: already diagnosed
        const key = self.facts.claimOf(self.io, w.task) orelse continue;
        // A cycle whose fact is nonetheless PROVEN is abandoned duplicate work, not a
        // failure: a second task claimed the same fact, the two waited on each other, and
        // the winner published. (Real in the corpus: a theorem and the synthetic its own
        // `arithmetic` step generates can each demand the other, while the theorem still
        // proves by the ordinary path.) Only an UNPROVEN fact is a genuine wedge.
        if (self.facts.lookup(self.io, key)) |state| if (state == .proven) continue;
        const home = self.interner.keyOf(key.namespace).namespace.file;
        const fid = self.fileOf(home) orelse continue;
        const decl = self.declOf(fid, key.name) orelse continue;
        const nt = ast.declName(decl);
        try members.append(self.arena, .{ .file = fid, .loc = nt.start, .name = self.interner.stringBytes(key.name) });
    }
    if (members.items.len == 0) return;
    const lessThan = struct {
        fn f(_: void, x: Member, y: Member) bool {
            if (x.file != y.file) return @intFromEnum(x.file) < @intFromEnum(y.file);
            return x.loc < y.loc;
        }
    }.f;
    std.mem.sort(Member, members.items, {}, lessThan);

    // one error per participant, at its declaration, naming the whole cycle.
    var names: std.ArrayList(u8) = .empty;
    for (members.items, 0..) |m, i| {
        if (i > 0) try names.appendSlice(self.arena, ", ");
        try names.appendSlice(self.arena, m.name);
    }
    for (members.items) |m| {
        try self.sink.add(@intFromEnum(m.file), m.loc, "'{s}' is part of a citation cycle ({s}) — each proof waits on the next, so none can be proved", .{ m.name, names.items });
    }
}
