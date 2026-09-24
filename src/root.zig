//! bpa core library. All proof-checking logic is exposed from here;
//! src/main.zig is a thin CLI wrapper.
//!
//! POST-FLIP (Step 8 W5): checking runs on the DEMAND ENGINE — parse tasks discover the
//! file set, the root scan racks a ProveTask per theorem, and Fetch/Prove tasks pull
//! everything cited on demand (see Engine.zig / Context.zig). The eager Elaborator and
//! `env` are gone. The Phase-5 rebuilds have landed: schemas, models, accelerants, defines,
//! holes, guarded funcs, `--fast` admit-trust and `--draft` all work on the demand path;
//! the summary reports accelerated/hole buckets again.

const std = @import("std");

pub const lexer = @import("lexer.zig");
pub const ast = @import("ast.zig");
pub const parser = @import("parser.zig");
pub const diagnostics = @import("diagnostics.zig");
pub const InternPool = @import("InternPool.zig");
pub const FactKV = @import("FactKV.zig");
pub const IdentKV = @import("IdentKV.zig");
pub const term = @import("term.zig");
pub const Verify = @import("Verify.zig");
pub const Engine = @import("Engine.zig");
pub const Context = @import("Context.zig");
pub const Walk = @import("Engine/ProveTask/Walk.zig");
pub const RefScan = @import("Engine/ProveTask/RefScan.zig");
pub const Elab = @import("Engine/ProveTask/Elab.zig");
pub const Prove = @import("Engine/ProveTask/Prove.zig");
pub const Schema = @import("Engine/ProveTask/Schema.zig");
pub const Delaborate = @import("Engine/ProveTask/Delaborate.zig");
pub const smt = @import("Engine/ProveTask/smt.zig");
pub const simplify = @import("Engine/ProveTask/simplify.zig");
pub const EqCert = @import("Engine/ProveTask/EqCert.zig");
pub const print = @import("print.zig");
pub const kernel = @import("kernel.zig");
pub const fmt = @import("fmt.zig");
pub const literate = @import("literate.zig");
pub const lint = @import("lint.zig");

pub const query = @import("query.zig");
pub const debug = @import("debug.zig");

pub const ReadFileFn = Context.ReadFileFn;

const builtin = @import("builtin");
/// Program-wide THREAD-SAFE general-purpose allocator — the backing for TRANSIENT scratch arenas
/// (recursion work-stacks, throwaway pools) that must be RECLAIMED, distinct from the durable main
/// arena (which is never reset). `smp_allocator` in release (a process-global thread-safe singleton
/// GPA — one per process); `DebugAllocator` in debug (leak/UAF detection; its `thread_safe`
/// defaults to `!single_threaded`). The engine is single-threaded today; the thread-safe choice is
/// forward-looking (the parked-queue/lock scaffolding anticipates multithreading) but free.
var debug_gpa: std.heap.DebugAllocator(.{}) = .init;
pub fn gpa() std.mem.Allocator {
    return if (builtin.mode == .Debug) debug_gpa.allocator() else std.heap.smp_allocator;
}

/// Build a fresh demand-checking Context (interner + KV tables + shared scratchpad).
fn newContext(
    io: std.Io,
    arena: std.mem.Allocator,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    verify: Verify,
    std_root: []const u8,
) !*Context {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const context = try arena.create(Context);
    context.* = .{
        .arena = arena,
        .gpa = gpa(), // program-wide thread-safe GPA for transient scratch (see `gpa`)
        .io = io,
        .sink = sink,
        .interner = interner,
        .facts = .init(interner),
        .idents = .init(interner),
        .read_ctx = read_ctx,
        .read_fn = read_fn,
        .verify = verify,
        .std_root = std_root,
    };
    return context;
}

/// Count the root file's checking outcome: how many local theorems are `proven` facts in
/// FactKV (published by their ProveTasks). We do NOT track how many theorems were DECLARED
/// — a file that proves zero theorems is a clean success (a declarations-only dependency).
const Counts = struct {
    proven: usize,
    /// root theorems whose proof ADMITTED at least one `using` word (`--fast`).
    accelerated: usize,
    /// the distinct `using` word names admitted across all root theorems (for disclosure).
    accelerated_names: []const []const u8,
};

/// A single-theorem check that named a SCHEMA proves nothing: a schema is checked at its
/// instantiations by design (its ProveTask only publishes a locator), so the run would end
/// "0 theorems proven" with no word of why. Say so, at the declaration. (A missing name is
/// the racked task's own diagnostic; an axiom is a legitimate statement-elaborating task.)
fn noteSchemaRoot(ctx: *Context, theorem: ?[]const u8) !void {
    const t = theorem orelse return;
    const name = try ctx.interner.internString(t);
    const decl = ctx.declOf(ctx.root_file, name) orelse return;
    const fact = ast.factOf(decl) orelse return;
    if (fact.params == null) return;
    try ctx.sink.add(@intCast(@intFromEnum(ctx.root_file)), fact.name.start, "'{s}' is a schema; it is checked at its instantiations — check a theorem that instantiates it", .{t});
}

/// `only` = a single-theorem check's theorem: the file's other theorems may have been PROVED
/// (demanded by the named one) but were not ASKED about, so they are not counted.
fn countRoot(context: *Context, only: ?[]const u8) !Counts {
    const want: ?InternPool.StrId = if (only) |t| try context.interner.internString(t) else null;
    var proven: usize = 0;
    var accelerated: usize = 0;
    // union of all admitted words across root theorems — the disclosure lists these names.
    var word_set = Verify.Word.Set.initEmpty();
    for (context.root_files.items) |rf| {
        const root_idx = @intFromEnum(rf);
        const root_parsed = context.parsed.get(root_idx);
        const root_source = context.files.get(root_idx).source;
        const root_pool_file = try context.fileIndex(context.files.get(root_idx).path);
        const ns = try context.interner.namespace(.universe, root_pool_file);
        for (root_parsed.decls) |decl| {
            if (decl != .theorem) continue;
            // count only LOCAL theorems (things this file sets out to PROVE); a theorem ALIAS is
            // a re-export, not a proof obligation (its origin is proved elsewhere). Under a
            // single-theorem check only the named one was ever proved, so only it counts.
            if (decl.theorem != .local) continue;
            const name_tok = ast.theoremName(decl.theorem);
            const name = try context.interner.internString(root_source[name_tok.start..name_tok.end]);
            if (want) |w| if (name != w) continue;
            if (context.facts.lookup(context.io, .{ .namespace = ns, .name = name })) |state| {
                if (state == .proven) {
                    proven += 1;
                    if (context.accelerated.get(state.proven)) |words| {
                        accelerated += 1;
                        word_set = word_set.unionWith(words);
                    }
                }
            }
        }
    }
    // render the union of admitted words as name strings (enum-declaration order).
    var names: std.ArrayList([]const u8) = .empty;
    var it = word_set.iterator();
    while (it.next()) |wd| try names.append(context.arena, @tagName(wd));
    return .{ .proven = proven, .accelerated = accelerated, .accelerated_names = names.items };
}

pub const CheckResult = struct {
    file: ast.File,
    sink: *diagnostics.Sink,
    declarations: usize,
    theorems_proven: usize,

    pub fn ok(self: *const CheckResult) bool {
        return self.sink.list.items.len == 0;
    }
};

/// An in-memory file set for tests: a read_fn that serves these paths and nothing else.
pub const MemFile = struct { path: []const u8, source: []const u8 };
const MemFiles = struct { files: []const MemFile };
fn readMem(ctx: ?*anyopaque, _: std.mem.Allocator, path: []const u8) anyerror![]const u8 {
    const mem: *const MemFiles = @ptrCast(@alignCast(ctx.?));
    for (mem.files) |f| if (std.mem.eql(u8, f.path, path)) return f.source;
    return error.FileNotFound;
}

/// Check in-memory files as the roots of one run (a directory check over a fake tree), with
/// the full report. Every path is a root; `library` asks for the unused-axiom report.
pub fn checkSources(arena: std.mem.Allocator, files: []const MemFile, library: bool) !ProjectResult {
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();
    const mem = try arena.create(MemFiles);
    mem.* = .{ .files = files };
    const roots = try arena.alloc(Context.Root, files.len);
    for (files, roots) |f, *r| r.* = .{ .path = f.path };
    const loaded = try loadProject(io, arena, roots, @ptrCast(mem), &readMem, .custom, .{}, "");
    return summarize(arena, loaded, roots, true, library);
}

/// Check a .bpa source (single file; imports unresolvable). All allocations go into
/// `arena`; diagnostics are collected in the result's sink (rendered by the caller).
pub fn checkSource(arena: std.mem.Allocator, source: []const u8) !CheckResult {
    return checkSourceTheorem(arena, source, null);
}

/// `checkSource` restricted to ONE root theorem (`theorem` = its name), or every root
/// theorem when null.
pub fn checkSourceTheorem(arena: std.mem.Allocator, source: []const u8, theorem: ?[]const u8) !CheckResult {
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();
    const mem = try arena.create(MemFiles);
    mem.* = .{ .files = try arena.dupe(MemFile, &.{.{ .path = "/check/source.bpa", .source = source }}) };
    const context = try newContext(io, arena, @ptrCast(mem), &readMem, .{}, "");
    _ = try context.loadRoots(&.{.{ .path = "/check/source.bpa", .theorem = theorem }});
    try noteSchemaRoot(context, theorem);
    const counts = try countRoot(context, theorem);
    return .{
        .file = context.parsed.get(@intFromEnum(context.root_file)),
        .sink = context.sink,
        .declarations = context.declarations,
        .theorems_proven = counts.proven,
    };
}

// --- multi-file checking (imports) ---

pub const ProjectResult = struct {
    files: []const diagnostics.FileSrc,
    sink: *diagnostics.Sink,
    declarations: usize,
    theorems_proven: usize,
    /// theorems whose imported proofs were trusted (not re-checked). Currently always 0 —
    /// import-proof re-checking is not a distinct trust axis on the demand path (an imported
    /// theorem is proved by its own ProveTask; `--fast import` only admits the CITATION).
    theorems_trusted: usize,
    theorems_accelerated: usize,
    accelerated_names: []const []const u8,
    holes: []const Hole,
    /// how many ROOTS were checked (1 for a file; a directory's file count).
    files_checked: usize,
    /// `--trace-facts`: one entry per resolved citation, in completion order. Empty unless
    /// asked. Accumulated during the run (the engine interleaves tasks, so writing as we go
    /// would shred the lines into each other) and printed by the driver at the end.
    fact_trace: []const []const u8,
    /// `--library`: the root files' axioms NO root theorem rests on — a library must not ship
    /// assumptions nothing uses. Empty unless asked. Same shape as `axioms` (never a hole).
    unused_axioms: []const Axiom,
    /// the axioms the checked theorem(s) transitively rest on — only computed when the caller
    /// asked (`--axioms`); empty otherwise. A HOLE reached by the proof appears here with
    /// `is_hole` set: it is an axiom to the kernel, and the report says so explicitly.
    axioms: []const Axiom,

    pub const Axiom = struct {
        name: []const u8,
        path: []const u8,
        line: usize,
        /// this "axiom" is a `hole` — an aspirational placeholder the kernel treats as an axiom
        is_hole: bool,
    };

    pub const Hole = struct {
        name: []const u8,
        path: []const u8,
        line: usize,
        /// theorem names that (transitively) rest on this hole
        dependents: []const []const u8,
    };

    pub fn ok(self: *const ProjectResult) bool {
        return self.sink.list.items.len == 0;
    }
};

/// The axioms the ROOT theorems transitively rest on (`--axioms`), sorted by file then line so
/// the report is stable. Reads `ctx.axiom_taint` — the set each proved root fact recorded — and
/// resolves every axiom Index through `ctx.axiom_origin` to a name + site. A hole is flagged:
/// the kernel treats it as an axiom, and the report should not quietly pass it off as one.
fn collectAxioms(arena: std.mem.Allocator, ctx: *Context, only: ?[]const u8) ![]const ProjectResult.Axiom {
    const want: ?InternPool.StrId = if (only) |t| try ctx.interner.internString(t) else null;
    // union the axiom sets of every root theorem that was actually proved (one, under a
    // single-theorem check — the others were never racked).
    var seen: std.AutoHashMapUnmanaged(InternPool.Index, void) = .empty;
    var out: std.ArrayList(ProjectResult.Axiom) = .empty;
    for (ctx.root_files.items) |rf| {
        const root_idx = @intFromEnum(rf);
        const rsrc = ctx.files.get(root_idx).source;
        const root_pf = try ctx.fileIndex(ctx.files.get(root_idx).path);
        const rns = try ctx.interner.namespace(.universe, root_pf);
        for (ctx.parsed.get(root_idx).decls) |decl| {
            if (decl != .theorem) continue;
            const nt = ast.theoremName(decl.theorem);
            const name = try ctx.interner.internString(rsrc[nt.start..nt.end]);
            if (want) |w| if (name != w) continue;
            const state = ctx.facts.lookup(ctx.io, .{ .namespace = rns, .name = name }) orelse continue;
            if (state != .proven) continue;
            const axs = ctx.axiom_taint.get(state.proven) orelse continue;
            for (axs) |a| {
                if ((try seen.getOrPut(arena, a)).found_existing) continue;
                if (try axiomSite(ctx, a)) |site| try out.append(arena, site);
            }
        }
    }
    std.mem.sort(ProjectResult.Axiom, out.items, {}, axiomLessThan);
    return out.items;
}

/// The loaded project state after a demand run: for tools that must READ the result
/// The loaded project state after a demand run: for tools that must READ the result
/// rather than just count it.
pub const LoadedProject = struct {
    interner: *InternPool,
    context: *Context,
    sink: *diagnostics.Sink,
    root_file: Context.FileId,
    files: []const diagnostics.FileSrc,
    declarations: usize,
};

/// What the paths a run names actually are. The thread-pool loader and the inline read go
/// through `read_fn`, so they work over anything; the io_uring loader opens the PATH itself,
/// so it is only eligible when the paths are real files on this machine.
pub const Source = enum { filesystem, custom };

/// Run the demand loader/checker and hand back the world. `checkProject` is this + the
/// count summary.
pub fn loadProject(
    io: std.Io,
    arena: std.mem.Allocator,
    roots: []const Context.Root,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    source: Source,
    verify: Verify,
    std_root: []const u8,
) !LoadedProject {
    const context = try newContext(io, arena, read_ctx, read_fn, verify, std_root);
    // canonicalize every root path (the engine keys files by canonical path, so a root and
    // the same file reached as an import are one FileId).
    const canon = try arena.alloc(Context.Root, roots.len);
    for (roots, canon) |r, *c| c.* = .{ .path = try std.fs.path.resolve(arena, &.{r.path}), .theorem = r.theorem };

    // The FILE LOADER, owned by this frame (see Engine/Loader.zig). The thread pool is
    // always built (cheap; it is the fallback): its gpa must be thread-safe and must really
    // free (`Group.Task.destroy`) — `gpa()`, never an arena. On Linux with no explicit
    // `--io-threads` the io_uring backend is tried first; a refusal (seccomp, an old kernel)
    // silently leaves the pool in charge. `loadRoots` drains every load before returning, so
    // neither teardown ever joins a thread mid-read. Declaration order = teardown order
    // reversed: loader detached from the context, ring, then pool.
    const pool_ceiling = @min(verify.io_threads orelse Verify.max_io_threads, Verify.max_io_threads);
    var threaded: std.Io.Threaded = .init(gpa(), .{ .concurrent_limit = .limited(pool_ceiling) });
    defer threaded.deinit();
    var loader: Engine.Loader = .{ .backend = .{ .pool = .{ .io = threaded.io() } } };
    const ring: ?*Engine.Loader.Ring = if (Engine.Loader.uring_supported and source == .filesystem and !verify.sync_io and verify.io_threads == null)
        Engine.Loader.Ring.init(gpa(), io) catch null
    else
        null;
    defer if (ring) |r| r.deinit();
    if (ring) |r| loader.backend = .{ .ring = r };
    context.loader = if (verify.sync_io) null else &loader;
    defer context.loader = null; // the backends die with this frame; the context outlives it
    if (context.loader) |l| {
        if (verify.trace_facts) context.traceLine(std.fmt.allocPrint(arena, "[load] backend = {s}\n", .{l.name()}) catch "");
        // pre-warm the pool: a directory check reads (at least) every root, a single-file
        // check a handful of imports — spawn those threads now, off the critical path, not
        // one at a time under the first submissions. Clamped to the ceiling (a hold beyond
        // it would be refused, harmlessly). A no-op for the ring.
        const floor: usize = if (roots.len > 1) roots.len else 5;
        l.prewarm(@min(floor, pool_ceiling));
    }
    const root_file = try context.loadRoots(canon);
    return .{
        .interner = context.interner,
        .context = context,
        .sink = context.sink,
        .root_file = root_file,
        .files = try context.fileList(arena),
        .declarations = context.declarations,
    };
}

pub fn checkProject(
    io: std.Io,
    arena: std.mem.Allocator,
    roots: []const Context.Root,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    source: Source,
    verify: Verify,
    std_root: []const u8,
    want_axioms: bool,
    library: bool,
) !ProjectResult {
    const loaded = try loadProject(io, arena, roots, read_ctx, read_fn, source, verify, std_root);
    return summarize(arena, loaded, roots, want_axioms, library);
}

/// The run's REPORT: counts, holes, and — when asked — the axiom report and the library's
/// unused axioms. Pure reading of the finished context.
fn summarize(arena: std.mem.Allocator, loaded: LoadedProject, roots: []const Context.Root, want_axioms: bool, library: bool) !ProjectResult {
    // a single-theorem check is one root with a theorem; a directory's roots name none.
    const theorem: ?[]const u8 = if (roots.len == 1) roots[0].theorem else null;
    try noteSchemaRoot(loaded.context, theorem);
    const counts = try countRoot(loaded.context, theorem);
    // resolve every REACHED hole (a `hole` decl whose ProveTask published) to a reportable
    // {name, path, line, dependents}. The summary discloses all sites (default rejects; --draft
    // allows). DEPENDENTS (blast-radius) = the ROOT theorems whose proof transitively rests on
    // the hole (from `hole_taint`); built by scanning the root theorems once.
    const ctx = loaded.context;
    // hole-name StrId -> the root theorem names that rest on it.
    var deps: std.AutoHashMapUnmanaged(InternPool.StrId, std.ArrayList([]const u8)) = .empty;
    for (ctx.root_files.items) |rf| {
        const root_idx = @intFromEnum(rf);
        const rsrc = ctx.files.get(root_idx).source;
        const root_pf = try ctx.fileIndex(ctx.files.get(root_idx).path);
        const rns = try ctx.interner.namespace(.universe, root_pf);
        // scan EVERY root theorem — LOCAL (proved here) AND ALIAS (a re-export of a fact proved
        // elsewhere). An alias resolves in the root ns to its ORIGIN fact Index, which carries
        // the origin's taint, so a re-exported hole-resting theorem shows in the blast-radius.
        for (ctx.parsed.get(root_idx).decls) |decl| {
            if (decl != .theorem) continue;
            const nt = ast.theoremName(decl.theorem);
            const tname_str = rsrc[nt.start..nt.end];
            const tname = try ctx.interner.internString(tname_str);
            const state = ctx.facts.lookup(ctx.io, .{ .namespace = rns, .name = tname }) orelse continue;
            if (state != .proven) continue;
            const taint = ctx.hole_taint.get(state.proven) orelse continue;
            for (taint) |hole_name| {
                const gop = try deps.getOrPut(arena, hole_name);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(arena, tname_str);
            }
        }
    }
    var holes: std.ArrayList(ProjectResult.Hole) = .empty;
    for (ctx.holes_reached.items) |h| {
        const fid = ctx.fileOf(h.file) orelse continue;
        const f = ctx.files.get(@intFromEnum(fid));
        const lc = std.zig.findLineColumn(f.source, h.loc);
        const dep_list: []const []const u8 = if (deps.get(h.name)) |d| d.items else &.{};
        try holes.append(arena, .{
            .name = ctx.interner.stringBytes(h.name),
            .path = f.path,
            .line = lc.line + 1,
            .dependents = dep_list,
        });
    }
    // `holes_reached` is filled in the order proofs REACHED the holes — i.e. in scheduling
    // order, which is not part of the output contract (a `--chaos` sweep prints a different
    // order per seed). Sort by declaration site, as the axiom report does.
    std.mem.sort(ProjectResult.Hole, holes.items, {}, holeLessThan);
    return .{
        .files = loaded.files,
        .sink = loaded.sink,
        .declarations = loaded.declarations,
        .theorems_proven = counts.proven,
        .theorems_trusted = 0,
        .theorems_accelerated = counts.accelerated,
        .accelerated_names = counts.accelerated_names,
        .holes = holes.items,
        .axioms = if (want_axioms) try collectAxioms(arena, ctx, theorem) else &.{},
        .files_checked = roots.len,
        .fact_trace = ctx.fact_trace.items,
        .unused_axioms = if (library) try collectUnusedAxioms(arena, ctx) else &.{},
    };
}

/// The site of an axiom Index for a report: a ground axiom's from `axiom_origin` (recorded at
/// publish), a schema axiom's from its locator key. Null = not an axiom we can place.
fn axiomSite(ctx: *Context, ix: InternPool.Index) !?ProjectResult.Axiom {
    const name: InternPool.StrId, const file: InternPool.Index, const loc: u32 = switch (ctx.interner.keyOf(ix)) {
        .schema => |sk| .{ sk.name, sk.file, sk.loc },
        else => if (ctx.axiom_origin.get(ix)) |o| .{ o.name, o.file, o.loc } else return null,
    };
    const fid = ctx.fileOf(file) orelse return null;
    const f = ctx.files.get(@intFromEnum(fid));
    var is_hole = false;
    for (ctx.holes_reached.items) |hh| {
        if (hh.file == file and hh.loc == loc) is_hole = true;
    }
    return .{
        .name = ctx.interner.stringBytes(name),
        .path = f.path,
        .line = std.zig.findLineColumn(f.source, loc).line + 1,
        .is_hole = is_hole,
    };
}

fn holeLessThan(_: void, x: ProjectResult.Hole, y: ProjectResult.Hole) bool {
    if (!std.mem.eql(u8, x.path, y.path)) return std.mem.lessThan(u8, x.path, y.path);
    if (x.line != y.line) return x.line < y.line;
    return std.mem.lessThan(u8, x.name, y.name);
}

fn axiomLessThan(_: void, x: ProjectResult.Axiom, y: ProjectResult.Axiom) bool {
    if (!std.mem.eql(u8, x.path, y.path)) return std.mem.lessThan(u8, x.path, y.path);
    return x.line < y.line;
}

/// Every axiom Index some ROOT theorem (local or re-exported) transitively rests on — the
/// library's USED set.
fn usedAxioms(arena: std.mem.Allocator, ctx: *Context) !std.AutoHashMapUnmanaged(InternPool.Index, void) {
    var used: std.AutoHashMapUnmanaged(InternPool.Index, void) = .empty;
    for (ctx.root_files.items) |rf| {
        const root_idx = @intFromEnum(rf);
        const rsrc = ctx.files.get(root_idx).source;
        const rns = try ctx.interner.namespace(.universe, try ctx.fileIndex(ctx.files.get(root_idx).path));
        for (ctx.parsed.get(root_idx).decls) |decl| {
            if (decl != .theorem) continue;
            const nt = ast.theoremName(decl.theorem);
            const name = try ctx.interner.internString(rsrc[nt.start..nt.end]);
            const state = ctx.facts.lookup(ctx.io, .{ .namespace = rns, .name = name }) orelse continue;
            if (state != .proven) continue;
            for (ctx.axiom_taint.get(state.proven) orelse continue) |a| try used.put(arena, a, {});
        }
    }
    // a fact a MODEL names as a discharger is used by the model machinery — it never appears in
    // a proof's citation closure, but it is exactly as consumed.
    var it = ctx.model_discharged.keyIterator();
    while (it.next()) |k| try used.put(arena, k.*, {});
    return used;
}

/// `--library`: the root files' LOCAL axioms (ground and schema) that no root theorem rests on.
/// An axiom never even demanded has no fact entry; one only elaborated as a root statement has
/// an entry but is in nobody's closure. Both are unused. Holes are not axioms here (they are
/// reported on their own terms).
fn collectUnusedAxioms(arena: std.mem.Allocator, ctx: *Context) ![]const ProjectResult.Axiom {
    var used = try usedAxioms(arena, ctx);
    defer used.deinit(arena);
    var out: std.ArrayList(ProjectResult.Axiom) = .empty;
    for (ctx.root_files.items) |rf| {
        const root_idx = @intFromEnum(rf);
        const f = ctx.files.get(root_idx);
        const rns = try ctx.interner.namespace(.universe, try ctx.fileIndex(f.path));
        for (ctx.parsed.get(root_idx).decls) |decl| {
            if (decl != .axiom or decl.axiom != .local) continue;
            const name_tok = decl.axiom.local.name;
            if (ctx.facts.lookup(ctx.io, .{ .namespace = rns, .name = name_tok.name })) |state| {
                if (state == .proven and used.contains(state.proven)) continue;
            }
            try out.append(arena, .{
                .name = ctx.interner.stringBytes(name_tok.name),
                .path = f.path,
                .line = std.zig.findLineColumn(f.source, name_tok.start).line + 1,
                .is_hole = false,
            });
        }
    }
    std.mem.sort(ProjectResult.Axiom, out.items, {}, axiomLessThan);
    return out.items;
}

/// `bpa check`'s non-flag positionals: `[trust words…] <file | dir> [theorem]`. The trust words
/// are a closed vocabulary (`Verify.Word.parse`), so the path is the FIRST positional that is
/// not one of them — a file or a directory, whatever it is named; at most one positional may
/// follow it — the theorem to check alone. Null = the shape is wrong (usage).
pub const CheckArgs = struct { words: []const []const u8, path: []const u8, theorem: ?[]const u8 };
pub fn splitCheckArgs(positionals: []const []const u8) ?CheckArgs {
    if (positionals.len == 0) return null;
    var i: usize = 0;
    while (i < positionals.len and Verify.Word.parse(positionals[i]) != null) i += 1;
    if (i == positionals.len) return null; // nothing but trust words
    const rest = positionals[i + 1 ..];
    if (rest.len > 1) return null;
    return .{ .words = positionals[0..i], .path = positionals[i], .theorem = if (rest.len == 1) rest[0] else null };
}

test "splitCheckArgs: words before the file, an optional theorem after it" {
    const one = splitCheckArgs(&.{"a.bpa"}).?;
    try std.testing.expectEqualStrings("a.bpa", one.path);
    try std.testing.expectEqual(@as(usize, 0), one.words.len);
    try std.testing.expect(one.theorem == null);
    const thm = splitCheckArgs(&.{ "a.bpa", "foo" }).?;
    try std.testing.expectEqualStrings("foo", thm.theorem.?);
    const words = splitCheckArgs(&.{ "tautology", "model", "lit.md", "foo" }).?;
    try std.testing.expectEqual(@as(usize, 2), words.words.len);
    try std.testing.expectEqualStrings("lit.md", words.path);
    try std.testing.expectEqualStrings("foo", words.theorem.?);
    try std.testing.expect(splitCheckArgs(&.{ "a.bpa", "foo", "bar" }) == null);
    try std.testing.expect(splitCheckArgs(&.{}) == null);
    // a DIRECTORY has no suffix: it is the first non-word positional, and may take no theorem
    // at the split level (the CLI rejects that pairing with its own message).
    const dir = splitCheckArgs(&.{ "arithmetic", "some/dir", "thm" }).?;
    try std.testing.expectEqualStrings("some/dir", dir.path);
    try std.testing.expectEqualStrings("thm", dir.theorem.?);
    try std.testing.expectEqual(@as(usize, 1), dir.words.len);
    // only trust words: no path
    try std.testing.expect(splitCheckArgs(&.{ "arithmetic", "tautology" }) == null);
}

const single_theorem_source =
    \\pred p
    \\pred q
    \\axiom pq: p
    \\theorem good: p
    \\proof
    \\  @conclusion |
    \\    p
    \\    [by cite pq]
    \\qed
    \\theorem broken: q
    \\proof
    \\  @conclusion |
    \\    q
    \\    [by cite pq]
    \\qed
    \\
;

test "a single-theorem check proves only the named theorem; the file's other proofs are not run" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    // the whole file: the broken proof is diagnosed.
    const whole = try checkSource(arena, single_theorem_source);
    try std.testing.expect(!whole.ok());
    // just `good`: clean, one theorem proven — `broken` is never run.
    const good = try checkSourceTheorem(arena, single_theorem_source, "good");
    try std.testing.expect(good.ok());
    try std.testing.expectEqual(@as(usize, 1), good.theorems_proven);
    // just `broken`: its diagnosis, nothing else.
    const broken = try checkSourceTheorem(arena, single_theorem_source, "broken");
    try std.testing.expect(!broken.ok());
    try std.testing.expectEqual(@as(usize, 0), broken.theorems_proven);
}

test "a single-theorem check: a missing name is the racked task's diagnostic; an axiom elaborates; a schema is noted" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    // the entry racks a ProveTask for the name; a miss is THAT task's diagnostic.
    const missing = try checkSourceTheorem(arena, single_theorem_source, "nosuch");
    try std.testing.expectEqual(@as(usize, 1), missing.sink.list.items.len);
    try std.testing.expectEqualStrings("reference not found: 'nosuch'", missing.sink.list.items[0].message);
    // an axiom is a legitimate root task (its statement is elaborated); nothing is PROVED.
    const axiom = try checkSourceTheorem(arena, single_theorem_source, "pq");
    try std.testing.expect(axiom.ok());
    try std.testing.expectEqual(@as(usize, 0), axiom.theorems_proven);
    const schema = try checkSourceTheorem(arena, "sort T\npred p(x: T)\ntheorem sch(prop: T -> Prop): forall x: T; prop(x) -> prop(x)\nproof\n  @conclusion |\n    forall x: T; prop(x) -> prop(x)\n    [using tautology]\nqed\n", "sch");
    try std.testing.expectEqual(@as(usize, 1), schema.sink.list.items.len);
    try std.testing.expectEqualStrings("'sch' is a schema; it is checked at its instantiations — check a theorem that instantiates it", schema.sink.list.items[0].message);
}

test "splitCheckArgs: --axioms is a flag, not a positional" {
    // the flag is stripped by main's loop before splitCheckArgs sees the positionals, so
    // the file + theorem shape is unaffected by it.
    const a = splitCheckArgs(&.{ "f.bpa", "thm" }).?;
    try std.testing.expectEqualStrings("f.bpa", a.path);
    try std.testing.expectEqualStrings("thm", a.theorem.?);
}

test "library: an axiom no root theorem rests on is unused; one reached through an import, or a schema reached by instantiation, is used" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const files = [_]MemFile{
        .{ .path = "/lib/base.bpa", .source =
        \\sort Nat
        \\const ZERO: Nat
        \\pred even(n: Nat)
        \\axiom zeroEven: even(ZERO)
        \\axiom spare: forall n: Nat; even(n)
        \\axiom evenInduction(prop: Nat -> Prop): prop(ZERO) -> forall n: Nat; prop(n)
        \\theorem zeroIsEven: even(ZERO)
        \\proof
        \\  @conclusion |
        \\    even(ZERO)
        \\    [by cite zeroEven]
        \\qed
        \\
        },
        .{ .path = "/lib/client.bpa", .source =
        \\import base <<< "base.bpa"
        \\sort Nat = base.Nat
        \\const ZERO = base.ZERO
        \\pred even = base.even
        \\theorem viaImport: even(ZERO)
        \\proof
        \\  @conclusion |
        \\    even(ZERO)
        \\    [using import(base) zeroIsEven]
        \\qed
        \\theorem allEven: even(ZERO) -> forall n: Nat; even(n)
        \\proof
        \\  @conclusion |
        \\    even(ZERO) -> forall n: Nat; even(n)
        \\    [using instantiation base.evenInduction(fun k: Nat => even(k))]
        \\qed
        \\
        },
    };
    const r = try checkSources(arena, &files, true);
    try std.testing.expect(r.ok());
    try std.testing.expectEqual(@as(usize, 3), r.theorems_proven);
    // `spare` alone is unused: zeroEven is cited, evenInduction is instantiated (a schema
    // reached through its locator), and the report names the site.
    try std.testing.expectEqual(@as(usize, 1), r.unused_axioms.len);
    try std.testing.expectEqualStrings("spare", r.unused_axioms[0].name);
    try std.testing.expectEqual(@as(usize, 5), r.unused_axioms[0].line);
    // the `--axioms` union sees both used axioms, the schema by its own name.
    try std.testing.expectEqual(@as(usize, 2), r.axioms.len);
}

test "library: a fact a model names as a discharger is USED, not unused" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const files = [_]MemFile{
        .{ .path = "/lib/theory.bpa", .source =
        \\sort Elem
        \\const UNIT: Elem
        \\func op(a: Elem, b: Elem) => Elem
        \\axiom opUnitLeft: forall a: Elem; op(UNIT, a) = a
        \\theorem opUnitTwice: forall a: Elem; op(UNIT, op(UNIT, a)) = op(UNIT, a)
        \\proof
        \\  @generalize-a |
        \\    fix a: Elem {
        \\      @unit-left |
        \\        forall b: Elem; op(UNIT, b) = b
        \\        [by cite opUnitLeft]
        \\      @conclusion-twice |
        \\        op(UNIT, op(UNIT, a)) = op(UNIT, a)
        \\        [by forall_elim(op(UNIT, a)) unit-left]
        \\    }
        \\  @conclusion |
        \\    forall a: Elem; op(UNIT, op(UNIT, a)) = op(UNIT, a)
        \\    [by forall_intro generalize-a]
        \\qed
        \\
        },
        .{ .path = "/lib/concrete.bpa", .source =
        \\import theory <<< "theory.bpa"
        \\sort Thing
        \\const ZED: Thing
        \\func combine(a: Thing, b: Thing) => Thing
        \\axiom combineZedLeft: forall a: Thing; combine(ZED, a) = a
        \\model ThingModel {
        \\  theory.Elem: Thing
        \\  theory.UNIT: ZED
        \\  theory.op: combine
        \\  theory.opUnitLeft <- combineZedLeft
        \\}
        \\theorem combineZedTwice: forall a: Thing; combine(ZED, combine(ZED, a)) = combine(ZED, a)
        \\proof
        \\  @conclusion |
        \\    forall a: Thing; combine(ZED, combine(ZED, a)) = combine(ZED, a)
        \\    [using model(ThingModel) theory.opUnitTwice]
        \\qed
        \\
        },
    };
    const r = try checkSources(arena, &files, true);
    try std.testing.expect(r.ok());
    // `combineZedLeft` is cited by NO proof — the model discharges `theory.opUnitLeft` with it.
    // That is a use.
    for (r.unused_axioms) |a| std.debug.print("unexpected unused: {s}\n", .{a.name});
    try std.testing.expectEqual(@as(usize, 0), r.unused_axioms.len);
}

test {
    std.testing.refAllDecls(@This());
    std.testing.refAllDecls(query.outline);
    std.testing.refAllDecls(query.theorem);
    std.testing.refAllDecls(query.whereis);
    std.testing.refAllDecls(query.search);
    std.testing.refAllDecls(query.uses);
    std.testing.refAllDecls(debug.taint);
    std.testing.refAllDecls(debug.accelerant);
    std.testing.refAllDecls(literate);
    std.testing.refAllDecls(lint);
    // engine task-payload sub-files (their tests aren't reached by the shallow @This() ref)
    std.testing.refAllDecls(Engine.ParseTask);
    std.testing.refAllDecls(Engine.ProveTask);
    std.testing.refAllDecls(Engine.FetchTask);
    std.testing.refAllDecls(Engine.ModelTask);
    std.testing.refAllDecls(@import("Engine/ProveTask/Prove.zig"));
    std.testing.refAllDecls(@import("Engine/ProveTask/Polynomial.zig"));
}
