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

fn countRoot(context: *Context) !Counts {
    const root_idx = @intFromEnum(context.root_file);
    const root_parsed = context.parsed.items[root_idx];
    const root_source = context.files.items[root_idx].source;
    const root_pool_file = try context.fileIndex(context.files.items[root_idx].path);
    const ns = try context.interner.namespace(.universe, root_pool_file);
    var proven: usize = 0;
    var accelerated: usize = 0;
    // union of all admitted words across root theorems — the disclosure lists these names.
    var word_set = Verify.Word.Set.initEmpty();
    for (root_parsed.decls) |decl| {
        if (decl != .theorem) continue;
        // count only LOCAL theorems (things this file sets out to PROVE); a theorem ALIAS is
        // a re-export, not a proof obligation (its origin is proved elsewhere).
        if (decl.theorem != .local) continue;
        const name_tok = ast.theoremName(decl.theorem);
        const name = try context.interner.internString(root_source[name_tok.start..name_tok.end]);
        if (context.root_theorem) |want| if (name != want) continue; // a single-theorem check
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

/// A read_fn for single-source checks (no imports resolvable).
fn readNone(_: ?*anyopaque, _: std.mem.Allocator, _: []const u8) anyerror![]const u8 {
    return error.FileNotFound;
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
    const context = try newContext(io, arena, null, &readNone, .{}, "");
    if (theorem) |t| context.root_theorem = try context.interner.internString(t);
    _ = try context.loadProject("/check/source.bpa", source);
    const counts = try countRoot(context);
    return .{
        .file = context.parsed.items[@intFromEnum(context.root_file)],
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
fn collectAxioms(arena: std.mem.Allocator, ctx: *Context) ![]const ProjectResult.Axiom {
    const root_idx = @intFromEnum(ctx.root_file);
    const rsrc = ctx.files.items[root_idx].source;
    const root_pf = try ctx.fileIndex(ctx.files.items[root_idx].path);
    const rns = try ctx.interner.namespace(.universe, root_pf);
    // union the axiom sets of every root theorem that was actually proved (one, under a
    // single-theorem check).
    var seen: std.AutoHashMapUnmanaged(InternPool.Index, void) = .empty;
    var out: std.ArrayList(ProjectResult.Axiom) = .empty;
    for (ctx.parsed.items[root_idx].decls) |decl| {
        if (decl != .theorem) continue;
        const nt = ast.theoremName(decl.theorem);
        const name = try ctx.interner.internString(rsrc[nt.start..nt.end]);
        if (ctx.root_theorem) |want| if (name != want) continue;
        const state = ctx.facts.lookup(ctx.io, .{ .namespace = rns, .name = name }) orelse continue;
        if (state != .proven) continue;
        const axs = ctx.axiom_taint.get(state.proven) orelse continue;
        for (axs) |a| {
            if ((try seen.getOrPut(arena, a)).found_existing) continue;
            const origin = ctx.axiom_origin.get(a) orelse continue;
            const fid = ctx.pool_file.get(origin.file) orelse continue;
            const f = ctx.files.items[@intFromEnum(fid)];
            var is_hole = false;
            for (ctx.holes_reached.items) |hh| {
                if (hh.file == origin.file and hh.loc == origin.loc) is_hole = true;
            }
            try out.append(arena, .{
                .name = ctx.interner.stringBytes(origin.name),
                .path = f.path,
                .line = std.zig.findLineColumn(f.source, origin.loc).line + 1,
                .is_hole = is_hole,
            });
        }
    }
    std.mem.sort(ProjectResult.Axiom, out.items, {}, struct {
        fn lessThan(_: void, x: ProjectResult.Axiom, y: ProjectResult.Axiom) bool {
            if (!std.mem.eql(u8, x.path, y.path)) return std.mem.lessThan(u8, x.path, y.path);
            return x.line < y.line;
        }
    }.lessThan);
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

/// Run the demand loader/checker and hand back the world. `checkProject` is this + the
/// count summary.
pub fn loadProject(
    io: std.Io,
    arena: std.mem.Allocator,
    root_path: []const u8,
    root_source: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    verify: Verify,
    std_root: []const u8,
    theorem: ?[]const u8,
) !LoadedProject {
    const context = try newContext(io, arena, read_ctx, read_fn, verify, std_root);
    if (theorem) |t| context.root_theorem = try context.interner.internString(t);
    const canonical_root = try std.fs.path.resolve(arena, &.{root_path});
    const root_file = try context.loadProject(canonical_root, root_source);
    return .{
        .interner = context.interner,
        .context = context,
        .sink = context.sink,
        .root_file = root_file,
        .files = context.files.items,
        .declarations = context.declarations,
    };
}

pub fn checkProject(
    io: std.Io,
    arena: std.mem.Allocator,
    root_path: []const u8,
    root_source: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    verify: Verify,
    std_root: []const u8,
    theorem: ?[]const u8,
    want_axioms: bool,
) !ProjectResult {
    const loaded = try loadProject(io, arena, root_path, root_source, read_ctx, read_fn, verify, std_root, theorem);
    const counts = try countRoot(loaded.context);
    // resolve every REACHED hole (a `hole` decl whose ProveTask published) to a reportable
    // {name, path, line, dependents}. The summary discloses all sites (default rejects; --draft
    // allows). DEPENDENTS (blast-radius) = the ROOT theorems whose proof transitively rests on
    // the hole (from `hole_taint`); built by scanning the root theorems once.
    const ctx = loaded.context;
    // hole-name StrId -> the root theorem names that rest on it.
    var deps: std.AutoHashMapUnmanaged(InternPool.StrId, std.ArrayList([]const u8)) = .empty;
    {
        const root_idx = @intFromEnum(ctx.root_file);
        const rsrc = ctx.files.items[root_idx].source;
        const root_pf = try ctx.fileIndex(ctx.files.items[root_idx].path);
        const rns = try ctx.interner.namespace(.universe, root_pf);
        // scan EVERY root theorem — LOCAL (proved here) AND ALIAS (a re-export of a fact proved
        // elsewhere). An alias resolves in the root ns to its ORIGIN fact Index, which carries
        // the origin's taint, so a re-exported hole-resting theorem shows in the blast-radius.
        for (ctx.parsed.items[root_idx].decls) |decl| {
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
        const fid = ctx.pool_file.get(h.file) orelse continue;
        const f = ctx.files.items[@intFromEnum(fid)];
        const lc = std.zig.findLineColumn(f.source, h.loc);
        const dep_list: []const []const u8 = if (deps.get(h.name)) |d| d.items else &.{};
        try holes.append(arena, .{
            .name = ctx.interner.stringBytes(h.name),
            .path = f.path,
            .line = lc.line + 1,
            .dependents = dep_list,
        });
    }
    return .{
        .files = loaded.files,
        .sink = loaded.sink,
        .declarations = loaded.declarations,
        .theorems_proven = counts.proven,
        .theorems_trusted = 0,
        .theorems_accelerated = counts.accelerated,
        .accelerated_names = counts.accelerated_names,
        .holes = holes.items,
        .axioms = if (want_axioms) try collectAxioms(arena, ctx) else &.{},
    };
}

/// `bpa check`'s non-flag positionals: `[trust words…] <file> [theorem]`. The file is the first
/// positional that names a `.bpa`/`.md` source (trust words never do); at most one positional
/// may follow it — the theorem to check alone. Null = the shape is wrong (usage).
pub const CheckArgs = struct { words: []const []const u8, path: []const u8, theorem: ?[]const u8 };
pub fn splitCheckArgs(positionals: []const []const u8) ?CheckArgs {
    if (positionals.len == 0) return null;
    var at: ?usize = null;
    for (positionals, 0..) |a, i| {
        if (std.mem.endsWith(u8, a, ".bpa") or std.mem.endsWith(u8, a, ".md")) {
            at = i;
            break;
        }
    }
    const i = at orelse positionals.len - 1; // no source-looking positional: the last one is the path
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
    // no source-looking positional at all: the last one is taken as the path (usage error later)
    try std.testing.expectEqualStrings("nope", splitCheckArgs(&.{ "x", "nope" }).?.path);
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

test "a single-theorem check names a missing theorem, an axiom, a schema" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const missing = try checkSourceTheorem(arena, single_theorem_source, "nosuch");
    try std.testing.expectEqual(@as(usize, 1), missing.sink.list.items.len);
    try std.testing.expectEqualStrings("no theorem 'nosuch' in this file", missing.sink.list.items[0].message);
    const axiom = try checkSourceTheorem(arena, single_theorem_source, "pq");
    try std.testing.expectEqualStrings("'pq' is an axiom, not a theorem", axiom.sink.list.items[0].message);
    const schema = try checkSourceTheorem(arena, "sort T\npred p(x: T)\ntheorem sch(prop: T -> Prop): forall x: T; prop(x) -> prop(x)\nproof\n  @conclusion |\n    forall x: T; prop(x) -> prop(x)\n    [using tautology]\nqed\n", "sch");
    try std.testing.expectEqualStrings("'sch' is a schema; it is checked at its instantiations", schema.sink.list.items[0].message);
}

test "splitCheckArgs: --axioms is a flag, not a positional" {
    // the flag is stripped by main's loop before splitCheckArgs sees the positionals, so
    // the file + theorem shape is unaffected by it.
    const a = splitCheckArgs(&.{ "f.bpa", "thm" }).?;
    try std.testing.expectEqualStrings("f.bpa", a.path);
    try std.testing.expectEqualStrings("thm", a.theorem.?);
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
