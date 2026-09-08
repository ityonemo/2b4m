//! bpa core library. All proof-checking logic is exposed from here;
//! src/main.zig is a thin CLI wrapper.
//!
//! POST-FLIP (Step 8 W5): checking runs on the DEMAND ENGINE — parse tasks discover the
//! file set, the root scan racks a ProveTask per theorem, and Fetch/Prove tasks pull
//! everything cited on demand (see Engine.zig / Context.zig). The eager Elaborator and
//! `env` are gone. RED-PHASE degradations (until the Phase-5 rebuilds): schemas, models,
//! accelerants, defines, aliases, guarded funcs and holes are unsupported (their files
//! diagnose); the summary no longer reports accelerated/trusted/hole buckets.

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

/// Count the root file's checking outcome: how many theorem DECLARATIONS it has, and how
/// many of them are `proven` facts in FactKV (published by their ProveTasks).
const Counts = struct {
    theorem_decls: usize,
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
    var decls: usize = 0;
    var proven: usize = 0;
    var accelerated: usize = 0;
    // union of all admitted words across root theorems — the disclosure lists these names.
    var word_set = Verify.Word.Set.initEmpty();
    for (root_parsed.decls) |decl| {
        if (decl != .theorem) continue;
        // count only LOCAL theorems (things this file sets out to PROVE); a theorem ALIAS is
        // a re-export, not a proof obligation (its origin is proved elsewhere).
        if (decl.theorem != .local) continue;
        decls += 1;
        const name_tok = ast.theoremName(decl.theorem);
        const name = try context.interner.internString(root_source[name_tok.start..name_tok.end]);
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
    return .{ .theorem_decls = decls, .proven = proven, .accelerated = accelerated, .accelerated_names = names.items };
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
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();
    const context = try newContext(io, arena, null, &readNone, .{}, "");
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
    /// number of `theorem` declarations in the TARGET (root) file — i.e. things
    /// this file set out to prove. Distinguishes a legitimately declarations-only
    /// dependency (0 theorem decls → nothing to check, fine) from a proof file
    /// that declared theorems but proved none (a real footgun). See the
    /// `theorems_proven == 0` branch in main.zig.
    target_theorem_decls: usize,
    /// theorems whose imported proofs were trusted (not re-checked). Currently always 0 —
    /// import-proof re-checking is not a distinct trust axis on the demand path (an imported
    /// theorem is proved by its own ProveTask; `--fast import` only admits the CITATION).
    theorems_trusted: usize,
    theorems_accelerated: usize,
    accelerated_names: []const []const u8,
    holes: []const Hole,

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
) !LoadedProject {
    const context = try newContext(io, arena, read_ctx, read_fn, verify, std_root);
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
) !ProjectResult {
    const loaded = try loadProject(io, arena, root_path, root_source, read_ctx, read_fn, verify, std_root);
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
        .target_theorem_decls = counts.theorem_decls,
        .theorems_trusted = 0,
        .theorems_accelerated = counts.accelerated,
        .accelerated_names = counts.accelerated_names,
        .holes = holes.items,
    };
}

test {
    std.testing.refAllDecls(@This());
    std.testing.refAllDecls(query.outline);
    std.testing.refAllDecls(query.theorem);
    std.testing.refAllDecls(query.whereis);
    std.testing.refAllDecls(query.search);
    std.testing.refAllDecls(query.uses);
    std.testing.refAllDecls(debug.taint);
    std.testing.refAllDecls(literate);
    std.testing.refAllDecls(lint);
    // engine task-payload sub-files (their tests aren't reached by the shallow @This() ref)
    std.testing.refAllDecls(Engine.ParseTask);
    std.testing.refAllDecls(Engine.ProveTask);
    std.testing.refAllDecls(Engine.FetchTask);
    std.testing.refAllDecls(Engine.ModelTask);
}
