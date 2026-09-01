//! bpa core library. All proof-checking logic is exposed from here;
//! src/main.zig is a thin CLI wrapper.

const std = @import("std");

pub const lexer = @import("lexer.zig");
pub const ast = @import("ast.zig");
pub const parser = @import("parser.zig");
pub const diagnostics = @import("diagnostics.zig");
pub const InternPool = @import("InternPool.zig");
pub const FactKV = @import("FactKV.zig");
pub const IdentKV = @import("IdentKV.zig");
pub const term = @import("term.zig");
pub const env = @import("env.zig");
pub const elaborate = @import("elaborate.zig");
pub const Verify = elaborate.Verify;
pub const Engine = @import("Engine.zig");
pub const Context = @import("Context.zig");
pub const Prover = @import("Engine/ProveTask/Prover.zig");
pub const print = @import("print.zig");
pub const kernel = @import("kernel.zig");
pub const fmt = @import("fmt.zig");
pub const literate = @import("literate.zig");
pub const lint = @import("lint.zig");
pub const simplify = @import("simplify.zig");
pub const smt = @import("accelerant/arithmetic/smt.zig");
pub const presburger = @import("accelerant/arithmetic/presburger.zig");
pub const farkas = @import("accelerant/arithmetic/farkas.zig");

pub const query = @import("query.zig");
pub const debug = @import("debug.zig");

pub const CheckResult = struct {
    file: ast.File,
    sink: *diagnostics.Sink,
    declarations: usize,
    theorems_proven: usize,

    pub fn ok(self: *const CheckResult) bool {
        return self.sink.list.items.len == 0;
    }
};

/// Check a .bpa source. All allocations go into `arena`; diagnostics are
/// collected in the result's sink (rendered by the caller).
pub fn checkSource(arena: std.mem.Allocator, source: []const u8) !CheckResult {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);

    var p: parser.Parser = .init(arena, source, sink);
    const file = try p.parseFile();

    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const environment = try arena.create(env.Env);
    environment.* = try .init(arena, interner);
    const file_id = try environment.newFile();

    var elab: elaborate.Elaborator = .init(arena, source, interner, pool, environment, sink, file_id);
    try elab.elaborateFile(file);

    var proven: usize = 0;
    for (environment.statements.items) |stmt| {
        // synthetic `model`-materialized theorems are machinery, not authored —
        // suppressed from the user-facing count.
        if (stmt == .theorem and stmt.theorem.proven and !stmt.theorem.synthetic) proven += 1;
    }
    return .{
        .file = file,
        .sink = sink,
        .declarations = file.decls.len,
        .theorems_proven = proven,
    };
}

// --- multi-file checking (imports) ---

pub const ReadFileFn = @import("Context.zig").ReadFileFn;

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
    theorems_trusted: usize,
    /// count of proven theorems that leaned on an accelerated tactic (the rest
    /// are just proven — no bucket). Disclosed in the summary.
    theorems_accelerated: usize,
    /// distinct accelerated-tactic names across accelerated theorems, first-use order
    accelerated_names: []const []const u8,
    /// every declared `hole`, each with where it sits and which theorems rest on
    /// it (transitively). Default mode rejects a nonempty list; --draft allows.
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

/// Check a root file and everything it imports. `verify` selects which layers
/// are actually verified (default: everything). When `verify.recheck_imports`
/// is false, imported files contribute their declarations but their proofs are
/// TRUSTED, not re-checked.
/// The elaborated project state: the shared interner/pool/env after loading the
/// root file and all its imports (imports resolved, synthetics materialized).
/// Returned by `loadProject` for tools that must READ the elaboration result
/// rather than just count it — e.g. `bpa debug accelerant`, which reads a
/// synthetic theorem (only created during elaboration) out of `environment`, and
/// needs imports loaded so cited statements resolve (incl. nested/recursive
/// synthetics like a `model` materialization citing another).
pub const LoadedProject = struct {
    interner: *InternPool,
    pool: *term.Pool,
    environment: *env.Env,
    sink: *diagnostics.Sink,
    root_file: env.FileId,
    files: []const diagnostics.FileSrc,
    declarations: usize,
};

/// Run the multi-file loader (imports depth-first, same as `checkProject`) and
/// hand back the elaborated env. `checkProject` is this + the count/hole summary.
pub fn loadProject(
    io: std.Io,
    arena: std.mem.Allocator,
    root_path: []const u8,
    root_source: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    verify: elaborate.Verify,
    std_root: []const u8,
) !LoadedProject {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const environment = try arena.create(env.Env);
    environment.* = try .init(arena, interner);

    var context: Context = .{
        .arena = arena,
        .io = io,
        .sink = sink,
        .interner = interner,
        .facts = .init(interner),
        .idents = .init(interner),
        .pool = pool,
        .environment = environment,
        .read_ctx = read_ctx,
        .read_fn = read_fn,
        .verify = verify,
        .std_root = std_root,
    };
    const canonical_root = try std.fs.path.resolve(arena, &.{root_path});
    const root_file = try context.loadProject(canonical_root, root_source);
    return .{
        .interner = interner,
        .pool = pool,
        .environment = environment,
        .sink = sink,
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
    verify: elaborate.Verify,
    std_root: []const u8,
) !ProjectResult {
    const loaded = try loadProject(io, arena, root_path, root_source, read_ctx, read_fn, verify, std_root);
    const sink = loaded.sink;
    const interner = loaded.interner;
    const environment = loaded.environment;
    const root_file = loaded.root_file;
    const loaded_view = struct { files: []const diagnostics.FileSrc, declarations: usize }{ .files = loaded.files, .declarations = loaded.declarations };

    var proven: usize = 0;
    var trusted: usize = 0;
    var accelerated: usize = 0;
    var target_theorem_decls: usize = 0;
    var accelerated_names: std.ArrayList([]const u8) = .empty;
    for (environment.statements.items) |stmt| {
        if (stmt != .theorem) continue;
        // synthetic `model`-materialized theorems are machinery, not authored.
        if (stmt.theorem.synthetic) continue;
        // count authored theorem DECLARATIONS in the target file (proven or not)
        // — the signal for "this file had something to prove".
        if (stmt.theorem.file == root_file) target_theorem_decls += 1;
        // a trusted import IS proven (it was proven in its own file; --faster/
        // --reckless just skipped re-checking it here) — so it counts toward
        // `proven`, with `trusted` as the disclosed subset.
        if (stmt.theorem.trusted) {
            proven += 1;
            trusted += 1;
        } else if (stmt.theorem.proven) {
            proven += 1;
            // a theorem that leaned on any accelerated tactic is disclosed; one
            // proved with no accelerated tactic is just proven (no bucket).
            if (stmt.theorem.accelerated.len != 0) {
                accelerated += 1;
                outer: for (stmt.theorem.accelerated) |o| {
                    const s = interner.stringBytes(o);
                    for (accelerated_names.items) |seen| {
                        if (std.mem.eql(u8, seen, s)) continue :outer;
                    }
                    try accelerated_names.append(arena, s);
                }
            }
        }
    }
    // enumerate holes: each `hole` decl (an axiom-kind Fact with is_hole), with
    // its location and the theorems that transitively rest on it.
    var holes: std.ArrayList(ProjectResult.Hole) = .empty;
    for (environment.statements.items) |stmt| {
        if (stmt != .axiom or !stmt.axiom.is_hole) continue;
        const h = stmt.axiom;
        var dependents: std.ArrayList([]const u8) = .empty;
        for (environment.statements.items) |dep| {
            if (dep != .theorem) continue;
            for (dep.theorem.holes) |hn| {
                if (hn == h.name) {
                    try dependents.append(arena, interner.stringBytes(dep.theorem.name));
                    break;
                }
            }
        }
        const src = loaded_view.files[@intFromEnum(h.file)].source;
        var line: usize = 1;
        for (src[0..@min(h.loc, src.len)]) |ch| {
            if (ch == '\n') line += 1;
        }
        try holes.append(arena, .{
            .name = interner.stringBytes(h.name),
            .path = loaded_view.files[@intFromEnum(h.file)].path,
            .line = line,
            .dependents = dependents.items,
        });
    }
    return .{
        .files = loaded_view.files,
        .sink = sink,
        .declarations = loaded_view.declarations,
        .theorems_proven = proven,
        .target_theorem_decls = target_theorem_decls,
        .theorems_trusted = trusted,
        .theorems_accelerated = accelerated,
        .accelerated_names = accelerated_names.items,
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
    std.testing.refAllDecls(debug.accelerant);
    std.testing.refAllDecls(debug.taint);
    std.testing.refAllDecls(literate);
    std.testing.refAllDecls(lint);
    // engine task-payload sub-files (their tests aren't reached by the shallow @This() ref)
    std.testing.refAllDecls(Engine.ParseTask);
    std.testing.refAllDecls(Engine.ProveTask);
    std.testing.refAllDecls(Engine.FetchTask);
}
