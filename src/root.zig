//! bpa core library. All proof-checking logic is exposed from here;
//! src/main.zig is a thin CLI wrapper.

const std = @import("std");

pub const lexer = @import("lexer.zig");
pub const ast = @import("ast.zig");
pub const parser = @import("parser.zig");
pub const diagnostics = @import("diagnostics.zig");
pub const intern = @import("intern.zig");
pub const term = @import("term.zig");
pub const env = @import("env.zig");
pub const elaborate = @import("elaborate.zig");
pub const Verify = elaborate.Verify;
pub const engine = @import("engine.zig");
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

    const interner = try arena.create(intern.Interner);
    interner.* = .init(arena);
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

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8;

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

/// raw-import-path StrId -> resolved child FileId, for one file.
const ImportMap = std.AutoHashMapUnmanaged(intern.StrId, env.FileId);

const Loader = struct {
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
    fn discover(self: *Loader, resolved_path: []const u8, source: []const u8) !env.FileId {
        const file_id = try self.environment.newFile();
        std.debug.assert(@intFromEnum(file_id) == self.files.items.len);
        try self.files.append(self.arena, .{ .path = resolved_path, .source = source });
        try self.parsed.append(self.arena, .{ .decls = &.{} });
        try self.import_maps.append(self.arena, .{});
        try self.by_path.put(self.arena, resolved_path, file_id);
        return file_id;
    }

    // -- PHASE A: engine-driven parse ---------------------------------------------
    // The task payload: the file to parse. FileId + source are already assigned/read at
    // discovery time (so the child's id exists before its parse runs — cyclic-import
    // safe). Parse fills `parsed[fid]`, resolves imports, and RACKS a parse task for each
    // newly-discovered import.
    const ParseTask = struct { file_id: env.FileId, source: []const u8, path: []const u8 };
    const ParseEngine = engine.Engine(Loader, ParseTask, std.mem.Allocator.Error);

    /// Run one parse task: parse the file, resolve its imports (discovering + racking
    /// child parse tasks), and record its import map. TRANSITIONAL: parse follows
    /// imports here only because the eager elaborator back-end (phase B) needs the whole
    /// transitive file set present. In the target demand-driven design, the PROVER pulls
    /// a file in when it cites into it; this import-following goes away then.
    fn runParse(self: *Loader, task: ParseTask, h: *ParseEngine.Handle) std.mem.Allocator.Error!void {
        const idx = @intFromEnum(task.file_id);
        self.sink.current_file = idx;
        var p: parser.Parser = .init(self.arena, task.source, self.sink);
        const parsed = try p.parseFile();
        self.parsed.items[idx] = parsed;
        self.declarations += parsed.decls.len;

        for (parsed.decls) |decl| {
            if (decl != .import) continue;
            const d = decl.import;
            const raw_quoted = task.source[d.path.start..d.path.end];
            const raw = raw_quoted[1 .. raw_quoted.len - 1];
            const resolved = if (std.mem.startsWith(u8, raw, "std/"))
                try std.fs.path.resolve(self.arena, &.{ self.std_root, raw["std/".len..] })
            else
                try std.fs.path.resolve(self.arena, &.{ std.fs.path.dirname(task.path) orelse ".", raw });

            const child: env.FileId = if (self.by_path.get(resolved)) |existing|
                existing // already discovered (incl. a cyclic re-reference) — reuse id
            else child: {
                const src = self.read_fn(self.read_ctx, self.arena, resolved) catch {
                    self.sink.current_file = idx;
                    try self.sink.add(d.path.start, "cannot open '{s}': file not found", .{resolved});
                    continue;
                };
                const cid = try self.discover(resolved, src);
                try h.rack(.{ .payload = .{ .file_id = cid, .source = src, .path = resolved }, .run = &runParseThunk });
                break :child cid;
            };
            const raw_id = try self.interner.intern(raw);
            try self.import_maps.items[idx].put(self.arena, raw_id, child);
        }
    }
    fn runParseThunk(ctx: *Loader, payload: ParseTask, h: *ParseEngine.Handle) std.mem.Allocator.Error!void {
        return ctx.runParse(payload, h);
    }

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
    fn run(self: *Loader, root_path: []const u8, root_source: []const u8) !env.FileId {
        self.root_file = try self.discover(root_path, root_source);
        var eng = ParseEngine.init(self.arena, self);
        try eng.rack(.{ .payload = .{ .file_id = self.root_file, .source = root_source, .path = root_path }, .run = &runParseThunk });
        try eng.run(); // parse phase to quiescence
        try self.elaborateAll(); // elaborate phase in dependency order
        return self.root_file;
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
    interner: *intern.Interner,
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
    const interner = try arena.create(intern.Interner);
    interner.* = .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const environment = try arena.create(env.Env);
    environment.* = try .init(arena, interner);

    var loader: Loader = .{
        .arena = arena,
        .sink = sink,
        .interner = interner,
        .pool = pool,
        .environment = environment,
        .read_ctx = read_ctx,
        .read_fn = read_fn,
        .verify = verify,
        .std_root = std_root,
    };
    const canonical_root = try std.fs.path.resolve(arena, &.{root_path});
    const root_file = try loader.run(canonical_root, root_source);
    return .{
        .interner = interner,
        .pool = pool,
        .environment = environment,
        .sink = sink,
        .root_file = root_file,
        .files = loader.files.items,
        .declarations = loader.declarations,
    };
}

pub fn checkProject(
    arena: std.mem.Allocator,
    root_path: []const u8,
    root_source: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    verify: elaborate.Verify,
    std_root: []const u8,
) !ProjectResult {
    const loaded = try loadProject(arena, root_path, root_source, read_ctx, read_fn, verify, std_root);
    const sink = loaded.sink;
    const interner = loaded.interner;
    const environment = loaded.environment;
    const root_file = loaded.root_file;
    const loader = struct { files: []const diagnostics.FileSrc, declarations: usize }{ .files = loaded.files, .declarations = loaded.declarations };

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
                    const s = interner.str(o);
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
                    try dependents.append(arena, interner.str(dep.theorem.name));
                    break;
                }
            }
        }
        const src = loader.files[@intFromEnum(h.file)].source;
        var line: usize = 1;
        for (src[0..@min(h.loc, src.len)]) |ch| {
            if (ch == '\n') line += 1;
        }
        try holes.append(arena, .{
            .name = interner.str(h.name),
            .path = loader.files[@intFromEnum(h.file)].path,
            .line = line,
            .dependents = dependents.items,
        });
    }
    return .{
        .files = loader.files,
        .sink = sink,
        .declarations = loader.declarations,
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
}
