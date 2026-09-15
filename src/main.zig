//! bpa CLI: `bpa check <file.bpa>`.

const std = @import("std");
const Io = std.Io;
const bpa = @import("bpa");

// User program, not a library: io lives in a global for convenience.
pub var io: Io = undefined;

fn fail(comptime fmt: []const u8, args: anytype) u8 {
    var buf: [512]u8 = undefined;
    var fw: Io.File.Writer = .init(.stderr(), io, &buf);
    const err = &fw.interface;
    err.print(fmt, args) catch {};
    err.flush() catch {};
    return 1;
}

/// `bpa fmt [--check] <file>`: whitespace/indentation normalizer.
/// In place by default; --check reports (exit 1) instead of rewriting.
fn fmtCommand(arena: std.mem.Allocator, rest: []const [:0]const u8) !u8 {
    var check_only = false;
    var path: ?[]const u8 = null;
    for (rest) |arg| {
        if (std.mem.eql(u8, arg, "--check")) {
            check_only = true;
        } else if (path == null) {
            path = arg;
        } else {
            return fail("usage: bpa fmt [--check] <file.bpa|.md>\n", .{});
        }
    }
    const p = path orelse return fail("usage: bpa fmt [--check] <file.bpa|.md>\n", .{});

    const source = Io.Dir.cwd().readFileAlloc(io, p, arena, .limited(64 << 20)) catch |e| switch (e) {
        error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{p}),
        else => return fail("error: cannot open '{s}': {t}\n", .{ p, e }),
    };
    // A `.md` is a literate document: reformat only the ```bpa blocks, leaving
    // prose verbatim. A `.bpa` is formatted whole.
    const formatted = if (std.mem.endsWith(u8, p, ".md"))
        try bpa.literate.formatLiterate(arena, source)
    else
        try bpa.fmt.format(arena, source);
    if (std.mem.eql(u8, source, formatted)) return 0;
    if (check_only) {
        return fail("{s}: not formatted\n", .{p});
    }
    try Io.Dir.cwd().writeFile(io, .{ .sub_path = p, .data = formatted });
    return 0;
}

/// `bpa lint <file>`: convention checks (binder order, later casing/labels).
/// Reports violations with locations; exit 1 if any (or a parse error). Reads
/// `.md` through the literate extractor and tells the linter the input was
/// literate so source-mirroring rules stay suspended.
fn lintCommand(arena: std.mem.Allocator, rest: []const [:0]const u8) !u8 {
    var path: ?[]const u8 = null;
    for (rest) |arg| {
        if (path == null) path = arg else return fail("usage: bpa lint <file.bpa|.md>\n", .{});
    }
    const p = path orelse return fail("usage: bpa lint <file.bpa|.md>\n", .{});
    const is_literate = std.mem.endsWith(u8, p, ".md");
    const source = readSource(arena, p) catch |e| switch (e) {
        error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{p}),
        else => return fail("error: cannot open '{s}': {t}\n", .{ p, e }),
    };
    const result = try bpa.lint.lint(arena, p, source, is_literate);
    return emitQuery(result.text, result.ok);
}

/// `bpa debug accelerant <file> <line>` | `<file> <theorem> <step-label>`: reprint the
/// synthetic theorem the named accelerant step produced, as re-parseable bpa source. Reads
/// `.md` through the literate extractor.
const debug_usage =
    "usage: bpa debug accelerant <file> <line>\n" ++
    "       bpa debug accelerant <file> <theorem> <step-label>\n" ++
    "       bpa debug taint <file> [theorem]\n";

/// `bpa debug <op>` — proof-machinery introspection.
///   accelerant — reprint the synthetic theorem an accelerated step produced.
///   taint      — per proof, every accelerated step at its file:line:col.
fn debugCommand(arena: std.mem.Allocator, std_root: []const u8, rest: []const [:0]const u8) !u8 {
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "accelerant")) {
        if (rest.len < 3) return fail(debug_usage, .{});
        const p = rest[1];
        const selector: bpa.debug.accelerant.Selector = if (rest.len == 3)
            (if (std.fmt.parseInt(usize, rest[2], 10)) |ln| .{ .line = ln } else |_| return fail(debug_usage, .{}))
        else if (rest.len == 4)
            .{ .step = .{ .theorem = rest[2], .label = rest[3] } }
        else
            return fail(debug_usage, .{});
        const source = readSource(arena, p) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{p}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ p, e }),
        };
        const result = try bpa.debug.accelerant.accelerant(io, arena, p, source, selector, null, readRaw, std_root);
        return emitQuery(result.text, result.ok);
    }
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "taint")) {
        if (rest.len < 2 or rest.len > 3) return fail(debug_usage, .{});
        const path = rest[1];
        const thm: ?[]const u8 = if (rest.len == 3) rest[2] else null;
        const source = readSource(arena, path) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{path}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ path, e }),
        };
        const result = try bpa.debug.taint.taint(arena, path, source, thm);
        return emitQuery(result.text, result.ok);
    }
    return fail(debug_usage, .{});
}

const query_usage =
    "usage: bpa query outline <file.bpa> [theorem]\n" ++
    "       bpa query claims <file.bpa> [theorem]\n" ++
    "       bpa query theorem <file.bpa> <theorem> [--sig]\n" ++
    "       bpa query whereis <file.bpa> <identifier>\n" ++
    "       bpa query search <file.bpa|dir> <query>\n" ++
    "       bpa query uses <file.bpa> [theorem]\n";

/// Print a query op's result (stdout when ok, stderr otherwise) and map to an
/// exit code.
fn emitQuery(text: []const u8, ok: bool) !u8 {
    var buf: [4096]u8 = undefined;
    const stream: Io.File = if (ok) .stdout() else .stderr();
    var fw: Io.File.Writer = .init(stream, io, &buf);
    const w = &fw.interface;
    try w.writeAll(text);
    try w.flush();
    return if (ok) 0 else 1;
}

fn readFile(arena: std.mem.Allocator, path: []const u8) ![]const u8 {
    return Io.Dir.cwd().readFileAlloc(io, path, arena, .limited(64 << 20)) catch |e| switch (e) {
        error.FileNotFound => return error.FileNotFound,
        else => return e,
    };
}

/// Read a file as bpa SOURCE: a `.md` is a literate document, so extract its
/// ```bpa blocks (prose masked, offsets preserved). Used by `check` and the
/// `query` commands so both operate on the same extracted source.
fn readSource(arena: std.mem.Allocator, path: []const u8) ![]const u8 {
    const raw = try readFile(arena, path);
    if (std.mem.endsWith(u8, path, ".md")) return bpa.literate.extract(arena, raw);
    return raw;
}

/// `bpa query <op> …` — read-only inspection.
///   outline <file> [theorem]  — proof skeleton (labels + block headers)
///   claims  <file> [theorem]  — proof skeleton (claim formulas, label-free)
///   theorem <file> <name>     — full source of a theorem (aliases followed)
fn queryCommand(arena: std.mem.Allocator, std_root: []const u8, rest: []const [:0]const u8) !u8 {
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "outline")) {
        if (rest.len < 2 or rest.len > 3) return fail(query_usage, .{});
        const path = rest[1];
        const thm: ?[]const u8 = if (rest.len == 3) rest[2] else null;
        const source = readSource(arena, path) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{path}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ path, e }),
        };
        const result = try bpa.query.outline.outline(arena, path, source, thm);
        return emitQuery(result.text, result.ok);
    }
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "claims")) {
        if (rest.len < 2 or rest.len > 3) return fail(query_usage, .{});
        const path = rest[1];
        const thm: ?[]const u8 = if (rest.len == 3) rest[2] else null;
        const source = readSource(arena, path) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{path}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ path, e }),
        };
        const result = try bpa.query.claims.claims(arena, path, source, thm);
        return emitQuery(result.text, result.ok);
    }
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "theorem")) {
        // `query theorem <file> <name> [--sig]` — --sig prints just the
        // statement (kind + name + formula, one line), no proof body.
        var sig_only = false;
        var path: ?[]const u8 = null;
        var name: ?[]const u8 = null;
        for (rest[1..]) |arg| {
            if (std.mem.eql(u8, arg, "--sig")) {
                sig_only = true;
            } else if (path == null) {
                path = arg;
            } else if (name == null) {
                name = arg;
            } else {
                return fail(query_usage, .{});
            }
        }
        const p = path orelse return fail(query_usage, .{});
        const n = name orelse return fail(query_usage, .{});
        const source = readSource(arena, p) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{p}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ p, e }),
        };
        const result = try bpa.query.theorem.theorem(arena, p, source, n, null, queryReadFile, std_root, sig_only);
        return emitQuery(result.text, result.ok);
    }
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "whereis")) {
        if (rest.len != 3) return fail(query_usage, .{});
        const path = rest[1];
        const ident = rest[2];
        const source = readSource(arena, path) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{path}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ path, e }),
        };
        const result = try bpa.query.whereis.whereis(arena, path, source, ident, null, queryReadFile, std_root);
        return emitQuery(result.text, result.ok);
    }
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "uses")) {
        if (rest.len < 2 or rest.len > 3) return fail(query_usage, .{});
        const path = rest[1];
        const thm: ?[]const u8 = if (rest.len == 3) rest[2] else null;
        const source = readSource(arena, path) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{path}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ path, e }),
        };
        const result = try bpa.query.uses.uses(arena, path, source, thm);
        return emitQuery(result.text, result.ok);
    }
    if (rest.len >= 1 and std.mem.eql(u8, rest[0], "search")) {
        if (rest.len != 3) return fail(query_usage, .{});
        const path = rest[1];
        const q = rest[2];
        const files = collectSearchFiles(arena, path, std_root) catch |e| switch (e) {
            error.FileNotFound => return fail("error: cannot open '{s}': not found\n", .{path}),
            else => return fail("error: cannot open '{s}': {t}\n", .{ path, e }),
        };
        const result = try bpa.query.search.search(arena, files, q);
        return emitQuery(result.text, result.ok);
    }
    return fail(query_usage, .{});
}

/// Every `.bpa` and `.md` under `dir`, recursively, as paths joined onto `dir` (so diagnostics
/// print the path the user would type), sorted for a stable run order.
fn collectCheckFiles(arena: std.mem.Allocator, dir_path: []const u8) ![]const []const u8 {
    var dir = try Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer dir.close(io);
    var walker = try dir.walk(arena);
    defer walker.deinit();
    var paths: std.ArrayList([]const u8) = .empty;
    while (try walker.next(io)) |entry| {
        if (entry.kind != .file) continue;
        const is_bpa = std.mem.endsWith(u8, entry.path, ".bpa");
        const is_md = std.mem.endsWith(u8, entry.path, ".md");
        if (!(is_bpa or is_md)) continue;
        try paths.append(arena, try std.fs.path.join(arena, &.{ dir_path, entry.path }));
    }
    std.mem.sort([]const u8, paths.items, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.lessThan(u8, a, b);
        }
    }.lessThan);
    return paths.items;
}

/// Build the `{path, source}` set `query search` runs over. A DIRECTORY yields
/// its top-level `.bpa` files (corpus discovery); a FILE yields that file plus
/// everything it transitively imports (scope-aware).
fn collectSearchFiles(arena: std.mem.Allocator, path: []const u8, std_root: []const u8) ![]const bpa.query.search.File {
    const cwd = Io.Dir.cwd();
    const st = try cwd.statFile(io, path, .{});
    var files: std.ArrayList(bpa.query.search.File) = .empty;
    if (st.kind == .directory) {
        var dir = try cwd.openDir(io, path, .{ .iterate = true });
        var it = dir.iterate();
        while (try it.next(io)) |entry| {
            // `.bpa` proofs and `.md` literate documents (readSource extracts
            // the ```bpa blocks from the latter).
            const is_bpa = std.mem.endsWith(u8, entry.name, ".bpa");
            const is_md = std.mem.endsWith(u8, entry.name, ".md");
            if (entry.kind != .file or !(is_bpa or is_md)) continue;
            const full = try std.fs.path.join(arena, &.{ path, entry.name });
            const src = readSource(arena, full) catch continue;
            try files.append(arena, .{ .path = full, .source = src });
        }
        return files.items;
    }
    // a file: it + its transitive imports (BFS over import decls).
    var seen: std.StringHashMapUnmanaged(void) = .empty;
    var queue: std.ArrayList([]const u8) = .empty;
    try queue.append(arena, path);
    var qi: usize = 0;
    while (qi < queue.items.len) : (qi += 1) {
        const p = queue.items[qi];
        if (seen.contains(p)) continue;
        try seen.put(arena, p, {});
        const src = readSource(arena, p) catch continue;
        try files.append(arena, .{ .path = p, .source = src });
        for (try importPaths(arena, src, p, std_root)) |imp| {
            if (!seen.contains(imp)) try queue.append(arena, imp);
        }
    }
    return files.items;
}

/// Resolve every `import ns <<< "path"` in `source` to its file path (loader's
/// std/-prefix + relative rule).
fn importPaths(arena: std.mem.Allocator, source: []const u8, from: []const u8, std_root: []const u8) ![]const []const u8 {
    var out: std.ArrayList([]const u8) = .empty;
    var lex: bpa.lexer.Lexer = .init(source);
    var after_import = false;
    while (true) {
        const t = lex.next();
        if (t.tag == .eof) break;
        if (t.tag == .keyword_import) {
            after_import = true;
        } else if (after_import and t.tag == .string) {
            const raw = source[t.start + 1 .. t.end - 1];
            const resolved = if (std.mem.startsWith(u8, raw, "std/"))
                try std.fs.path.resolve(arena, &.{ std_root, raw["std/".len..] })
            else
                try std.fs.path.resolve(arena, &.{ std.fs.path.dirname(from) orelse ".", raw });
            try out.append(arena, resolved);
            after_import = false;
        }
    }
    return out.items;
}

/// `ReadFileFn` for cross-file alias resolution in `query theorem`.
fn queryReadFile(ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8 {
    _ = ctx;
    return readSource(arena, path);
}

pub fn main(init: std.process.Init) !u8 {
    const arena = init.arena.allocator();
    io = init.io;

    const args = try init.minimal.args.toSlice(arena);
    if (args.len == 2 and std.mem.eql(u8, args[1], "--help")) {
        var buf: [1024]u8 = undefined;
        var fw: Io.File.Writer = .init(.stdout(), io, &buf);
        const out = &fw.interface;
        try out.writeAll(
            \\bpa — a proof checker
            \\
            \\usage: bpa check [--fast | --fast-only W… | --fast-except W…] [--draft] [--axioms] [--library] <file.bpa | dir> [theorem]
            \\       bpa fmt [--check] <file.bpa|.md>
            \\       bpa lint <file.bpa|.md>
            \\       bpa debug accelerant <file> <line | theorem step-label>
            \\       bpa debug taint <file> [theorem]
            \\       bpa query outline <file.bpa> [theorem]
            \\       bpa query claims <file.bpa> [theorem]
            \\       bpa query theorem <file.bpa> <theorem> [--sig]
            \\       bpa query whereis <file.bpa> <identifier>
            \\       bpa query search <file.bpa|dir> <query>
            \\       bpa query uses <file.bpa> [theorem]
            \\
            \\check proves every theorem of the file; with a theorem name it proves
            \\only that one (and what it cites) — the rest of the file is not run.
            \\A DIRECTORY checks every .bpa and .md under it (recursively) in one
            \\pass — a fact two files cite is proved once — and prints one line.
            \\--library (a directory) additionally FAILS on any axiom declared in the
            \\directory that no theorem in it rests on: a library ships no unused
            \\assumptions.
            \\--axioms additionally reports what the proof BOTTOMS OUT IN: every
            \\axiom it transitively rests on, with the site each was declared at.
            \\A `hole` is an axiom as far as the kernel is concerned, so it is
            \\listed too and marked — which means --axioms only reaches a
            \\hole-bearing proof under --draft (default mode rejects it first).
            \\check reports every failure as
            \\  file:line:col: error: <message>
            \\on stderr (exit 1), or a summary line on stdout (exit 0).
            \\Import paths beginning "std/" resolve in the standard library
            \\($BPA_STD_DIR, default ./std).
            \\
            \\By default check VERIFIES EVERYTHING: every `using` step (an
            \\accelerant, or a model/import citation) produces a checkable
            \\certificate the kernel re-checks; `by` primitives always are.
            \\`--fast` defers that work per `using` WORD to speed up iteration
            \\(the run discloses exactly which words it admitted):
            \\  --fast            trust ALL `using` words
            \\  --fast-only W…    trust ONLY the listed words (allowlist)
            \\  --fast-except W…  trust all words EXCEPT the listed (denylist)
            \\Words are accelerant tactics (arithmetic, tautology, polynomial,
            \\simplify, …, plus their `_quantified` variants) and the engine
            \\words model / import (group word `engine`); `instantiation` is
            \\never trustable. Re-run plain `bpa check` to fully verify.
            \\
            \\fmt normalizes whitespace and indentation in place; --check
            \\reports instead of rewriting. On a literate `.md` it reformats
            \\only the ```bpa blocks, leaving prose verbatim.
            \\
            \\lint reports convention violations check ignores (they don't affect
            \\validity) — currently canonical binder order (a leading forall
            \\must bind in first-appearance order). See CONVENTIONS.md.
            \\
            \\debug accelerant reprints the synthetic theorem an accelerated step
            \\produced (statement + proof, as valid bpa that round-trips through
            \\check). Select the step by line number, or by enclosing theorem +
            \\step-label.
            \\debug taint flags, per proof, every step whose rule can fall back to
            \\an accelerated verdict (arithmetic/tautology/polynomial/assoc_commut/
            \\assoc/extensionality), at its file:line:col — where trust enters the proof; a
            \\clean report means every step is kernel-checked.
            \\
            \\query outline prints a proof's structural skeleton: one line per
            \\step (bare label), with a header on steps that open a nesting
            \\block (fix / assume / unpack / case). With no theorem argument it
            \\outlines every proof in the file.
            \\query claims is the same skeleton but shows each step's CLAIM
            \\FORMULA instead of its label — the propositions the proof
            \\establishes, label-free (block openers keep fix/assume/case headers).
            \\query theorem prints the full source of one theorem (following
            \\aliases across files to the real proof; axioms are marked).
            \\query whereis traces an identifier through every alias/import hop
            \\to its original definition (the file-chase as one command).
            \\query uses lists, per proof, the rules/tactics it invokes and the
            \\axioms/theorems/schemas it cites (its dependency audit).
            \\
        );
        try out.flush();
        return 0;
    }
    const std_root = init.environ_map.get("BPA_STD_DIR") orelse "std";
    if (args.len >= 2 and std.mem.eql(u8, args[1], "fmt")) {
        return fmtCommand(arena, args[2..]);
    }
    if (args.len >= 2 and std.mem.eql(u8, args[1], "query")) {
        return queryCommand(arena, std_root, args[2..]);
    }
    if (args.len >= 2 and std.mem.eql(u8, args[1], "lint")) {
        return lintCommand(arena, args[2..]);
    }
    if (args.len >= 2 and std.mem.eql(u8, args[1], "debug")) {
        return debugCommand(arena, std_root, args[2..]);
    }
    const usage = "usage: bpa check [--fast | --fast-only W… | --fast-except W…] [--draft] [--axioms] [--library] <file.bpa | dir> [theorem]\n       bpa fmt [--check] <file.bpa|.md>\n       bpa lint <file.bpa|.md>\n       bpa debug accelerant <file> <line | theorem step-label>\n       bpa debug taint <file> [theorem]\n       bpa query outline <file.bpa> [theorem]\n       bpa query claims <file.bpa> [theorem]\n       bpa query theorem <file.bpa> <theorem> [--sig]\n       bpa query whereis <file.bpa> <identifier>\n       bpa query search <file.bpa|dir> <query>\n       bpa query uses <file.bpa> [theorem]\n";
    if (args.len < 3 or !std.mem.eql(u8, args[1], "check")) {
        return fail(usage, .{});
    }
    // --fast TRUST FLAGS: a `using` step whose WORD is trusted is accelerated (its proof is not
    // generated/checked — the word ADMITS it via its own fast check). `by` primitives are ALWAYS
    // kernel-checked. Grammar (the three modes are mutually exclusive):
    //   --fast                 trust ALL `using` words
    //   --fast-only W…         trust ONLY the listed words (allowlist)
    //   --fast-except W…       trust all words EXCEPT the listed (denylist)
    // Words are the 17 individual `using` words plus group words `engine` and `<tactic>_all`
    // (the six tactics that have a `_quantified` variant). See src/Verify.zig `Word.parse`.
    // `--draft` (allows holes / relaxes author-hygiene; NOT a trust bypass) is orthogonal.
    const Mode = enum { none, all, only, except };
    var verify: bpa.Verify = .{};
    var draft = false;
    var axioms = false;
    var library = false;
    var mode: Mode = .none;
    var listed: bpa.Verify.Word.Set = bpa.Verify.Word.Set.initEmpty(); // the W… allow/deny list
    // Non-flag positionals: the trust WORDS (only valid with --fast-only/--fast-except), the
    // PATH (the first positional naming a .bpa/.md source), then an optional THEOREM name —
    // see `splitCheckArgs`.
    var positionals: std.ArrayList([]const u8) = .empty;
    for (args[2..]) |arg| {
        const flag: ?Mode = if (std.mem.eql(u8, arg, "--fast")) .all else if (std.mem.eql(u8, arg, "--fast-only")) .only else if (std.mem.eql(u8, arg, "--fast-except")) .except else null;
        if (flag) |m| {
            if (mode != .none) return fail("error: at most one of --fast / --fast-only / --fast-except\n", .{});
            mode = m;
        } else if (std.mem.eql(u8, arg, "--draft")) {
            draft = true;
        } else if (std.mem.eql(u8, arg, "--axioms")) {
            axioms = true;
        } else if (std.mem.eql(u8, arg, "--library")) {
            library = true;
        } else if (std.mem.startsWith(u8, arg, "--")) {
            return fail("error: unknown flag '{s}'\n{s}", .{ arg, usage });
        } else {
            try positionals.append(arena, arg);
        }
    }
    const split = bpa.splitCheckArgs(positionals.items) orelse return fail(usage, .{});
    const root_path = split.path;
    const words = split.words;
    // bare --fast (and no-fast) take no trust words; --fast-only/--fast-except require them.
    switch (mode) {
        .none, .all => if (words.len > 0) return fail(usage, .{}),
        .only, .except => if (words.len == 0) return fail("error: {s} needs at least one word (e.g. `--fast-only tautology`)\n", .{if (mode == .only) "--fast-only" else "--fast-except"}),
    }
    for (words) |wtext| {
        const set = bpa.Verify.Word.parse(wtext) orelse
            return fail("error: unknown trust word '{s}' (see `bpa check` help)\n", .{wtext});
        listed = listed.unionWith(set);
    }
    // resolve the trusted set from the mode.
    verify.trusted = switch (mode) {
        .none => bpa.Verify.Word.Set.initEmpty(),
        .all => bpa.Verify.Word.all(),
        .only => listed, // allowlist
        .except => bpa.Verify.Word.all().differenceWith(listed), // denylist
    };
    // --draft is for WIP proofs: allow holes AND relax author-hygiene checks
    // (dead steps, redundant fallbacks, …). One coarse bit read by all of them.
    verify.draft = draft;

    // the root must EXIST (a typo'd path is a usage-level error, said plainly); its bytes are
    // the engine's business — each root's ParseTask reads them, like any file's.
    const root_stat = Io.Dir.cwd().statFile(io, root_path, .{}) catch |e| switch (e) {
        error.FileNotFound => return fail("error: cannot open '{s}': file not found\n", .{root_path}),
        else => return fail("error: cannot open '{s}': {t}\n", .{ root_path, e }),
    };
    // A DIRECTORY is every `.bpa` and `.md` under it, recursively, each a root of the same
    // engine pass (a fact two of them cite is proved once). A `.md` with no bpa is a root
    // that parses to nothing. A theorem selector needs one file.
    const is_dir = root_stat.kind == .directory;
    if (library and !is_dir) return fail("error: --library checks a directory (a library is its whole file set); '{s}' is a file\n", .{root_path});
    const roots: []const bpa.Context.Root = if (is_dir) blk: {
        if (split.theorem != null) return fail("error: a theorem selects within one file; '{s}' is a directory\n", .{root_path});
        const paths = try collectCheckFiles(arena, root_path);
        if (paths.len == 0) return fail("error: no .bpa or .md files under '{s}'\n", .{root_path});
        const rs = try arena.alloc(bpa.Context.Root, paths.len);
        for (paths, rs) |pth, *r| r.* = .{ .path = pth };
        break :blk rs;
    } else &.{.{ .path = root_path, .theorem = split.theorem }};

    var result = try bpa.checkProject(io, arena, roots, null, readRaw, verify, std_root, axioms, library);
    if (!result.ok()) {
        var buf: [4096]u8 = undefined;
        var fw: Io.File.Writer = .init(.stderr(), io, &buf);
        const err = &fw.interface;
        try result.sink.render(err, result.files);
        try err.flush();
        return 1;
    }
    // Holes: aspirational placeholders. Default mode REJECTS any file that has
    // them (they are enumerated with their dependents as the reason) so a
    // hole-bearing result is never mistaken for complete; --draft allows them.
    if (result.holes.len > 0 and !draft) {
        var buf: [4096]u8 = undefined;
        var fw: Io.File.Writer = .init(.stderr(), io, &buf);
        const err = &fw.interface;
        try err.print("error: {d} hole(s) remain (default mode rejects holes; use --draft while filling them):\n", .{result.holes.len});
        for (result.holes) |h| {
            try err.print("  - {s}  ({s}:{d})", .{ h.name, h.path, h.line });
            if (h.dependents.len > 0) {
                try err.writeAll("  — rested on by: ");
                for (h.dependents, 0..) |d, i| {
                    if (i > 0) try err.writeAll(", ");
                    try err.writeAll(d);
                }
            }
            try err.writeAll("\n");
        }
        try err.flush();
        return 1;
    }
    // `--library`: a library must not ship assumptions nothing rests on. Every root-file
    // axiom no root theorem's proof reaches is an error (each named at its declaration).
    if (result.unused_axioms.len > 0) {
        var ebuf: [4096]u8 = undefined;
        var efw: Io.File.Writer = .init(.stderr(), io, &ebuf);
        const err = &efw.interface;
        try err.print("error: {d} unused axiom(s) — no theorem in the library rests on them:\n", .{result.unused_axioms.len});
        for (result.unused_axioms) |a| try err.print("  - {s}  ({s}:{d})\n", .{ a.name, a.path, a.line });
        try err.flush();
        return 1;
    }
    var buf: [256]u8 = undefined;
    var fw: Io.File.Writer = .init(.stdout(), io, &buf);
    const out = &fw.interface;
    // ONE aggregate line: a directory adds its file count.
    if (is_dir) {
        try out.print("OK: {d} files, {d} declarations, {d} theorems proven", .{ result.files_checked, result.declarations, result.theorems_proven });
    } else {
        try out.print("OK: {d} declarations, {d} theorems proven", .{ result.declarations, result.theorems_proven });
    }
    // --fast trust disclosure. When at least one step was ACTUALLY ADMITTED (a trusted `using`
    // word accepted it without a kernel-checked proof), the result is NOT fully verified — say so
    // loudly, listing HOW MANY theorems accelerated and under WHICH words (the words actually
    // admitted, not the whole trusted set). If a `--fast` set was given but NOTHING used it, the
    // run is fully verified in practice; note that so the trust flag isn't silently ignored.
    // Strict runs (no trusted set) say nothing.
    // `--axioms`: what the checked proof(s) BOTTOM OUT IN. A `hole` is an axiom to the kernel,
    // so it is listed here too and marked as one — default mode has already rejected a
    // hole-bearing run above, so a hole only reaches this report under --draft.
    if (axioms) {
        if (result.axioms.len == 0) {
            try out.writeAll("\n  — rests on no axioms");
        } else {
            try out.print("\n  — rests on {d} axiom(s):", .{result.axioms.len});
            for (result.axioms) |a| {
                try out.print("\n      {s}  ({s}:{d})", .{ a.name, a.path, a.line });
                if (a.is_hole) try out.writeAll("  — HOLE");
            }
        }
    }
    if (result.theorems_accelerated > 0) {
        try out.print("\n  \u{2014} NOT FULLY VERIFIED: {d} theorem(s) accelerated (admitted, not proved): ", .{result.theorems_accelerated});
        for (result.accelerated_names, 0..) |name, i| {
            if (i > 0) try out.writeAll(", ");
            try out.writeAll(name);
        }
    } else if (verify.trusted.count() > 0) {
        try out.print("\n  \u{2014} (--fast set given, but no step used a trusted word — fully verified)", .{});
    }
    if (result.theorems_trusted > 0) {
        try out.print(" ({d} via trusted imports)", .{result.theorems_trusted});
    }
    // --draft with holes: loud disclosure that the result rests on aspirational
    // placeholders, listing them (like the --fast banner). Exit stays 0.
    if (draft and result.holes.len > 0) {
        try out.print("\n  \u{2014} DRAFT — {d} hole(s) unfilled (aspirational; the result is conditional on them):", .{result.holes.len});
        for (result.holes) |h| {
            try out.print(" {s}", .{h.name});
        }
        try out.writeAll("; re-run `bpa check` (no --draft) once filled.");
    }
    try out.writeAll("\n");
    try out.flush();
    return 0;
}

/// The ENGINE's file reader: raw bytes. The engine's ParseTask does the literate extraction
/// itself (a `.md` root and a `.md` import are the same to it), so the CLI must NOT extract
/// here — extracting twice would blank an already-extracted source.
fn readRaw(ctx: ?*anyopaque, arena: std.mem.Allocator, path: []const u8) anyerror![]const u8 {
    _ = ctx;
    return readFile(arena, path);
}
