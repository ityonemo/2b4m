//! `bpa query theorem <file> <name>` — the full source of one theorem.
//!
//! Prints the declaration verbatim: its leading doc-comment (the contiguous
//! `//` block directly above it, blank-line-terminated), the `theorem <name>:`
//! statement, and the whole `proof … qed` body, exactly as written.
//!
//! An ALIAS (`theorem addZeroRight = peano.addZeroRight`) is a pointer, not a
//! proof, so it is RESOLVED: follow the qualified target across the import graph
//! (reusing the loader's `std/`-prefix + relative path rule) until the real
//! proof is found, and print THAT. A `forward` name resolves to its later
//! definition in the same file.
//!
//! Pure text extraction over a re-lex — never elaborates. Cross-file hops go
//! through the caller-supplied `ReadFileFn`, so the CLI owns filesystem access.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");
const Token = lexer.Token;

pub const Result = struct {
    text: []const u8,
    ok: bool,
};

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: Allocator, path: []const u8) anyerror![]const u8;

/// Resolve and render `name` from `path`. Follows aliases across files via
/// `read_fn`. `std_root` is where `std/…` imports resolve (as in the loader).
pub fn theorem(
    arena: Allocator,
    path: []const u8,
    source: []const u8,
    name: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    std_root: []const u8,
    sig_only: bool,
) Allocator.Error!Result {
    var q: Query = .{ .arena = arena, .read_ctx = read_ctx, .read_fn = read_fn, .std_root = std_root, .sig_only = sig_only };
    return q.resolve(path, source, name, 0);
}

const Query = struct {
    arena: Allocator,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    std_root: []const u8,
    /// `--sig`: emit just the statement (kind + name + formula), wrap-collapsed
    /// to one line, no doc-comment, no proof body.
    sig_only: bool = false,

    const max_hops = 32; // alias-chain depth guard (cycles / runaway)

    fn err(self: *Query, comptime fmt: []const u8, args: anytype) Allocator.Error!Result {
        return .{ .text = try std.fmt.allocPrint(self.arena, fmt ++ "\n", args), .ok = false };
    }

    fn resolve(self: *Query, path: []const u8, source: []const u8, name: []const u8, hop: u32) Allocator.Error!Result {
        if (hop > max_hops) return self.err("error: alias chain too deep resolving '{s}'", .{name});

        const sink = try self.arena.create(diagnostics.Sink);
        sink.* = .init(self.arena);
        var p: parser.Parser = .init(self.arena, source, sink);
        const file = try p.parseFile();
        if (sink.list.items.len > 0) {
            var out: std.Io.Writer.Allocating = .init(self.arena);
            const files = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
            sink.render(&out.writer, &files) catch return error.OutOfMemory;
            return .{ .text = try out.toOwnedSlice(), .ok = false };
        }

        // find the named declaration. A `theorem`/`schema` WITH a proof is the
        // real thing (print it). An `axiom` has no proof — print its statement
        // marked "axiomatic". An `alias` points elsewhere (follow it).
        for (file.decls) |decl| switch (decl) {
            // a theorem (incl. proof-carrying schema = theorem with params) prints its proof;
            // a theorem alias follows to its target.
            .theorem => |t| switch (t) {
                .local => |l| if (nameEql(source, l.fact.name, name)) return self.printSpan(source, name),
                .alias => |a| if (nameEql(source, a.name, name)) return self.follow(path, source, tokenText(source, a.target), hop),
            },
            // an axiom (incl. axiom-schema = axiom with params) is an assumption family; an
            // axiom alias follows to its target.
            .axiom => |ax| switch (ax) {
                .local => |f| if (nameEql(source, f.name, name)) return self.printAxiom(source, name),
                .alias => |a| if (nameEql(source, a.name, name)) return self.follow(path, source, tokenText(source, a.target), hop),
            },
            else => {},
        };
        return self.err("error: no theorem '{s}' in this file", .{name});
    }

    /// Follow an alias target: bare `name` => later definition in THIS file;
    /// qualified `ns.name` => resolve `ns` to its import path and recurse there.
    fn follow(self: *Query, path: []const u8, source: []const u8, target: []const u8, hop: u32) Allocator.Error!Result {
        if (std.mem.lastIndexOfScalar(u8, target, '.')) |dot| {
            const ns = target[0..dot];
            const local = target[dot + 1 ..];
            const maybe_path = findImportPath(source, path, ns, self.std_root, self.arena) catch return error.OutOfMemory;
            const import_path = maybe_path orelse
                return self.err("error: alias target namespace '{s}' is not imported", .{ns});
            const src = self.read_fn(self.read_ctx, self.arena, import_path) catch
                return self.err("error: cannot open '{s}': file not found", .{import_path});
            return self.resolve(import_path, src, local, hop + 1);
        }
        // bare target: a forward/local name — resolve within this same file.
        return self.resolve(path, source, target, hop + 1);
    }

    /// Emit the declaration's verbatim source span: leading `//` comment block
    /// through the terminating `qed` (or the target token, for a bare alias).
    /// Under `--sig`, emit just the statement (keyword → before `proof`),
    /// wrap-collapsed to one line.
    fn printSpan(self: *Query, source: []const u8, name: []const u8) Allocator.Error!Result {
        if (self.sig_only) {
            const span = try stmtSpanOf(self.arena, source, name) orelse
                return self.err("error: no theorem '{s}' in this file", .{name});
            return self.emitLine(try collapse(self.arena, source[span.start..span.end]));
        }
        const span = try spanOf(self.arena, source, name) orelse
            return self.err("error: no theorem '{s}' in this file", .{name});
        var out: std.Io.Writer.Allocating = .init(self.arena);
        out.writer.writeAll(source[span.start..span.end]) catch return error.OutOfMemory;
        out.writer.writeByte('\n') catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = true };
    }

    /// An axiom has no proof to inspect: print its verbatim statement (leading
    /// comment through the statement), prefixed with a marker so the caller
    /// knows this is a postulate, not a derivation. Under `--sig`, just the
    /// statement, one line, no marker.
    fn printAxiom(self: *Query, source: []const u8, name: []const u8) Allocator.Error!Result {
        const span = try axiomSpanOf(self.arena, source, name) orelse
            return self.err("error: no theorem '{s}' in this file", .{name});
        if (self.sig_only) {
            return self.emitLine(try collapse(self.arena, source[stmtStart(source, span.start)..span.end]));
        }
        var out: std.Io.Writer.Allocating = .init(self.arena);
        out.writer.writeAll("// axiomatic — postulated, no proof\n") catch return error.OutOfMemory;
        out.writer.writeAll(source[span.start..span.end]) catch return error.OutOfMemory;
        out.writer.writeByte('\n') catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = true };
    }

    fn emitLine(self: *Query, line: []const u8) Allocator.Error!Result {
        var out: std.Io.Writer.Allocating = .init(self.arena);
        out.writer.print("{s}\n", .{line}) catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = true };
    }
};

/// The statement span of a `theorem`/`schema`: the keyword through the token
/// just before `proof` (drops the leading doc-comment and the proof body).
fn stmtSpanOf(arena: Allocator, source: []const u8, name: []const u8) Allocator.Error!?Span {
    const toks = try lexAll(arena, source);
    var i: usize = 0;
    while (i + 1 < toks.len) : (i += 1) {
        const t = toks[i];
        if (t.tag != .keyword_theorem) continue;
        const nm = toks[i + 1];
        if (nm.tag != .identifier or !std.mem.eql(u8, source[nm.start..nm.end], name)) continue;
        var j = i + 1;
        while (j < toks.len) : (j += 1) {
            if (toks[j].tag == .keyword_proof) return .{ .start = t.start, .end = toks[j - 1].end };
        }
        return null;
    }
    return null;
}

/// For an axiom span whose `.start` is the comment-extended start, back up to
/// the `axiom` keyword so `--sig` drops the doc-comment.
fn stmtStart(source: []const u8, span_start: u32) u32 {
    // the axiom span starts at the leading comment; find the `axiom` keyword
    // after it. Scan forward for "axiom " at a line start.
    var i: usize = span_start;
    while (i + 6 <= source.len) : (i += 1) {
        if ((i == 0 or source[i - 1] == '\n') and std.mem.startsWith(u8, source[i..], "axiom ")) {
            return @intCast(i);
        }
    }
    return span_start;
}

/// Collapse internal whitespace/newline runs to single spaces; trim ends.
fn collapse(arena: Allocator, s: []const u8) Allocator.Error![]const u8 {
    var buf: std.ArrayList(u8) = .empty;
    var in_space = false;
    for (s) |c| {
        if (c == ' ' or c == '\t' or c == '\n' or c == '\r') {
            in_space = true;
            continue;
        }
        if (in_space and buf.items.len > 0) try buf.append(arena, ' ');
        in_space = false;
        try buf.append(arena, c);
    }
    return buf.toOwnedSlice(arena);
}

const Span = struct { start: u32, end: u32 };

/// The source span of `theorem <name>: … proof … qed`, extended backward over
/// the contiguous `//`-comment block directly above (stopping at a blank line).
fn spanOf(arena: Allocator, source: []const u8, name: []const u8) Allocator.Error!?Span {
    const toks = try lexAll(arena, source);
    // locate `theorem <name>` (name is the token right after the keyword)
    var i: usize = 0;
    while (i + 1 < toks.len) : (i += 1) {
        const t = toks[i];
        if (t.tag != .keyword_theorem) continue;
        const nm = toks[i + 1];
        if (nm.tag != .identifier or !std.mem.eql(u8, source[nm.start..nm.end], name)) continue;

        const start = leadingComments(source, toks, i);
        // scan forward to this theorem's `qed`. Proofs don't nest, so the first
        // `qed` after the keyword terminates it.
        var j = i + 1;
        while (j < toks.len) : (j += 1) {
            if (toks[j].tag == .keyword_qed) return .{ .start = start, .end = toks[j].end };
        }
        return null; // no qed (shouldn't happen for a parsed theorem)
    }
    return null;
}

/// The source span of a bare `axiom <name>: <formula>` (no proof body),
/// comment-extended like `spanOf`. The statement ends at the last token before
/// the next declaration keyword / comment / EOF.
fn axiomSpanOf(arena: Allocator, source: []const u8, name: []const u8) Allocator.Error!?Span {
    const toks = try lexAll(arena, source);
    var i: usize = 0;
    while (i + 1 < toks.len) : (i += 1) {
        const t = toks[i];
        if (t.tag != .keyword_axiom) continue;
        const nm = toks[i + 1];
        if (nm.tag != .identifier or !std.mem.eql(u8, source[nm.start..nm.end], name)) continue;

        const start = leadingComments(source, toks, i);
        // the statement ends just before the next top-level boundary token.
        var end = t.end;
        var j = i + 1;
        while (j < toks.len) : (j += 1) {
            switch (toks[j].tag) {
                .keyword_import, .keyword_forward, .keyword_sort, .keyword_const, .keyword_define, .keyword_func, .keyword_pred, .keyword_axiom, .keyword_theorem, .comment, .eof => break,
                else => end = toks[j].end,
            }
        }
        return .{ .start = start, .end = end };
    }
    return null;
}

/// Lex the whole source into a token array, comments kept (needed to locate the
/// leading doc-comment and the divider/strategy boundary exactly).
fn lexAll(arena: Allocator, source: []const u8) Allocator.Error![]const Token {
    var toks: std.ArrayList(Token) = .empty;
    var lex: lexer.Lexer = .init(source);
    lex.keep_comments = true;
    while (true) {
        const t = lex.next();
        try toks.append(arena, t);
        if (t.tag == .eof) break;
    }
    return toks.items;
}

/// Walk back from the `theorem` keyword token (index `kw`) over immediately
/// preceding `comment` tokens, as long as each sits on its own line with no
/// blank line between it and what follows. Returns the start offset.
fn leadingComments(source: []const u8, toks: []const Token, kw: usize) u32 {
    var start = toks[kw].start;
    var k = kw;
    while (k > 0) {
        const prev = toks[k - 1];
        if (prev.tag != .comment) break;
        // the gap between the comment's end and the current start must be a
        // single newline (no blank line) for it to be an attached doc-comment.
        if (blankLineBetween(source[prev.end..start])) break;
        start = prev.start;
        k -= 1;
    }
    return start;
}

fn blankLineBetween(gap: []const u8) bool {
    var newlines: usize = 0;
    for (gap) |c| {
        if (c == '\n') newlines += 1;
        if (newlines >= 2) return true;
    }
    return false;
}

/// Resolve an import namespace `ns` to its file path within `source`, using the
/// same rule as the loader: `std/…` targets resolve under `std_root`, others
/// relative to the importing file's directory.
fn findImportPath(source: []const u8, path: []const u8, ns: []const u8, std_root: []const u8, arena: Allocator) !?[]const u8 {
    var lex: lexer.Lexer = .init(source);
    var prev: Token = .{ .tag = .eof, .start = 0, .end = 0 };
    var import_ns: ?[]const u8 = null;
    while (true) {
        const t = lex.next();
        if (t.tag == .eof) break;
        // `import <ns> <<< "path"` — capture ns after the keyword, path after <<<
        if (prev.tag == .keyword_import and t.tag == .identifier) {
            import_ns = source[t.start..t.end];
        } else if (t.tag == .string and import_ns != null) {
            if (std.mem.eql(u8, import_ns.?, ns)) {
                const quoted = source[t.start..t.end];
                const raw = quoted[1 .. quoted.len - 1];
                if (std.mem.startsWith(u8, raw, "std/"))
                    return try std.fs.path.resolve(arena, &.{ std_root, raw["std/".len..] });
                return try std.fs.path.resolve(arena, &.{ std.fs.path.dirname(path) orelse ".", raw });
            }
            import_ns = null;
        }
        prev = t;
    }
    return null;
}

fn tokenText(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}

fn nameEql(source: []const u8, t: Token, name: []const u8) bool {
    return std.mem.eql(u8, source[t.start..t.end], name);
}
