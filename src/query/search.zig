//! `2b4m query search <path> <query>` — fuzzy/token search over theorem and
//! axiom names + statements. `<path>` is a directory (search every `.b4m`
//! under it — corpus discovery) or a file (search it + everything it
//! transitively imports — scope-aware, citable-from-here). Ranks by name
//! substring/token hits, then statement token overlap. One line per hit,
//! best first.
//!
//! Self-contained and deterministic — no ML/embeddings (that's a later,
//! caching-era upgrade). This module is PURE: the caller (main.zig) enumerates
//! files and reads them, passing `{path, source}` pairs here.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");
const Token = lexer.Token;

pub const File = struct { path: []const u8, source: []const u8 };
pub const Result = struct { text: []const u8, ok: bool };

const Hit = struct {
    score: i32,
    path: []const u8,
    line: usize,
    kind: []const u8,
    sig: []const u8, // one-line "kind name: formula"
};

/// Search `files` for `query`. Returns the ranked hit list as text.
pub fn search(arena: Allocator, files: []const File, query: []const u8) Allocator.Error!Result {
    const terms = try tokenize(arena, query);

    var hits: std.ArrayList(Hit) = .empty;
    for (files) |f| {
        const sink = try arena.create(diagnostics.Sink);
        sink.* = .init(arena);
        var p: parser.Parser = .init(arena, f.source, sink);
        const parsed = try p.parseFile();
        if (sink.list.items.len > 0) continue; // skip unparseable files silently

        for (parsed.decls) |decl| {
            const cand = try candidate(arena, f.source, decl) orelse continue;
            const sc = score(terms, cand.name, cand.sig);
            if (sc <= 0) continue;
            const loc = std.zig.findLineColumn(f.source, cand.name_off);
            try hits.append(arena, .{
                .score = sc,
                .path = f.path,
                .line = loc.line + 1,
                .kind = cand.kind,
                .sig = cand.sig,
            });
        }
    }

    std.mem.sort(Hit, hits.items, {}, lessThan);

    var out: std.Io.Writer.Allocating = .init(arena);
    if (hits.items.len == 0) {
        out.writer.print("no theorem or axiom matching '{s}'\n", .{query}) catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = false };
    }
    for (hits.items) |h| {
        out.writer.print("{s}:{d}:  {s}\n", .{ h.path, h.line, h.sig }) catch return error.OutOfMemory;
    }
    return .{ .text = try out.toOwnedSlice(), .ok = true };
}

fn lessThan(_: void, a: Hit, b: Hit) bool {
    if (a.score != b.score) return a.score > b.score; // higher score first
    // stable tiebreak: path then line
    const c = std.mem.order(u8, a.path, b.path);
    if (c != .eq) return c == .lt;
    return a.line < b.line;
}

const Candidate = struct { name: []const u8, name_off: u32, kind: []const u8, sig: []const u8 };

/// A searchable declaration (theorem or axiom, incl. schemas) → its name +
/// one-line signature. Others (func/pred/import/alias/…) are skipped.
fn candidate(arena: Allocator, source: []const u8, decl: ast.Decl) Allocator.Error!?Candidate {
    return switch (decl) {
        // a theorem (incl. proof-carrying schema = theorem with params); alias skipped.
        .theorem => |t| switch (t) {
            .local => |l| .{
                .name = tok(source, l.fact.name),
                .name_off = l.fact.name.start,
                .kind = "theorem",
                .sig = try stmtSig(arena, source, .keyword_theorem, tok(source, l.fact.name)),
            },
            .alias => null,
        },
        // an axiom (incl. axiom-schema = axiom with params); alias skipped.
        .axiom => |a| switch (a) {
            .local => |f| .{
                .name = tok(source, f.name),
                .name_off = f.name.start,
                .kind = "axiom",
                .sig = try stmtSig(arena, source, .keyword_axiom, tok(source, f.name)),
            },
            .alias => null,
        },
        else => null,
    };
}

/// The one-line statement `<kw> <name>: <formula>` — the keyword through the
/// token before `proof` (theorems) or before the next declaration (axioms),
/// whitespace-collapsed. Re-lexes to find the span exactly.
fn stmtSig(arena: Allocator, source: []const u8, kw: lexer.Token.Tag, name: []const u8) Allocator.Error![]const u8 {
    var toks: std.ArrayList(Token) = .empty;
    var lex: lexer.Lexer = .init(source);
    lex.keep_comments = true;
    while (true) {
        const t = lex.next();
        try toks.append(arena, t);
        if (t.tag == .eof) break;
    }
    var i: usize = 0;
    while (i + 1 < toks.items.len) : (i += 1) {
        const t = toks.items[i];
        if (t.tag != kw) continue;
        const nm = toks.items[i + 1];
        if (nm.tag != .identifier or !std.mem.eql(u8, source[nm.start..nm.end], name)) continue;
        var j = i + 1;
        var end = nm.end;
        while (j < toks.items.len) : (j += 1) {
            switch (toks.items[j].tag) {
                .keyword_proof => break,
                .keyword_import, .keyword_forward, .keyword_sort, .keyword_const, .keyword_define, .keyword_func, .keyword_pred, .keyword_axiom, .keyword_theorem, .comment, .eof => if (j > i + 1) break,
                else => end = toks.items[j].end,
            }
        }
        return collapse(arena, source[t.start..end]);
    }
    return collapse(arena, name);
}

// -- scoring ---------------------------------------------------------------

/// Higher is better. Name matches weigh most; statement token overlap adds a
/// smaller amount. Substring beats token; exact-name beats substring.
fn score(terms: []const []const u8, name: []const u8, sig: []const u8) i32 {
    if (terms.len == 0) return 0;
    var s: i32 = 0;
    for (terms) |term| {
        var hit = false;
        // exact name (case-insensitive)
        if (eqIgnoreCase(name, term)) {
            s += 100;
            hit = true;
        } else if (containsIgnoreCase(name, term)) {
            // substring of the name (e.g. "cancel" in "mulCancelLeft")
            s += 40;
            hit = true;
        }
        // token overlap with the statement (name is included in sig)
        if (containsIgnoreCase(sig, term)) {
            s += 8;
            hit = true;
        }
        if (!hit) return 0; // every query term must match somewhere (AND)
    }
    return s;
}

// -- text helpers ----------------------------------------------------------

/// Split on whitespace and camelCase/underscore boundaries → lowercase tokens.
fn tokenize(arena: Allocator, s: []const u8) Allocator.Error![]const []const u8 {
    var out: std.ArrayList([]const u8) = .empty;
    var it = std.mem.tokenizeAny(u8, s, " \t\n\r");
    while (it.next()) |w| {
        try out.append(arena, w);
    }
    return out.items;
}

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

fn tok(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}

fn lower(c: u8) u8 {
    return if (c >= 'A' and c <= 'Z') c + 32 else c;
}

fn eqIgnoreCase(a: []const u8, b: []const u8) bool {
    if (a.len != b.len) return false;
    for (a, b) |x, y| if (lower(x) != lower(y)) return false;
    return true;
}

fn containsIgnoreCase(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0) return true;
    if (needle.len > haystack.len) return false;
    var i: usize = 0;
    while (i + needle.len <= haystack.len) : (i += 1) {
        var ok = true;
        for (needle, 0..) |n, k| {
            if (lower(haystack[i + k]) != lower(n)) {
                ok = false;
                break;
            }
        }
        if (ok) return true;
    }
    return false;
}
