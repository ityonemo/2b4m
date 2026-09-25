//! `2b4m query whereis <file> <identifier>` — trace an identifier to its origin.
//!
//! Given a file and a name, follow every alias/import hop from where the name is
//! referenced to its ORIGINAL definition, printing the chain: each hop's
//! `file:line` and source line, with the final definition marked `[origin]`.
//!
//! This is the file-chase made a query: grep finds one hop (`X = ns.X`); this
//! walks the whole alias graph across files so you don't re-grep per hop. Works
//! for any named declaration (theorem/axiom/func/pred/sort/const/define/schema)
//! and for import namespaces (whose origin is the imported file itself).
//!
//! Cross-file hops go through the caller-supplied `ReadFileFn`, reusing the
//! loader's `std/`-prefix + relative path resolution.

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

pub fn whereis(
    arena: Allocator,
    path: []const u8,
    source: []const u8,
    name: []const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    std_root: []const u8,
) Allocator.Error!Result {
    var q: Query = .{ .arena = arena, .read_ctx = read_ctx, .read_fn = read_fn, .std_root = std_root };
    var out: std.Io.Writer.Allocating = .init(arena);
    q.out = &out.writer;
    q.out.print("{s}\n", .{name}) catch return error.OutOfMemory;
    const ok = q.trace(path, source, name, 0) catch return error.OutOfMemory;
    return .{ .text = try out.toOwnedSlice(), .ok = ok };
}

const Query = struct {
    arena: Allocator,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    std_root: []const u8,
    out: *std.Io.Writer = undefined,

    const max_hops = 32;

    fn err(self: *Query, comptime fmt: []const u8, args: anytype) Allocator.Error!bool {
        self.out.print("  error: " ++ fmt ++ "\n", args) catch return error.OutOfMemory;
        return false;
    }

    /// Emit one chain hop: `  <path>:<line>:  <source line>` (+ ` [origin]`).
    fn hop(self: *Query, path: []const u8, source: []const u8, tok: Token, origin: bool) Allocator.Error!void {
        const loc = std.zig.findLineColumn(source, tok.start);
        const line_text = sourceLine(source, tok.start);
        self.out.print("  {s}:{d}:  {s}{s}\n", .{
            path, loc.line + 1, line_text, if (origin) "  [origin]" else "",
        }) catch return error.OutOfMemory;
    }

    /// Follow the alias/import chain to its origin. Each hop advances at most one
    /// link, so this is LINEAR (tail) recursion — expressed here as a loop over
    /// the mutable (path, source, name) cursor, bounded by `max_hops`.
    fn trace(self: *Query, path_in: []const u8, source_in: []const u8, name_in: []const u8, depth_in: u32) Allocator.Error!bool {
        var path = path_in;
        var source = source_in;
        var name = name_in;
        var depth = depth_in;
        while (true) {
            if (depth > max_hops) return self.err("alias chain too deep", .{});

            const sink = try self.arena.create(diagnostics.Sink);
            sink.* = .init(self.arena);
            var p: parser.Parser = .init(self.arena, source, sink);
            const file = try p.parseFile();
            if (sink.list.items.len > 0) {
                const files = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
                sink.render(self.out, &files) catch return error.OutOfMemory;
                return false;
            }

            var advanced = false;
            for (file.decls) |decl| {
                const d = declName(source, decl);
                if (d == null or !std.mem.eql(u8, d.?.name, name)) continue;
                // an alias (any kind) points onward: print this hop, then follow the target.
                if (ast.aliasOf(&decl)) |a| {
                    try self.hop(path, source, a.name, false);
                    const target = tokenText(source, a.target);
                    if (std.mem.lastIndexOfScalar(u8, target, '.')) |dot| {
                        const ns = target[0..dot];
                        const local = target[dot + 1 ..];
                        const maybe_next = findImportPath(source, path, ns, self.std_root, self.arena) catch return error.OutOfMemory;
                        const next = maybe_next orelse
                            return self.err("alias target namespace '{s}' is not imported", .{ns});
                        const src = self.read_fn(self.read_ctx, self.arena, next) catch
                            return self.err("cannot open '{s}'", .{next});
                        path = next;
                        source = src;
                        name = local;
                    } else {
                        // bare target: a forward/local name in this same file.
                        name = target;
                    }
                    depth += 1;
                    advanced = true;
                    break;
                }
                switch (decl) {
                    // an import namespace: the origin IS the imported file.
                    .import => |im| {
                        const raw_quoted = tokenText(source, im.path);
                        const raw = raw_quoted[1 .. raw_quoted.len - 1];
                        const resolved = findImportPath(source, path, name, self.std_root, self.arena) catch return error.OutOfMemory;
                        try self.hop(path, source, im.ns, false);
                        self.out.print("  {s}  [origin: imported file]\n", .{resolved orelse raw}) catch return error.OutOfMemory;
                        return true;
                    },
                    // any real definition: this is the origin.
                    else => {
                        try self.hop(path, source, d.?.token, true);
                        return true;
                    },
                }
            }
            if (!advanced) return self.err("no declaration named '{s}' in {s}", .{ name, path });
        }
    }
};

const Named = struct { name: []const u8, token: Token };

/// The declared name + its token for any named decl (null for `forward`, which
/// is a manifest entry, not a definition — its real def appears elsewhere).
fn declName(source: []const u8, decl: ast.Decl) ?Named {
    if (decl == .forward) return null; // a manifest entry, not a definition
    const t = ast.declName(&decl);
    return .{ .name = source[t.start..t.end], .token = t };
}

/// Resolve import namespace `ns` to its file path (loader's rule: `std/…`
/// under std_root, else relative to the importing file's dir).
fn findImportPath(source: []const u8, path: []const u8, ns: []const u8, std_root: []const u8, arena: Allocator) !?[]const u8 {
    var lex: lexer.Lexer = .init(source);
    var prev: Token = .{ .tag = .eof, .start = 0, .end = 0 };
    var import_ns: ?[]const u8 = null;
    while (true) {
        const t = lex.next();
        if (t.tag == .eof) break;
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

/// The whole source line containing byte `off`, trimmed of trailing whitespace.
fn sourceLine(source: []const u8, off: u32) []const u8 {
    var start = off;
    while (start > 0 and source[start - 1] != '\n') start -= 1;
    var end = off;
    while (end < source.len and source[end] != '\n') end += 1;
    return std.mem.trimEnd(u8, source[start..end], " \t\r");
}
