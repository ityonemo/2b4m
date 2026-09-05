//! `bpa query outline <file> [theorem]` — the structural skeleton of a proof.
//!
//! Walks the parsed AST (never elaborates) and prints, per proof, one line per
//! step: the bare label, and — only for steps that OPEN A NESTING BLOCK — a
//! trailing header naming what the block introduces:
//!   fix k
//!   assume <formula>
//!   unpack u from <source>
//!   case <disj>            (each arm: `<label> assume <formula>`)
//! Plain claim steps (modus_ponens, rewrite, forall_elim, axiom, …) are bare
//! labels: no rule, no refs, no formula. Nesting is shown by indentation
//! (2 spaces per block level).
//!
//! With a theorem argument, outlines that one proof; without, outlines EVERY
//! proof-carrying declaration in the file (theorems + proof-carrying schemas).
//!
//! Rendering reuses the source text directly: a formula's surface syntax is the
//! slice of `source` spanning its tokens, whitespace-collapsed — so headers read
//! exactly as written, without a separate pretty-printer.

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

/// Parse `source` and render the outline. On a parse error, `ok` is false and
/// `text` is the rendered diagnostics (same `path:line:col: error:` form as
/// `bpa check`). `theorem` null => outline every proof in the file.
pub fn outline(
    arena: Allocator,
    path: []const u8,
    source: []const u8,
    theorem: ?[]const u8,
) Allocator.Error!Result {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);

    var p: parser.Parser = .init(arena, source, sink);
    const file = try p.parseFile();

    var out: std.Io.Writer.Allocating = .init(arena);
    const w = &out.writer;

    if (sink.list.items.len > 0) {
        const files = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
        sink.render(w, &files) catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = false };
    }

    const ok = if (theorem) |name|
        renderOne(arena, w, source, file, name) catch return error.OutOfMemory
    else
        renderAll(arena, w, source, file) catch return error.OutOfMemory;

    return .{ .text = try out.toOwnedSlice(), .ok = ok };
}

/// A proof-carrying declaration, uniformly: theorems and proof-carrying schemas.
const Proof = struct { kind: []const u8, name: Token, steps: []const ast.Step };

fn asProof(decl: ast.Decl) ?Proof {
    return switch (decl) {
        // a theorem carries a proof; a proof-carrying schema is just a theorem with params.
        .theorem => |t| switch (t) {
            .local => |l| .{ .kind = if (l.fact.params != null) "schema" else "theorem", .name = l.fact.name, .steps = l.steps },
            .alias => null,
        },
        else => null,
    };
}

// -- every proof in the file (no theorem argument) --------------------------

fn renderAll(arena: Allocator, w: *std.Io.Writer, source: []const u8, file: ast.File) !bool {
    var first = true;
    for (file.decls) |decl| {
        const proof = asProof(decl) orelse continue;
        if (!first) try w.writeAll("\n");
        first = false;
        try renderProof(arena, w, source, proof);
    }
    return true;
}

// -- one named proof --------------------------------------------------------

fn renderOne(arena: Allocator, w: *std.Io.Writer, source: []const u8, file: ast.File, name: []const u8) !bool {
    for (file.decls) |decl| {
        const proof = asProof(decl) orelse continue;
        if (std.mem.eql(u8, tokenText(source, proof.name), name)) {
            try renderProof(arena, w, source, proof);
            return true;
        }
    }
    try w.print("error: no theorem '{s}' in this file\n", .{name});
    return false;
}

fn renderProof(arena: Allocator, w: *std.Io.Writer, source: []const u8, proof: Proof) !void {
    try w.print("{s} {s}\n", .{ proof.kind, tokenText(source, proof.name) });
    for (proof.steps) |step| try renderStep(arena, w, source, step, 1);
}

fn renderStep(arena: Allocator, w: *std.Io.Writer, source: []const u8, step: ast.Step, depth: u32) !void {
    try w.splatByteAll(' ', depth * 2);
    try w.writeAll(tokenText(source, step.label));
    switch (step.body) {
        .claim => {
            // a bare label — no rule, refs, or formula
            try w.writeAll("\n");
        },
        .fix => |b| {
            try w.print("  fix {s}\n", .{tokenText(source, b.name)});
            for (b.steps) |s| try renderStep(arena, w, source, s, depth + 1);
        },
        .assume => |b| {
            try w.print("  assume {s}\n", .{try formulaText(arena, source, b.formula)});
            for (b.steps) |s| try renderStep(arena, w, source, s, depth + 1);
        },
        .unpack => |b| {
            try w.print("  unpack {s} from {s}\n", .{
                tokenText(source, b.name), tokenText(source, b.from),
            });
            for (b.steps) |s| try renderStep(arena, w, source, s, depth + 1);
        },
        .case => |b| {
            try w.print("  case {s}\n", .{tokenText(source, b.disj)});
            // each arm is its own scope: a header line + its own steps, so a
            // multi-statement arm (or a nested block inside one) stays legible.
            for (b.arms) |arm| {
                try w.splatByteAll(' ', (depth + 1) * 2);
                try w.print("{s}  assume {s}\n", .{
                    tokenText(source, arm.label), try formulaText(arena, source, arm.assumption),
                });
                for (arm.steps) |s| try renderStep(arena, w, source, s, depth + 2);
            }
        },
    }
}

// -- source-span rendering ---------------------------------------------------

fn tokenText(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}

/// Surface syntax of a formula: the source slice spanning all its tokens, with
/// internal runs of whitespace/newlines collapsed to a single space. Faithful
/// to what was written, no pretty-printer needed.
///
/// The AST stores only content tokens, not the structural `(`/`)` around a call
/// or explicit-paren group — so the token span can omit a trailing `)` (a
/// call's close) or a leading `(` (a wrapping group). Rebalance by scanning the
/// source outward: consume one `)` forward per unmatched `(`, and one `(`
/// backward per unmatched `)`.
fn formulaText(arena: Allocator, source: []const u8, e: *const ast.Expr) ![]const u8 {
    var lo: u32 = std.math.maxInt(u32);
    var hi: u32 = 0;
    spanExpr(e, &lo, &hi);

    var opens: i32 = 0;
    for (source[lo..hi]) |c| {
        if (c == '(') opens += 1;
        if (c == ')') opens -= 1;
    }
    // more `(` than `)` inside: close them by walking forward.
    while (opens > 0 and hi < source.len) : (hi += 1) {
        if (source[hi] == ')') opens -= 1;
    }
    // more `)` than `(` inside: open them by walking backward.
    while (opens < 0 and lo > 0) {
        lo -= 1;
        if (source[lo] == '(') opens += 1;
    }
    return collapse(arena, source[lo..hi]);
}

fn spanTok(t: Token, lo: *u32, hi: *u32) void {
    if (t.start < lo.*) lo.* = t.start;
    if (t.end > hi.*) hi.* = t.end;
}

fn spanExpr(e: *const ast.Expr, lo: *u32, hi: *u32) void {
    switch (e.*) {
        .name => |t| spanTok(t, lo, hi),
        .call => |c| {
            spanTok(c.callee, lo, hi);
            for (c.args) |a| spanExpr(a, lo, hi);
        },
        .binary => |b| {
            spanTok(b.tok, lo, hi);
            spanExpr(b.lhs, lo, hi);
            spanExpr(b.rhs, lo, hi);
        },
        .not => |n| {
            spanTok(n.tok, lo, hi);
            spanExpr(n.operand, lo, hi);
        },
        .quant => |q| {
            spanTok(q.tok, lo, hi);
            for (q.binders) |b| {
                spanTok(b.name, lo, hi);
                spanTok(b.sort, lo, hi);
            }
            spanExpr(q.body, lo, hi);
        },
        .lambda => |l| {
            spanTok(l.tok, lo, hi);
            for (l.binders) |b| {
                spanTok(b.name, lo, hi);
                spanTok(b.sort, lo, hi);
            }
            spanExpr(l.body, lo, hi);
        },
    }
}

/// Collapse internal whitespace runs (incl. newlines from a wrapped formula) to
/// single spaces; trim ends. Arena-allocated.
fn collapse(arena: Allocator, s: []const u8) ![]const u8 {
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
