//! `bpa debug taint <file> [theorem]` — the acceleration (trust-entry) audit of
//! a proof: where does trust enter, if anywhere?
//!
//! Walks the parsed AST (never elaborates) and reports every step whose
//! justification rule is an **accelerated tactic** — one that, when it cannot
//! emit a certificate, falls back to a decision-procedure verdict the kernel
//! does not re-derive (and that `bpa check` rejects by default, admitting only
//! under `--fast`). Those rules are `arithmetic`, `tautology`, `polynomial`,
//! `assoc_commut`, and `assoc` (the ACCELERATION.md registry) plus the
//! quantified variants `assoc_commut_quantified` / `assoc_quantified`, which run
//! the same accelerated core. (`simplify` and `simplify_quantified` emit kernel
//! steps by construction — the certificate IS the rewrite chain — so they
//! never accelerate.)
//!
//! This is the "does my file use any accelerated tactic?" audit: it lists, per proof, the
//! `file:line` of every step that *could* be accelerated. It is a syntactic
//! upper bound — a step may still certify and stay kernel-checked — so a clean
//! report (no accelerated tactics) guarantees every step is kernel-checked, while a flagged
//! step is "check this one under a real `bpa check`". Pure over the AST, like
//! `outline`/`uses`: no elaboration.
//!
//! With a theorem argument, audits that one proof; without, audits EVERY
//! proof-carrying declaration in the file.

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

/// The accelerated tactics (ACCELERATION.md registry). A step citing one of
/// these is a potential acceleration site; every other rule is always
/// kernel-checked.
const accelerated_rules = [_][]const u8{
    "arithmetic",       "tautology",
    "polynomial",       "assoc_commut",
    "assoc",            "assoc_commut_quantified",
    "assoc_quantified", "ext",
    "ext_quantified",
};

fn isAcceleratedRule(name: []const u8) bool {
    for (accelerated_rules) |r| {
        if (std.mem.eql(u8, r, name)) return true;
    }
    return false;
}

pub fn taint(
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
        renderOne(arena, w, path, source, file, name) catch return error.OutOfMemory
    else
        renderAll(arena, w, path, source, file) catch return error.OutOfMemory;

    return .{ .text = try out.toOwnedSlice(), .ok = ok };
}

const Proof = struct { kind: []const u8, name: Token, steps: []const ast.Step };

fn asProof(decl: ast.Decl) ?Proof {
    return switch (decl) {
        .theorem => |t| switch (t) {
            .local => |l| .{ .kind = if (l.fact.params != null) "schema" else "theorem", .name = l.fact.name, .steps = l.steps },
            .alias => null,
        },
        else => null,
    };
}

/// One accelerated-tactic step: its rule and where it sits.
const Hit = struct { rule: []const u8, line: usize, col: usize };

fn renderAll(arena: Allocator, w: *std.Io.Writer, path: []const u8, source: []const u8, file: ast.File) !bool {
    var any = false;
    for (file.decls) |decl| {
        const proof = asProof(decl) orelse continue;
        var hits: std.ArrayList(Hit) = .empty;
        try collect(arena, source, proof.steps, &hits);
        if (hits.items.len == 0) continue;
        if (any) try w.writeAll("\n");
        any = true;
        try renderProof(w, path, source, proof, hits.items);
    }
    if (!any) try w.writeAll("no accelerated tactics — every step is kernel-checked\n");
    return true;
}

fn renderOne(arena: Allocator, w: *std.Io.Writer, path: []const u8, source: []const u8, file: ast.File, name: []const u8) !bool {
    for (file.decls) |decl| {
        const proof = asProof(decl) orelse continue;
        if (!std.mem.eql(u8, tokenText(source, proof.name), name)) continue;
        var hits: std.ArrayList(Hit) = .empty;
        try collect(arena, source, proof.steps, &hits);
        if (hits.items.len == 0) {
            try w.print("theorem {s}: no accelerated tactics — every step is kernel-checked\n", .{name});
        } else {
            try renderProof(w, path, source, proof, hits.items);
        }
        return true;
    }
    try w.print("error: no theorem '{s}' in this file\n", .{name});
    return false;
}

fn renderProof(w: *std.Io.Writer, path: []const u8, source: []const u8, proof: Proof, hits: []const Hit) !void {
    try w.print("{s} {s}\n", .{ proof.kind, tokenText(source, proof.name) });
    for (hits) |h| {
        try w.print("  {s}:{d}:{d}: {s}\n", .{ path, h.line, h.col, h.rule });
    }
}

fn collect(arena: Allocator, source: []const u8, steps: []const ast.Step, hits: *std.ArrayList(Hit)) !void {
    for (steps) |step| {
        switch (step.body) {
            .claim => |c| {
                const rule = tokenText(source, c.rule);
                if (isAcceleratedRule(rule)) {
                    const lc = lineCol(source, c.rule.start);
                    try hits.append(arena, .{ .rule = rule, .line = lc.line, .col = lc.col });
                }
            },
            .assume => |b| try collect(arena, source, b.steps, hits),
            .fix => |b| try collect(arena, source, b.steps, hits),
            .unpack => |b| try collect(arena, source, b.steps, hits),
            .case => |b| for (b.arms) |arm| try collect(arena, source, arm.steps, hits),
        }
    }
}

fn tokenText(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}

/// 1-based line/column of byte offset `at` (matches diagnostic coordinates).
fn lineCol(source: []const u8, at: u32) struct { line: usize, col: usize } {
    var line: usize = 1;
    var col: usize = 1;
    var i: usize = 0;
    while (i < at and i < source.len) : (i += 1) {
        if (source[i] == '\n') {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    return .{ .line = line, .col = col };
}
