//! `bpa query uses <file> [theorem]` — the citation/dependency audit of a proof.
//!
//! Walks the parsed AST (never elaborates) and reports, per proof, what each
//! one leans on:
//!   - **rules** — the distinct justification rules/tactics its steps invoke
//!     (`modus_ponens`, `arithmetic`, `rewrite`, `forall_elim`, …), each with a
//!     count;
//!   - **cites** — the distinct names it pulls in by `[by axiom X]`,
//!     `[by theorem Y]`, or `[by instantiate S(…)]` — i.e. the OTHER
//!     declarations this proof depends on, as opposed to its own step labels.
//!
//! This is the semantic answer to "which proofs use `assoc`?", "who cites this
//! accelerated tactic?", and "what does theorem X depend on?" — questions `grep` botches
//! because `[by …]` can wrap across lines and an alias hides the real target.
//!
//! With a theorem argument, audits that one proof; without, audits EVERY
//! proof-carrying declaration in the file. Pure over the AST — like `outline`,
//! it does not resolve names or check anything.

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

pub fn uses(
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
        .theorem => |t| switch (t) {
            .local => |l| .{ .kind = if (l.fact.params != null) "schema" else "theorem", .name = l.fact.name, .steps = l.steps },
            .alias => null,
        },
        else => null,
    };
}

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

/// A distinct name with an occurrence count, kept in first-seen order.
const Tally = struct {
    names: std.ArrayList([]const u8) = .empty,
    counts: std.ArrayList(u32) = .empty,

    fn bump(self: *Tally, arena: Allocator, name: []const u8) !void {
        for (self.names.items, 0..) |n, i| {
            if (std.mem.eql(u8, n, name)) {
                self.counts.items[i] += 1;
                return;
            }
        }
        try self.names.append(arena, name);
        try self.counts.append(arena, 1);
    }
};

fn renderProof(arena: Allocator, w: *std.Io.Writer, source: []const u8, proof: Proof) !void {
    // Collect the rule tally and the set of LOCAL step labels first — a ref is a
    // "cite" (external dependency) exactly when it is NOT one of this proof's own
    // labels. Schema names from `[by instantiate S(…)]` are always cites.
    var rules: Tally = .{};
    var cites: Tally = .{};
    var labels: std.StringHashMapUnmanaged(void) = .empty;

    collectLabels(arena, source, proof.steps, &labels) catch return error.OutOfMemory;
    walk(arena, source, proof.steps, &rules, &cites, &labels) catch return error.OutOfMemory;

    try w.print("{s} {s}\n", .{ proof.kind, tokenText(source, proof.name) });

    try w.writeAll("  rules:");
    if (rules.names.items.len == 0) {
        try w.writeAll(" (none)");
    } else {
        for (rules.names.items, rules.counts.items) |n, c| {
            if (c == 1) try w.print(" {s}", .{n}) else try w.print(" {s}×{d}", .{ n, c });
        }
    }
    try w.writeAll("\n");

    try w.writeAll("  cites:");
    if (cites.names.items.len == 0) {
        try w.writeAll(" (none)");
    } else {
        for (cites.names.items) |n| try w.print(" {s}", .{n});
    }
    try w.writeAll("\n");
}

/// Every step/block label defined anywhere in this proof (all nesting levels).
fn collectLabels(
    arena: Allocator,
    source: []const u8,
    steps: []const ast.Step,
    labels: *std.StringHashMapUnmanaged(void),
) !void {
    for (steps) |step| {
        try labels.put(arena, tokenText(source, step.label), {});
        switch (step.body) {
            .claim => {},
            .assume => |b| try collectLabels(arena, source, b.steps, labels),
            .fix => |b| try collectLabels(arena, source, b.steps, labels),
            .unpack => |b| try collectLabels(arena, source, b.steps, labels),
            .case => |b| for (b.arms) |arm| {
                try labels.put(arena, tokenText(source, arm.label), {});
                try collectLabels(arena, source, arm.steps, labels);
            },
        }
    }
}

fn walk(
    arena: Allocator,
    source: []const u8,
    steps: []const ast.Step,
    rules: *Tally,
    cites: *Tally,
    labels: *const std.StringHashMapUnmanaged(void),
) !void {
    for (steps) |step| {
        switch (step.body) {
            .claim => |c| {
                try rules.bump(arena, tokenText(source, c.rule));
                // `instantiate` names its schema in `c.schema`, always a cite.
                if (c.schema) |s| try cites.bump(arena, tokenText(source, s));
                // a ref is an external cite unless it is one of this proof's
                // own labels (a sibling/ancestor step reference).
                for (c.refs) |ref| {
                    const name = tokenText(source, ref);
                    if (!labels.contains(name)) try cites.bump(arena, name);
                }
            },
            .assume => |b| try walk(arena, source, b.steps, rules, cites, labels),
            .fix => |b| try walk(arena, source, b.steps, rules, cites, labels),
            .unpack => |b| {
                // `unpack u from <src>`: the source is a cite unless local.
                const name = tokenText(source, b.from);
                if (!labels.contains(name)) try cites.bump(arena, name);
                try walk(arena, source, b.steps, rules, cites, labels);
            },
            .case => |b| {
                // `case <disj>`: the disjunction step is a cite unless local.
                const name = tokenText(source, b.disj);
                if (!labels.contains(name)) try cites.bump(arena, name);
                for (b.arms) |arm| try walk(arena, source, arm.steps, rules, cites, labels);
            },
        }
    }
}

fn tokenText(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}
