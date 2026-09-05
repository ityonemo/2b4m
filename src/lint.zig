//! `bpa lint <file>` — convention checks over the parsed AST (never elaborates,
//! never checks soundness). Reports style/consistency violations that `check`
//! deliberately ignores because they don't affect validity; the point is to keep
//! the corpus internally consistent so mechanisms that rely on SYNTACTIC shape
//! stay frictionless.
//!
//! Rules:
//!
//! 1. **Canonical binder order.** A leading `forall` block must bind its
//!    variables in FIRST-APPEARANCE order — the order they first occur, left to
//!    right, in the body. A statement's signature is a property of WHAT IT SAYS,
//!    not how it is proved; letting proof convenience permute the binders makes
//!    two logically-identical facts fail α-matching (the `model` mechanism's
//!    binder-order trap — `∀c,b,a; add(add(a,b),c)=…` vs a local `∀a,b,c; …`
//!    that would otherwise discharge it directly). Keeping every statement
//!    canonical means a local fact and any abstract axiom it discharges land in
//!    the same order, so no adapter theorem is needed.
//!
//! FUTURE RULES (not yet implemented) — this is where the corpus's naming and
//! style conventions (today enforced only by review) will move:
//!   - **casing**: sorts `ProudCamelCase`, consts `ALLCAPS`, funcs/preds/vars
//!     `snake_case` (never one letter), axioms/theorems `camelCase` spelled out,
//!     labels/`[by …]` refs kebab-case — flag a declaration that violates its
//!     kind's case.
//!   - **label quality**: bare-counter / abbreviation labels (`eq2`, `gen-a`),
//!     the dump-test conventions in agents/style-guide.md.
//!   - **strategy comments**, phase comments, import-alias discipline, etc.
//!
//! `.md` NOTE: a literate transliteration (e.g. `aata/*.md`) deliberately mirrors
//! its SOURCE's notation — one-letter book variables, the book's theorem names,
//! aliased symbols (see agents/style-guide.md "Transcription exception"). So the
//! naming/casing/label rules above must be SUSPENDED when linting a `.md` (only
//! the source-agnostic structural rules, like binder order, apply there). The
//! caller passes whether the input was literate; rules opt in/out on that flag.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("ast.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const diagnostics = @import("diagnostics.zig");
const Token = lexer.Token;

pub const Result = struct {
    text: []const u8,
    /// true = no violations (and no parse errors)
    ok: bool,
};

/// `is_literate` = the input came from a `.md` transliteration; naming/casing/
/// label rules (which mirror the source's notation, not bpa's) are suspended for
/// it. Rule 1 (binder order) is source-agnostic and always applies.
pub fn lint(arena: Allocator, path: []const u8, source: []const u8, is_literate: bool) Allocator.Error!Result {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);

    var p: parser.Parser = .init(arena, source, sink);
    const file = try p.parseFile();

    // a parse error is reported as-is (same channel); lint can't run on a
    // malformed AST.
    if (sink.list.items.len == 0) {
        for (file.decls) |*decl| try lintDecl(arena, sink, source, decl, is_literate);
    }

    var out: std.Io.Writer.Allocating = .init(arena);
    if (sink.list.items.len > 0) {
        const files = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
        sink.render(&out.writer, &files) catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = false };
    }
    return .{ .text = "", .ok = true };
}

fn lintDecl(arena: Allocator, sink: *diagnostics.Sink, source: []const u8, decl: *const ast.Decl, is_literate: bool) Allocator.Error!void {
    // (future casing/label rules will gate on `is_literate` — suspended for .md)
    _ = is_literate;
    const formula: *const ast.Expr = switch (decl.*) {
        // only a LOCAL fact has a formula to lint; an alias points elsewhere.
        .axiom, .hole => |a| switch (a) {
            .local => |f| f.formula,
            .alias => return,
        },
        .theorem => |t| switch (t) {
            .local => |l| l.fact.formula,
            .alias => return,
        },
        else => return, // sorts/consts/funcs/preds/imports/aliases/models: nothing to lint
    };
    try checkBinderOrder(arena, sink, source, formula);
}

/// Rule 1: a leading `forall` block binds in first-appearance-in-body order.
/// Only the OUTERMOST contiguous `forall` run is checked (a nested quantifier
/// under an `->` or another operator is a separate scope, linted on its own if
/// it heads its own statement — here we stay conservative and lint the prefix
/// that shares one body). A binder that never occurs in the body (vacuous) is
/// skipped in the appearance list; it can sit anywhere without a warning.
fn checkBinderOrder(arena: Allocator, sink: *diagnostics.Sink, source: []const u8, formula: *const ast.Expr) Allocator.Error!void {
    if (formula.* != .quant or formula.quant.q != .forall) return;
    const q = formula.quant;

    // declared order: the binder names, as written.
    var declared: std.ArrayList([]const u8) = .empty;
    for (q.binders) |b| try declared.append(arena, tokenText(source, b.name));

    // first-appearance order: walk the body, recording each declared name the
    // first time it is seen.
    var appeared: std.ArrayList([]const u8) = .empty;
    var seen: std.StringHashMapUnmanaged(void) = .empty;
    try recordAppearance(arena, source, q.body, declared.items, &appeared, &seen);

    // compare, ignoring vacuous binders (declared but never appearing): the
    // canonical order is the appearance order; a declared name absent from the
    // body imposes no constraint. So filter `declared` to those that appear,
    // preserving declared order, and require it to equal `appeared`.
    var declared_appearing: std.ArrayList([]const u8) = .empty;
    for (declared.items) |name| {
        if (seen.contains(name)) try declared_appearing.append(arena, name);
    }
    if (declared_appearing.items.len != appeared.items.len) return; // shouldn't happen
    for (declared_appearing.items, appeared.items) |d, a| {
        if (!std.mem.eql(u8, d, a)) {
            try sink.add(q.tok.start, "non-canonical binder order: 'forall {s}' should be 'forall {s}' (first-appearance order in the body)", .{
                try join(arena, declared.items), try join(arena, canonicalOrder(arena, declared.items, appeared.items) catch declared.items),
            });
            return;
        }
    }
}

/// DFS the body, appending each name in `targets` to `appeared` the first time
/// it is encountered as a `name` leaf.
fn recordAppearance(
    arena: Allocator,
    source: []const u8,
    e: *const ast.Expr,
    targets: []const []const u8,
    appeared: *std.ArrayList([]const u8),
    seen: *std.StringHashMapUnmanaged(void),
) Allocator.Error!void {
    switch (e.*) {
        .name => |t| {
            const txt = tokenText(source, t);
            for (targets) |name| {
                if (std.mem.eql(u8, name, txt)) {
                    if (!seen.contains(name)) {
                        try seen.put(arena, name, {});
                        try appeared.append(arena, name);
                    }
                    return;
                }
            }
        },
        .call => |c| for (c.args) |arg| try recordAppearance(arena, source, arg, targets, appeared, seen),
        .binary => |b| {
            try recordAppearance(arena, source, b.lhs, targets, appeared, seen);
            try recordAppearance(arena, source, b.rhs, targets, appeared, seen);
        },
        .not => |n| try recordAppearance(arena, source, n.operand, targets, appeared, seen),
        // a nested quantifier/lambda is a new scope; a shadowing binder there
        // hides the outer name, so stop descending into a body that rebinds one
        // of our targets. Otherwise descend (the inner body may still mention
        // our variables).
        .quant => |inner| {
            if (bindsAny(source, inner.binders, targets)) return;
            try recordAppearance(arena, source, inner.body, targets, appeared, seen);
        },
        .lambda => |l| {
            if (bindsAny(source, l.binders, targets)) return;
            try recordAppearance(arena, source, l.body, targets, appeared, seen);
        },
    }
}

fn bindsAny(source: []const u8, binders: []const ast.Binder, targets: []const []const u8) bool {
    for (binders) |b| {
        const txt = tokenText(source, b.name);
        for (targets) |name| if (std.mem.eql(u8, name, txt)) return true;
    }
    return false;
}

/// The suggested canonical declared list: appearance order for the appearing
/// binders, with any vacuous binders appended in their original relative order.
fn canonicalOrder(arena: Allocator, declared: []const []const u8, appeared: []const []const u8) Allocator.Error![]const []const u8 {
    var out: std.ArrayList([]const u8) = .empty;
    try out.appendSlice(arena, appeared);
    for (declared) |name| {
        var in_app = false;
        for (appeared) |a| {
            if (std.mem.eql(u8, a, name)) in_app = true;
        }
        if (!in_app) try out.append(arena, name);
    }
    return out.items;
}

fn join(arena: Allocator, names: []const []const u8) Allocator.Error![]const u8 {
    var out: std.Io.Writer.Allocating = .init(arena);
    for (names, 0..) |n, i| {
        if (i > 0) out.writer.writeAll(", ") catch return error.OutOfMemory;
        out.writer.writeAll(n) catch return error.OutOfMemory;
    }
    return out.toOwnedSlice();
}

fn tokenText(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}
