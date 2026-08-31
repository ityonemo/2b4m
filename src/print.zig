//! Term printer. MUST re-emit valid surface syntax: an obligation printed in a
//! diagnostic can be pasted verbatim as a lemma statement. Round-trip property
//! (parse -> elaborate -> render is a fixpoint) is tested below.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("InternPool.zig");
const term = @import("term.zig");
const TermId = term.TermId;
const Env = @import("env.zig").Env;

/// Render `id` as surface syntax. Binder hints are freshened against free
/// variables and enclosing binders so the output re-parses to the same term.
pub fn render(
    arena: Allocator,
    pool: *const term.Pool,
    env: *const Env,
    interner: *const InternPool,
    id: TermId,
) Allocator.Error![]const u8 {
    var out: std.Io.Writer.Allocating = .init(arena);
    var p: Printer = .{
        .arena = arena,
        .pool = pool,
        .env = env,
        .interner = interner,
    };
    try p.collectFvars(id);
    p.print(&out.writer, id, 0) catch return error.OutOfMemory;
    return out.toOwnedSlice();
}

// precedence levels: implies=1 (right-assoc) < or=2 < and=3 < cmp=4 < not=5
const Printer = struct {
    arena: Allocator,
    pool: *const term.Pool,
    env: *const Env,
    interner: *const InternPool,
    /// names of free variables anywhere in the term (binder hints must avoid)
    fvar_names: std.StringHashMapUnmanaged(void) = .empty,
    /// enclosing binder names, innermost last
    bound: std.ArrayList([]const u8) = .empty,

    /// Display name of an fvar: the elaborator disambiguates same-named
    /// eigenvariables of disjoint sibling `fix` blocks by appending `#<n>` to
    /// the interned name (`x` -> `x#2`). `#` can never appear in a userland
    /// identifier (the lexer forbids it), so trimming at the first `#` recovers
    /// the name the author wrote without any risk of colliding with a real name.
    fn displayName(self: *const Printer, name: InternPool.StrId) []const u8 {
        const s = self.interner.stringBytes(name);
        return if (std.mem.indexOfScalar(u8, s, '#')) |i| s[0..i] else s;
    }

    fn collectFvars(self: *Printer, id: TermId) Allocator.Error!void {
        switch (self.pool.get(id)) {
            .bvar => {},
            .fvar => |v| try self.fvar_names.put(self.arena, self.displayName(v.name), {}),
            .app, .pred => |a| for (self.pool.args(a)) |arg| try self.collectFvars(arg),
            .eq => |p| {
                try self.collectFvars(p.lhs);
                try self.collectFvars(p.rhs);
            },
            .not => |t| try self.collectFvars(t),
            .bin => |b| {
                try self.collectFvars(b.lhs);
                try self.collectFvars(b.rhs);
            },
            .quant => |q| try self.collectFvars(q.body),
        }
    }

    fn taken(self: *const Printer, name: []const u8) bool {
        if (self.fvar_names.contains(name)) return true;
        for (self.bound.items) |b| {
            if (std.mem.eql(u8, b, name)) return true;
        }
        return false;
    }

    const Error = std.Io.Writer.Error || Allocator.Error;

    fn print(self: *Printer, w: *std.Io.Writer, id: TermId, min_prec: u8) Error!void {
        switch (self.pool.get(id)) {
            .bvar => |i| {
                const name = self.bound.items[self.bound.items.len - 1 - i];
                try w.writeAll(name);
            },
            .fvar => |v| try w.writeAll(self.displayName(v.name)),
            .app, .pred => |a| {
                try w.writeAll(self.interner.stringBytes(self.env.sym(a.sym).name));
                if (a.args_len > 0) {
                    try w.writeAll("(");
                    for (self.pool.args(a), 0..) |arg, i| {
                        if (i > 0) try w.writeAll(", ");
                        try self.print(w, arg, 0);
                    }
                    try w.writeAll(")");
                }
            },
            .eq => |p| {
                try self.print(w, p.lhs, 5);
                try w.writeAll(" = ");
                try self.print(w, p.rhs, 5);
            },
            .not => |t| {
                // sugar: not(eq) renders as !=
                if (self.pool.get(t) == .eq) {
                    const p = self.pool.get(t).eq;
                    try self.print(w, p.lhs, 5);
                    try w.writeAll(" != ");
                    try self.print(w, p.rhs, 5);
                    return;
                }
                try w.writeAll("not ");
                try self.print(w, t, 5);
            },
            .bin => |b| {
                const prec: u8, const op: []const u8 = switch (b.op) {
                    .implies => .{ 1, " -> " },
                    .or_op => .{ 2, " or " },
                    .and_op => .{ 3, " and " },
                };
                const need_parens = min_prec > prec;
                if (need_parens) try w.writeAll("(");
                // implies is right-assoc; or/and are left-assoc
                const lhs_prec: u8 = if (b.op == .implies) prec + 1 else prec;
                const rhs_prec: u8 = if (b.op == .implies) prec else prec + 1;
                try self.printBoolOperand(w, b.lhs, b.op, lhs_prec);
                try w.writeAll(op);
                try self.printBoolOperand(w, b.rhs, b.op, rhs_prec);
                if (need_parens) try w.writeAll(")");
            },
            .quant => |q| {
                // binds to the end of the formula: parenthesize unless we are
                // already in lowest-precedence (rightmost) position
                const need_parens = min_prec > 1;
                if (need_parens) try w.writeAll("(");
                const hint = self.displayName(q.hint);
                var name = hint;
                var n: u32 = 2;
                while (self.taken(name)) : (n += 1) {
                    name = try std.fmt.allocPrint(self.arena, "{s}_{d}", .{ hint, n });
                }
                try w.print("{s} {s}: {s}; ", .{
                    if (q.q == .forall) "forall" else "exists",
                    name,
                    self.env.sortName(self.interner, q.sort),
                });
                try self.bound.append(self.arena, name);
                try self.print(w, q.body, 0);
                _ = self.bound.pop();
                if (need_parens) try w.writeAll(")");
            },
        }
    }

    /// Print an operand of the boolean operator `parent_op`, forcing parens
    /// when the operand is a *different* boolean operator (or a `not`). This
    /// keeps output legal under the parser's mixed-boolean-operator paren rule:
    /// same-op chains (`a or b or c`) print bare; any mix is parenthesized.
    fn printBoolOperand(self: *Printer, w: *std.Io.Writer, id: TermId, parent_op: anytype, min_prec: u8) Error!void {
        const node = self.pool.get(id);
        const force = switch (node) {
            .bin => |b| b.op != parent_op, // different and/or/-> => parens
            // a real `not` needs parens; but `not(eq)` prints as `!=`, a
            // comparison, which the parser does not treat as a boolean op
            .not => |t| self.pool.get(t) != .eq,
            else => false,
        };
        if (force) {
            try w.writeAll("(");
            try self.print(w, id, 0);
            try w.writeAll(")");
        } else {
            try self.print(w, id, min_prec);
        }
    }
};

// --- tests ---

const testing = std.testing;
const TestCtx = @import("elaborate.zig").TestCtx;

const header =
    \\sort Nat
    \\const ZERO: Nat
    \\func succ(n: Nat): Nat
    \\func add(a: Nat, b: Nat): Nat
    \\pred even(n: Nat)
    \\pred p
    \\pred q
    \\
;

/// parse+elaborate `formula`, render it, re-parse+re-elaborate the rendering,
/// and require the second render to be a fixpoint (and both checks clean).
fn expectRoundTrip(formula: []const u8) !void {
    const gpa = testing.allocator;

    const src1 = try std.mem.concat(gpa, u8, &.{ header, "axiom rt: ", formula, "\n" });
    defer gpa.free(src1);
    var ctx1 = try TestCtx.run(gpa, src1);
    defer ctx1.deinit(gpa);
    for (ctx1.sink.list.items) |d| std.debug.print("unexpected: {s}\n", .{d.message});
    try testing.expectEqual(0, ctx1.sink.list.items.len);
    const f1 = ctx1.env.findStatement(@enumFromInt(0), try ctx1.interner.internString("rt")).?.axiom.formula;
    const rendered1 = try render(ctx1.arena_state.allocator(), ctx1.pool, ctx1.env, ctx1.interner, f1);

    const src2 = try std.mem.concat(gpa, u8, &.{ header, "axiom rt: ", rendered1, "\n" });
    defer gpa.free(src2);
    var ctx2 = try TestCtx.run(gpa, src2);
    defer ctx2.deinit(gpa);
    try testing.expectEqual(0, ctx2.sink.list.items.len);
    const f2 = ctx2.env.findStatement(@enumFromInt(0), try ctx2.interner.internString("rt")).?.axiom.formula;
    const rendered2 = try render(ctx2.arena_state.allocator(), ctx2.pool, ctx2.env, ctx2.interner, f2);

    try testing.expectEqualStrings(rendered1, rendered2);
}

test "printer round-trips precedence and quantifier corpus" {
    try expectRoundTrip("p -> q -> p");
    try expectRoundTrip("(p -> q) -> p");
    try expectRoundTrip("(p and q) or p");
    try expectRoundTrip("p and (q or p)");
    try expectRoundTrip("not (p and q)");
    try expectRoundTrip("(not p) and (not q)");
    // mixed operators: the printer must emit parser-legal parens so its own
    // output re-parses (the two are kept consistent by the paren rule)
    try expectRoundTrip("(p -> q) -> ((not q) -> (not p))");
    try expectRoundTrip("((p and q) or p) -> (q and (not p))");
    try expectRoundTrip("forall x: Nat; x = x");
    try expectRoundTrip("forall x, y: Nat; add(x, y) = add(y, x)");
    try expectRoundTrip("(forall x: Nat; even(x)) -> p");
    try expectRoundTrip("p -> forall x: Nat; exists y: Nat; succ(x) = y");
    try expectRoundTrip("forall x: Nat; x != ZERO -> exists y: Nat; x = succ(y)");
    try expectRoundTrip("forall x: Nat; not (x = ZERO and even(x))");
}

test "binder hints freshen against free variables" {
    const gpa = testing.allocator;
    var ctx = try TestCtx.run(gpa, header);
    defer ctx.deinit(gpa);
    const arena = ctx.arena_state.allocator();
    const pool = ctx.pool;

    // build: forall x: Nat; x_free = x_bound  (hint 'x' collides with fvar 'x')
    const Nat = ctx.env.findSort(@enumFromInt(0), try ctx.interner.internString("Nat")).?;
    const x_name = try ctx.interner.internString("x");
    const x_free = try pool.add(.{ .fvar = .{ .name = x_name, .sort = Nat } });
    const b0 = try pool.add(.{ .bvar = 0 });
    const body = try pool.add(.{ .eq = .{ .lhs = x_free, .rhs = b0 } });
    const t = try pool.add(.{ .quant = .{ .q = .forall, .sort = Nat, .hint = x_name, .body = body } });

    const rendered = try render(arena, pool, ctx.env, ctx.interner, t);
    try testing.expectEqualStrings("forall x_2: Nat; x = x_2", rendered);
}
