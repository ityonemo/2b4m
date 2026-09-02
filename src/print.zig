//! Term printer. MUST re-emit valid surface syntax: an obligation printed in a
//! diagnostic can be pasted verbatim as a lemma statement.
//!
//! POOL-NATIVE (post demand-flip): a term's `app.sym` / `quant.sort` fields are
//! numerically InternPool `Index`es, so names come straight from the pool
//! (`nameOf`/`sortName`) — no `env` parameter.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("InternPool.zig");
const term = @import("term.zig");
const TermId = term.TermId;

/// Render `id` as surface syntax. Binder hints are freshened against free
/// variables and enclosing binders so the output re-parses to the same term.
pub fn render(
    arena: Allocator,
    pool: *const term.Pool,
    interner: *const InternPool,
    id: TermId,
) Allocator.Error![]const u8 {
    var out: std.Io.Writer.Allocating = .init(arena);
    var p: Printer = .{
        .arena = arena,
        .pool = pool,
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
    interner: *const InternPool,
    /// names of free variables anywhere in the term (binder hints must avoid)
    fvar_names: std.StringHashMapUnmanaged(void) = .empty,
    /// enclosing binder names, innermost last
    bound: std.ArrayList([]const u8) = .empty,

    /// Display name of an fvar: the prover disambiguates same-named
    /// eigenvariables of disjoint sibling `fix` blocks by appending `#<n>` to
    /// the interned name (`x` -> `x#2`). `#` can never appear in a userland
    /// identifier (the lexer forbids it), so trimming at the first `#` recovers
    /// the name the author wrote without any risk of colliding with a real name.
    fn displayName(self: *const Printer, name: InternPool.StrId) []const u8 {
        const s = self.interner.stringBytes(name);
        return if (std.mem.indexOfScalar(u8, s, '#')) |i| s[0..i] else s;
    }

    fn symName(self: *const Printer, sym: term.SymId) []const u8 {
        return self.interner.stringBytes(self.interner.nameOf(@enumFromInt(@intFromEnum(sym))));
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
                try w.writeAll(self.symName(a.sym));
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
                    self.interner.sortName(@enumFromInt(@intFromEnum(q.sort))),
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

/// Pool-backed fixture: sort Nat, funcs/preds minted straight into the pool
/// (mint index == the SymId/SortId a term carries in the demand world).
const Fixture = struct {
    interner: *InternPool,
    pool: *term.Pool,
    arena: Allocator,
    nat: term.SortId,
    add: term.SymId,
    even: term.SymId,

    fn init(arena: Allocator) !Fixture {
        const interner = try arena.create(InternPool);
        interner.* = try .init(arena);
        const pool = try arena.create(term.Pool);
        pool.* = .init(arena);
        const nat_ix = try interner.mintSort(.{ .name = try interner.internString("Nat"), .loc = 0, .refinement = null });
        const nat2 = [_]InternPool.Index{ nat_ix, nat_ix };
        const add_sig = try interner.get(.{ .sig = .{ .result = nat_ix, .result_refined = .none, .args = &nat2 } });
        const add_ix = try interner.mintFunc(.{ .sig = add_sig, .guard = InternPool.no_term, .param_names = &.{}, .name = try interner.internString("add"), .loc = 0 });
        const nat1 = [_]InternPool.Index{nat_ix};
        const even_sig = try interner.get(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &nat1 } });
        const even_ix = try interner.mintPred(.{ .sig = even_sig, .guard = InternPool.no_term, .param_names = &.{}, .name = try interner.internString("even"), .loc = 0 });
        return .{
            .interner = interner,
            .pool = pool,
            .arena = arena,
            .nat = @enumFromInt(@intFromEnum(nat_ix)),
            .add = @enumFromInt(@intFromEnum(add_ix)),
            .even = @enumFromInt(@intFromEnum(even_ix)),
        };
    }
};

test "printer renders pool-named apps, quantifiers, precedence parens" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fx = try Fixture.init(arena);
    const pool = fx.pool;

    // forall x: Nat; even(add(x, x)) -> even(x)
    const b0 = try pool.add(.{ .bvar = 0 });
    const add_xx = try pool.addApp(.app, fx.add, &.{ b0, b0 });
    const even_add = try pool.addApp(.pred, fx.even, &.{add_xx});
    const even_x = try pool.addApp(.pred, fx.even, &.{b0});
    const imp = try pool.add(.{ .bin = .{ .op = .implies, .lhs = even_add, .rhs = even_x } });
    const t = try pool.add(.{ .quant = .{ .q = .forall, .sort = fx.nat, .hint = try fx.interner.internString("x"), .body = imp } });

    const rendered = try render(arena, pool, fx.interner, t);
    try testing.expectEqualStrings("forall x: Nat; even(add(x, x)) -> even(x)", rendered);
}

test "binder hints freshen against free variables" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fx = try Fixture.init(arena);
    const pool = fx.pool;

    // build: forall x: Nat; x_free = x_bound  (hint 'x' collides with fvar 'x')
    const x_name = try fx.interner.internString("x");
    const x_free = try pool.add(.{ .fvar = .{ .name = x_name, .sort = fx.nat } });
    const b0 = try pool.add(.{ .bvar = 0 });
    const body = try pool.add(.{ .eq = .{ .lhs = x_free, .rhs = b0 } });
    const t = try pool.add(.{ .quant = .{ .q = .forall, .sort = fx.nat, .hint = x_name, .body = body } });

    const rendered = try render(arena, pool, fx.interner, t);
    try testing.expectEqualStrings("forall x_2: Nat; x = x_2", rendered);
}

test "mixed boolean operators parenthesize parser-legally" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const fx = try Fixture.init(arena);
    const pool = fx.pool;

    const x = try pool.add(.{ .fvar = .{ .name = try fx.interner.internString("x"), .sort = fx.nat } });
    const p = try pool.addApp(.pred, fx.even, &.{x});
    const andpp = try pool.add(.{ .bin = .{ .op = .and_op, .lhs = p, .rhs = p } });
    const orq = try pool.add(.{ .bin = .{ .op = .or_op, .lhs = andpp, .rhs = p } });
    const notp = try pool.add(.{ .not = p });
    const imp = try pool.add(.{ .bin = .{ .op = .implies, .lhs = orq, .rhs = notp } });

    const rendered = try render(arena, pool, fx.interner, imp);
    try testing.expectEqualStrings("((even(x) and even(x)) or even(x)) -> (not even(x))", rendered);
}
