//! Delaborate — the inverse of expression elaboration: a kernel `term.TermId` back to an
//! `ast.Expr` tree. The SIBLING of `print.zig` (which renders a term to surface *text*):
//! same structural walk, but emitting AST NODES instead of bytes — no intermediate string,
//! no reparse. `print.zig`'s round-trip test is the correctness oracle the two share.
//!
//! WHY: an accelerant that GENERATES a synthetic decl (e.g. `specialize`'s synthetic schema,
//! whose body is built from the caller's kernel-term claim/premises) needs those terms as
//! `ast.Expr` so the ordinary demand pipeline (parse-shaped ProveTask → Elab → kernel)
//! re-elaborates + re-checks them. The terms exist only as kernel `TermId`s at the call
//! site; this bridges them to AST. See memory `accelerants-emit-ast`.
//!
//! SYNTHETIC TOKENS: every emitted `Token` carries a stamped `.name`/`.qualifier` StrId (the
//! only thing engine consumers read past parsing) and a caller-supplied `loc` in `.start`/
//! `.end` (a valid offset in the target file, used only if a diagnostic renders it — a
//! synthetic never-failing body never triggers one). No source buffer is materialized.
//!
//! BINDER NAMES: a quantifier binder is emitted as a fresh sequential name `b1, b2, …` keyed
//! to its DEPTH — bvars are de Bruijn (positional), so the printed name is cosmetic; a fresh
//! per-depth name is collision-free and re-closes to the identical de Bruijn structure
//! (alpha-equal to the original). `bN` interns like any identifier.
//!
//! LIMITS (caller's responsibility): a FREE fvar delaborates to its `#`-trimmed name, which
//! re-resolves only if that name is in the re-elaboration scope — so the caller must ensure
//! the term has no free caller-locals it can't resolve there (`specialize` abstracts those
//! into schema params). A refined/anonymous sort (no IdentKV name) has no re-resolvable sort
//! token — flagged, not handled here.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const Token = lexer.Token;
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;

const Delaborate = @This();

arena: Allocator,
pool: *const term.Pool,
interner: *InternPool,
/// dummy source offset stamped into every synthetic token's start/end (diagnostics only).
loc: u32,
/// enclosing binder NAMES (their interned StrIds), innermost last — a bvar indexes this.
bound: std.ArrayList(StrId) = .empty,

/// Delaborate `id` into a fresh `ast.Expr` tree on `arena`. `loc` is stamped into every
/// synthetic token (a valid offset in the file the AST will be elaborated against).
pub fn run(arena: Allocator, pool: *const term.Pool, interner: *InternPool, id: TermId, loc: u32) Allocator.Error!*const ast.Expr {
    var d: Delaborate = .{ .arena = arena, .pool = pool, .interner = interner, .loc = loc };
    return d.go(id);
}

/// A synthetic identifier token carrying the stamped name (no qualifier).
fn tok(self: *Delaborate, name: StrId) Token {
    return .{ .tag = .identifier, .start = self.loc, .end = self.loc, .name = name };
}

fn box(self: *Delaborate, e: ast.Expr) Allocator.Error!*const ast.Expr {
    const p = try self.arena.create(ast.Expr);
    p.* = e;
    return p;
}

/// The name a bound variable at de Bruijn index `i` was emitted under.
fn boundName(self: *const Delaborate, i: u16) StrId {
    return self.bound.items[self.bound.items.len - 1 - i];
}

/// A fresh binder name `b<depth>` for a quantifier entered at the current depth.
fn freshBinder(self: *Delaborate) Allocator.Error!StrId {
    const bytes = try std.fmt.allocPrint(self.arena, "b{d}", .{self.bound.items.len + 1});
    return self.interner.internString(bytes) catch error.OutOfMemory;
}

/// An fvar/sort NAME's display form: trim at the first `#` (the hygiene mangle), which can
/// never appear in a userland name — recovering the name the author wrote. Re-interned so
/// the emitted token's stamped id matches what re-elaboration will look up.
fn displayId(self: *Delaborate, name: StrId) Allocator.Error!StrId {
    const s = self.interner.stringBytes(name);
    if (std.mem.indexOfScalar(u8, s, '#')) |i| {
        return self.interner.internString(s[0..i]) catch error.OutOfMemory;
    }
    return name;
}

fn go(self: *Delaborate, id: TermId) Allocator.Error!*const ast.Expr {
    switch (self.pool.get(id)) {
        .bvar => |i| return self.box(.{ .name = self.tok(self.boundName(i)) }),
        .fvar => |v| return self.box(.{ .name = self.tok(try self.displayId(v.name)) }),
        .app, .pred => |a| {
            const callee = self.tok(self.interner.nameOf(@enumFromInt(@intFromEnum(a.sym))));
            if (a.args_len == 0) return self.box(.{ .name = callee });
            const src = self.pool.args(a);
            const args = try self.arena.alloc(*const ast.Expr, src.len);
            for (src, args) |arg, *out| out.* = try self.go(arg);
            return self.box(.{ .call = .{ .callee = callee, .args = args } });
        },
        .eq => |p| return self.binary(.equal, p.lhs, p.rhs),
        .not => |t| {
            // sugar mirror: not(eq) delaborates to a `!=` comparison (matches print.zig).
            if (self.pool.get(t) == .eq) {
                const p = self.pool.get(t).eq;
                return self.binary(.not_equal, p.lhs, p.rhs);
            }
            return self.box(.{ .not = .{ .tok = self.tok(.none), .operand = try self.go(t) } });
        },
        .bin => |b| {
            const op: ast.Expr.BinOp = switch (b.op) {
                .implies => .implies,
                .and_op => .and_op,
                .or_op => .or_op,
            };
            return self.binary(op, b.lhs, b.rhs);
        },
        .quant => |q| {
            const bname = try self.freshBinder();
            const sort_tok = self.tok(self.interner.nameOf(@enumFromInt(@intFromEnum(q.sort))));
            const binders = try self.arena.alloc(ast.Binder, 1);
            binders[0] = .{ .name = self.tok(bname), .sort = sort_tok };
            try self.bound.append(self.arena, bname);
            const body = try self.go(q.body);
            _ = self.bound.pop();
            return self.box(.{ .quant = .{
                .q = if (q.q == .forall) .forall else .exists,
                .tok = self.tok(.none),
                .binders = binders,
                .body = body,
            } });
        },
    }
}

fn binary(self: *Delaborate, op: ast.Expr.BinOp, lhs: TermId, rhs: TermId) Allocator.Error!*const ast.Expr {
    return self.box(.{ .binary = .{ .op = op, .tok = self.tok(.none), .lhs = try self.go(lhs), .rhs = try self.go(rhs) } });
}
