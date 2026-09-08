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

/// Delaborate a term to an `ast.Expr`. ITERATIVE two-color post-order (was native recursion) —
/// a deep term can't overflow. A node is EXPANDED (children pushed reversed) then REBUILT from its
/// children's ast results (on a results stack). A `.quant` also pushes an `enter` (fresh binder
/// name onto `self.bound`, so the body's bvars resolve) and, after its body, a `pop_bound`. Scratch
/// stacks on the pool's GPA, freed on return; the built AST is on `self.arena` (durable).
fn go(self: *Delaborate, root: TermId) Allocator.Error!*const ast.Expr {
    var scratch: std.heap.ArenaAllocator = .init(self.pool.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();
    const Frame = union(enum) {
        expand: TermId,
        rebuild: TermId, // its children's ast results are the top of `results`
        pop_bound,
    };
    var work: std.ArrayList(Frame) = .empty;
    var results: std.ArrayList(*const ast.Expr) = .empty;
    try work.append(a, .{ .expand = root });
    while (work.pop()) |frame| switch (frame) {
        .pop_bound => _ = self.bound.pop(),
        .expand => |id| {
            switch (self.pool.get(id)) {
                // leaves build directly onto `results`.
                .bvar => |i| try results.append(a, try self.box(.{ .name = self.tok(self.boundName(i)) })),
                .fvar => |v| try results.append(a, try self.box(.{ .name = self.tok(try self.displayId(v.name)) })),
                .app, .pred => |ap| {
                    if (ap.args_len == 0) {
                        const callee = self.tok(self.interner.nameOf(@enumFromInt(@intFromEnum(ap.sym))));
                        try results.append(a, try self.box(.{ .name = callee }));
                    } else {
                        try work.append(a, .{ .rebuild = id });
                        const src = self.pool.args(ap);
                        var i: usize = src.len;
                        while (i > 0) {
                            i -= 1;
                            try work.append(a, .{ .expand = src[i] }); // reversed → arg 0 first
                        }
                    }
                },
                .eq, .not, .bin => {
                    try work.append(a, .{ .rebuild = id });
                    // push children reversed (rhs then lhs) so lhs result lands first.
                    switch (self.pool.get(id)) {
                        .eq => |p| {
                            try work.append(a, .{ .expand = p.rhs });
                            try work.append(a, .{ .expand = p.lhs });
                        },
                        .not => |t| try work.append(a, .{ .expand = t }),
                        .bin => |b| {
                            try work.append(a, .{ .expand = b.rhs });
                            try work.append(a, .{ .expand = b.lhs });
                        },
                        else => unreachable,
                    }
                },
                .quant => |q| {
                    // ENTER: fresh binder name in scope for the body; rebuild after; pop after that.
                    const bname = try self.freshBinder();
                    try self.bound.append(self.arena, bname);
                    try work.append(a, .pop_bound);
                    try work.append(a, .{ .rebuild = id });
                    try work.append(a, .{ .expand = q.body });
                },
            }
        },
        .rebuild => |id| switch (self.pool.get(id)) {
            .app, .pred => |ap| {
                const callee = self.tok(self.interner.nameOf(@enumFromInt(@intFromEnum(ap.sym))));
                const n = ap.args_len;
                const kids = results.items[results.items.len - n ..];
                const args = try self.arena.dupe(*const ast.Expr, kids);
                results.items.len -= n;
                try results.append(a, try self.box(.{ .call = .{ .callee = callee, .args = args } }));
            },
            .eq => {
                const rhs = results.pop().?;
                const lhs = results.pop().?;
                try results.append(a, try self.boxBinary(.equal, lhs, rhs));
            },
            .not => |t| {
                const inner = results.pop().?;
                // sugar mirror: not(eq) delaborates to `!=` (matches print.zig). The eq's operands
                // are `inner`'s children — but `inner` is already the `=` ast; re-wrap as `!=`.
                if (self.pool.get(t) == .eq) {
                    try results.append(a, self.rewrapNotEq(inner));
                } else {
                    try results.append(a, try self.box(.{ .not = .{ .tok = self.tok(.none), .operand = inner } }));
                }
            },
            .bin => |b| {
                const rhs = results.pop().?;
                const lhs = results.pop().?;
                const op: ast.Expr.BinOp = switch (b.op) {
                    .implies => .implies,
                    .and_op => .and_op,
                    .or_op => .or_op,
                };
                try results.append(a, try self.boxBinary(op, lhs, rhs));
            },
            .quant => |q| {
                const body = results.pop().?;
                const sort_tok = self.tok(self.interner.nameOf(@enumFromInt(@intFromEnum(q.sort))));
                const binders = try self.arena.alloc(ast.Binder, 1);
                binders[0] = .{ .name = self.tok(self.bound.items[self.bound.items.len - 1]), .sort = sort_tok };
                try results.append(a, try self.box(.{ .quant = .{
                    .q = if (q.q == .forall) .forall else .exists,
                    .tok = self.tok(.none),
                    .binders = binders,
                    .body = body,
                } }));
            },
            .bvar, .fvar => unreachable, // leaves never rebuild
        },
    };
    return results.items[0];
}

/// Build a binary ast node from already-built operand ASTs.
fn boxBinary(self: *Delaborate, op: ast.Expr.BinOp, lhs: *const ast.Expr, rhs: *const ast.Expr) Allocator.Error!*const ast.Expr {
    return self.box(.{ .binary = .{ .op = op, .tok = self.tok(.none), .lhs = lhs, .rhs = rhs } });
}

/// Given an already-built `=` binary ast, re-wrap it as `!=` (the not(eq) sugar). The `=` node's
/// operands are reused verbatim.
fn rewrapNotEq(self: *Delaborate, eq_ast: *const ast.Expr) *const ast.Expr {
    const e = eq_ast.binary;
    return self.box(.{ .binary = .{ .op = .not_equal, .tok = self.tok(.none), .lhs = e.lhs, .rhs = e.rhs } }) catch eq_ast;
}
