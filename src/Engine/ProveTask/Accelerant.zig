//! Accelerant producers — the per-accelerant half of the `using` framework.
//!
//! An accelerant (`using specialize …`, `using tautology …`, …) is sugar for a GENERATED
//! synthetic schema that the ordinary demand pipeline proves + the kernel re-checks. The
//! re-entry-safe demand PLUMBING (hash-name, front-gate FactKV/IdentKV, registerDecl, rack
//! the instance ProveTask, emit schema_instance) lives ONCE on the `Prove` driver
//! (`demandUsing`/`lowerUsing`). Each accelerant supplies ONLY a PRODUCER: given the citing
//! step, build the synthetic `ast.Decl.schema` + the args to instantiate at + the premise
//! refs to discharge. This file holds the producers + the small synthetic-AST builders they
//! share. See memory `accelerants-emit-ast`.
//!
//! SYNTHETIC AST: nodes carry stamped `.name`/`.qualifier` StrIds (all a consumer reads past
//! parsing) + a dummy loc; formula sub-trees over kernel terms are built with `Delaborate`
//! (term -> ast.Expr). A schema body's args are abstracted into value params by substituting
//! each arg term with a fresh param fvar BEFORE delaborating, so the params appear naturally.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const Token = lexer.Token;
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const Delaborate = @import("Delaborate.zig");

/// What a producer hands back to the shared `using` plumbing: a synthetic schema to prove +
/// how the call site instantiates and discharges it.
pub const Synthetic = struct {
    /// deterministic (re-entry-stable) name for the synthetic schema, e.g. `specialize{hash}`
    name: StrId,
    /// the synthetic `.schema` decl (params + body + proof steps), all synthetic AST
    decl: ast.Decl,
    /// the args to instantiate the schema at (value per param) — caller-site AST exprs
    args: []const *const ast.Expr,
    /// the premise step-refs the call site discharges against the instance's `->` antecedents
    premises: []const Token,
    /// Caller-scope bindings (display-name → the abstracted free eigenvar) that must be in the
    /// caller's Elab scope while its `args` are elaborated. Normally a producer abstracts only
    /// caller `fix`-bound eigenvars, whose display name the proof-local scope already resolves —
    /// so this is empty. But a LOCAL specialize head can carry a free fvar INHERITED from a
    /// schema-instance monomorphization (e.g. `induction`'s `prop` was instantiated at a lambda
    /// mentioning the OUTER proof's `fix b`): inside the instance ProveTask that `b#N` is a free
    /// constant with NO source binder, so its display-name arg (`b`) would fail to re-resolve.
    /// The plumbing installs these bindings so the arg elaborates back to the very fvar.
    fvar_binds: []const FvarBind = &.{},

    pub const FvarBind = struct { name: StrId, fvar: StrId, sort: SortId };
};

/// A minimal synthetic-AST builder: mints tokens/exprs/steps on `arena`, all stamped with a
/// single dummy `loc`. Interns names through `interner`.
pub const Builder = struct {
    arena: Allocator,
    interner: *InternPool,
    pool: *const term.Pool,
    loc: u32,

    pub fn tok(self: *Builder, name: StrId) Token {
        return .{ .tag = .identifier, .start = self.loc, .end = self.loc, .name = name };
    }

    pub fn intern(self: *Builder, bytes: []const u8) Allocator.Error!StrId {
        return self.interner.internString(bytes) catch error.OutOfMemory;
    }

    /// A `name` expr referencing `name`.
    pub fn nameExpr(self: *Builder, name: StrId) Allocator.Error!*const ast.Expr {
        const e = try self.arena.create(ast.Expr);
        e.* = .{ .name = self.tok(name) };
        return e;
    }

    /// Delaborate a kernel term into a fresh AST sub-tree (via `Delaborate`).
    pub fn termExpr(self: *Builder, id: TermId) Allocator.Error!*const ast.Expr {
        return Delaborate.run(self.arena, self.pool, self.interner, id, self.loc);
    }

    /// `lhs -> rhs`.
    pub fn implies(self: *Builder, lhs: *const ast.Expr, rhs: *const ast.Expr) Allocator.Error!*const ast.Expr {
        const e = try self.arena.create(ast.Expr);
        e.* = .{ .binary = .{ .op = .implies, .tok = self.tok(.none), .lhs = lhs, .rhs = rhs } };
        return e;
    }

    /// A claim step `@label | <formula> [<kw> <rule> <refs>]`.
    pub fn claimStep(self: *Builder, label: StrId, formula: *const ast.Expr, kind: ast.Step.Claim.Kind, rule: StrId, args: []const *const ast.Expr, refs: []const Token) Allocator.Error!ast.Step {
        return .{ .label = self.tok(label), .body = .{ .claim = .{
            .formula = formula,
            .kind = kind,
            .rule = self.tok(rule),
            .schema = null,
            .args = args,
            .refs = refs,
        } } };
    }

    /// An `assume <formula> { steps }` block step.
    pub fn assumeStep(self: *Builder, label: StrId, formula: *const ast.Expr, steps: []const ast.Step) Allocator.Error!ast.Step {
        return .{ .label = self.tok(label), .body = .{ .assume = .{ .formula = formula, .steps = steps } } };
    }
};
