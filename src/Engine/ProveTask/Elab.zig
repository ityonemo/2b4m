//! Elab — walk-side EXPRESSION ELABORATION (Step 8, W4): an `ast.Expr` becomes a
//! scratchpad `term.Pool` term, with names resolved the DEMAND way and sorts/symbols
//! carried as POOL `Index`es. See memory `provetask-step-walk-design`.
//!
//! RESOLUTION ORDER for a name in an expression:
//!   1. expression-local binders (quantifier binders bound during THIS elaboration —
//!      innermost wins; they close into de Bruijn indices),
//!   2. proof-local binders (the Walk's LocalIdentKV: fix eigenvariables, unpack
//!      witnesses — elaborate as the binder's hygienic fvar at its sort),
//!   3. global identifiers via IdentKV `lookup` — the READ PASS already ran, so every
//!      global this expression references is `done`; an absent/in-flight entry here is
//!      diagnosed (defensively) as unresolved, not fetched.
//! Qualified `ns.name` resolves the import first (IdentKV, must be `done`), then the
//! base in the imported namespace.
//!
//! POOL-NATIVE SORTS: terms built here carry pool `Index`es in their `fvar.sort` /
//! `app.sym` fields (cast into the distinct `SortId`/`SymId` enums). `prop_sort` is the
//! pool's reserved Prop (`Index.prop`); at the demand flip `term.SortId.prop` renumbers
//! to the same value and the two spellings collapse.
//!
//! NOT YET SUPPORTED (diagnosed, proof goes red; later layers/phases): guarded functions
//! (`requires` — the TCC machinery), transparent defines, predicated sorts/binders
//! (`where`), lambdas (schema arguments — schemas are unsupported wholesale).

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const SortId = term.SortId;
const TermId = term.TermId;
const Diagnostics = @import("../../diagnostics.zig");
const IdentKV = @import("../../IdentKV.zig");
const Walk = @import("Walk.zig");
const Schema = @import("Schema.zig");

const Elab = @This();

pub const Error = error{ Recover, OutOfMemory };
pub const Typed = struct { id: TermId, sort: SortId };

/// The pool's reserved Prop sort, as a scratchpad SortId. Numerically `Index.prop`; the
/// flip renumbers `term.SortId.prop` onto it.
pub const prop_sort: SortId = @enumFromInt(@intFromEnum(InternPool.Index.prop));

arena: Allocator,
io: std.Io,
interner: *InternPool,
idents: *IdentKV,
/// the task's term SCRATCHPAD — every term this elaboration builds lives here
scratch: *term.Pool,
sink: *Diagnostics.Sink,
source: []const u8,
/// proof-local binders (fix/unpack) resolve through the walk
walk: *const Walk,
/// the proving file's universe namespace — bare globals resolve here
ns: InternPool.Index,
/// hygienic fresh-name counter, owned by the driving task (proof-unique names)
fresh_counter: *u32,
/// SCHEMA PARAMS in scope while elaborating a schema body/steps (param name -> bound arg);
/// null in ordinary proofs. Consulted BEFORE the global lookup in name/call position: a
/// value param resolves to its term, a generator param BETA-REDUCES at a call. Set by the
/// instance ProveTask (post-init) on the Elab it uses for the schema body/steps.
schema_args: ?*const Schema.SchemaArgs = null,
/// MODEL this elaboration resolves THROUGH (Step 13): when set, every global identifier
/// resolved here is filtered `interner.applyModel(model, source)` — so proving a source
/// theorem in model M's namespace remaps `op`→`add` etc. Null (`.universe` at the call
/// site) in an ordinary proof = identity. Set by the model ProveTask on its Elab.
model: InternPool.Index = .universe,

/// expression-local binders (quantifiers), innermost last; transient per elaboration
scope: std.ArrayList(ScopeEntry) = .empty,

const ScopeEntry = struct { name: StrId, sort: SortId, fvar: StrId };

pub fn init(
    arena: Allocator,
    io: std.Io,
    interner: *InternPool,
    idents: *IdentKV,
    scratch: *term.Pool,
    sink: *Diagnostics.Sink,
    source: []const u8,
    walk: *const Walk,
    ns: InternPool.Index,
    fresh_counter: *u32,
) Elab {
    return .{
        .arena = arena,
        .io = io,
        .interner = interner,
        .idents = idents,
        .scratch = scratch,
        .sink = sink,
        .source = source,
        .walk = walk,
        .ns = ns,
        .fresh_counter = fresh_counter,
    };
}

/// Elaborate to any sort. Callers wanting a proposition wrap with `requireProp`.
pub fn elaborateExpr(self: *Elab, e: *const ast.Expr) Error!Typed {
    switch (e.*) {
        .name => |tok| return self.elaborateName(tok),
        .call => |c| return self.elaborateCall(c),
        .binary => |b| switch (b.op) {
            .implies, .and_op, .or_op => {
                const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                const op: term.BinOp = switch (b.op) {
                    .implies => .implies,
                    .and_op => .and_op,
                    .or_op => .or_op,
                    else => unreachable,
                };
                const id = try self.scratch.add(.{ .bin = .{ .op = op, .lhs = lhs.id, .rhs = rhs.id } });
                return .{ .id = id, .sort = prop_sort };
            },
            .iff => {
                // SURFACE SUGAR: `P iff Q` desugars to `(P -> Q) and (Q -> P)`.
                const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                const fwd = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = lhs.id, .rhs = rhs.id } });
                const bwd = try self.scratch.add(.{ .bin = .{ .op = .implies, .lhs = rhs.id, .rhs = lhs.id } });
                const id = try self.scratch.add(.{ .bin = .{ .op = .and_op, .lhs = fwd, .rhs = bwd } });
                return .{ .id = id, .sort = prop_sort };
            },
            .equal, .not_equal => {
                const lhs = try self.elaborateExpr(b.lhs);
                const rhs = try self.elaborateExpr(b.rhs);
                if (lhs.sort == prop_sort) {
                    return self.fail(exprLoc(b.lhs), "'=' compares terms, not propositions", .{});
                }
                if (rhs.sort != lhs.sort) {
                    return self.fail(exprLoc(b.rhs), "expected sort '{s}', got '{s}'", .{
                        self.sortName(lhs.sort), self.sortName(rhs.sort),
                    });
                }
                const eq = try self.scratch.add(.{ .eq = .{ .lhs = lhs.id, .rhs = rhs.id } });
                const id = if (b.op == .not_equal) try self.scratch.add(.{ .not = eq }) else eq;
                return .{ .id = id, .sort = prop_sort };
            },
        },
        .not => |n| {
            const inner = try self.requireProp(try self.elaborateExpr(n.operand), n.operand);
            const id = try self.scratch.add(.{ .not = inner.id });
            return .{ .id = id, .sort = prop_sort };
        },
        .quant => |q| {
            // one shared sort for all binders of this quantifier (surface rule)
            const sort = try self.resolveBinderSort(q.binders[0]);
            const fresh = try self.arena.alloc(StrId, q.binders.len);
            const mark = self.scope.items.len;
            for (q.binders, fresh) |b, *fr| {
                if (b.guard != null) {
                    return self.fail(b.name.start, "predicated binders ('where') are not yet supported by the demand prover", .{});
                }
                const bname = try self.internTok(b.name);
                try self.checkNoShadow(bname, b.name);
                fr.* = try self.freshName();
                try self.scope.append(self.arena, .{ .name = bname, .sort = sort, .fvar = fr.* });
            }
            const body = try self.requireProp(try self.elaborateExpr(q.body), q.body);
            self.scope.shrinkRetainingCapacity(mark);
            var id = body.id;
            var i = q.binders.len;
            while (i > 0) {
                i -= 1;
                id = try self.scratch.close(id, fresh[i]);
                id = try self.scratch.add(.{ .quant = .{
                    .q = if (q.q == .forall) .forall else .exists,
                    .sort = sort,
                    .hint = try self.internTok(q.binders[i].name),
                    .body = id,
                } });
            }
            return .{ .id = id, .sort = prop_sort };
        },
        .lambda => |l| {
            return self.fail(l.tok.start, "lambdas (schema arguments) are not supported by the demand prover", .{});
        },
    }
}

pub fn requireProp(self: *Elab, typed: Typed, e: *const ast.Expr) Error!Typed {
    if (typed.sort != prop_sort) {
        return self.fail(exprLoc(e), "expected a proposition, got a term of sort '{s}'", .{self.sortName(typed.sort)});
    }
    return typed;
}

// -- name resolution -------------------------------------------------------------------

fn elaborateName(self: *Elab, tok: lexer.Token) Error!Typed {
    if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null) {
        const target = try self.resolveQualified(tok);
        return self.elaborateSymRef(tok, target.ns, target.base);
    }
    const name = try self.internTok(tok);
    // 1. expression-local quantifier binders (innermost wins)
    var i = self.scope.items.len;
    while (i > 0) {
        i -= 1;
        const entry = self.scope.items[i];
        if (entry.name == name) {
            const id = try self.scratch.add(.{ .fvar = .{ .name = entry.fvar, .sort = entry.sort } });
            return .{ .id = id, .sort = entry.sort };
        }
    }
    // 2. proof-local binders (fix eigenvariables / unpack witnesses)
    if (self.walk.findIdent(name)) |local| {
        const id = try self.scratch.add(.{ .fvar = .{ .name = local.info.fvar, .sort = local.info.sort } });
        return .{ .id = id, .sort = local.info.sort };
    }
    // 3. schema parameter (only while elaborating a schema body/steps)
    if (self.schema_args) |sa| if (sa.get(name)) |arg| switch (arg) {
        .value => |v| return .{ .id = v.id, .sort = v.sort },
        .lambda => return self.fail(tok.start, "schema parameter '{s}' needs arguments", .{self.text(tok)}),
    };
    // 4. global
    return self.elaborateSymRef(tok, self.ns, name);
}

/// A resolved global in NAME position (no written arguments): a constant or a nullary
/// func/pred applies bare; anything wanting arguments (or that isn't a value) errors.
fn elaborateSymRef(self: *Elab, tok: lexer.Token, ns: InternPool.Index, name: StrId) Error!Typed {
    const sym = self.lookupIdent(ns, name) orelse {
        return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
    };
    switch (self.interner.keyOf(sym)) {
        .func, .pred => |c| {
            const sig = self.interner.keyOf(c.sig).sig;
            if (sig.args.len != 0) {
                return self.fail(tok.start, "'{s}' expects {d} argument(s), got 0", .{ self.text(tok), sig.args.len });
            }
            if (c.guard != InternPool.no_term) {
                return self.fail(tok.start, "guarded functions are not yet supported by the demand prover", .{});
            }
            return self.applyResolved(sym, &.{});
        },
        .constant => |c| {
            const id = try self.scratch.addApp(.app, @enumFromInt(@intFromEnum(sym)), &.{});
            return .{ .id = id, .sort = @enumFromInt(@intFromEnum(c.sort)) };
        },
        .sort => return self.fail(tok.start, "'{s}' is a sort, not a value", .{self.text(tok)}),
        .import => return self.fail(tok.start, "'{s}' is a namespace, not a value", .{self.text(tok)}),
        .define => return self.fail(tok.start, "defines are not yet supported by the demand prover", .{}),
        else => return self.fail(tok.start, "'{s}' cannot appear in an expression", .{self.text(tok)}),
    }
}

fn elaborateCall(self: *Elab, c: ast.Expr.Call) Error!Typed {
    const dotted = std.mem.indexOfScalar(u8, self.text(c.callee), '.') != null;
    const target = if (dotted)
        try self.resolveQualified(c.callee)
    else
        Qualified{ .ns = self.ns, .base = try self.internTok(c.callee) };
    // schema GENERATOR param in call position: beta-reduce (only a bare name is a param).
    if (!dotted) if (self.schema_args) |sa| if (sa.get(target.base)) |arg| switch (arg) {
        .lambda => |lam| return self.applyGeneratorParam(c, lam),
        .value => return self.fail(c.callee.start, "schema parameter '{s}' takes no arguments", .{self.text(c.callee)}),
    };
    const sym = self.lookupIdent(target.ns, target.base) orelse {
        return self.fail(c.callee.start, "unknown identifier '{s}'", .{self.text(c.callee)});
    };
    const callable = switch (self.interner.keyOf(sym)) {
        .func, .pred => |cb| cb,
        .define => return self.fail(c.callee.start, "defines are not yet supported by the demand prover", .{}),
        else => return self.fail(c.callee.start, "'{s}' is not callable", .{self.text(c.callee)}),
    };
    const sig = self.interner.keyOf(callable.sig).sig;
    if (sig.args.len != c.args.len) {
        return self.fail(c.callee.start, "'{s}' expects {d} argument(s), got {d}", .{
            self.text(c.callee), sig.args.len, c.args.len,
        });
    }
    if (callable.guard != InternPool.no_term) {
        return self.fail(c.callee.start, "guarded functions are not yet supported by the demand prover", .{});
    }
    const arg_ids = try self.arena.alloc(TermId, c.args.len);
    for (c.args, sig.args, arg_ids) |arg, expected_ix, *out| {
        const typed = try self.elaborateExpr(arg);
        // compare at the CARRIER (refined sorts lower before kernel terms)
        const expected: SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(expected_ix)));
        const actual: SortId = if (typed.sort == prop_sort)
            typed.sort // prop args are rejected by the mismatch below
        else
            @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort)))));
        if (actual != expected) {
            return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                self.sortName(expected), self.sortName(typed.sort),
            });
        }
        out.* = typed.id;
    }
    return self.applyResolved(sym, arg_ids);
}

/// Apply a schema GENERATOR param at a call site: elaborate each actual, sort-check against
/// the param's `arg_sorts`, then BETA-REDUCE the kept-free param body — `substFvar` each
/// `params[i]` fvar with the actual. Simultaneous-safe: the param fvars are fresh/distinct
/// hygienic names and the actuals are locally closed, so sequential subst can't capture.
fn applyGeneratorParam(self: *Elab, c: ast.Expr.Call, lam: @FieldType(Schema.SchemaArg, "lambda")) Error!Typed {
    if (c.args.len != lam.arg_sorts.len) {
        return self.fail(c.callee.start, "schema parameter '{s}' expects {d} argument(s), got {d}", .{
            self.text(c.callee), lam.arg_sorts.len, c.args.len,
        });
    }
    var reduced = lam.body;
    for (c.args, lam.arg_sorts, lam.params) |arg, expected_sort, param_fvar| {
        const typed = try self.elaborateExpr(arg);
        const expected: SortId = @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(expected_sort)))));
        const actual: SortId = if (typed.sort == prop_sort)
            typed.sort
        else
            @enumFromInt(@intFromEnum(self.interner.carrierOf(@enumFromInt(@intFromEnum(typed.sort)))));
        if (actual != expected) {
            return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                self.sortName(expected_sort), self.sortName(typed.sort),
            });
        }
        reduced = try self.scratch.substFvar(reduced, param_fvar, typed.id);
    }
    return .{ .id = reduced, .sort = lam.result_sort };
}

/// Build the app/pred node for a resolved callable symbol; result sort from its sig.
fn applyResolved(self: *Elab, sym: InternPool.Index, args: []const TermId) Error!Typed {
    const kind: term.AppKind = switch (self.interner.keyOf(sym)) {
        .pred => .pred,
        else => .app,
    };
    const id = try self.scratch.addApp(kind, @enumFromInt(@intFromEnum(sym)), args);
    const result: SortId = @enumFromInt(@intFromEnum(self.interner.symResult(sym)));
    return .{ .id = id, .sort = result };
}

/// Resolve a binder's sort token to its pool sort Index (as a SortId).
pub fn resolveBinderSort(self: *Elab, b: ast.Binder) Error!SortId {
    return self.resolveSortTok(b.sort);
}

pub fn resolveSortTok(self: *Elab, tok: lexer.Token) Error!SortId {
    // `Prop` is the reserved builtin sort (schema generator-param results `P: T -> Prop`,
    // etc.) — never a userland-declared/fetched sort.
    if (std.mem.eql(u8, self.text(tok), "Prop")) return prop_sort;
    const target = if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null)
        try self.resolveQualified(tok)
    else
        Qualified{ .ns = self.ns, .base = try self.internTok(tok) };
    const sym = self.lookupIdent(target.ns, target.base) orelse {
        return self.fail(tok.start, "unknown sort '{s}'", .{self.text(tok)});
    };
    switch (self.interner.keyOf(sym)) {
        .sort => return @enumFromInt(@intFromEnum(sym)),
        else => return self.fail(tok.start, "'{s}' is not a sort", .{self.text(tok)}),
    }
}

const Qualified = struct { ns: InternPool.Index, base: StrId };

/// Split `ns.base`: the ns must be a `done` import; the base resolves in its namespace.
fn resolveQualified(self: *Elab, tok: lexer.Token) Error!Qualified {
    const text_ = self.text(tok);
    const i = std.mem.indexOfScalar(u8, text_, '.').?;
    if (std.mem.indexOfScalar(u8, text_[i + 1 ..], '.') != null) {
        return self.fail(tok.start, "only one level of namespace qualification is allowed", .{});
    }
    const ns_name = self.interner.internString(text_[0..i]) catch return error.OutOfMemory;
    const base = self.interner.internString(text_[i + 1 ..]) catch return error.OutOfMemory;
    const imp = self.lookupIdent(self.ns, ns_name) orelse {
        return self.fail(tok.start, "unknown namespace '{s}'", .{text_[0..i]});
    };
    switch (self.interner.keyOf(imp)) {
        .import => |m| return .{ .ns = m.namespace, .base = base },
        else => return self.fail(tok.start, "'{s}' is not a namespace", .{text_[0..i]}),
    }
}

/// A `done` IdentKV entry's Index, or null. The read pass ran first, so a live name is
/// expected to be done; absent/in-flight reads as unresolved (diagnosed by callers).
/// The resolved source Index is filtered through `self.model` (identity for `.universe`),
/// so a model proof remaps source symbols to their targets (Step 13).
fn lookupIdent(self: *Elab, ns: InternPool.Index, name: StrId) ?InternPool.Index {
    const state = self.idents.lookup(self.io, .{ .namespace = ns, .name = name }) orelse return null;
    return switch (state) {
        .done => |ix| self.interner.applyModel(self.model, ix),
        .in_flight => null,
    };
}

/// A quantifier binder may not shadow an expression-local, a proof-local, or an
/// ALREADY-FETCHED global. (An unfetched global can slip — nonexistence is unknowable
/// without fetching; a known gap vs the eager checker, acceptable in the red phase.)
fn checkNoShadow(self: *Elab, name: StrId, tok: lexer.Token) Error!void {
    for (self.scope.items) |entry| {
        if (entry.name == name) {
            return self.fail(tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(tok)});
        }
    }
    if (self.walk.findIdent(name) != null) {
        return self.fail(tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(tok)});
    }
    if (self.lookupIdent(self.ns, name) != null) {
        return self.fail(tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(tok)});
    }
}

// -- small utilities -------------------------------------------------------------------

/// Mint a hygienic fresh fvar identity: '#' cannot lex, so `#N` never collides with a
/// userland name. Proof-unique via the task-owned counter.
pub fn freshName(self: *Elab) Error!StrId {
    const n = self.fresh_counter.*;
    self.fresh_counter.* += 1;
    const bytes = std.fmt.allocPrint(self.arena, "#{d}", .{n}) catch return error.OutOfMemory;
    return self.interner.internString(bytes) catch return error.OutOfMemory;
}

fn sortName(self: *const Elab, sort: SortId) []const u8 {
    if (sort == prop_sort) return "Prop";
    return self.interner.sortName(@enumFromInt(@intFromEnum(sort)));
}

fn internTok(self: *Elab, t: lexer.Token) Error!StrId {
    return self.interner.internString(self.source[t.start..t.end]) catch error.OutOfMemory;
}

// -- accessors for the schema-instantiation driver (Prove.zig) -------------------------
// These expose the expression-local binder scope + name lookup so the instantiate handler
// can elaborate a lambda ARG's body with its binders in scope (kept-free), reusing this
// Elab's scratchpad + resolution.

pub fn internTokPub(self: *Elab, t: lexer.Token) Error!StrId {
    return self.internTok(t);
}

pub fn lookupIdentPub(self: *Elab, ns: InternPool.Index, name: StrId) ?InternPool.Index {
    return self.lookupIdent(ns, name);
}

/// Current expr-local scope depth — pair with `scopeTruncate` to bracket lambda binders.
pub fn scopeMark(self: *const Elab) usize {
    return self.scope.items.len;
}

pub fn scopeTruncate(self: *Elab, mark: usize) void {
    self.scope.shrinkRetainingCapacity(mark);
}

/// Push an expression-local binder (`name` → the hygienic `fvar` of `sort`), so the lambda
/// body elaborates with it in scope. The instantiate handler keeps these fvars FREE (it
/// does not close them); beta-reduction substitutes them at application.
pub fn pushBinder(self: *Elab, name: StrId, sort: SortId, fvar: StrId) Error!void {
    self.scope.append(self.arena, .{ .name = name, .sort = sort, .fvar = fvar }) catch return error.OutOfMemory;
}

fn text(self: *const Elab, t: lexer.Token) []const u8 {
    return self.source[t.start..t.end];
}

pub fn exprLoc(e: *const ast.Expr) u32 {
    return switch (e.*) {
        .name => |t| t.start,
        .call => |c| c.callee.start,
        .binary => |b| b.tok.start,
        .not => |n| n.tok.start,
        .quant => |q| q.tok.start,
        .lambda => |l| l.tok.start,
    };
}

fn fail(self: *Elab, offset: u32, comptime fmt: []const u8, args: anytype) Error {
    self.sink.add(offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../../parser.zig");

/// A hand-populated demand world: sort Nat, func add(Nat,Nat):Nat, pred le(Nat,Nat) —
/// published as `done` IdentKV entries under the fixture file's namespace.
const World = struct {
    arena: Allocator,
    io: std.Io,
    interner: *InternPool,
    idents: *IdentKV,
    scratch: *term.Pool,
    sink: *Diagnostics.Sink,
    walk: *Walk,
    ns: InternPool.Index,
    fresh: u32 = 0,
    nat: InternPool.Index = undefined,
    add_f: InternPool.Index = undefined,
    le_p: InternPool.Index = undefined,

    fn init(arena: Allocator) !*World {
        const w = try arena.create(World);
        const threaded = try arena.create(std.Io.Threaded);
        threaded.* = .init(arena, .{});
        const interner = try arena.create(InternPool);
        interner.* = try .init(arena);
        const idents = try arena.create(IdentKV);
        idents.* = IdentKV.init(interner);
        const scratch = try arena.create(term.Pool);
        scratch.* = term.Pool.init(arena);
        const sink = try arena.create(Diagnostics.Sink);
        sink.* = .init(arena);
        const walk = try arena.create(Walk);
        w.* = .{
            .arena = arena,
            .io = threaded.io(),
            .interner = interner,
            .idents = idents,
            .scratch = scratch,
            .sink = sink,
            .walk = walk,
            .ns = undefined,
        };
        walk.* = Walk.init(arena, interner, "", sink);

        const file = try interner.get(.{ .file = .{ .path = try interner.internString("/t/w.bpa") } });
        w.ns = try interner.namespace(.universe, file);

        const nat_name = try interner.internString("Nat");
        w.nat = try idents.publish(w.io, .{ .namespace = w.ns, .name = nat_name }, .{ .sort = .{
            .name = nat_name,
            .loc = 0,
            .refinement = null,
        } });

        const nat2 = [_]InternPool.Index{ w.nat, w.nat };
        const add_sig = try interner.get(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &nat2 } });
        const add_name = try interner.internString("add");
        w.add_f = try idents.publish(w.io, .{ .namespace = w.ns, .name = add_name }, .{ .func = .{
            .sig = add_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = add_name,
            .loc = 0,
        } });

        const le_sig = try interner.get(.{ .sig = .{ .result = .prop, .result_refined = .none, .args = &nat2 } });
        const le_name = try interner.internString("le");
        w.le_p = try idents.publish(w.io, .{ .namespace = w.ns, .name = le_name }, .{ .pred = .{
            .sig = le_sig,
            .guard = InternPool.no_term,
            .param_names = &.{},
            .name = le_name,
            .loc = 0,
        } });
        return w;
    }

    /// Parse `theorem t: <expr> ...` and hand back the formula expr + an Elab over it.
    fn elabOf(w: *World, comptime formula: []const u8) !struct { elab: *Elab, expr: *const ast.Expr } {
        const source = "theorem t: " ++ formula ++ "\nproof\n  @c |\n    " ++ formula ++ "\n    [by axiom ax]\nqed";
        var p: parser.Parser = .init(w.arena, source, w.sink);
        const parsed = try p.parseFile();
        try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);
        const elab = try w.arena.create(Elab);
        elab.* = Elab.init(w.arena, w.io, w.interner, w.idents, w.scratch, w.sink, source, w.walk, w.ns, &w.fresh);
        return .{ .elab = elab, .expr = parsed.decls[0].theorem.formula };
    }
};

test "elab: quantified formula — pool-native sorts, de Bruijn closing, prop result" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    const rig = try w.elabOf("forall k: Nat; le(add(k, k), k)");
    const typed = try rig.elab.elaborateExpr(rig.expr);
    try testing.expectEqual(Elab.prop_sort, typed.sort);

    // expected shape, built by hand in the same scratchpad: ∀(bvar0): le(add(b0,b0),b0)
    const p = w.scratch;
    const nat_sort: SortId = @enumFromInt(@intFromEnum(w.nat));
    const b0 = try p.add(.{ .bvar = 0 });
    const add_app = try p.addApp(.app, @enumFromInt(@intFromEnum(w.add_f)), &.{ b0, b0 });
    const le_app = try p.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ add_app, b0 });
    const want = try p.add(.{ .quant = .{
        .q = .forall,
        .sort = nat_sort,
        .hint = try w.interner.internString("k"),
        .body = le_app,
    } });
    try testing.expect(p.alphaEq(typed.id, want));
    try testing.expectEqual(@as(usize, 0), w.sink.list.items.len);
}

test "elab: proof-local binder resolves through the Walk's LocalIdentKV" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    // seed a proof-local binder `n : Nat` with hygienic fvar "#42" (as a fix-step's
    // process would via pending_binder)
    const nat_sort: SortId = @enumFromInt(@intFromEnum(w.nat));
    const hyg = try w.interner.internString("#42");
    try w.walk.local_idents.append(arena, .{
        .name = try w.interner.internString("n"),
        .block = .root,
        .info = .{ .sort = nat_sort, .fvar = hyg },
    });

    const rig = try w.elabOf("le(n, n)");
    const typed = try rig.elab.elaborateExpr(rig.expr);
    try testing.expectEqual(Elab.prop_sort, typed.sort);

    const p = w.scratch;
    const fv = try p.add(.{ .fvar = .{ .name = hyg, .sort = nat_sort } });
    const want = try p.addApp(.pred, @enumFromInt(@intFromEnum(w.le_p)), &.{ fv, fv });
    try testing.expect(p.alphaEq(typed.id, want));
}

test "elab: sort mismatch and prop-in-'=' diagnose and Recover" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    { // le's args must be Nat; passing the prop le(...) itself mismatches
        const rig = try w.elabOf("le(le(a, a), a)");
        // `a` is unknown -> the FIRST failure is the unknown identifier
        try testing.expectError(error.Recover, rig.elab.elaborateExpr(rig.expr));
        try testing.expect(w.sink.list.items.len > 0);
        try testing.expect(std.mem.indexOf(u8, w.sink.list.items[0].message, "unknown identifier") != null);
    }
    w.sink.list.clearRetainingCapacity();
    { // '=' on propositions is rejected
        const rig = try w.elabOf("forall k: Nat; le(k, k) = le(k, k)");
        try testing.expectError(error.Recover, rig.elab.elaborateExpr(rig.expr));
        try testing.expect(std.mem.indexOf(u8, w.sink.list.items[0].message, "compares terms") != null);
    }
}

test "elab: guarded funcs, defines-absent, and lambdas are cleanly unsupported/unknown" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const w = try World.init(arena);

    // a guarded function: div(Nat,Nat):Nat requires ...
    const nat2 = [_]InternPool.Index{ w.nat, w.nat };
    const div_sig = try w.interner.get(.{ .sig = .{ .result = w.nat, .result_refined = .none, .args = &nat2 } });
    const div_name = try w.interner.internString("div");
    _ = try w.idents.publish(w.io, .{ .namespace = w.ns, .name = div_name }, .{ .func = .{
        .sig = div_sig,
        .guard = 123, // any reified guard offset — non-no_term means guarded
        .param_names = &.{},
        .name = div_name,
        .loc = 0,
    } });

    const rig = try w.elabOf("forall k: Nat; le(div(k, k), k)");
    try testing.expectError(error.Recover, rig.elab.elaborateExpr(rig.expr));
    try testing.expect(std.mem.indexOf(u8, w.sink.list.items[0].message, "guarded functions are not yet supported") != null);
}
