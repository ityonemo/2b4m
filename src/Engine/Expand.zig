//! Expand — the DEFINE-EXPANSION pre-pass: the one place a `define` is unfolded.
//!
//! THE LIFECYCLE (user ruling, 2026-09-11). A `define` is a MACRO, not an identifier: it never
//! enters IdentKV, never mints a pool Item, is never the answer to "what is this name?". Before
//! any AST walk that needs MEANING (FetchTask producing a decl, ProveTask's goal phase + steps,
//! a `--fast` statement α-match, a guarded func's `requires`), the consumer runs this pass over
//! the decl's AST and gets back DEFINE-FREE AST:
//!   1. make sure every import the AST names is known — rack what is missing, suspend;
//!   2. look every name up in the define registry (`ctx.declOf`, populated by ParseTask for
//!      every file — a define is registered at PARSE, before anything can ask about it);
//!   3. substitute each define's body (params → the use's argument ASTs);
//!   4. a substituted body may name further imports and further defines — repeat.
//! Everything downstream (RefScan's name enumeration, FetchTask's kind checks on alias targets
//! and `where` guards, Elab) therefore never meets a define. FetchTask reaching a `.define`
//! decl is the invariant violated (diagnosed: "expands where used; cannot be named here").
//!
//! The parsed AST is NEVER mutated (queries/lint/fmt show what the author wrote); the pass
//! builds a new tree on the arena, sharing untouched subtrees.
//!
//! SUBSTITUTION IS HYGIENIC. A define's body is instantiated in the define's HOME context:
//!   - params → the caller's already-expanded argument ASTs, bound SIMULTANEOUSLY (a param's
//!     arg is never re-scanned for another param's name — `define_no_capture`);
//!   - the body's own binders are renamed to fresh `name#N` (never lexable, so no caller name
//!     collides; a nested expansion of the same define gets distinct names);
//!   - every free GLOBAL of the body resolves in the HOME file and is emitted as a `.symbol`
//!     IDENTITY token (lexer.Token.Tag.symbol) — the substituted body means the same thing in
//!     any file, and the ambient model still applies at elaboration;
//!   - every emitted token is re-stamped at the USE SITE (a synthetic token: start == end), so
//!     a diagnostic inside an expansion points at the use in the file being checked, not at an
//!     offset in the define's home file.
//! At the ROOT (the consumer's own AST, depth 0) free globals stay NAME tokens — the read pass
//! demands them as today — unless `symbolize_root` (an AST with no read pass of its own).
//!
//! DEMANDS: a qualified name needs its import resolved (IdentKV) and the target file PARSED;
//! a body global needs its identifier FETCHED. Each miss racks the task and records a blocker;
//! the walk continues (the unresolved name is left as written) and `finish` suspends on the
//! last blocker — the caller returns and re-runs the whole pass on resume (idempotent: every
//! earlier demand then hits `done`). ITERATIVE throughout (explicit frames; no recursion).

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const Token = lexer.Token;
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const Index = InternPool.Index;
const Context = @import("../Context.zig");
const Engine = @import("../Engine.zig");
const FetchTask = @import("FetchTask.zig");

pub const Options = struct {
    /// names bound at the root — schema params, a func's params — shadow globals, never expand.
    scope: []const StrId = &.{},
    /// resolve the ROOT's free globals to `.symbol` identities too (demanding them): for an AST
    /// elaborated by a throwaway Elab with no read pass of its own (a guarded func's `requires`).
    symbolize_root: bool = false,
    /// the MODEL the AST will be elaborated under (a transfer): a source symbol the model maps
    /// ONTO A DEFINE (`ctx.model_define_targets`) is expanded like a define — its body in the
    /// model's PARENT space (exact symbols, not subject to the model). `.universe` = none.
    model: Index = .universe,
};

const DefineSite = struct { file: Index, name: StrId };
const Param = struct { name: StrId, arg: *const ast.Expr };

/// The context a subtree is expanded IN: which file its free names resolve in, which define
/// params are bound, whether globals symbolize, where its tokens are stamped.
const Env = struct {
    file: Index,
    fid: Context.FileId,
    params: []const Param,
    /// the define this env instantiates (cycle guard through `parent`); null at the root
    def: ?DefineSite,
    parent: ?*const Env,
    symbolize: bool,
    /// the use-site offset every token of an expansion is re-stamped at; null at the root
    loc: ?u32,
    /// EXACT symbols: this body is a model target's (parent-space) — its globals are emitted
    /// with `.qualifier = .universe` so the elaborator applies NO model to them.
    exact: bool = false,
};

/// A binder in scope during the walk: its written name and the name it was renamed to
/// (the same StrId at the root; a fresh `name#N` inside an expansion).
const Scoped = struct { name: StrId, fresh: StrId };

const Expander = struct {
    ctx: *Context,
    h: *Engine.Handle,
    arena: Allocator,
    /// the ROOT file (the consumer's decl) and its dense id
    file: Index,
    fid: Context.FileId,
    opts: Options,
    /// root-context locals beyond `opts.scope`: proof-local `fix`/`unpack` names (the steps walk)
    locals: std.ArrayList(StrId) = .empty,
    /// expression-local binders, innermost last (pushed/popped by quantifier/lambda frames)
    scope: std.ArrayList(Scoped) = .empty,
    /// the most recent demand this run could not satisfy (rack → resume → retry)
    blocker: ?Engine.TaskIndex = null,
    /// a misuse was diagnosed (no result this run)
    failed: bool = false,

    fn root(self: *const Expander) Env {
        return .{ .file = self.file, .fid = self.fid, .params = &.{}, .def = null, .parent = null, .symbolize = self.opts.symbolize_root, .loc = null };
    }

    // -- diagnostics -------------------------------------------------------------------

    fn fail(self: *Expander, loc: u32, comptime fmt: []const u8, args: anytype) Allocator.Error!void {
        // the sink already points at the root file (the consumer set current_file); every
        // offset this pass reports is a root-file offset (use sites / restamped tokens).
        self.ctx.sink.add(loc, fmt, args) catch return error.OutOfMemory;
        self.failed = true;
    }

    fn text(self: *const Expander, name: StrId) []const u8 {
        return self.ctx.interner.stringBytes(name);
    }

    // -- demands ---------------------------------------------------------------------

    /// The file a (possibly qualified) token's base name lives in, resolving the qualifier as
    /// an import of `env.file`. Null = not known yet (a demand was racked / a parse is pending)
    /// or not an import (elaboration diagnoses the misuse).
    const Target = struct { file: Index, fid: Context.FileId };
    fn targetOf(self: *Expander, env: *const Env, tok: Token) Allocator.Error!?Target {
        if (tok.qualifier == Index.none) return .{ .file = env.file, .fid = env.fid };
        const ns = try self.ctx.interner.namespace(.universe, env.file);
        const state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = ns, .name = tok.qualifier }) orelse {
            self.blocker = try self.h.rackIndexed(try FetchTask.new(self.ctx.arena, .{ .file = env.file, .name = tok.qualifier, .loc = tok.start, .loc_file = env.file }));
            return null;
        };
        const imp = switch (state) {
            .done => |ix| ix,
            .in_flight => |owner| {
                self.blocker = owner;
                return null;
            },
        };
        const target_file = switch (self.ctx.interner.keyOf(imp)) {
            .import => |m| self.ctx.interner.keyOf(m.namespace).namespace.file,
            else => return null, // not a namespace — the elaborator diagnoses
        };
        switch (try self.ctx.demandParse(self.h, target_file)) {
            .parsed => {},
            .parsing => |t| {
                self.blocker = t;
                return null;
            },
            .unparsed => return null, // undiscovered — the elaborator diagnoses
        }
        const fid = self.ctx.pool_file.get(target_file) orelse return null;
        return .{ .file = target_file, .fid = fid };
    }

    const Resolved = union(enum) {
        define: struct { site: DefineSite, fid: Context.FileId, decl: *const ast.Decl, exact: bool = false },
        other, // a non-define (or nothing) — resolves through the ordinary identifier path
        pending, // a demand is outstanding; leave the name as written this run
    };

    /// Is `tok` (resolved in `env`) a define — directly, through a chain of const/func/pred
    /// ALIASES ending on one (followed by name through the registry: identity by origin; a
    /// looping chain is cut by the bound), or — under a model — a source symbol the model maps
    /// ONTO a define (a `.model_target` resolution: the body is the parent space's, exact)?
    fn resolveDefine(self: *Expander, env: *const Env, tok: Token) Allocator.Error!Resolved {
        const direct = try self.resolveDeclDefine(env, tok);
        if (direct != .other) return direct;
        // model-mapped: only for names the MODEL applies to (a parent-space body is exact), and
        // only for names the registry knows as SYMBOLS (const/func/pred, local or alias) — a fact
        // name in argument position (`assoc(opAssoc)`) or an unknown name is never demanded as
        // an identifier here (the elaborator/read pass own those diagnostics).
        if (self.opts.model == .universe or self.opts.model == Index.none or env.exact) return .other;
        const target = (try self.targetOf(env, tok)) orelse return if (self.blocker != null) .pending else .other;
        const sym_decl = self.ctx.declOf(target.fid, tok.name) orelse return .other;
        switch (sym_decl.*) {
            .constant, .func, .pred => {},
            else => return .other,
        }
        const sym = (try self.demandGlobal(env, tok)) orelse return if (self.blocker != null) .pending else .other;
        const d = self.ctx.modelDefineTarget(self.opts.model, sym) orelse return .other;
        const fid = self.ctx.pool_file.get(d.file) orelse return .other;
        const def_decl = self.ctx.declOf(fid, d.name) orelse return .other;
        return .{ .define = .{ .site = .{ .file = d.file, .name = d.name }, .fid = fid, .decl = def_decl, .exact = true } };
    }

    fn resolveDeclDefine(self: *Expander, env: *const Env, tok: Token) Allocator.Error!Resolved {
        var target = (try self.targetOf(env, tok)) orelse return if (self.blocker != null) .pending else .other;
        var name = tok.name;
        var hops: u32 = 0;
        while (hops < 64) : (hops += 1) {
            const decl = self.ctx.declOf(target.fid, name) orelse return .other;
            const alias: ast.Alias = switch (decl.*) {
                .define => return .{ .define = .{ .site = .{ .file = target.file, .name = name }, .fid = target.fid, .decl = decl } },
                .constant => |c| switch (c) {
                    .alias => |a| a,
                    else => return .other,
                },
                .func => |f| switch (f) {
                    .alias => |a| a,
                    else => return .other,
                },
                .pred => |p| switch (p) {
                    .alias => |a| a,
                    else => return .other,
                },
                else => return .other,
            };
            // follow the alias: its target resolves in the ALIAS's file.
            const alias_env: Env = .{ .file = target.file, .fid = target.fid, .params = &.{}, .def = null, .parent = null, .symbolize = false, .loc = null };
            target = (try self.targetOf(&alias_env, alias.target)) orelse return if (self.blocker != null) .pending else .other;
            name = alias.target.name;
        }
        return .other;
    }

    /// The identifier `tok` names (resolved in `env`), demanding it if unfetched. Null =
    /// pending (blocker recorded) or unresolvable here (left to the elaborator).
    fn demandGlobal(self: *Expander, env: *const Env, tok: Token) Allocator.Error!?Index {
        const target = (try self.targetOf(env, tok)) orelse return null;
        const ns = try self.ctx.interner.namespace(.universe, target.file);
        const state = self.ctx.idents.lookup(self.ctx.io, .{ .namespace = ns, .name = tok.name }) orelse {
            self.blocker = try self.h.rackIndexed(try FetchTask.new(self.ctx.arena, .{ .file = target.file, .name = tok.name, .loc = env.loc orelse tok.start, .loc_file = self.file }));
            return null;
        };
        return switch (state) {
            .done => |ix| ix,
            .in_flight => |owner| {
                self.blocker = owner;
                return null;
            },
        };
    }

    // -- tokens ----------------------------------------------------------------------

    /// A token as it appears in the OUTPUT: re-stamped at the expansion's use site (a synthetic
    /// token, start == end) inside an expansion; verbatim at the root.
    fn stamp(env: *const Env, tok: Token) Token {
        const loc = env.loc orelse return tok;
        var t = tok;
        t.start = loc;
        t.end = loc;
        return t;
    }

    fn symTok(env: *const Env, tok: Token, sym: Index) Token {
        const loc = env.loc orelse tok.start;
        return .{ .tag = .symbol, .start = loc, .end = loc, .name = sym, .qualifier = if (env.exact) .universe else .none };
    }

    fn nameTok(env: *const Env, tok: Token, name: StrId) Token {
        var t = stamp(env, tok);
        t.name = name;
        return t;
    }

    fn fresh(self: *Expander, name: StrId) Allocator.Error!StrId {
        self.ctx.expand_fresh += 1;
        const bytes = try std.fmt.allocPrint(self.arena, "{s}#{d}", .{ self.text(name), self.ctx.expand_fresh });
        return self.ctx.interner.internString(bytes) catch return error.OutOfMemory;
    }

    /// A bare name's LOCAL binding, innermost first: an expression binder (renamed inside an
    /// expansion), else a root local (proof `fix`/`unpack` names, the root `scope`).
    fn local(self: *const Expander, env: *const Env, name: StrId) ?StrId {
        var i = self.scope.items.len;
        while (i > 0) {
            i -= 1;
            if (self.scope.items[i].name == name) return self.scope.items[i].fresh;
        }
        // root locals are only visible at the root (a define body sees no caller local).
        if (env.parent != null) return null;
        for (self.locals.items) |l| if (l == name) return name;
        for (self.opts.scope) |s| if (s == name) return name;
        return null;
    }

    /// A BINDER-GUARD token: like `globalTok`, but never symbolizes while the name's
    /// define-resolution is outstanding — symbolizing demands it as an IDENTIFIER, and a name
    /// that turns out to be a define is a misuse there (FetchTask's `.define` arm). The
    /// guard desugaring handles a RESOLVED define; this covers the pending window.
    fn guardTok(self: *Expander, env: *const Env, tok: Token) Allocator.Error!Token {
        if (tok.tag != .symbol and (try self.resolveDefine(env, tok)) == .pending) return stamp(env, tok);
        return self.globalTok(env, tok);
    }

    /// A GLOBAL-position token (a callee, a sort, a guard, a bare/qualified name that is no
    /// local/param/define): symbolized when the env demands it, else copied (re-stamped).
    fn globalTok(self: *Expander, env: *const Env, tok: Token) Allocator.Error!Token {
        if (tok.tag == .symbol) return tok;
        if (!env.symbolize) return stamp(env, tok);
        const sym = (try self.demandGlobal(env, tok)) orelse return stamp(env, tok);
        return symTok(env, tok, sym);
    }

    fn box(self: *Expander, e: ast.Expr) Allocator.Error!*const ast.Expr {
        const p = try self.arena.create(ast.Expr);
        p.* = e;
        return p;
    }

    // -- the expression machine ------------------------------------------------------

    const Frame = union(enum) {
        expand: struct { e: *const ast.Expr, env: *const Env },
        rebuild: struct { e: *const ast.Expr, env: *const Env, binders: []const ast.Binder = &.{} },
        pop_scope: usize,
    };

    /// Expand `root_e` in the root env. Returns the (possibly shared) expanded tree.
    fn expandExpr(self: *Expander, root_e: *const ast.Expr, root_env: *const Env) Allocator.Error!*const ast.Expr {
        var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
        defer scratch.deinit();
        const a = scratch.allocator();
        var work: std.ArrayList(Frame) = .empty;
        var results: std.ArrayList(*const ast.Expr) = .empty;
        try work.append(a, .{ .expand = .{ .e = root_e, .env = root_env } });
        while (work.pop()) |frame| switch (frame) {
            .pop_scope => |mark| self.scope.shrinkRetainingCapacity(mark),
            .expand => |x| switch (x.e.*) {
                .name => |tok| if (try self.leaf(x.env, x.e, tok, &work, a)) |r| try results.append(a, r),
                .call => |c| {
                    try work.append(a, .{ .rebuild = .{ .e = x.e, .env = x.env } });
                    var i: usize = c.args.len;
                    while (i > 0) {
                        i -= 1;
                        try work.append(a, .{ .expand = .{ .e = c.args[i], .env = x.env } });
                    }
                },
                .binary => |b| {
                    try work.append(a, .{ .rebuild = .{ .e = x.e, .env = x.env } });
                    try work.append(a, .{ .expand = .{ .e = b.rhs, .env = x.env } });
                    try work.append(a, .{ .expand = .{ .e = b.lhs, .env = x.env } });
                },
                .not => |n| {
                    try work.append(a, .{ .rebuild = .{ .e = x.e, .env = x.env } });
                    try work.append(a, .{ .expand = .{ .e = n.operand, .env = x.env } });
                },
                .quant, .lambda => {
                    // INLINE `where` over a DEFINE'd guard (`forall x: Nat where isBig; B`): the
                    // guard is a predicate MACRO, so the binder desugars to its meaning — one
                    // single-binder quantifier per binder, the guard's call as the body's
                    // antecedent (∀: `isBig(x) -> B`) / conjunct (∃: `isBig(x) and B`) — and the
                    // rewritten node is expanded like any other (the call expands). Matches the
                    // kernel's guarded-∀ shape (`∀x; guard(x) -> …`, one binder at a time). An
                    // opaque guard stays a binder guard (the elaborator relativizes it).
                    if (x.e.* == .quant) if (try self.desugarDefineGuards(x.env, x.e.quant)) |rewritten| {
                        try work.append(a, .{ .expand = .{ .e = rewritten, .env = x.env } });
                        continue;
                    };
                    const binders = switch (x.e.*) {
                        .quant => |q| q.binders,
                        .lambda => |l| l.binders,
                        else => unreachable,
                    };
                    const body = switch (x.e.*) {
                        .quant => |q| q.body,
                        .lambda => |l| l.body,
                        else => unreachable,
                    };
                    const mark = self.scope.items.len;
                    const nb = try self.arena.alloc(ast.Binder, binders.len);
                    for (binders, nb) |b, *out| {
                        const fresh_name = if (x.env.symbolize) try self.fresh(b.name.name) else b.name.name;
                        try self.scope.append(self.arena, .{ .name = b.name.name, .fresh = fresh_name });
                        out.* = .{
                            .name = nameTok(x.env, b.name, fresh_name),
                            .sort = try self.globalTok(x.env, b.sort),
                            // a binder GUARD naming a define is desugared away above; one that
                            // survives here is an opaque predicate, so symbolize it — unless its
                            // resolution is still PENDING, in which case leave the name as
                            // written (the pass re-runs) rather than demanding a define as an
                            // identifier. `guardTok` makes that distinction.
                            .guard = if (b.guard) |g| try self.guardTok(x.env, g) else null,
                        };
                    }
                    try work.append(a, .{ .pop_scope = mark });
                    try work.append(a, .{ .rebuild = .{ .e = x.e, .env = x.env, .binders = nb } });
                    try work.append(a, .{ .expand = .{ .e = body, .env = x.env } });
                },
            },
            .rebuild => |r| switch (r.e.*) {
                .call => |c| {
                    const n = c.args.len;
                    const args = try self.arena.dupe(*const ast.Expr, results.items[results.items.len - n ..]);
                    results.items.len -= n;
                    try self.rebuildCall(r.env, c, args, &work, &results, a);
                },
                .binary => |b| {
                    const rhs = results.pop().?;
                    const lhs = results.pop().?;
                    try results.append(a, try self.box(.{ .binary = .{ .op = b.op, .tok = stamp(r.env, b.tok), .lhs = lhs, .rhs = rhs, .paren = b.paren } }));
                },
                .not => |n| {
                    const operand = results.pop().?;
                    try results.append(a, try self.box(.{ .not = .{ .tok = stamp(r.env, n.tok), .operand = operand, .paren = n.paren } }));
                },
                .quant => |q| {
                    const body = results.pop().?;
                    try results.append(a, try self.box(.{ .quant = .{ .q = q.q, .tok = stamp(r.env, q.tok), .binders = r.binders, .body = body } }));
                },
                .lambda => |l| {
                    const body = results.pop().?;
                    try results.append(a, try self.box(.{ .lambda = .{ .tok = stamp(r.env, l.tok), .binders = r.binders, .body = body } }));
                },
                .name => unreachable,
            },
        };
        std.debug.assert(results.items.len == 1);
        return results.items[0];
    }

    /// If any binder of `q` carries a DEFINE'd guard, the desugared quantifier (see the `.quant`
    /// arm); else null. A guard whose resolution is pending is treated as opaque this run (the
    /// resume re-expands from the parsed AST).
    fn desugarDefineGuards(self: *Expander, env: *const Env, q: @FieldType(ast.Expr, "quant")) Allocator.Error!?*const ast.Expr {
        var any = false;
        for (q.binders) |b| if (b.guard) |g| switch (try self.resolveDefine(env, g)) {
            .define => any = true,
            // PENDING: a demand is outstanding (an alias hop needs its import). Leave the
            // quantifier alone — `finish` suspends and the whole pass re-runs — rather than
            // reading it as "not a define" and leaving an opaque binder guard, which would
            // then be demanded as an IDENTIFIER (and a define is never one).
            .pending => return null,
            .other => {},
        };
        if (!any) return null;
        var body = q.body;
        var i = q.binders.len;
        while (i > 0) {
            i -= 1;
            const b = q.binders[i];
            const nb = try self.arena.alloc(ast.Binder, 1);
            nb[0] = b;
            if (b.guard) |g| if ((try self.resolveDefine(env, g)) == .define) {
                // (resolution settled above: a PENDING guard returned early.)
                const arg = try self.box(.{ .name = b.name });
                const args = try self.arena.alloc(*const ast.Expr, 1);
                args[0] = arg;
                const gcall = try self.box(.{ .call = .{ .callee = g, .args = args } });
                const op: ast.Expr.BinOp = if (q.q == .forall) .implies else .and_op;
                body = try self.box(.{ .binary = .{ .op = op, .tok = q.tok, .lhs = gcall, .rhs = body } });
                nb[0].guard = null;
            };
            body = try self.box(.{ .quant = .{ .q = q.q, .tok = q.tok, .binders = nb, .body = body } });
        }
        return body;
    }

    /// A NAME position. A define param → its bound arg; a binder → its (renamed) token; a
    /// nullary define → its body (pushed for expansion in the define's env — NULL here, the
    /// body frame produces the result in this leaf's place); a global → symbolized or copied.
    fn leaf(self: *Expander, env: *const Env, e: *const ast.Expr, tok: Token, work: *std.ArrayList(Frame), a: Allocator) Allocator.Error!?*const ast.Expr {
        if (tok.tag == .symbol) return e;
        if (tok.qualifier == Index.none) {
            for (env.params) |p| if (p.name == tok.name) return p.arg;
            if (self.local(env, tok.name)) |fresh_name| {
                if (fresh_name == tok.name and env.loc == null) return e;
                return self.box(.{ .name = nameTok(env, tok, fresh_name) });
            }
        }
        switch (try self.resolveDefine(env, tok)) {
            .define => |d| {
                const def = d.decl.define;
                if (def.params.len != 0) {
                    try self.fail(env.loc orelse tok.start, "'{s}' is a define with {d} parameter(s); apply it: {s}(…)", .{ self.text(tok.name), def.params.len, self.text(tok.name) });
                    return e;
                }
                const inner = try self.instantiate(env, d.site, d.fid, def, tok, &.{}, &.{}, d.exact);
                if (inner) |ienv| {
                    // the body expands in the define's env; its result lands in this leaf's place.
                    try work.append(a, .{ .expand = .{ .e = def.value, .env = ienv } });
                    return null;
                }
                return e;
            },
            .pending => return e,
            .other => {},
        }
        const t = try self.globalTok(env, tok);
        if (t.tag == tok.tag and t.name == tok.name and env.loc == null) return e;
        return self.box(.{ .name = t });
    }

    /// A CALL, its args already expanded. A define callee → its body instantiated at the args
    /// (pushed for expansion); a param callee is a misuse; a global callee symbolizes/copies.
    fn rebuildCall(self: *Expander, env: *const Env, c: ast.Expr.Call, args: []const *const ast.Expr, work: *std.ArrayList(Frame), results: *std.ArrayList(*const ast.Expr), a: Allocator) Allocator.Error!void {
        const tok = c.callee;
        if (tok.tag != .symbol and tok.qualifier == Index.none) {
            for (env.params) |p| if (p.name == tok.name) {
                try self.fail(env.loc orelse tok.start, "define parameter '{s}' is not callable", .{self.text(tok.name)});
                return results.append(a, try self.box(.{ .call = .{ .callee = stamp(env, tok), .args = args } }));
            };
            if (self.local(env, tok.name)) |fresh_name| {
                return results.append(a, try self.box(.{ .call = .{ .callee = nameTok(env, tok, fresh_name), .args = args } }));
            }
        }
        if (tok.tag != .symbol) switch (try self.resolveDefine(env, tok)) {
            // PENDING: a demand is outstanding (an alias hop needs its import fetched, say).
            // Leave the call as written — `finish` suspends and the whole pass re-runs — and
            // do NOT fall through to `globalTok`: symbolizing would demand this name as an
            // IDENTIFIER, and if it resolves to a define that demand is a misuse (FetchTask's
            // `.define` arm), diagnosed against another file's offsets.
            .pending => return results.append(a, try self.box(.{ .call = .{ .callee = stamp(env, tok), .args = args } })),
            .define => |d| {
                const def = d.decl.define;
                if (def.params.len != args.len) {
                    try self.fail(env.loc orelse tok.start, "'{s}' expects {d} argument(s), got {d}", .{ self.text(tok.name), def.params.len, args.len });
                    return results.append(a, try self.box(.{ .call = .{ .callee = stamp(env, tok), .args = args } }));
                }
                const inner = try self.instantiate(env, d.site, d.fid, def, tok, def.params, args, d.exact);
                if (inner) |ienv| {
                    // the body frame produces this call's result in its place.
                    try work.append(a, .{ .expand = .{ .e = def.value, .env = ienv } });
                    return;
                }
                return results.append(a, try self.box(.{ .call = .{ .callee = stamp(env, tok), .args = args } }));
            },
            .other => {},
        };
        const callee = try self.globalTok(env, tok);
        try results.append(a, try self.box(.{ .call = .{ .callee = callee, .args = args } }));
    }

    /// Build the env a define's body expands in: params bound to `args` (simultaneously — the
    /// map is consulted per name, args are never re-scanned), home file, symbolizing, tokens
    /// stamped at the use site. Null after a diagnosed misuse (cycle) or a pending demand
    /// the alias-shape lint needs.
    fn instantiate(self: *Expander, env: *const Env, site: DefineSite, fid: Context.FileId, def: anytype, use: Token, params: []const Token, args: []const *const ast.Expr, exact: bool) Allocator.Error!?*const Env {
        const use_loc = env.loc orelse use.start;
        // cycle guard: the define is already being instantiated up the chain.
        var cur: ?*const Env = env;
        while (cur) |c| : (cur = c.parent) {
            if (c.def) |d| if (d.file == site.file and d.name == site.name) {
                try self.fail(use_loc, "cyclic define '{s}'", .{self.text(site.name)});
                return null;
            };
        }
        const bound = try self.arena.alloc(Param, params.len);
        for (params, args, bound) |p, arg, *b| b.* = .{ .name = p.name, .arg = arg };
        const ienv = try self.arena.create(Env);
        // a model target's body is parent-space (exact); a body reached FROM an exact body is too.
        ienv.* = .{ .file = site.file, .fid = fid, .params = bound, .def = site, .parent = env, .symbolize = true, .loc = use_loc, .exact = exact or env.exact };
        try self.lintAliasShaped(ienv, site, def, use_loc);
        return ienv;
    }

    /// A define that merely FORWARDS an opaque symbol — `define f(p1, …, pn) = ns.g(p1, …, pn)`
    /// (each arg the same-position param, nothing else) or `define X = ns.C` — is an ALIAS
    /// written as a macro: an alias binds the local name to the origin's identity (`pred f =
    /// ns.g`, keeping its KIND for downstream aliases); a define is a substitution with no
    /// identity of its own. Hard error unless --draft; diagnosed once per define, at its first
    /// use. Forwarding another DEFINE is left alone (there is no alias form for a macro).
    fn lintAliasShaped(self: *Expander, ienv: *const Env, site: DefineSite, def: anytype, use_loc: u32) Allocator.Error!void {
        if (self.ctx.verify.draft) return;
        const callee: Token = switch (def.value.*) {
            .name => |tok| if (def.params.len == 0) tok else return,
            .call => |c| blk: {
                if (c.args.len != def.params.len) return;
                for (c.args, def.params) |arg, param| {
                    if (arg.* != .name) return;
                    if (arg.name.qualifier != Index.none or arg.name.name != param.name) return;
                }
                break :blk c.callee;
            },
            else => return,
        };
        for (def.params) |param| if (callee.qualifier == Index.none and callee.name == param.name) return;
        if (self.ctx.expand_linted.contains(.{ .file = site.file, .name = site.name })) return;
        switch (try self.resolveDefine(ienv, callee)) {
            .define, .pending => return, // forwards a define / not resolvable yet — no verdict
            .other => {},
        }
        const target = (try self.demandGlobal(ienv, callee)) orelse return;
        const keyword: []const u8 = switch (self.ctx.interner.keyOf(target)) {
            .constant => "const",
            .func => "func",
            .pred => "pred",
            else => return,
        };
        try self.ctx.expand_linted.put(self.ctx.arena, .{ .file = site.file, .name = site.name }, {});
        const cname = if (callee.qualifier != Index.none)
            try std.fmt.allocPrint(self.arena, "{s}.{s}", .{ self.text(callee.qualifier), self.text(callee.name) })
        else
            self.text(callee.name);
        try self.fail(use_loc, "define '{s}' only forwards '{s}' — it is an alias, not a macro; write `{s} {s} = {s}` (--draft allows)", .{ self.text(site.name), cname, keyword, self.text(site.name), cname });
    }

    // -- the steps machine -----------------------------------------------------------

    /// How a finished block frame attaches to its parent.
    const Finish = union(enum) {
        root,
        assume: struct { label: Token, formula: *const ast.Expr },
        fix: struct { label: Token, name: Token, sort: Token },
        unpack: struct { label: Token, name: Token, sort: Token, from: Token },
        arm: struct { label: Token, assumption: *const ast.Expr },
    };

    const BlockFrame = struct {
        steps: []const ast.Step,
        idx: usize = 0,
        out: std.ArrayList(ast.Step) = .empty,
        scope_mark: usize,
        finish: Finish,
    };

    /// A `case` in progress: its arms expand one block frame at a time.
    const CaseFrame = struct {
        label: Token,
        goal: *const ast.Expr,
        disj: Token,
        arms: []const ast.Step.CaseBlock.Arm,
        arm_idx: usize = 0,
        out: std.ArrayList(ast.Step.CaseBlock.Arm) = .empty,
    };

    fn expandSteps(self: *Expander, steps: []const ast.Step, env: *const Env) Allocator.Error![]const ast.Step {
        var scratch: std.heap.ArenaAllocator = .init(self.ctx.gpa);
        defer scratch.deinit();
        const a = scratch.allocator();
        var blocks: std.ArrayList(BlockFrame) = .empty;
        var cases: std.ArrayList(CaseFrame) = .empty;
        try blocks.append(a, .{ .steps = steps, .scope_mark = self.locals.items.len, .finish = .root });
        while (true) {
            const f = &blocks.items[blocks.items.len - 1];
            if (f.idx < f.steps.len) {
                const step = f.steps[f.idx];
                switch (step.body) {
                    .claim => |c| {
                        const formula = try self.expandExpr(c.formula, env);
                        const args = try self.arena.alloc(*const ast.Expr, c.args.len);
                        for (c.args, args) |arg, *out| out.* = try self.expandExpr(arg, env);
                        try f.out.append(self.arena, .{ .label = step.label, .body = .{ .claim = .{
                            .formula = formula,
                            .kind = c.kind,
                            .rule = c.rule,
                            .schema = c.schema,
                            .args = args,
                            .refs = c.refs,
                            .fallback = c.fallback,
                        } } });
                        f.idx += 1;
                    },
                    .assume => |blk| {
                        const formula = try self.expandExpr(blk.formula, env);
                        try blocks.append(a, .{ .steps = blk.steps, .scope_mark = self.locals.items.len, .finish = .{ .assume = .{ .label = step.label, .formula = formula } } });
                    },
                    .fix => |blk| {
                        const mark = self.locals.items.len;
                        try self.locals.append(self.arena, blk.name.name);
                        try blocks.append(a, .{ .steps = blk.steps, .scope_mark = mark, .finish = .{ .fix = .{ .label = step.label, .name = blk.name, .sort = blk.sort } } });
                    },
                    .unpack => |blk| {
                        const mark = self.locals.items.len;
                        try self.locals.append(self.arena, blk.name.name);
                        try blocks.append(a, .{ .steps = blk.steps, .scope_mark = mark, .finish = .{ .unpack = .{ .label = step.label, .name = blk.name, .sort = blk.sort, .from = blk.from } } });
                    },
                    .case => |cb| {
                        const goal = try self.expandExpr(cb.goal, env);
                        try cases.append(a, .{ .label = step.label, .goal = goal, .disj = cb.disj, .arms = cb.arms });
                        // the first arm's frame; later arms are pushed as each finishes.
                        try self.pushArm(&blocks, &cases, env, a);
                    },
                }
                continue;
            }
            // this block is complete: attach it to its parent (or return the root).
            var done = blocks.pop().?;
            self.locals.shrinkRetainingCapacity(done.scope_mark);
            const body = try done.out.toOwnedSlice(self.arena);
            switch (done.finish) {
                .root => return body,
                .assume => |x| {
                    const parent = &blocks.items[blocks.items.len - 1];
                    try parent.out.append(self.arena, .{ .label = x.label, .body = .{ .assume = .{ .formula = x.formula, .steps = body } } });
                    parent.idx += 1;
                },
                .fix => |x| {
                    const parent = &blocks.items[blocks.items.len - 1];
                    try parent.out.append(self.arena, .{ .label = x.label, .body = .{ .fix = .{ .name = x.name, .sort = x.sort, .steps = body } } });
                    parent.idx += 1;
                },
                .unpack => |x| {
                    const parent = &blocks.items[blocks.items.len - 1];
                    try parent.out.append(self.arena, .{ .label = x.label, .body = .{ .unpack = .{ .name = x.name, .sort = x.sort, .from = x.from, .steps = body } } });
                    parent.idx += 1;
                },
                .arm => |x| {
                    const cf = &cases.items[cases.items.len - 1];
                    try cf.out.append(self.arena, .{ .label = x.label, .assumption = x.assumption, .steps = body });
                    cf.arm_idx += 1;
                    if (cf.arm_idx < cf.arms.len) {
                        try self.pushArm(&blocks, &cases, env, a);
                    } else {
                        var finished = cases.pop().?;
                        const parent = &blocks.items[blocks.items.len - 1];
                        try parent.out.append(self.arena, .{ .label = finished.label, .body = .{ .case = .{
                            .goal = finished.goal,
                            .disj = finished.disj,
                            .arms = try finished.out.toOwnedSlice(self.arena),
                        } } });
                        parent.idx += 1;
                    }
                },
            }
        }
    }

    fn pushArm(self: *Expander, blocks: *std.ArrayList(BlockFrame), cases: *std.ArrayList(CaseFrame), env: *const Env, a: Allocator) Allocator.Error!void {
        const cf = &cases.items[cases.items.len - 1];
        const arm = cf.arms[cf.arm_idx];
        const assumption = try self.expandExpr(arm.assumption, env);
        try blocks.append(a, .{ .steps = arm.steps, .scope_mark = self.locals.items.len, .finish = .{ .arm = .{ .label = arm.label, .assumption = assumption } } });
    }

    /// Yield for the caller: suspend on the last blocker, or report a diagnosed misuse.
    fn finish(self: *Expander) Verdict {
        if (self.blocker) |b| {
            self.h.suspendOn(b);
            return .suspended;
        }
        if (self.failed) return .failed;
        return .ready;
    }
};

const Verdict = enum { ready, suspended, failed };

/// A pass's result: `ready` (the define-free AST), `suspended` (a demand was racked and
/// `h.suspendOn` set — return; the consumer re-runs on resume), or `failed` (a misuse was
/// diagnosed — no publish).
pub fn Outcome(comptime T: type) type {
    return union(enum) { ready: T, suspended, failed };
}

fn init(ctx: *Context, h: *Engine.Handle, file: Index, opts: Options) Allocator.Error!?Expander {
    const fid = ctx.pool_file.get(file) orelse return null;
    return .{ .ctx = ctx, .h = h, .arena = ctx.arena, .file = file, .fid = fid, .opts = opts };
}

/// Expand one expression (a stated formula, a `requires` precondition) in `file`'s context.
pub fn expandFormula(ctx: *Context, h: *Engine.Handle, file: Index, e: *const ast.Expr, opts: Options) Allocator.Error!Outcome(*const ast.Expr) {
    var x = (try init(ctx, h, file, opts)) orelse return .{ .ready = e }; // undiscovered file — the caller diagnoses
    const env = x.root();
    const out = try x.expandExpr(e, &env);
    return switch (x.finish()) {
        .ready => .{ .ready = out },
        .suspended => .suspended,
        .failed => .failed,
    };
}

pub const Proof = struct { formula: *const ast.Expr, steps: []const ast.Step };

/// Expand a proof-carrying decl (stated formula + steps) in `file`'s context.
pub fn expandProof(ctx: *Context, h: *Engine.Handle, file: Index, formula: *const ast.Expr, steps: []const ast.Step, opts: Options) Allocator.Error!Outcome(Proof) {
    var x = (try init(ctx, h, file, opts)) orelse return .{ .ready = .{ .formula = formula, .steps = steps } };
    const env = x.root();
    const f = try x.expandExpr(formula, &env);
    const s = try x.expandSteps(steps, &env);
    return switch (x.finish()) {
        .ready => .{ .ready = .{ .formula = f, .steps = s } },
        .suspended => .suspended,
        .failed => .failed,
    };
}

/// The SOURCE-AST map for a model transfer: pairs each step formula / claim arg / assume
/// formula / case goal / arm assumption of `model_proof` (expanded WITH the model) with the
/// same node of `source_proof` (expanded WITHOUT it). Both derive from one parsed decl, so the
/// STEP structure is identical; only expression subtrees differ (and an unchanged subtree is
/// the same pointer in both — those need no entry). ITERATIVE lockstep over the blocks.
pub fn pairSource(ctx: *Context, model_proof: Proof, source_proof: Proof) Allocator.Error!*const std.AutoHashMapUnmanaged(*const ast.Expr, *const ast.Expr) {
    const map = try ctx.arena.create(std.AutoHashMapUnmanaged(*const ast.Expr, *const ast.Expr));
    map.* = .empty;
    if (model_proof.formula != source_proof.formula) try map.put(ctx.arena, model_proof.formula, source_proof.formula);
    var scratch: std.heap.ArenaAllocator = .init(ctx.gpa);
    defer scratch.deinit();
    const a = scratch.allocator();
    const Pair = struct { m: []const ast.Step, s: []const ast.Step };
    var work: std.ArrayList(Pair) = .empty;
    try work.append(a, .{ .m = model_proof.steps, .s = source_proof.steps });
    while (work.pop()) |pr| {
        std.debug.assert(pr.m.len == pr.s.len);
        for (pr.m, pr.s) |ms, ss| switch (ms.body) {
            .claim => |mc| {
                const sc = ss.body.claim;
                if (mc.formula != sc.formula) try map.put(ctx.arena, mc.formula, sc.formula);
                for (mc.args, sc.args) |ma, sa| if (ma != sa) try map.put(ctx.arena, ma, sa);
            },
            .assume => |mb| {
                const sb = ss.body.assume;
                if (mb.formula != sb.formula) try map.put(ctx.arena, mb.formula, sb.formula);
                try work.append(a, .{ .m = mb.steps, .s = sb.steps });
            },
            .fix => |mb| try work.append(a, .{ .m = mb.steps, .s = ss.body.fix.steps }),
            .unpack => |mb| try work.append(a, .{ .m = mb.steps, .s = ss.body.unpack.steps }),
            .case => |mc| {
                const sc = ss.body.case;
                if (mc.goal != sc.goal) try map.put(ctx.arena, mc.goal, sc.goal);
                for (mc.arms, sc.arms) |ma, sa| {
                    if (ma.assumption != sa.assumption) try map.put(ctx.arena, ma.assumption, sa.assumption);
                    try work.append(a, .{ .m = ma.steps, .s = sa.steps });
                }
            },
        };
    }
    return map;
}
