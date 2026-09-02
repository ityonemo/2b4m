//! Kernel terms: flat pool of immutable nodes, u32 ids, LOCALLY NAMELESS —
//! bound variables are de Bruijn indices (`bvar`), free variables are named
//! (`fvar`). This is the soundness core:
//!   - substituting a locally-closed term for an fvar can never capture
//!     (binders are indices, not names), so substFvar needs no renaming;
//!   - alpha-equivalence is structural equality ignoring binder name hints;
//!   - eigenvariable conditions are fvar occurrence checks.
//! There is deliberately NO lambda node: lambdas exist only in the surface AST
//! and are beta-reduced away during elaboration.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("InternPool.zig");
const StrId = InternPool.StrId;

pub const SortId = enum(u32) {
    /// the builtin sort of propositions — numerically the POOL's reserved Prop Item
    /// (`InternPool.Index.prop`): in the demand world a SortId IS a pool Index, and the
    /// pool seeds universe(0) / "Prop" string(1) / Prop sort(2).
    prop = 2,
    _,
};
pub const SymId = enum(u32) { _ };
pub const TermId = enum(u32) { _ };

pub const Quantifier = enum(u8) { forall, exists };
pub const BinOp = enum(u8) { and_op, or_op, implies };
pub const AppKind = enum { app, pred };

pub const Node = union(enum) {
    /// bound variable: de Bruijn index (innermost binder = 0)
    bvar: u16,
    /// free variable (or eigenvariable): named, sorted
    fvar: Fvar,
    /// function/constant application (constants are 0-ary funcs)
    app: App,
    /// predicate application
    pred: App,
    /// equality between two terms of the same (non-prop) sort
    eq: Pair,
    not: TermId,
    bin: Bin,
    quant: Quant,

    pub const Fvar = struct { name: StrId, sort: SortId };
    pub const App = struct { sym: SymId, args_start: u32, args_len: u16 };
    pub const Pair = struct { lhs: TermId, rhs: TermId };
    pub const Bin = struct { op: BinOp, lhs: TermId, rhs: TermId };
    pub const Quant = struct { q: Quantifier, sort: SortId, hint: StrId, body: TermId };
};

/// Leaf action for the shared traversal: what to do at bvar/fvar nodes.
/// `depth` = number of binders passed on the way down.
const Transform = union(enum) {
    /// fvar `name` -> bvar(depth)   (build a quantifier body: "close over x")
    close: StrId,
    /// bvar(depth) -> `term`        (instantiate a binder: "open with u")
    open: TermId,
    /// fvar `name` -> `term`        (capture-free by construction)
    subst_fvar: struct { name: StrId, term: TermId },
};

pub const Pool = struct {
    arena: Allocator,
    nodes: std.ArrayList(Node) = .empty,
    extra: std.ArrayList(TermId) = .empty,

    pub fn init(arena: Allocator) Pool {
        return .{ .arena = arena };
    }

    pub fn get(self: *const Pool, id: TermId) Node {
        return self.nodes.items[@intFromEnum(id)];
    }

    pub fn add(self: *Pool, node: Node) Allocator.Error!TermId {
        const id: TermId = @enumFromInt(self.nodes.items.len);
        try self.nodes.append(self.arena, node);
        return id;
    }

    /// Build an app/pred node from a symbol and argument list.
    pub fn addApp(self: *Pool, kind: AppKind, sym: SymId, arg_ids: []const TermId) Allocator.Error!TermId {
        const start: u32 = @intCast(self.extra.items.len);
        try self.extra.appendSlice(self.arena, arg_ids);
        const app: Node.App = .{ .sym = sym, .args_start = start, .args_len = @intCast(arg_ids.len) };
        return self.add(switch (kind) {
            .app => .{ .app = app },
            .pred => .{ .pred = app },
        });
    }

    pub fn args(self: *const Pool, app: Node.App) []const TermId {
        return self.extra.items[app.args_start..][0..app.args_len];
    }

    // --- the substitution calculus ---
    // Invariant: every public TermId is locally closed (no loose bvars) except
    // quantifier bodies and stored guards (params as loose bvars); the public
    // entry points preserve local closure. Replacement terms must be locally
    // closed, which is why no shifting is ever needed.

    /// fvar `name` -> bound variable of a new innermost binder.
    /// The result is a body with one loose bvar, ready to wrap in a `quant`.
    pub fn close(self: *Pool, id: TermId, name: StrId) Allocator.Error!TermId {
        return self.walk(id, .{ .close = name }, 0);
    }

    /// Instantiate the binder of quantifier body `id` with locally-closed `u`.
    pub fn open(self: *Pool, id: TermId, u: TermId) Allocator.Error!TermId {
        return self.walk(id, .{ .open = u }, 0);
    }

    /// Substitute locally-closed `u` for every occurrence of fvar `name`.
    pub fn substFvar(self: *Pool, id: TermId, name: StrId, u: TermId) Allocator.Error!TermId {
        return self.walk(id, .{ .subst_fvar = .{ .name = name, .term = u } }, 0);
    }

    /// Replace every subterm alpha-equal to `from` with `to` (all occurrences).
    /// `from`/`to` are locally closed (equation sides), so no depth shifting is
    /// needed. Mirrors the kernel's `rewriteMatches` acceptance (all-occurrences
    /// is a valid instance of its "some occurrences" congruence walk), so a step
    /// justified by rewriting toward this result kernel-checks. Used by the
    /// `chain` accelerant to construct each rewrite target.
    pub fn rewriteAll(self: *Pool, id: TermId, from: TermId, to: TermId) Allocator.Error!TermId {
        if (self.alphaEq(id, from)) return to;
        switch (self.get(id)) {
            .bvar, .fvar => return id,
            .app => |a| {
                // Snapshot the arg ids FIRST: each recursive rewriteAll appends to
                // `self.extra` (via addApp) and may reallocate it, invalidating the
                // `self.args(a)` slice mid-iteration. Copy into the arena-stable
                // `new_args`, then rewrite in place.
                const new_args = try self.arena.alloc(TermId, a.args_len);
                @memcpy(new_args, self.args(a));
                for (new_args) |*na| na.* = try self.rewriteAll(na.*, from, to);
                return self.addApp(.app, a.sym, new_args);
            },
            .pred => |a| {
                const new_args = try self.arena.alloc(TermId, a.args_len);
                @memcpy(new_args, self.args(a));
                for (new_args) |*na| na.* = try self.rewriteAll(na.*, from, to);
                return self.addApp(.pred, a.sym, new_args);
            },
            .eq => |p| return self.add(.{ .eq = .{ .lhs = try self.rewriteAll(p.lhs, from, to), .rhs = try self.rewriteAll(p.rhs, from, to) } }),
            .not => |t| return self.add(.{ .not = try self.rewriteAll(t, from, to) }),
            .bin => |b| return self.add(.{ .bin = .{ .op = b.op, .lhs = try self.rewriteAll(b.lhs, from, to), .rhs = try self.rewriteAll(b.rhs, from, to) } }),
            .quant => |q| return self.add(.{ .quant = .{ .q = q.q, .sort = q.sort, .hint = q.hint, .body = try self.rewriteAll(q.body, from, to) } }),
        }
    }

    /// Does fvar `name` occur (free) anywhere in `id`? (eigenvariable check)
    pub fn occursFree(self: *const Pool, id: TermId, name: StrId) bool {
        switch (self.get(id)) {
            .bvar => return false,
            .fvar => |v| return v.name == name,
            .app, .pred => |a| {
                for (self.args(a)) |arg| {
                    if (self.occursFree(arg, name)) return true;
                }
                return false;
            },
            .eq => |p| return self.occursFree(p.lhs, name) or self.occursFree(p.rhs, name),
            .not => |t| return self.occursFree(t, name),
            .bin => |b| return self.occursFree(b.lhs, name) or self.occursFree(b.rhs, name),
            .quant => |q| return self.occursFree(q.body, name),
        }
    }

    /// Does any function/predicate application in `id` use a symbol whose
    /// declared name is `name`? (Used by the named-theory contract to detect a
    /// goal referencing an arithmetic symbol the theory failed to provide.)
    /// `EnvT` is duck-typed to avoid a term->env import cycle: it needs
    /// `sym(SymId) -> struct { name: StrId, ... }`.
    pub fn usesSymNamed(self: *const Pool, env: anytype, name: StrId, id: TermId) bool {
        switch (self.get(id)) {
            .bvar, .fvar => return false,
            .app, .pred => |a| {
                if (env.sym(a.sym).name == name) return true;
                for (self.args(a)) |arg| {
                    if (self.usesSymNamed(env, name, arg)) return true;
                }
                return false;
            },
            .eq => |p| return self.usesSymNamed(env, name, p.lhs) or self.usesSymNamed(env, name, p.rhs),
            .not => |t| return self.usesSymNamed(env, name, t),
            .bin => |b| return self.usesSymNamed(env, name, b.lhs) or self.usesSymNamed(env, name, b.rhs),
            .quant => |q| return self.usesSymNamed(env, name, q.body),
        }
    }

    /// Alpha-equivalence: structural equality ignoring quantifier name hints
    /// (bound variables are indices, so hints carry no meaning).
    pub fn alphaEq(self: *const Pool, a: TermId, b: TermId) bool {
        if (a == b) return true;
        const na = self.get(a);
        const nb = self.get(b);
        if (std.meta.activeTag(na) != std.meta.activeTag(nb)) return false;
        switch (na) {
            .bvar => |i| return i == nb.bvar,
            .fvar => |v| return v.name == nb.fvar.name and v.sort == nb.fvar.sort,
            .app => |x| return self.appEq(x, nb.app),
            .pred => |x| return self.appEq(x, nb.pred),
            .eq => |p| return self.alphaEq(p.lhs, nb.eq.lhs) and self.alphaEq(p.rhs, nb.eq.rhs),
            .not => |t| return self.alphaEq(t, nb.not),
            .bin => |x| return x.op == nb.bin.op and
                self.alphaEq(x.lhs, nb.bin.lhs) and self.alphaEq(x.rhs, nb.bin.rhs),
            .quant => |q| return q.q == nb.quant.q and q.sort == nb.quant.sort and
                self.alphaEq(q.body, nb.quant.body), // hint deliberately ignored
        }
    }

    fn appEq(self: *const Pool, x: Node.App, y: Node.App) bool {
        if (x.sym != y.sym or x.args_len != y.args_len) return false;
        for (self.args(x), self.args(y)) |ax, ay| {
            if (!self.alphaEq(ax, ay)) return false;
        }
        return true;
    }

    /// A total structural order over terms, consistent with alphaEq
    /// (alpha-equal terms compare `.eq`; quantifier hints ignored). Used to
    /// canonicalize AC-rearranged sums: both sides sort their summands the
    /// same way iff the multisets match. Only totality and consistency
    /// matter for soundness — the certificate is kernel-checked, so a
    /// mis-order can only fail to join, never prove a falsehood.
    pub fn termOrder(self: *const Pool, a: TermId, b: TermId) std.math.Order {
        if (a == b) return .eq;
        const na = self.get(a);
        const nb = self.get(b);
        const ta = @intFromEnum(std.meta.activeTag(na));
        const tb = @intFromEnum(std.meta.activeTag(nb));
        if (ta != tb) return std.math.order(ta, tb);
        switch (na) {
            .bvar => |i| return std.math.order(i, nb.bvar),
            .fvar => |v| {
                const by_name = std.math.order(@intFromEnum(v.name), @intFromEnum(nb.fvar.name));
                if (by_name != .eq) return by_name;
                return std.math.order(@intFromEnum(v.sort), @intFromEnum(nb.fvar.sort));
            },
            .app => |x| return self.appOrder(x, nb.app),
            .pred => |x| return self.appOrder(x, nb.pred),
            .eq => |p| {
                const l = self.termOrder(p.lhs, nb.eq.lhs);
                return if (l != .eq) l else self.termOrder(p.rhs, nb.eq.rhs);
            },
            .not => |t| return self.termOrder(t, nb.not),
            .bin => |x| {
                const op = std.math.order(@intFromEnum(x.op), @intFromEnum(nb.bin.op));
                if (op != .eq) return op;
                const l = self.termOrder(x.lhs, nb.bin.lhs);
                return if (l != .eq) l else self.termOrder(x.rhs, nb.bin.rhs);
            },
            .quant => |q| {
                const qk = std.math.order(@intFromEnum(q.q), @intFromEnum(nb.quant.q));
                if (qk != .eq) return qk;
                const srt = std.math.order(@intFromEnum(q.sort), @intFromEnum(nb.quant.sort));
                if (srt != .eq) return srt;
                return self.termOrder(q.body, nb.quant.body); // hint ignored
            },
        }
    }

    fn appOrder(self: *const Pool, x: Node.App, y: Node.App) std.math.Order {
        const sym = std.math.order(@intFromEnum(x.sym), @intFromEnum(y.sym));
        if (sym != .eq) return sym;
        const len = std.math.order(x.args_len, y.args_len);
        if (len != .eq) return len;
        for (self.args(x), self.args(y)) |ax, ay| {
            const o = self.termOrder(ax, ay);
            if (o != .eq) return o;
        }
        return .eq;
    }

    /// Shared recursion for close/open/substFvar. Returns the original id when
    /// nothing changed underneath (keeps the pool small via sharing).
    fn walk(self: *Pool, id: TermId, t: Transform, depth: u16) Allocator.Error!TermId {
        switch (self.get(id)) {
            .bvar => |i| switch (t) {
                // replacement is locally closed => no shifting needed
                .open => |u| return if (i == depth) u else id,
                else => return id,
            },
            .fvar => |v| switch (t) {
                .close => |name| return if (v.name == name) self.add(.{ .bvar = depth }) else id,
                .subst_fvar => |s| return if (v.name == s.name) s.term else id,
                .open => return id,
            },
            .app => |a| return self.walkApp(id, .app, a, t, depth),
            .pred => |a| return self.walkApp(id, .pred, a, t, depth),
            .eq => |p| {
                const lhs = try self.walk(p.lhs, t, depth);
                const rhs = try self.walk(p.rhs, t, depth);
                if (lhs == p.lhs and rhs == p.rhs) return id;
                return self.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
            },
            .not => |inner| {
                const w = try self.walk(inner, t, depth);
                if (w == inner) return id;
                return self.add(.{ .not = w });
            },
            .bin => |b| {
                const lhs = try self.walk(b.lhs, t, depth);
                const rhs = try self.walk(b.rhs, t, depth);
                if (lhs == b.lhs and rhs == b.rhs) return id;
                return self.add(.{ .bin = .{ .op = b.op, .lhs = lhs, .rhs = rhs } });
            },
            .quant => |q| {
                const body = try self.walk(q.body, t, depth + 1);
                if (body == q.body) return id;
                return self.add(.{ .quant = .{ .q = q.q, .sort = q.sort, .hint = q.hint, .body = body } });
            },
        }
    }

    fn walkApp(
        self: *Pool,
        id: TermId,
        kind: AppKind,
        a: Node.App,
        t: Transform,
        depth: u16,
    ) Allocator.Error!TermId {
        // args() aliases extra.items; the recursive walks below may grow
        // extra, and ArrayList growth poisons the abandoned buffer — copy
        // the argument ids out before recursing
        const old_args = try self.arena.dupe(TermId, self.args(a));
        const new_args = try self.arena.alloc(TermId, old_args.len);
        var changed = false;
        for (old_args, new_args) |arg, *out| {
            const w = try self.walk(arg, t, depth);
            if (w != arg) changed = true;
            out.* = w;
        }
        if (!changed) return id;
        return self.addApp(kind, a.sym, new_args);
    }

    /// A structure-interpretation mapping for `remapFormula`: rewrite each
    /// SortId and SymId of a source theory to its image in the target. The maps
    /// are small association lists (a theory's primitives: a carrier + a few
    /// ops), looked up linearly. An entry absent from a map is left unchanged
    /// (sorts/syms the mapping doesn't mention — e.g. `Prop`, shared builtins —
    /// pass through). `guard`, when set, relativizes: every quantifier over the
    /// mapped `carrier` sort gets its body wrapped `guard(x) -> body`.
    pub const Remap = struct {
        pub const SortPair = struct { from: SortId, to: SortId };
        pub const SymPair = struct { from: SymId, to: SymId };
        pub const Guard = struct { pred: SymId, carrier: SortId };
        /// a source symbol whose model TARGET is a `define`d (transparent) symbol:
        /// the remap replaces the source application not with an application of the
        /// target symbol (which would leave a dangling `DEFINED` name) but with the
        /// target's BODY, expanded. `from` is the source SymId; `body` its target
        /// define's stored term. (Current defines are nullary — no arg substitution.)
        pub const Expand = struct { from: SymId, body: TermId };

        sorts: []const SortPair,
        syms: []const SymPair,
        /// carrier-guard relativization (guarded models); null = unguarded
        guard: ?Guard = null,
        /// source symbols whose target is a transparent define — expanded to `body`
        expands: []const Expand = &.{},

        pub fn sort(self: Remap, s: SortId) SortId {
            for (self.sorts) |m| if (m.from == s) return m.to;
            return s;
        }
        pub fn sym(self: Remap, s: SymId) SymId {
            for (self.syms) |m| if (m.from == s) return m.to;
            return s;
        }
        /// If source symbol `s`'s target is a transparent define, its expanded body.
        pub fn expansionOf(self: Remap, s: SymId) ?TermId {
            for (self.expands) |e| if (e.from == s) return e.body;
            return null;
        }

        fn hasSortFrom(self: Remap, s: SortId) bool {
            for (self.sorts) |m| if (m.from == s) return true;
            return false;
        }
        fn hasSymFrom(self: Remap, s: SymId) bool {
            for (self.syms) |m| if (m.from == s) return true;
            return false;
        }

        /// Does `formula` mention any sort or symbol this remap substitutes?
        /// ("Is it affected by the substitution?") A fact that is NOT affected is
        /// substitution-invariant — a materialized proof may cite it as-is (the
        /// remap is the identity on it). A fact that IS affected must be
        /// accounted for by the mapping, or citing it is the forbidden case.
        /// See MODEL-DESIGN.md (materialization citation rule).
        pub fn affects(self: Remap, pool: *const Pool, formula: TermId) bool {
            switch (pool.get(formula)) {
                .bvar => return false,
                .fvar => |v| return self.hasSortFrom(v.sort),
                .app, .pred => |a| {
                    if (self.hasSymFrom(a.sym)) return true;
                    for (pool.args(a)) |arg| if (self.affects(pool, arg)) return true;
                    return false;
                },
                .eq => |p| return self.affects(pool, p.lhs) or self.affects(pool, p.rhs),
                .not => |t| return self.affects(pool, t),
                .bin => |b| return self.affects(pool, b.lhs) or self.affects(pool, b.rhs),
                .quant => |q| return self.hasSortFrom(q.sort) or self.affects(pool, q.body),
            }
        }
    };

    /// Rewrite a source-theory formula through a structure interpretation
    /// (`Remap`): substitute every SortId and SymId to its image, and — for a
    /// guarded model — inject `guard(x) ->` at each quantifier over the mapped
    /// carrier. Locally-nameless representation makes this capture-free: binder
    /// STRUCTURE (de Bruijn indices, nesting) is preserved exactly; only the
    /// sorts/syms decorating it change. This is the `model` transfer engine —
    /// run OUT (remap a source theorem to the target goal) and IN (remap a
    /// source axiom to check the discharging local fact). See MODEL-DESIGN.md.
    ///
    /// NOTE the `carrier` in `guard` is the SOURCE sort (pre-remap): the guard
    /// fires on a `quant` whose (source) sort is the carrier, so we test before
    /// substituting. The injected `guard(bvar 0)` references the just-bound
    /// variable; because we inject INSIDE the quantifier body the de Bruijn
    /// index 0 is correct (innermost binder).
    pub fn remapFormula(self: *Pool, id: TermId, remap: Remap) Allocator.Error!TermId {
        switch (self.get(id)) {
            .bvar => return id,
            .fvar => |v| {
                const s = remap.sort(v.sort);
                if (s == v.sort) return id;
                return self.add(.{ .fvar = .{ .name = v.name, .sort = s } });
            },
            .app => |a| return self.remapApp(.app, a, remap),
            .pred => |a| return self.remapApp(.pred, a, remap),
            .eq => |p| {
                const lhs = try self.remapFormula(p.lhs, remap);
                const rhs = try self.remapFormula(p.rhs, remap);
                return self.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
            },
            .not => |inner| return self.add(.{ .not = try self.remapFormula(inner, remap) }),
            .bin => |b| {
                const lhs = try self.remapFormula(b.lhs, remap);
                const rhs = try self.remapFormula(b.rhs, remap);
                return self.add(.{ .bin = .{ .op = b.op, .lhs = lhs, .rhs = rhs } });
            },
            .quant => |q| {
                var body = try self.remapFormula(q.body, remap);
                // guard relativization: a binder over the (source) carrier is
                // restricted to the guarded subset. The connective differs by
                // quantifier: `∀x; P` → `∀x; guard(x) -> P` (implication), but
                // `∃x; P` → `∃x; guard(x) and P` (conjunction) — an existential
                // asserts a witness that is BOTH in the subset AND satisfies P.
                if (remap.guard) |g| {
                    if (q.sort == g.carrier) {
                        const bound = try self.add(.{ .bvar = 0 });
                        const guard_app = try self.addApp(.pred, g.pred, &.{bound});
                        const connective: BinOp = switch (q.q) {
                            .forall => .implies,
                            .exists => .and_op,
                        };
                        body = try self.add(.{ .bin = .{ .op = connective, .lhs = guard_app, .rhs = body } });
                    }
                }
                return self.add(.{ .quant = .{
                    .q = q.q,
                    .sort = remap.sort(q.sort),
                    .hint = q.hint,
                    .body = body,
                } });
            },
        }
    }

    fn remapApp(self: *Pool, kind: AppKind, a: Node.App, remap: Remap) Allocator.Error!TermId {
        // a source symbol whose TARGET is a transparent define expands to the
        // target's body — otherwise the remap would leave a dangling `DEFINED`
        // name where the goal has the expanded form. (Current defines are nullary,
        // so there are no args to substitute into the body.)
        if (remap.expansionOf(a.sym)) |body| return body;
        // args() aliases extra.items; recursion may grow it (stale-slice trap,
        // see walkApp) — copy argument ids out before recursing.
        const old_args = try self.arena.dupe(TermId, self.args(a));
        const new_args = try self.arena.alloc(TermId, old_args.len);
        for (old_args, new_args) |arg, *out| out.* = try self.remapFormula(arg, remap);
        return self.addApp(kind, remap.sym(a.sym), new_args);
    }

    // === DURABLE serialization: scratchpad <-> InternPool `extra` ===================
    //
    // Terms are NOT interned Items (bpa is explicit — no term dedup). A DURABLE term (a
    // fact's formula, a callable's guard, a define's body) lives as a SELF-CONTAINED u32
    // run in the InternPool's `extra`; this Pool is the per-task SCRATCHPAD where terms are
    // constructed (TermId = index into `nodes`). `reify` serializes a scratchpad term into
    // `extra`; `copyIn` rebuilds a durable term into fresh scratchpad nodes. The calculus
    // (walk/alphaEq/…) only ever runs on the scratchpad TermId form.
    //
    // RUN FORMAT — `[word_count, ...payload...]`. Payload is a POST-ORDER sequence of nodes
    // (children before parents), so a child ref is a back-reference to an earlier node's
    // LOCAL index (0-based within the payload). The ROOT is the last node. Each node is a
    // variable-width u32 group headed by a tag (values match `Node`'s field order):
    //   bvar  [0, debruijn]
    //   fvar  [1, name:Index, sort:Index]
    //   app   [2, sym:Index, argc, argloc0, …]     (arglocN = local node index)
    //   pred  [3, sym:Index, argc, argloc0, …]
    //   eq    [4, lhs_loc, rhs_loc]
    //   not   [5, operand_loc]
    //   bin   [6, op, lhs_loc, rhs_loc]
    //   quant [7, q, sort:Index, hint:Index, body_loc]
    // Index-typed fields are DURABLE pool Indexes (interned strings/sorts/syms); child
    // positions are LOCAL back-refs. No dedup, no sharing across runs (each durable term is
    // owned by exactly one entity), so an inlined run makes reify/copyIn a linear splice.

    const TermTag = enum(u32) { bvar, fvar, app, pred, eq, not, bin, quant };

    /// Mutable state threaded through the post-order reify DFS.
    const Reifier = struct {
        pool: *const Pool,
        arena: Allocator,
        words: std.ArrayList(u32) = .empty, // the payload (node groups, post-order)
        next_ordinal: u32 = 0, // next node's LOCAL index (0-based by appearance)
        seen: std.AutoHashMapUnmanaged(TermId, u32) = .empty, // TermId -> its local ordinal

        /// Emit `id`'s subtree post-order; return `id`'s LOCAL node ordinal. A repeated
        /// scratchpad TermId is emitted once (shared within this run).
        fn go(r: *Reifier, id: TermId) Allocator.Error!u32 {
            if (r.seen.get(id)) |ord| return ord;
            const node = r.pool.get(id);
            switch (node) {
                .bvar => |b| try r.emit(&.{ @intFromEnum(TermTag.bvar), b }),
                .fvar => |v| try r.emit(&.{ @intFromEnum(TermTag.fvar), @intFromEnum(v.name), @intFromEnum(v.sort) }),
                .not => |t| {
                    const c = try r.go(t);
                    try r.emit(&.{ @intFromEnum(TermTag.not), c });
                },
                .eq => |p| {
                    const l = try r.go(p.lhs);
                    const rr = try r.go(p.rhs);
                    try r.emit(&.{ @intFromEnum(TermTag.eq), l, rr });
                },
                .bin => |b| {
                    const l = try r.go(b.lhs);
                    const rr = try r.go(b.rhs);
                    try r.emit(&.{ @intFromEnum(TermTag.bin), @intFromEnum(b.op), l, rr });
                },
                .quant => |q| {
                    const body = try r.go(q.body);
                    try r.emit(&.{ @intFromEnum(TermTag.quant), @intFromEnum(q.q), @intFromEnum(q.sort), @intFromEnum(q.hint), body });
                },
                .app, .pred => |a| {
                    const tag: TermTag = if (node == .app) .app else .pred;
                    // args must precede this node — reify them first, capturing ordinals.
                    // (self.args aliases pool.extra, but reify never writes pool.extra, so
                    // the slice is stable across the loop.)
                    const arg_ids = r.pool.args(a);
                    const arg_ords = try r.arena.alloc(u32, arg_ids.len);
                    for (arg_ids, arg_ords) |arg, *out| out.* = try r.go(arg);
                    var group: std.ArrayList(u32) = .empty;
                    try group.append(r.arena, @intFromEnum(tag));
                    try group.append(r.arena, @intFromEnum(a.sym));
                    try group.append(r.arena, @intCast(arg_ids.len));
                    try group.appendSlice(r.arena, arg_ords);
                    try r.emit(group.items);
                },
            }
            const ord = r.next_ordinal - 1; // emit() bumped it
            try r.seen.put(r.arena, id, ord);
            return ord;
        }

        fn emit(r: *Reifier, group: []const u32) Allocator.Error!void {
            try r.words.appendSlice(r.arena, group);
            r.next_ordinal += 1;
        }
    };

    /// Serialize scratchpad term `id` into `ip`'s `extra` as a self-contained run; return
    /// the run's start offset. A pool WRITE — the caller must hold `ip`'s write-mutex.
    /// Run = `[word_count, ...post-order node groups...]`.
    pub fn reify(self: *const Pool, id: TermId, ip: *InternPool) Allocator.Error!u32 {
        var r: Reifier = .{ .pool = self, .arena = ip.arena };
        _ = try r.go(id);
        var run: std.ArrayList(u32) = .empty;
        try run.append(ip.arena, @intCast(r.words.items.len));
        try run.appendSlice(ip.arena, r.words.items);
        return ip.appendExtraRun(run.items);
    }

    /// Rebuild a durable term (serialized at `off` in `ip.extra`) into THIS scratchpad;
    /// return the root's fresh `TermId`. Walks the payload node-by-node (post-order, so a
    /// child ordinal always resolves to an already-built TermId); the LAST node is the root.
    pub fn copyIn(self: *Pool, ip: *const InternPool, off: u32) Allocator.Error!TermId {
        const word_count = ip.extraRunLen(off);
        const payload = ip.extraRun(off + 1, word_count);
        // ordinal -> rebuilt scratchpad TermId (grows as we walk; capacity = node count is
        // unknown up-front, so use a dynamic list).
        var built: std.ArrayList(TermId) = .empty;
        var i: usize = 0;
        while (i < payload.len) {
            const tag: TermTag = @enumFromInt(payload[i]);
            const id: TermId = switch (tag) {
                .bvar => blk: {
                    const b: u16 = @intCast(payload[i + 1]);
                    i += 2;
                    break :blk try self.add(.{ .bvar = b });
                },
                .fvar => blk: {
                    const name: StrId = @enumFromInt(payload[i + 1]);
                    const sort: SortId = @enumFromInt(payload[i + 2]);
                    i += 3;
                    break :blk try self.add(.{ .fvar = .{ .name = name, .sort = sort } });
                },
                .not => blk: {
                    const c = built.items[payload[i + 1]];
                    i += 2;
                    break :blk try self.add(.{ .not = c });
                },
                .eq => blk: {
                    const l = built.items[payload[i + 1]];
                    const rr = built.items[payload[i + 2]];
                    i += 3;
                    break :blk try self.add(.{ .eq = .{ .lhs = l, .rhs = rr } });
                },
                .bin => blk: {
                    const op: BinOp = @enumFromInt(payload[i + 1]);
                    const l = built.items[payload[i + 2]];
                    const rr = built.items[payload[i + 3]];
                    i += 4;
                    break :blk try self.add(.{ .bin = .{ .op = op, .lhs = l, .rhs = rr } });
                },
                .quant => blk: {
                    const q: Quantifier = @enumFromInt(payload[i + 1]);
                    const sort: SortId = @enumFromInt(payload[i + 2]);
                    const hint: StrId = @enumFromInt(payload[i + 3]);
                    const body = built.items[payload[i + 4]];
                    i += 5;
                    break :blk try self.add(.{ .quant = .{ .q = q, .sort = sort, .hint = hint, .body = body } });
                },
                .app, .pred => blk: {
                    const sym: SymId = @enumFromInt(payload[i + 1]);
                    const argc = payload[i + 2];
                    const args_buf = try self.arena.alloc(TermId, argc);
                    for (args_buf, 0..) |*out, j| out.* = built.items[payload[i + 3 + j]];
                    i += 3 + argc;
                    break :blk try self.addApp(if (tag == .app) .app else .pred, sym, args_buf);
                },
            };
            try built.append(self.arena, id);
        }
        return built.items[built.items.len - 1]; // root = last node (post-order)
    }
};

// --- tests ---

const testing = std.testing;

const nat: SortId = @enumFromInt(1);
fn sid(n: u32) StrId {
    return @enumFromInt(n);
}
fn tsym(n: u32) SymId {
    return @enumFromInt(n);
}

test "close/open round-trip" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // x = x  with x free
    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const x_eq_x = try p.add(.{ .eq = .{ .lhs = x, .rhs = x } });

    // close over x: bvar0 = bvar0
    const body = try p.close(x_eq_x, sid(1));
    const b0 = p.get(body).eq;
    try testing.expectEqual(Node{ .bvar = 0 }, p.get(b0.lhs));

    // open with a fresh fvar y: y = y, alpha-equal to original modulo the name
    const y = try p.add(.{ .fvar = .{ .name = sid(2), .sort = nat } });
    const reopened = try p.open(body, y);
    const r = p.get(reopened).eq;
    try testing.expectEqual(sid(2), p.get(r.lhs).fvar.name);

    // open with x restores the original exactly
    const restored = try p.open(body, x);
    try testing.expect(p.alphaEq(restored, x_eq_x));
}

test "classic capture case: substituting y for x under a binder named y cannot capture" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // forall y: nat. x = y   (x free, y bound — hint says "y")
    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const by = try p.add(.{ .bvar = 0 });
    const inner = try p.add(.{ .eq = .{ .lhs = x, .rhs = by } });
    const t = try p.add(.{ .quant = .{ .q = .forall, .sort = nat, .hint = sid(2), .body = inner } });

    // substitute the FREE variable y for x
    const y_free = try p.add(.{ .fvar = .{ .name = sid(2), .sort = nat } });
    const result = try p.substFvar(t, sid(1), y_free);

    // result must be: forall y'. y = y'  — i.e. fvar y NOT captured as bvar
    const rq = p.get(result).quant;
    const req = p.get(rq.body).eq;
    try testing.expectEqual(Node{ .fvar = .{ .name = sid(2), .sort = nat } }, p.get(req.lhs));
    try testing.expectEqual(Node{ .bvar = 0 }, p.get(req.rhs));
}

test "alphaEq ignores binder hints, distinguishes structure" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // forall n: nat. n = n   vs   forall m: nat. m = m   (different hints)
    const b0 = try p.add(.{ .bvar = 0 });
    const body = try p.add(.{ .eq = .{ .lhs = b0, .rhs = b0 } });
    const tn = try p.add(.{ .quant = .{ .q = .forall, .sort = nat, .hint = sid(1), .body = body } });
    const tm = try p.add(.{ .quant = .{ .q = .forall, .sort = nat, .hint = sid(2), .body = body } });
    try testing.expect(p.alphaEq(tn, tm));

    // exists n. n = n differs from forall n. n = n
    const te = try p.add(.{ .quant = .{ .q = .exists, .sort = nat, .hint = sid(1), .body = body } });
    try testing.expect(!p.alphaEq(tn, te));

    // different fvar names are NOT alpha-equal (free names are meaningful)
    const fx = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const fy = try p.add(.{ .fvar = .{ .name = sid(2), .sort = nat } });
    try testing.expect(!p.alphaEq(fx, fy));
}

test "occursFree sees through binders; open substitutes at correct depth" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // body of `forall a. exists b. f(a, x)`: bvar1 under two binders + free x
    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const b1 = try p.add(.{ .bvar = 1 });
    const fx = try p.addApp(.app, tsym(1), &.{ b1, x });
    const feq = try p.add(.{ .eq = .{ .lhs = fx, .rhs = x } });
    const ex = try p.add(.{ .quant = .{ .q = .exists, .sort = nat, .hint = sid(3), .body = feq } });

    try testing.expect(p.occursFree(ex, sid(1)));
    try testing.expect(!p.occursFree(ex, sid(2)));

    // open the OUTER binder (bvar 1 inside `ex` since it sits under one quant):
    const z = try p.add(.{ .fvar = .{ .name = sid(4), .sort = nat } });
    const opened = try p.open(ex, z);
    const oq = p.get(opened).quant;
    const oeq = p.get(oq.body).eq;
    const oapp = p.get(oeq.lhs).app;
    try testing.expectEqual(Node{ .fvar = .{ .name = sid(4), .sort = nat } }, p.get(p.args(oapp)[0]));
    // x untouched
    try testing.expectEqual(Node{ .fvar = .{ .name = sid(1), .sort = nat } }, p.get(p.args(oapp)[1]));
}

test "unchanged subtrees share ids (no pool bloat)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const c = try p.add(.{ .fvar = .{ .name = sid(2), .sort = nat } });
    const t = try p.add(.{ .eq = .{ .lhs = x, .rhs = c } });

    const before = p.nodes.items.len;
    const unchanged = try p.substFvar(t, sid(9), x); // sid(9) doesn't occur
    try testing.expectEqual(t, unchanged);
    try testing.expectEqual(before, p.nodes.items.len);
}

test "termOrder: total, consistent with alphaEq, transitive" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const y = try p.add(.{ .fvar = .{ .name = sid(2), .sort = nat } });
    const z = try p.add(.{ .fvar = .{ .name = sid(3), .sort = nat } });
    // a second x built independently must compare .eq (consistency w/ alphaEq)
    const x2 = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });

    try testing.expectEqual(std.math.Order.eq, p.termOrder(x, x2));
    try testing.expect(p.alphaEq(x, x2));
    try testing.expectEqual(std.math.Order.lt, p.termOrder(x, y));
    try testing.expectEqual(std.math.Order.gt, p.termOrder(y, x));
    // transitivity: x < y < z
    try testing.expectEqual(std.math.Order.lt, p.termOrder(y, z));
    try testing.expectEqual(std.math.Order.lt, p.termOrder(x, z));

    // compound atoms order structurally and stay total
    const fx = try p.addApp(.app, tsym(7), &.{x});
    const fy = try p.addApp(.app, tsym(7), &.{y});
    try testing.expectEqual(std.math.Order.lt, p.termOrder(fx, fy));
    // different tags: fvar (leaf) vs app compare by tag, consistently
    try testing.expect(p.termOrder(x, fx) != .eq);
    try testing.expectEqual(p.termOrder(x, fx), invert(p.termOrder(fx, x)));
}

fn invert(o: std.math.Order) std.math.Order {
    return switch (o) {
        .lt => .gt,
        .gt => .lt,
        .eq => .eq,
    };
}

fn ssort(n: u32) SortId {
    return @enumFromInt(n);
}

test "remapFormula: unguarded sort+sym substitution over a quantified formula" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // source theory: sort Grp = 1, op = sym 1.
    // formula: forall a: Grp; op(a, a) = a   (a group-flavoured shape)
    const grp = ssort(1);
    const rat = ssort(2);
    const op = tsym(1);
    const add = tsym(2);

    const a_fv = try p.add(.{ .fvar = .{ .name = sid(1), .sort = grp } });
    const op_aa = try p.addApp(.app, op, &.{ a_fv, a_fv });
    const eq = try p.add(.{ .eq = .{ .lhs = op_aa, .rhs = a_fv } });
    const body = try p.close(eq, sid(1));
    const src = try p.add(.{ .quant = .{ .q = .forall, .sort = grp, .hint = sid(1), .body = body } });

    // remap Grp->Rat, op->add.
    const remap: Pool.Remap = .{
        .sorts = &.{.{ .from = grp, .to = rat }},
        .syms = &.{.{ .from = op, .to = add }},
    };
    const out = try p.remapFormula(src, remap);

    // expected: forall a: Rat; add(a, a) = a
    const a2 = try p.add(.{ .fvar = .{ .name = sid(1), .sort = rat } });
    const add_aa = try p.addApp(.app, add, &.{ a2, a2 });
    const eq2 = try p.add(.{ .eq = .{ .lhs = add_aa, .rhs = a2 } });
    const body2 = try p.close(eq2, sid(1));
    const want = try p.add(.{ .quant = .{ .q = .forall, .sort = rat, .hint = sid(1), .body = body2 } });

    try testing.expect(p.alphaEq(out, want));
}

test "remapFormula: guarded model injects guard(x) -> at the carrier binder" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // source: forall a: Grp; op(a, a) = a   remapped Grp->Rat, op->mul,
    // GUARDED by nonzero (pred sym 9) over the carrier Grp.
    const grp = ssort(1);
    const rat = ssort(2);
    const op = tsym(1);
    const mul = tsym(3);
    const nonzero = tsym(9);

    const a_fv = try p.add(.{ .fvar = .{ .name = sid(1), .sort = grp } });
    const op_aa = try p.addApp(.app, op, &.{ a_fv, a_fv });
    const eq = try p.add(.{ .eq = .{ .lhs = op_aa, .rhs = a_fv } });
    const body = try p.close(eq, sid(1));
    const src = try p.add(.{ .quant = .{ .q = .forall, .sort = grp, .hint = sid(1), .body = body } });

    const remap: Pool.Remap = .{
        .sorts = &.{.{ .from = grp, .to = rat }},
        .syms = &.{.{ .from = op, .to = mul }},
        .guard = .{ .pred = nonzero, .carrier = grp },
    };
    const out = try p.remapFormula(src, remap);

    // expected: forall a: Rat; nonzero(a) -> mul(a, a) = a
    // build the body with a bvar-0 guard antecedent.
    const a2 = try p.add(.{ .fvar = .{ .name = sid(1), .sort = rat } });
    const mul_aa = try p.addApp(.app, mul, &.{ a2, a2 });
    const eq2 = try p.add(.{ .eq = .{ .lhs = mul_aa, .rhs = a2 } });
    const guard_a = try p.addApp(.pred, nonzero, &.{a2});
    const impl = try p.add(.{ .bin = .{ .op = .implies, .lhs = guard_a, .rhs = eq2 } });
    // close over BOTH occurrences (guard's a and body's a share name sid(1))
    const body2 = try p.close(impl, sid(1));
    const want = try p.add(.{ .quant = .{ .q = .forall, .sort = rat, .hint = sid(1), .body = body2 } });

    try testing.expect(p.alphaEq(out, want));
}

test "remapFormula: guarded model uses `and` (not `->`) for an EXISTENTIAL binder" {
    // ∃x; P(x) relativized to a subset is `∃x; guard(x) and P(x)` — a witness
    // that is BOTH in the subset AND satisfies P. (Using `->` here would be a
    // near-vacuous, unsound relativization; regression-pin the `and`.)
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    const grp = ssort(1);
    const rat = ssort(2);
    const op = tsym(1);
    const mul = tsym(3);
    const nonzero = tsym(9);

    // source: exists a: Grp; op(a, a) = a
    const a_fv = try p.add(.{ .fvar = .{ .name = sid(1), .sort = grp } });
    const op_aa = try p.addApp(.app, op, &.{ a_fv, a_fv });
    const eq = try p.add(.{ .eq = .{ .lhs = op_aa, .rhs = a_fv } });
    const body = try p.close(eq, sid(1));
    const src = try p.add(.{ .quant = .{ .q = .exists, .sort = grp, .hint = sid(1), .body = body } });

    const remap: Pool.Remap = .{
        .sorts = &.{.{ .from = grp, .to = rat }},
        .syms = &.{.{ .from = op, .to = mul }},
        .guard = .{ .pred = nonzero, .carrier = grp },
    };
    const out = try p.remapFormula(src, remap);

    // expected: exists a: Rat; nonzero(a) and mul(a, a) = a  (AND, not implies)
    const a2 = try p.add(.{ .fvar = .{ .name = sid(1), .sort = rat } });
    const mul_aa = try p.addApp(.app, mul, &.{ a2, a2 });
    const eq2 = try p.add(.{ .eq = .{ .lhs = mul_aa, .rhs = a2 } });
    const guard_a = try p.addApp(.pred, nonzero, &.{a2});
    const conj = try p.add(.{ .bin = .{ .op = .and_op, .lhs = guard_a, .rhs = eq2 } });
    const body2 = try p.close(conj, sid(1));
    const want = try p.add(.{ .quant = .{ .q = .exists, .sort = rat, .hint = sid(1), .body = body2 } });

    try testing.expect(p.alphaEq(out, want));

    // and NOT the `->` form (the pre-fix bug).
    const impl = try p.add(.{ .bin = .{ .op = .implies, .lhs = guard_a, .rhs = eq2 } });
    const bad_body = try p.close(impl, sid(1));
    const bad = try p.add(.{ .quant = .{ .q = .exists, .sort = rat, .hint = sid(1), .body = bad_body } });
    try testing.expect(!p.alphaEq(out, bad));
}

test "remapFormula: sorts/syms absent from the map pass through unchanged" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    var pool: Pool = .init(arena_state.allocator());
    const p = &pool;

    // formula mentions Prop-level pred `related` (sym 5) over sort 1, plus a
    // sort 3 the map doesn't touch — remap only sort 1 -> 2.
    const s1 = ssort(1);
    const s3 = ssort(3);
    const related = tsym(5);

    const a_fv = try p.add(.{ .fvar = .{ .name = sid(1), .sort = s1 } });
    const b_fv = try p.add(.{ .fvar = .{ .name = sid(2), .sort = s3 } });
    const rel = try p.addApp(.pred, related, &.{ a_fv, b_fv });

    const remap: Pool.Remap = .{
        .sorts = &.{.{ .from = s1, .to = ssort(2) }},
        .syms = &.{}, // related untouched
    };
    const out = try p.remapFormula(rel, remap);
    const on = p.get(out).pred;
    // related stays; first arg's sort became 2; second arg's sort stays 3.
    try testing.expectEqual(related, on.sym);
    try testing.expectEqual(ssort(2), p.get(p.args(on)[0]).fvar.sort);
    try testing.expectEqual(s3, p.get(p.args(on)[1]).fvar.sort);
}

// --- durable serialization: reify -> extra -> copyIn round-trips ---
// (Repurposed from the retired InternPool `term_*` Item tests: terms are no longer
// interned entities; these verify the term round-trips through the pool's `extra` instead.)

/// Round-trip `id` through `ip.extra` and back into the SAME scratchpad `p`, asserting the
/// rebuilt term is alpha-equal to the original. Same-pool round-trip works because the repr
/// is locally-nameless with no dedup: `copyIn` appends fresh-but-structurally-identical
/// nodes, so `alphaEq(rebuilt, id)` holds.
fn expectReifyRoundTrip(io: std.Io, ip: *InternPool, p: *Pool, id: TermId) !void {
    ip.lockWrite(io);
    const off = try p.reify(id, ip);
    ip.unlockWrite(io);
    const rebuilt = try p.copyIn(ip, off);
    try testing.expect(p.alphaEq(rebuilt, id));
}

test "reify/copyIn: every node kind round-trips through extra" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var pool: Pool = .init(arena);
    const p = &pool;
    var ip: InternPool = try .init(arena);
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    // bvar, fvar
    const b0 = try p.add(.{ .bvar = 0 });
    try expectReifyRoundTrip(io, &ip, p, b0);
    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    try expectReifyRoundTrip(io, &ip, p, x);

    // app(add, x, b0) and pred(P, x) — variable-length, with shared subterms
    const add = tsym(7);
    const app = try p.addApp(.app, add, &.{ x, b0 });
    try expectReifyRoundTrip(io, &ip, p, app);
    const pred = try p.addApp(.pred, tsym(9), &.{x});
    try expectReifyRoundTrip(io, &ip, p, pred);

    // eq, not
    const eq = try p.add(.{ .eq = .{ .lhs = app, .rhs = b0 } });
    try expectReifyRoundTrip(io, &ip, p, eq);
    const neg = try p.add(.{ .not = eq });
    try expectReifyRoundTrip(io, &ip, p, neg);

    // bin (all ops), quant (both), nested — the whole tree
    const conj = try p.add(.{ .bin = .{ .op = .and_op, .lhs = eq, .rhs = neg } });
    try expectReifyRoundTrip(io, &ip, p, conj);
    const body = try p.close(conj, sid(1)); // close over x -> a loose bvar
    const fa = try p.add(.{ .quant = .{ .q = .forall, .sort = nat, .hint = sid(1), .body = body } });
    try expectReifyRoundTrip(io, &ip, p, fa);
    const ex = try p.add(.{ .quant = .{ .q = .exists, .sort = nat, .hint = sid(2), .body = body } });
    try expectReifyRoundTrip(io, &ip, p, ex);
}

test "reify/copyIn: shared subterm emitted once, rebuilt consistently" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var pool: Pool = .init(arena);
    const p = &pool;
    var ip: InternPool = try .init(arena);
    var threaded: std.Io.Threaded = .init(arena, .{});
    const io = threaded.io();

    // f(x, x): x appears twice — reify emits it once (dedup within the run), copyIn
    // rebuilds a valid tree either way; assert structural round-trip.
    const x = try p.add(.{ .fvar = .{ .name = sid(1), .sort = nat } });
    const fxx = try p.addApp(.app, tsym(1), &.{ x, x });
    try expectReifyRoundTrip(io, &ip, p, fxx);
}
