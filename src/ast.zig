//! Surface AST for .b4m files. Arena-allocated tree; nodes reference source
//! tokens for diagnostics. Terms and formulas share one Expr type — the
//! elaborator sorts them out by sort. Lambdas exist only here, never in
//! kernel terms.

const std = @import("std");
const Token = @import("lexer.zig").Token;

/// A binder `x: S` or an INLINE-REFINED binder `x: S where inH` — the optional
/// `guard` predicate-NAME mints an anonymous refined sort (`S` narrowed by inH,
/// applied to the binder variable). Bare pred name; conjunctions use a `define`d pred.
pub const Binder = struct { name: Token, sort: Token, guard: ?Token = null };

/// Schema parameter, e.g. `P: nat -> prop`. arg_sorts empty = plain value param.
pub const SchemaParam = struct { name: Token, arg_sorts: []const Token, result: Token };

pub const Expr = union(enum) {
    name: Token,
    call: Call,
    binary: Binary,
    not: Not,
    quant: Quant,
    lambda: Lambda,

    pub const Call = struct { callee: Token, args: []const *const Expr };
    // `iff` is SURFACE-ONLY sugar: the parser records it, elaboration desugars
    // `P iff Q` to `(P -> Q) and (Q -> P)`. It never reaches the kernel term
    // language (term.BinOp stays and/or/implies).
    pub const BinOp = enum { implies, and_op, or_op, iff, equal, not_equal };
    pub const Binary = struct {
        op: BinOp,
        tok: Token,
        lhs: *const Expr,
        rhs: *const Expr,
        /// set when this node was wrapped in explicit parentheses in the
        /// source. Used only to enforce the mixed-boolean-operator paren rule
        /// during parsing; ignored everywhere else.
        paren: bool = false,
    };
    pub const Not = struct {
        tok: Token,
        operand: *const Expr,
        /// see Binary.paren
        paren: bool = false,
    };
    pub const Quant = struct {
        q: enum { forall, exists },
        tok: Token,
        binders: []const Binder,
        body: *const Expr,
    };
    pub const Lambda = struct { tok: Token, binders: []const Binder, body: *const Expr };
};

pub const Step = struct {
    label: Token,
    body: Body,

    pub const Body = union(enum) {
        claim: Claim,
        assume: Block,
        fix: FixBlock,
        unpack: UnpackBlock,
        case: CaseBlock,
    };
    pub const Claim = struct {
        formula: *const Expr,
        /// which justification keyword introduced this step: `by` for the kernel
        /// primitives (pure inference, always checked), `using` for accelerants
        /// (engine proof-generation: accelerants + `instantiation` + `model`). The
        /// parser enforces the vocabulary partition; dispatch keys on `rule`, not this.
        kind: Kind,
        rule: Token,
        /// schema name, only when rule is `instantiation`
        schema: ?Token,
        args: []const *const Expr,
        refs: []const Token,
        /// `arithmetic ... fallback(<thm>)`: a manually-proven theorem to cite
        /// as the certificate when the certifier chain declines (instead of the
        /// hard error). Keeps the step kernel-checked. Arithmetic-only for now.
        fallback: ?Token = null,

        pub const Kind = enum { by, using };
    };
    pub const Block = struct { formula: *const Expr, steps: []const Step };
    pub const FixBlock = struct { name: Token, sort: Token, steps: []const Step };
    pub const UnpackBlock = struct { name: Token, sort: Token, from: Token, steps: []const Step };
    /// `case disj { arm* }` — eliminate the disjunction proved by step
    /// `disj`, one `arm` per (left-nested) disjunct, all arms concluding the
    /// step's goal. Sugar for a hand-written (nested) `or_elim`.
    pub const CaseBlock = struct {
        /// the shared goal every arm concludes (stated on the step line)
        goal: *const Expr,
        disj: Token,
        arms: []const Arm,
        /// one arm: `label| assume <disjunct> { steps }`
        pub const Arm = struct { label: Token, assumption: *const Expr, steps: []const Step };
    };
};

/// A re-export alias `<kind> name = target` — binds a LOCAL name to an entity that lives
/// under `target` (a qualified `ns.origin` or a same-file name). Uniform + GUARD-FREE: a
/// sort's `where` guard is NOT here — a guarded sort is `Sort.guarded`, a distinct variant
/// (the grammar only allows `where` on a sort, so no alias kind but sort ever carried one).
/// "Identity by origin": resolution binds `name` to `target`'s existing entity, mints
/// nothing (see memory `alias-collapse`).
pub const Alias = struct { name: Token, target: Token };

/// `sort N` (root) | `sort N = T` (re-export) | `sort N = T where p` (refined/predicated).
pub const Sort = union(enum) {
    local: Token, // the sort's name
    alias: Alias,
    /// `sort H = G where inH` — a PREDICATED SORT: carrier `parent` narrowed by `guard`
    /// (a unary pred name). Every use injects the guard (hypothesis at binders, obligation
    /// at applications).
    guarded: struct { name: Token, parent: Token, guards: []const Token },
};

pub const Constant = union(enum) {
    local: struct { name: Token, sort: Token },
    alias: Alias,
};

pub const Func = union(enum) {
    local: struct { name: Token, params: []const Binder, result: Token, requires: ?*const Expr },
    alias: Alias,
};

pub const Pred = union(enum) {
    local: struct { name: Token, params: []const Binder },
    alias: Alias,
};

/// The stated proposition of an axiom/theorem/hole. `params` non-null ⇒ it is a SCHEMA (a
/// parametric template — `axiom foo(prop: T -> Prop): …`); the parser sets it from the
/// optional `(params)`, so "a schema is an axiom with params" is a downstream reading, not a
/// separate decl kind. A theorem wraps a `Fact` + its proof steps.
pub const Fact = struct { name: Token, formula: *const Expr, params: ?[]const SchemaParam = null };

pub const Axiom = union(enum) {
    local: Fact,
    alias: Alias,
};

pub const Theorem = union(enum) {
    local: struct { fact: Fact, steps: []const Step },
    alias: Alias,
};

pub const Decl = union(enum) {
    /// `import ns <<< "path.b4m"` — binds a namespace to a loaded file
    import: struct { ns: Token, path: Token },
    /// `forward name` — a manifest entry: promises `name` is defined later in
    /// this file as a theorem (checked at end of file; nothing else)
    forward: struct { name: Token },
    sort: Sort,
    constant: Constant,
    /// `define NAME[(params)] = expr` — a transparent (macro) abbreviation: every
    /// use expands to the body at elaboration (with actual args substituted for the
    /// params); the kernel never sees the name. `params` empty = nullary.
    /// `define f(a, b) = body` — a transparent MACRO. Params are bare NAMES (no sorts): the
    /// args arrive already elaborated and are substituted by name, so the body's own
    /// elaboration types everything; a declared sort would be a second, redundant source.
    define: struct { name: Token, params: []const Token, value: *const Expr },
    func: Func,
    pred: Pred,
    axiom: Axiom,
    /// `hole name: formula` — an aspirational placeholder, accepted like an axiom but
    /// disclosed as a hole (default mode rejects; --draft allows). Same shape as Axiom.
    hole: Axiom,
    theorem: Theorem,
    /// `model <Name> { <src>: <tgt> …; <src> <- <localThm> … }` — a model of an imported
    /// theory. The `:` symbol/sort interpretations and the `<-` obligation discharges are
    /// SPLIT into two lists (they resolve against different tables — idents vs facts). NO
    /// carrier/guard header: the model is GUARDED exactly when a sort mapping's TARGET is a
    /// predicated sort. See MODEL-DESIGN.md.
    model: struct {
        name: Token,
        identifiers: []const IdentMapping,
        obligations: []const Mapping,
    },
};

pub const IdentMapping = union(enum) {
    basic: Mapping,
    refined_sort: struct {
        mapping: Mapping,
        dischargers: []const Token,
    },
    closed_operation: struct {
        mapping: Mapping,
        closure_facts: []const Token,
    },
};

/// One line in a `model` block. Two forms, distinguished by operator:
///   `src : tgt`       — a SYMBOL/SORT interpretation (`.symbol`): map a source
///                       sort or function/predicate to a local one.
///   `src <- localThm` — an AXIOM OBLIGATION discharge (`.obligation`): the local
///                       fact `localThm` discharges the source axiom `src`.
/// `<target>@<projected>` (`group.opAssoc <- HSubGroup@subgroup.opAssoc`) is a
/// MODEL-PROJECTION value — discharge this obligation by transferring the
/// `projected` theorem THROUGH the model named `target`. `projection` is the
/// qualified projected name (the `@`-tail, sans `@`); null for a plain target.
/// Projection is only meaningful on an `.obligation` line.
pub const Mapping = struct {
    source: Token,
    target: Token,
    projection: ?Token = null,
};

pub const File = struct { decls: []const Decl };

// -- per-entity name() accessors (the local/alias union → its declared name token) ---------
pub fn sortName(s: Sort) Token {
    return switch (s) {
        .local => |t| t,
        .alias => |a| a.name,
        .guarded => |g| g.name,
    };
}
pub fn constantName(c: Constant) Token {
    return switch (c) {
        .local => |l| l.name,
        .alias => |a| a.name,
    };
}
pub fn funcName(f: Func) Token {
    return switch (f) {
        .local => |l| l.name,
        .alias => |a| a.name,
    };
}
pub fn predName(p: Pred) Token {
    return switch (p) {
        .local => |l| l.name,
        .alias => |a| a.name,
    };
}
pub fn axiomName(a: Axiom) Token {
    return switch (a) {
        .local => |f| f.name,
        .alias => |al| al.name,
    };
}
pub fn theoremName(t: Theorem) Token {
    return switch (t) {
        .local => |l| l.fact.name,
        .alias => |a| a.name,
    };
}

/// The LOCAL `Fact` if `decl` is a local axiom/theorem/hole (else null — an alias, or a
/// non-fact). `Fact.params != null` ⇒ it is a SCHEMA. For the schema/instance path, which
/// keys off "is this a fact-with-params" rather than a distinct decl kind.
pub fn factOf(decl: *const Decl) ?Fact {
    return switch (decl.*) {
        .axiom, .hole => |a| switch (a) {
            .local => |f| f,
            .alias => null,
        },
        .theorem => |t| switch (t) {
            .local => |l| l.fact,
            .alias => null,
        },
        else => null,
    };
}

/// The re-export `Alias` if `decl` is ANY alias (sort/const/func/pred/axiom/theorem),
/// else null. For consumers that FOLLOW an alias to its target (query whereis/theorem).
pub fn aliasOf(decl: *const Decl) ?Alias {
    return switch (decl.*) {
        .sort => |s| if (s == .alias) s.alias else null,
        .constant => |c| if (c == .alias) c.alias else null,
        .func => |f| if (f == .alias) f.alias else null,
        .pred => |p| if (p == .alias) p.alias else null,
        .axiom => |a| if (a == .alias) a.alias else null,
        .hole => |a| if (a == .alias) a.alias else null,
        .theorem => |t| if (t == .alias) t.alias else null,
        else => null,
    };
}

/// The NAME token of a declaration — the single token every named decl carries (import→ns,
/// everything else→name). Used to key the by-name AST registry (`Context.ast_index`) and to
/// read the stamped `name` StrId for name-keyed lookups. `forward` is a manifest promise,
/// not a definition — it has a name but is not registry-addressable as a decl.
pub fn declName(decl: *const Decl) Token {
    return switch (decl.*) {
        .import => |d| d.ns,
        .forward => |d| d.name,
        .sort => |s| sortName(s),
        .constant => |c| constantName(c),
        .define => |d| d.name,
        .func => |f| funcName(f),
        .pred => |p| predName(p),
        .axiom => |a| axiomName(a),
        .hole => |a| axiomName(a),
        .theorem => |t| theoremName(t),
        .model => |d| d.name,
    };
}

/// One deferred dump action: emit a literal slice, or expand an Expr node.
const DumpAct = union(enum) { text: []const u8, node: *const Expr };

/// Debug/test dump of an Expr as an s-expression. Identifier text comes from source.
/// Iterative (explicit action-stack, no recursion): expanding a node pushes its
/// sub-actions REVERSED so they pop in emission order — output is byte-identical.
pub fn dumpExpr(arena: std.mem.Allocator, w: *std.Io.Writer, source: []const u8, e: *const Expr) std.Io.Writer.Error!void {
    var stack: std.ArrayList(DumpAct) = .empty;
    stack.append(arena, .{ .node = e }) catch return error.WriteFailed;
    while (stack.pop()) |act| switch (act) {
        .text => |s| try w.writeAll(s),
        .node => |node| switch (node.*) {
            .name => |t| try w.writeAll(source[t.start..t.end]),
            .call => |c| {
                // emit: "(callee" arg0-preceded-by-space … ")"
                var acts: std.ArrayList(DumpAct) = .empty;
                const open = std.fmt.allocPrint(arena, "({s}", .{source[c.callee.start..c.callee.end]}) catch return error.WriteFailed;
                acts.append(arena, .{ .text = open }) catch return error.WriteFailed;
                for (c.args) |a| {
                    acts.append(arena, .{ .text = " " }) catch return error.WriteFailed;
                    acts.append(arena, .{ .node = a }) catch return error.WriteFailed;
                }
                acts.append(arena, .{ .text = ")" }) catch return error.WriteFailed;
                pushReversed(arena, &stack, acts.items) catch return error.WriteFailed;
            },
            .binary => |b| {
                const open = std.fmt.allocPrint(arena, "({t} ", .{b.op}) catch return error.WriteFailed;
                pushReversed(arena, &stack, &.{
                    .{ .text = open }, .{ .node = b.lhs }, .{ .text = " " }, .{ .node = b.rhs }, .{ .text = ")" },
                }) catch return error.WriteFailed;
            },
            .not => |n| pushReversed(arena, &stack, &.{
                .{ .text = "(not " }, .{ .node = n.operand }, .{ .text = ")" },
            }) catch return error.WriteFailed,
            .quant => |q| {
                var acts: std.ArrayList(DumpAct) = .empty;
                const open = std.fmt.allocPrint(arena, "({t}", .{q.q}) catch return error.WriteFailed;
                acts.append(arena, .{ .text = open }) catch return error.WriteFailed;
                for (q.binders) |b| {
                    const bt = std.fmt.allocPrint(arena, " {s}:{s}", .{
                        source[b.name.start..b.name.end], source[b.sort.start..b.sort.end],
                    }) catch return error.WriteFailed;
                    acts.append(arena, .{ .text = bt }) catch return error.WriteFailed;
                }
                acts.append(arena, .{ .text = " " }) catch return error.WriteFailed;
                acts.append(arena, .{ .node = q.body }) catch return error.WriteFailed;
                acts.append(arena, .{ .text = ")" }) catch return error.WriteFailed;
                pushReversed(arena, &stack, acts.items) catch return error.WriteFailed;
            },
            .lambda => |l| {
                var acts: std.ArrayList(DumpAct) = .empty;
                acts.append(arena, .{ .text = "(fun" }) catch return error.WriteFailed;
                for (l.binders) |b| {
                    const bt = std.fmt.allocPrint(arena, " {s}:{s}", .{
                        source[b.name.start..b.name.end], source[b.sort.start..b.sort.end],
                    }) catch return error.WriteFailed;
                    acts.append(arena, .{ .text = bt }) catch return error.WriteFailed;
                }
                acts.append(arena, .{ .text = " " }) catch return error.WriteFailed;
                acts.append(arena, .{ .node = l.body }) catch return error.WriteFailed;
                acts.append(arena, .{ .text = ")" }) catch return error.WriteFailed;
                pushReversed(arena, &stack, acts.items) catch return error.WriteFailed;
            },
        },
    };
}

/// Push `acts` onto the action-stack in reverse, so they pop front-to-back.
fn pushReversed(arena: std.mem.Allocator, stack: *std.ArrayList(DumpAct), acts: []const DumpAct) !void {
    var i: usize = acts.len;
    while (i > 0) {
        i -= 1;
        try stack.append(arena, acts[i]);
    }
}
