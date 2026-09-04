//! Surface AST for .bpa files. Arena-allocated tree; nodes reference source
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

pub const AliasKind = enum { sort, constant, func, pred, axiom, theorem };

pub const Decl = union(enum) {
    /// `import ns <<< "path.bpa"` — binds a namespace to a loaded file
    import: struct { ns: Token, path: Token },
    /// `forward name` — a manifest entry: promises `name` is defined later in
    /// this file as a theorem (checked at end of file; nothing else)
    forward: struct { name: Token },
    /// `sort Nat = peano.Nat` etc — a local name for an imported entity.
    /// A SORT alias may carry `where <pred>` — a PREDICATED SORT
    /// (`sort H = G where inH`): H resolves to G's sort but every use injects the
    /// guard `inH` (hypothesis at binders, obligation at applications). `guard` is
    /// null for a plain alias and for non-sort alias kinds.
    alias: struct { kind: AliasKind, name: Token, target: Token, guard: ?Token = null },
    sort: struct { name: Token },
    constant: struct { name: Token, sort: Token },
    /// `define NAME[(params)] = expr` — a transparent (macro) abbreviation: every
    /// use expands to the body at elaboration (with actual args substituted for the
    /// params); the kernel never sees the name. The body may be a term (a defined
    /// const/function) or a prop (a defined predicate). `params` empty = nullary.
    define: struct { name: Token, params: []const Binder, value: *const Expr },
    func: struct { name: Token, params: []const Binder, result: Token, requires: ?*const Expr },
    pred: struct { name: Token, params: []const Binder },
    axiom: struct { name: Token, formula: *const Expr },
    /// `hole name: formula` — an aspirational placeholder, accepted like an
    /// axiom but disclosed as a hole (default mode rejects; --draft allows).
    hole: struct { name: Token, formula: *const Expr },
    schema: struct {
        name: Token,
        params: []const SchemaParam,
        formula: *const Expr,
        /// proof-carrying schema: re-checked per instantiation (never at decl)
        steps: ?[]const Step,
    },
    theorem: struct { name: Token, formula: *const Expr, steps: []const Step },
    /// `model <Name> { <src>: <tgt> ... }` — declares that some local structure is a
    /// model of an imported theory. Each `Mapping` binds a source-theory entity
    /// (`group.op`, `group.opAssoc` — a qualified token) to the local symbol/fact
    /// that plays it. There is NO carrier/guard header: the target carrier is
    /// whatever the source carrier maps to, and the model is GUARDED exactly when a
    /// sort-mapping's TARGET is a predicated sort (`group.Grp: H`, `H = Grp where inH`)
    /// — that mapping supplies the guard. See MODEL-DESIGN.md.
    model: struct {
        name: Token,
        mappings: []const Mapping,
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
    kind: Kind,
    source: Token,
    target: Token,
    projection: ?Token = null,

    pub const Kind = enum { symbol, obligation };
};

pub const File = struct { decls: []const Decl };

/// Debug/test dump of an Expr as an s-expression. Identifier text comes from source.
pub fn dumpExpr(w: *std.Io.Writer, source: []const u8, e: *const Expr) std.Io.Writer.Error!void {
    switch (e.*) {
        .name => |t| try w.writeAll(source[t.start..t.end]),
        .call => |c| {
            try w.print("({s}", .{source[c.callee.start..c.callee.end]});
            for (c.args) |a| {
                try w.writeAll(" ");
                try dumpExpr(w, source, a);
            }
            try w.writeAll(")");
        },
        .binary => |b| {
            try w.print("({t} ", .{b.op});
            try dumpExpr(w, source, b.lhs);
            try w.writeAll(" ");
            try dumpExpr(w, source, b.rhs);
            try w.writeAll(")");
        },
        .not => |n| {
            try w.writeAll("(not ");
            try dumpExpr(w, source, n.operand);
            try w.writeAll(")");
        },
        .quant => |q| {
            try w.print("({t}", .{q.q});
            for (q.binders) |b| try w.print(" {s}:{s}", .{
                source[b.name.start..b.name.end],
                source[b.sort.start..b.sort.end],
            });
            try w.writeAll(" ");
            try dumpExpr(w, source, q.body);
            try w.writeAll(")");
        },
        .lambda => |l| {
            try w.writeAll("(fun");
            for (l.binders) |b| try w.print(" {s}:{s}", .{
                source[b.name.start..b.name.end],
                source[b.sort.start..b.sort.end],
            });
            try w.writeAll(" ");
            try dumpExpr(w, source, l.body);
            try w.writeAll(")");
        },
    }
}
