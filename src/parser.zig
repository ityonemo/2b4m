//! Recursive-descent parser for .b4m files.
//! Error recovery: on a parse error inside a declaration, record one diagnostic
//! and skip to the next top-level declaration keyword.
//!
//! Expression grammar (one unified Expr for terms and formulas):
//!   expr    := quant | lambda | implies
//!   quant   := ('forall'|'exists') binders ';' expr
//!   lambda  := 'fun' lbinders '=>' expr
//!   lbinders := binders (',' binders)*   // each group its own sort
//!   binders := ident (',' ident)* ':' ident
//!   implies := or ('->' expr)?          // right-assoc, lowest precedence
//!   or      := and ('or' and)*
//!   and     := cmp ('and' cmp)*
//!   cmp     := unary (('='|'!=') unary)?  // non-associative
//!   unary   := 'not' unary | primary
//!   primary := ident | ident '(' expr,* ')' | '(' expr ')'

const std = @import("std");
const Allocator = std.mem.Allocator;
const lexer = @import("lexer.zig");
const Token = lexer.Token;
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig");
const InternPool = @import("InternPool.zig");

const ParseError = error{ Recover, OutOfMemory };

/// Is `name` a `by`-side KERNEL primitive? Derived from `InternPool.RuleStr` (the reserved
/// rule vocabulary) minus the `using`-side words its `keyword()` marks (`instantiation`,
/// `model`) — one source of truth, so a new kernel rule added to RuleStr is admitted here
/// automatically. Anything else (accelerant names, typos) is `using`-side.
fn isKernelRule(name: []const u8) bool {
    inline for (@typeInfo(InternPool.RuleStr).@"enum".fields) |f| {
        if (@field(InternPool.RuleStr, f.name).keyword() == .by and std.mem.eql(u8, name, f.name)) {
            return true;
        }
    }
    return false;
}

/// Tactics that accept a `(theory)` argument naming the module their
/// vocabulary + lemmas resolve against (reusing the claim's `schema` slot).
/// The right-hand side of a clause's defining relation: the `=` of a function clause or the
/// `iff` of a predicate one. Descends a leading `->`, because a clause may state its guard as
/// an ANTECEDENT rather than with `when` (`(not (i = k)) -> coeff(monomial(a, k), i) = zeroR`
/// — the shape the whole `monomial` family uses). Null for any other shape, which cannot
/// state an obligation.
fn rhsOf(e: *const ast.Expr) ?*const ast.Expr {
    return switch (e.*) {
        .binary => |b| switch (b.op) {
            .equal, .iff => b.rhs,
            .implies => rhsOf(b.rhs),
            else => null,
        },
        else => null,
    };
}

/// The namespace a clause's CONSTRUCTOR pattern is qualified by, if any — `peano.succ(n)`
/// yields `peano`. That is the theory whose vacuity schema `definition_consistency` needs, and
/// reading it off the token's qualifier is purely syntactic (the parser has no sorts).
///
/// Read from the matched ARGUMENTS only, never the right-hand side: a clause's RHS is full of
/// unrelated qualifiers (`cpower(a, NAT_ZERO) = complex.ONE` would yield `complex`), and it is
/// the pattern that names the constructors. Searched across every clause, since a split
/// commonly writes one side unqualified through a local alias (`NAT_ZERO`) and the other
/// qualified (`peano.succ`). Null when no pattern is qualified: the file owns its
/// constructors, so local resolution is right.
fn constructorTheory(clauses: []const Parser.Clause, sym: lexer.Token) ?lexer.Token {
    for (clauses) |c| {
        const app = findApplication(c.body, sym) orelse continue;
        for (app.args) |arg| {
            if (qualifierIn(arg)) |q| return q;
        }
    }
    return null;
}

fn qualifierIn(e: *const ast.Expr) ?lexer.Token {
    switch (e.*) {
        .call => |c| {
            if (c.callee.qualifier != InternPool.StrId.none) {
                var t = c.callee;
                t.name = c.callee.qualifier;
                t.qualifier = InternPool.StrId.none;
                return t;
            }
            for (c.args) |a| if (qualifierIn(a)) |q| return q;
            return null;
        },
        .binary => |b| return qualifierIn(b.lhs) orelse qualifierIn(b.rhs),
        .not => |n| return qualifierIn(n.operand),
        .quant => |q| return qualifierIn(q.body),
        .lambda => |l| return qualifierIn(l.body),
        .name => |t| {
            if (t.qualifier == InternPool.StrId.none) return null;
            var out = t;
            out.name = t.qualifier;
            out.qualifier = InternPool.StrId.none;
            return out;
        },
    }
}

/// The LEFT-hand side of a clause's defining relation, descending a leading `->` the same way
/// `rhsOf` does. This is the clause's defining APPLICATION, which pins each clause variable's
/// sort by argument position.
fn lhsOf(e: *const ast.Expr) ?*const ast.Expr {
    return switch (e.*) {
        .binary => |b| switch (b.op) {
            .equal, .iff => b.lhs,
            .implies => lhsOf(b.rhs),
            else => null,
        },
        else => null,
    };
}

/// A clause's guard written as a leading `->` ANTECEDENT, else null. The `when` form and this
/// one mean the same thing (the parser desugars `when` to exactly this), so a consistency
/// obligation must read both.
fn antecedentOf(e: *const ast.Expr) ?*const ast.Expr {
    return switch (e.*) {
        .binary => |b| if (b.op == .implies) b.lhs else null,
        else => null,
    };
}

/// Is the clause EXPLICIT — the defined symbol standing alone as the left-hand side?
///
/// An explicit clause is a REWRITE (`f(Z) = Z`, `p(x) iff q(x)`): the symbol is eliminable,
/// which is what makes the definition conservative, and the only obligation it owes is that
/// its clauses AGREE where they overlap (`consistency:`).
///
/// An IMPLICIT clause has the symbol somewhere else — `mul(a, recip(a)) = ONE` characterizes
/// `recip` by a property rather than giving its value. There is no rewrite direction, the
/// symbol is not eliminable, and the clause asserts that a value with that property EXISTS.
/// So it owes `existence:` and `uniqueness:` instead. Without them a user can derive a
/// contradiction — see PAINPOINTS 16f, which reaches `ZERO = ONE` over `std/peano.b4m`.
///
/// The test reads the LEFT side only. `f(s(n)) = s(f(n))` is EXPLICIT even though `f` also
/// appears on the right: the left side is still a rewrite target, and the right-hand
/// recurrence is what `termination:` governs.
///
/// Called on the clause BODY, after any `when` guard has been split off, so a guarded clause
/// is classified by its equation rather than its condition.
fn clauseIsExplicit(e: *const ast.Expr, name: lexer.Token) bool {
    // an implication guard (`(not (i = k)) -> coeff(...) = ZERO`) classifies by its CONSEQUENT
    const body = switch (e.*) {
        .binary => |b| if (b.op == .implies) b.rhs else e,
        else => e,
    };
    // No top-level equation or biconditional = nothing to rewrite with, so IMPLICIT. Reached
    // by a clause that is a bare predicate application: `hasSize(a, size(a)) when isFinite(a)`
    // (`std/set/finite.b4m`) characterizes `size` without equating it to anything, and its own
    // comment says so — "a set's size is whatever size it has".
    const eq = switch (body.*) {
        .binary => |b| switch (b.op) {
            .equal, .iff => b,
            else => return false,
        },
        else => return false,
    };
    return switch (eq.lhs.*) {
        .call => |c| c.callee.name == name.name,
        .name => |n| n.name == name.name,
        else => false,
    };
}

/// The clause's application of the symbol being DEFINED, searched left-to-right. A clause
/// states its symbol applied to the patterns it matches (`coeff(monomial(a, k), k) = a`
/// applies `monomial`, nested inside another call), so the search descends.
/// Every application of `name` on a clause's RIGHT-HAND SIDE, in source order — the clause's
/// RECURSIVE CALLS. Collects all of them, where `findApplication` stops at the first: `fib`'s
/// step arm calls twice (`fib(sub(k, ONE))`, `fib(sub(k, TWO))`) and the generated predicate
/// transcribes both.
///
/// Reads the RIGHT side only. A clause whose LHS nests the symbol in an accessor
/// (`coeff(monomial(a, k), i) = zeroR`) is not recursive at all — 19 such clauses in `std`,
/// and the naive "symbol appears twice" test flags every one.
fn collectRecursiveCalls(
    arena: std.mem.Allocator,
    e: *const ast.Expr,
    name: lexer.Token,
    out: *std.ArrayList(ast.Expr.Call),
) std.mem.Allocator.Error!void {
    switch (e.*) {
        .call => |c| {
            if (c.callee.name == name.name) try out.append(arena, c);
            for (c.args) |a| try collectRecursiveCalls(arena, a, name, out);
        },
        .binary => |b| {
            try collectRecursiveCalls(arena, b.lhs, name, out);
            try collectRecursiveCalls(arena, b.rhs, name, out);
        },
        .not => |n| try collectRecursiveCalls(arena, n.operand, name, out),
        .quant => |q| try collectRecursiveCalls(arena, q.body, name, out),
        .lambda => |l| try collectRecursiveCalls(arena, l.body, name, out),
        .name => {},
    }
}

/// Does `e` mention the bare name `nm` anywhere? Reads a definition clause's GUARD to find
/// which parameters it constrains — the slots the author declares as controlling the recursion.
fn mentionsName(e: *const ast.Expr, nm: InternPool.StrId) bool {
    return switch (e.*) {
        .name => |n| n.name == nm,
        .call => |c| {
            if (c.callee.name == nm) return true;
            for (c.args) |a| if (mentionsName(a, nm)) return true;
            return false;
        },
        .binary => |b| mentionsName(b.lhs, nm) or mentionsName(b.rhs, nm),
        .not => |n| mentionsName(n.operand, nm),
        .quant => |q| mentionsName(q.body, nm),
        .lambda => |l| mentionsName(l.body, nm),
    };
}

/// Is the DISJUNCTION of all arm conditions a propositional tautology — i.e. do the arms
/// provably cover the domain, by propositional logic alone?
///
/// This is the autodetection route for `totality:`. Decided by truth-table over the distinct
/// ATOMS of the conditions, treating every non-propositional subformula as opaque — the same
/// reading `tautology` uses. So it recognizes, with no theorem required:
///
///   - two-way complementarity: `n = ZERO` against `n != ZERO`     (56 of 62 `std` blocks)
///   - a PREDICATE split:       `p(x)` against `not p(x)`
///   - `swap`'s three-way:      `x = u`, `x = v`, `x != u and x != v`
///
/// and refuses `n = ZERO` against `less_than(ONE, n)`, which leaves a real gap at `ONE`. That
/// refusal is the point: an author must then name a theorem, which is exactly where to look.
/// `monus`'s missing floor clause hid here for sessions — its arms never overlapped, so
/// `consistency:` was satisfied while `i < j` matched neither arm.
///
/// SYNTACTIC AND CONSERVATIVE. Atoms are compared as written (`exprsEqual`), never reasoned
/// about: a detector that decides `n = ZERO or ONE < n` by arithmetic is a prover, and a prover
/// here can be wrong. An equation and its negation are linked by construction (the atom is the
/// same, the polarity differs); nothing else is.
fn conditionsCoverPropositionally(arena: std.mem.Allocator, conds: []const *const ast.Expr) bool {
    if (conds.len == 0) return false;
    var atoms: std.ArrayList(*const ast.Expr) = .empty;
    for (conds) |c| collectAtoms(arena, c, &atoms) catch return false;
    if (atoms.items.len == 0 or atoms.items.len > 16) return false; // same cap `tautology` uses
    // every assignment must satisfy at least one condition
    const n = atoms.items.len;
    var assign: u32 = 0;
    const limit = @as(u32, 1) << @intCast(n);
    while (assign < limit) : (assign += 1) {
        var any = false;
        for (conds) |c| if (evalUnder(c, atoms.items, assign)) {
            any = true;
            break;
        };
        if (!any) return false; // a gap: this assignment satisfies no arm
    }
    return true;
}

/// Every maximal non-propositional subformula of `e`, deduplicated.
///
/// A DISEQUATION IS THE NEGATION OF ITS EQUATION, not a separate atom — `n != ZERO` registers
/// the atom `n = ZERO` and is read with inverted polarity. Without that, `n = ZERO` and
/// `n != ZERO` would be independent atoms, the truth table would admit "both false", and the
/// commonest covering shape in the corpus would go undetected.
fn collectAtoms(arena: std.mem.Allocator, e: *const ast.Expr, out: *std.ArrayList(*const ast.Expr)) std.mem.Allocator.Error!void {
    switch (e.*) {
        .not => |n| return collectAtoms(arena, n.operand, out),
        .binary => |b| switch (b.op) {
            .and_op, .or_op, .implies, .iff => {
                try collectAtoms(arena, b.lhs, out);
                try collectAtoms(arena, b.rhs, out);
                return;
            },
            // `x != t` contributes the atom `x = t`; polarity is `evalUnder`'s business.
            .not_equal => {
                const positive = try arena.create(ast.Expr);
                positive.* = .{ .binary = .{ .op = .equal, .tok = b.tok, .lhs = b.lhs, .rhs = b.rhs } };
                for (out.items) |have| if (exprsEqual(have, positive)) return;
                try out.append(arena, positive);
                return;
            },
            else => {},
        },
        else => {},
    }
    for (out.items) |have| if (exprsEqual(have, e)) return;
    try out.append(arena, e);
}

/// Truth of `e` under the bit-assignment `assign` over `atoms`.
fn evalUnder(e: *const ast.Expr, atoms: []const *const ast.Expr, assign: u32) bool {
    switch (e.*) {
        .not => |n| return !evalUnder(n.operand, atoms, assign),
        .binary => |b| switch (b.op) {
            // the mirror of `collectAtoms`: look up `x = t` and invert.
            .not_equal => {
                for (atoms, 0..) |a, i| {
                    if (a.* != .binary or a.binary.op != .equal) continue;
                    if (!exprsEqual(a.binary.lhs, b.lhs) or !exprsEqual(a.binary.rhs, b.rhs)) continue;
                    return (assign >> @intCast(i)) & 1 == 0;
                }
                return false;
            },
            .and_op => return evalUnder(b.lhs, atoms, assign) and evalUnder(b.rhs, atoms, assign),
            .or_op => return evalUnder(b.lhs, atoms, assign) or evalUnder(b.rhs, atoms, assign),
            .implies => return !evalUnder(b.lhs, atoms, assign) or evalUnder(b.rhs, atoms, assign),
            .iff => return evalUnder(b.lhs, atoms, assign) == evalUnder(b.rhs, atoms, assign),
            else => {},
        },
        else => {},
    }
    for (atoms, 0..) |a, i| if (exprsEqual(a, e)) return (assign >> @intCast(i)) & 1 == 1;
    return false;
}

/// Structural equality of two clause expressions, by the names the parser can see. The
/// question a complementarity test asks is "the same term as written", not "provably equal",
/// so syntactic comparison is the right instrument and keeps the check deterministic from
/// source text.
fn exprsEqual(a: *const ast.Expr, b: *const ast.Expr) bool {
    return switch (a.*) {
        .name => |x| switch (b.*) {
            .name => |y| x.name == y.name and x.qualifier == y.qualifier,
            else => false,
        },
        .call => |x| switch (b.*) {
            .call => |y| {
                if (x.callee.name != y.callee.name) return false;
                if (x.args.len != y.args.len) return false;
                for (x.args, y.args) |xa, ya| if (!exprsEqual(xa, ya)) return false;
                return true;
            },
            else => false,
        },
        .binary => |x| switch (b.*) {
            .binary => |y| x.op == y.op and exprsEqual(x.lhs, y.lhs) and exprsEqual(x.rhs, y.rhs),
            else => false,
        },
        .not => |x| switch (b.*) {
            .not => |y| exprsEqual(x.operand, y.operand),
            else => false,
        },
        else => false,
    };
}

/// Does this arm's argument NARROW its slot? A pattern narrows — whether it is an application
/// (`succ(ZERO)`) or a bare CONSTANT (`ZERO`). A bare VARIABLE does not: that slot is
/// unconstrained, so there is nothing to negate.
///
/// The two bare-name cases are told apart by the declared parameter: a name matching it is the
/// parameter itself, anything else is a global the arm matches on. That is the same
/// convention `collectClauseVars` reads — lower-case single tokens are variables, and a
/// declaration's own parameter list says which. It does mean an arm that RENAMES the parameter
/// (`convolution(a, b, j, ZERO)` where the declaration says `p, q, j, m`) reads as narrowing
/// slot 0 and generates a spurious `p != a` antecedent; no such clause exists in the corpus,
/// and the narrower reading would need the elaborator's variable-vs-global verdict, which the
/// parser does not have.
///
/// Compares SYNTACTICALLY, which is all the parser can do and all that is wanted: the
/// obligation must be deterministic from source text.
fn narrowsSlot(arm: *const ast.Expr, param: ast.Binder) bool {
    return switch (arm.*) {
        .name => |n| n.name != param.name.name,
        else => true,
    };
}

/// The RHS of a clause, after any `when`/implication guard has been split off. Null when the
/// clause has no top-level equation or biconditional.
fn clauseRhs(e: *const ast.Expr) ?*const ast.Expr {
    const body = switch (e.*) {
        .binary => |b| if (b.op == .implies) b.rhs else e,
        else => e,
    };
    return switch (body.*) {
        .binary => |b| switch (b.op) {
            .equal, .iff => b.rhs,
            else => null,
        },
        else => null,
    };
}

fn findApplication(e: *const ast.Expr, name: lexer.Token) ?ast.Expr.Call {
    switch (e.*) {
        .call => |c| {
            if (c.callee.name == name.name) return c;
            for (c.args) |a| if (findApplication(a, name)) |f| return f;
            return null;
        },
        .binary => |b| return findApplication(b.lhs, name) orelse findApplication(b.rhs, name),
        .not => |n| return findApplication(n.operand, name),
        .quant => |q| return findApplication(q.body, name),
        .lambda => |l| return findApplication(l.body, name),
        .name => return null,
    }
}

/// Append `b` unless a binder of that name is already present — first-appearance order, so
/// the binder list is a function of the text.
fn addBinder(arena: std.mem.Allocator, list: *std.ArrayList(ast.Binder), b: ast.Binder) std.mem.Allocator.Error!void {
    for (list.items) |have| if (have.name.name == b.name.name) return;
    try list.append(arena, b);
}

fn isTheoryRule(name: []const u8) bool {
    return std.mem.eql(u8, name, "arithmetic") or
        std.mem.eql(u8, name, "polynomial") or
        std.mem.eql(u8, name, "polynomial_quantified") or
        std.mem.eql(u8, name, "extensionality") or
        std.mem.eql(u8, name, "extensionality_quantified") or
        std.mem.eql(u8, name, "definition_consistency") or
        std.mem.eql(u8, name, "model") or
        std.mem.eql(u8, name, "import");
}

pub const Parser = struct {
    arena: Allocator,
    source: []const u8,
    lex: lexer.Lexer,
    tok: Token,
    sink: *Diagnostics.Sink,
    /// The file every diagnostic this parser records belongs to — its offsets index
    /// `source`. Set at `init`; see diagnostics.zig on why the file is never ambient.
    file: u32 = 0,
    /// When set, every non-reserved token the parser consumes is interned and
    /// carries its `StrId` (`Token.name`/`.qualifier`) — see `initInterning`.
    interner: ?*InternPool = null,
    /// Interning failure is remembered here (stamping happens inside the
    /// infallible `advance`) and surfaced as OutOfMemory when `parseFile` returns.
    intern_oom: bool = false,
    /// DESUGARED declarations a `parseDecl` produced BESIDES its return value, drained by
    /// `parseFile` right after it. A DEFINITION BLOCK (`pred p(x: T): <clauses>`) is one
    /// source declaration that becomes several AST ones — the `pred`/`func` itself, returned
    /// normally, plus one `axiom` per clause staged here. Nothing downstream learns that
    /// definitions exist: they are axioms by the time anyone looks.
    pending: std.ArrayList(ast.Decl) = .empty,
    /// Namespaces declared by `import` that no qualifier has mentioned yet, each with the
    /// offset of its declaration. An import is USED iff some token in the file carries its
    /// name as a `ns.` qualifier — a purely SYNTACTIC fact, which is why this lives in the
    /// parser rather than in the six-odd engine sites that resolve a qualifier to a target.
    /// Those sites are reached on DEMAND, so an import nothing happens to cite is never
    /// resolved and a dangling one passes `check` (see `uncited-fact-alias-proves-nothing`).
    /// `stamp` removes a name the moment it appears as a qualifier; whatever remains at
    /// `parseFile`'s end is dead. Keyed by `StrId`, so this only arms under `initInterning`
    /// — parse-only tools (fmt/lint/query) leave ids `.none` and skip the check.
    unused_imports: std.AutoArrayHashMapUnmanaged(InternPool.StrId, PendingImport) = .empty,

    /// Non-`fact` ALIASES (`sort A = ns.B`, and the same for const/func/pred) that no bare
    /// name has mentioned yet. Same shape as `unused_imports` and deliberately NOT shared
    /// code with it: the two answer different questions over different token kinds (an
    /// import is used by a QUALIFIER, an alias by a BARE name), so a common mechanism would
    /// need a mode flag to tell them apart and earn nothing.
    ///
    /// WHY NON-`fact` ONLY: a `fact` alias is a genuine re-export — a theory's takeaway
    /// result, meant to be cited from outside, so "unused here" is normal. Sort/const/func/
    /// pred aliases are local vocabulary; a consumer should import the theory that OWNS a
    /// symbol rather than borrow an intermediate file's nickname for it (identity is by
    /// origin — see `alias-collapse` — so routing through the nickname gains nothing).
    ///
    /// ONE DRAIN SITE SUFFICES: `stamp` runs from the single `advance`, so every token in
    /// the file passes through it. A bare local name is used in ~10 syntactic positions
    /// (expressions, callees, binder sorts and guards, a guarded sort's parent, a model
    /// block's targets/dischargers/closure facts, func params and results); enumerating
    /// them would be complete only until someone adds the eleventh.
    unused_aliases: std.AutoArrayHashMapUnmanaged(InternPool.StrId, PendingAlias) = .empty,
    /// `--library` on a `.b4m` file: enforce the HEADER STRUCTURE rule below. Off for a
    /// working-directory check and for every literate `.md` (a document's prose drives its
    /// order), so the parser is unchanged outside a published-library check.
    library_structure: bool = false,
    /// set by `checkHeaderStructure` at the first `theorem`/`lemma`/`model`
    past_header: bool = false,

    /// Namespaces this file re-exports at least one `fact` from. Applied to
    /// `unused_aliases` ONCE at `parseFile`'s end, not eagerly at each `fact`, so the
    /// exemption does not depend on whether the `fact` is written above or below the alias
    /// — declaration order carries no meaning here.
    fact_namespaces: std.AutoArrayHashMapUnmanaged(InternPool.StrId, void) = .empty,

    /// An `import` awaiting its first qualifier: where it was declared, and the path it
    /// names. The PATH is in the message because the most costly version of this bug is a
    /// MISSPELLED path — "import 'group_lagrange' is never used" sends the author looking
    /// for a dead import when the real fault was a typo two directories deep.
    const PendingImport = struct { at: u32, path: InternPool.StrId };

    /// An alias awaiting its first bare mention: where it was declared, its keyword (for the
    /// message — "sort"/"const"/"oper"/"pred"), and the NAMESPACE it was aliased from.
    ///
    /// The namespace is what implements the AGGREGATOR EXEMPTION. A `fact` re-exported from
    /// namespace N is a statement written in N's vocabulary, and a consumer citing it needs
    /// that vocabulary under THIS file's names to say anything about the result. So
    /// `std/peano.b4m` must keep `pred less_than = order.less_than` even though it never
    /// says `less_than` itself: its 16 neighbouring `fact`s (`trichotomy`,
    /// `lessThanTransitive`, …) are phrased in it, and citing `peano.trichotomy` yields
    /// `… less_than(a, b) or a = b or less_than(b, a)`.
    ///
    /// Found the hard way: deleting it left `peano.b4m` passing ALONE (93 decls, 17
    /// theorems) and failing the library sweep with `reference not found: 'less_than'` —
    /// an undemanded `fact` is never resolved, so only a whole-library strict run sees it.
    const PendingAlias = struct { at: u32, kind: []const u8, from: InternPool.StrId };

    pub fn init(arena: Allocator, source: []const u8, sink: *Diagnostics.Sink) Parser {
        return initInFile(arena, source, sink, 0);
    }

    /// `init` for a driver that knows which file it is parsing (the demand engine); the
    /// bare `init` is for single-file callers (lint, query) whose file index is 0.
    pub fn initInFile(arena: Allocator, source: []const u8, sink: *Diagnostics.Sink, file: u32) Parser {
        var lex: lexer.Lexer = .init(source);
        const first = lex.next();
        return .{ .arena = arena, .source = source, .lex = lex, .tok = first, .sink = sink, .file = file };
    }

    /// Like `init`, but every non-reserved token is interned into `interner` as
    /// it is consumed, so the AST's tokens carry their `StrId`s. This is the
    /// ENGINE's parse entry: past parsing, names are integers — engine code
    /// never re-derives (or compares) name text from source. Parse-only tools
    /// (query/lint/fmt) keep plain `init`; their tokens' ids stay `.none`.
    pub fn initInterning(arena: Allocator, source: []const u8, sink: *Diagnostics.Sink, interner: *InternPool) Parser {
        return initInterningInFile(arena, source, sink, interner, 0);
    }

    /// `initInterning` for a driver that knows its file index (the demand engine).
    pub fn initInterningInFile(arena: Allocator, source: []const u8, sink: *Diagnostics.Sink, interner: *InternPool, file: u32) Parser {
        var p = initInFile(arena, source, sink, file);
        p.interner = interner;
        p.tok = p.stamp(p.tok);
        return p;
    }

    fn advance(self: *Parser) Token {
        const t = self.tok;
        self.tok = self.stamp(self.lex.next());
        return t;
    }

    /// Stamp `Token.name`/`.qualifier` for the stringy tags (no-op without an
    /// interner): identifier/kebab — the name, split at a `.` into
    /// qualifier+name; at_label — the same, sans the `@` sigil; string — the
    /// contents sans quotes (never split: paths contain dots). Reserved tokens
    /// pass through untouched. A multi-dot name (`a.b.c`) stamps qualifier=`a`,
    /// name=`b.c` verbatim — resolution diagnoses it downstream.
    fn stamp(self: *Parser, t: Token) Token {
        const ip = self.interner orelse return t;
        var tok = t;
        switch (t.tag) {
            .identifier, .kebab_identifier, .at_label => {
                const chars = self.source[t.start + @intFromBool(t.tag == .at_label) .. t.end];
                if (std.mem.indexOfScalar(u8, chars, '.')) |i| {
                    if (std.mem.indexOfScalar(u8, chars[i + 1 ..], '.') != null) {
                        // diagnosed here (parse time) so resolution never has to re-inspect
                        // name text; the token still stamps (qualifier + dotted remainder).
                        self.sink.add(self.file, t.start, "only one level of namespace qualification is allowed", .{}) catch {
                            self.intern_oom = true;
                            return tok;
                        };
                    }
                    tok.qualifier = ip.internString(chars[0..i]) catch {
                        self.intern_oom = true;
                        return tok;
                    };
                    // this token USES that namespace — whatever it resolves to downstream.
                    _ = self.unused_imports.swapRemove(tok.qualifier);
                    tok.name = ip.internString(chars[i + 1 ..]) catch {
                        self.intern_oom = true;
                        return tok;
                    };
                } else {
                    tok.name = ip.internString(chars) catch {
                        self.intern_oom = true;
                        return tok;
                    };
                    // a BARE name USES any local alias of that name. An alias's own name
                    // token also lands here, but harmlessly: each arm records itself AFTER
                    // consuming it, so there is nothing yet to remove (same ordering the
                    // import arm relies on).
                    _ = self.unused_aliases.swapRemove(tok.name);
                }
            },
            .string => tok.name = ip.internString(self.source[t.start + 1 .. t.end - 1]) catch {
                self.intern_oom = true;
                return tok;
            },
            // `model` doubles as a RULE word (`using model(M) …`) — its StrId is reserved,
            // so stamping is a constant, no interning. (`axiom`/`theorem` are NO LONGER rule
            // words — fact citation is `cite` — so their keyword tokens aren't stamped.)
            .keyword_model => tok.name = InternPool.RuleStr.model.id(),
            else => {},
        }
        return tok;
    }

    /// Record an alias as presumed-dead until some bare name mentions it. Called at the END
    /// of each non-`fact` alias arm, so the alias's own name token has already passed through
    /// `stamp` with nothing to drain. A re-declaration keeps the FIRST offset.
    fn presumeAliasDead(self: *Parser, name: Token, kind: []const u8, target: Token) ParseError!void {
        if (self.interner == null) return;
        const gop = try self.unused_aliases.getOrPut(self.arena, name.name);
        if (!gop.found_existing) gop.value_ptr.* = .{ .at = name.start, .kind = kind, .from = target.qualifier };
    }

    /// Note that this file re-exports a `fact` from `ns`. Every alias drawn from `ns` is then
    /// exempt (applied at `parseFile`'s end): the fact's statement is written in that
    /// namespace's vocabulary, so this file's aliases of it are part of what the re-export
    /// publishes, not dead weight. See `PendingAlias.from`.
    fn noteFactNamespace(self: *Parser, ns: InternPool.StrId) ParseError!void {
        if (self.interner == null or ns == InternPool.StrId.none) return;
        try self.fact_namespaces.put(self.arena, ns, {});
    }

    fn text(self: *const Parser, t: Token) []const u8 {
        return self.source[t.start..t.end];
    }

    /// Report an error at the current token and begin recovery.
    /// Stage the theorem a `_` entry stands for: `definition-<symbol>-{i,j}`, stating that
    /// pair's synthesized obligation, proved by one `definition_consistency` step.
    ///
    /// The name is the user's mangle (`InternPool.consistencyPairName`) — unreachable from
    /// source two ways over (`{` is not an identifier character, and the kebab
    /// `definition-<symbol>` half is rejected in a declaration-name position), and derived
    /// from the symbol and pair indices rather than a counter, so it is stable across runs.
    ///
    /// The step's theory SELECTOR is read off the clause patterns: a constructor written
    /// `peano.succ(n)` carries its namespace as a token QUALIFIER, which is exactly the
    /// theory whose vacuity schema the tactic needs — and reading it is syntactic, so the
    /// parser needs no sorts. With no qualified pattern (a file that owns its own
    /// constructors, or the complementary route, which needs no schema at all) the step goes
    /// bare and the names resolve locally.
    fn stageConsistencyTheorem(self: *Parser, name: Token, obligation: *const ast.Expr, p: usize, arms: usize, selector: ?Token) ParseError!void {
        const ip = self.interner orelse return; // fmt/lint/query parse without interning
        const cons: ast.Consistency = .{ .arms = arms, .entries = &.{} };
        const pair = cons.pairAt(p);
        var mangled = name;
        mangled.name = ip.consistencyPairName(self.arena, self.text(name), pair.i, pair.j) catch {
            self.intern_oom = true;
            return;
        };
        const rule = ip.internString("definition_consistency") catch {
            self.intern_oom = true;
            return;
        };
        var rule_tok = name;
        rule_tok.name = rule;
        const label = ip.internString("conclusion") catch {
            self.intern_oom = true;
            return;
        };
        var label_tok = name;
        label_tok.name = label;
        const steps = try self.arena.alloc(ast.Step, 1);
        steps[0] = .{ .label = label_tok, .body = .{ .claim = .{
            .formula = obligation,
            .kind = .using,
            .rule = rule_tok,
            .schema = selector,
            .args = &.{},
            .refs = &.{},
        } } };
        try self.pending.append(self.arena, .{
            .theorem = .{
                .local = .{
                    // EXPORTED, not a lemma: the uncited-lemma check would reject it (nothing cites
                    // an obligation — discharging it IS its purpose), and the name is unwritable from
                    // source anyway, so exporting it reaches nobody.
                    .fact = .{ .name = mangled, .formula = obligation },
                    .steps = steps,
                },
            },
        });
    }

    /// Stage the GENERATED predicate a recursive definition's termination obligation is stated
    /// over: `<f>Grounded`, a pure TRANSCRIPTION of the recursive arm's call sites.
    ///
    /// The rule (design/definition-wellformedness.md): in the recursive arm, replace every `f(t…)`
    /// with `<f>Grounded(t…)` and DROP the surrounding non-recursive structure — `fib(k) =
    /// add(fib(sub(k,ONE)), fib(sub(k,TWO)))` transcribes to `fibGrounded(k) iff
    /// fibGrounded(sub(k,ONE)) and fibGrounded(sub(k,TWO))`. The arm's own arithmetic
    /// (`add`) is not termination's business; only WHERE it recurses is.
    ///
    /// The result is a DEFINITION BLOCK, not an axiom — eliminable, as the "no generated
    /// axioms" rule demands. A recursive PRED owes nothing itself: it constrains a truth
    /// assignment rather than constructing a value, and a POSITIVE one always has a solution.
    /// Positivity is structural here, since the substitution puts `<f>Grounded` exactly where
    /// `f` stood, which is never under a negation.
    ///
    /// The author NAMES this predicate in the `{theorem, predicate}` pair, so the declaration
    /// is reachable from source — unlike the mangled consistency theorems. Naming it after the
    /// symbol is required, not cosmetic: two recursive `oper`s in one file would collide on a
    /// fixed name.
    fn stageGroundedPredicate(
        self: *Parser,
        name: Token,
        params: []const ast.Binder,
        clauses: []const Clause,
        rec: usize,
        pred_name: Token,
    ) ParseError!void {
        const clause = clauses[rec];
        const rhs = clauseRhs(clause.body) orelse return;
        var calls: std.ArrayList(ast.Expr.Call) = .empty;
        try collectRecursiveCalls(self.arena, rhs, name, &calls);
        if (calls.items.len == 0) return;

        // the clause's LHS application supplies the HEAD's arguments — whatever patterns the
        // recursive arm matches on (`fib(k)` -> `fibGrounded(k)`).
        const head_app = findApplication(clause.body, name) orelse return;

        // ONLY THE CONTROLLING SLOTS (user, 2026-11-25). A slot is controlling when the
        // recursive arm's own GUARD mentions its parameter — `cappedRun(…) when n != ZERO`
        // declares `n` to be what controls the recursion, and `monus(…) when i != ZERO and
        // j != ZERO` declares both of its. Every other slot RIDES: it may change (an exponent
        // walking up or down beside the length) but termination does not depend on it.
        //
        // READING IT OFF THE GUARD, not off "the argument differs from the head's". That was
        // the first criterion and it is wrong: `segment`'s riding exponent is written
        // `succ(c)`, which differs from `c` while getting LARGER, so "differs" classifies a
        // riding slot as controlling. The guard is the author's own statement of what shrinks,
        // which is exactly the question.
        //
        // Why this matters rather than being tidiness. Transcribing a riding slot puts its
        // arithmetic into the predicate, and if that arithmetic is GUARDED the predicate
        // becomes uninstantiable where the guard fails — while the arm's guard only ever
        // covers the slots it controls. `segment` made
        //
        //     segmentGrounded(j, c, n) iff (segmentGrounded(prev(j), succ(c), prev(n)) or …)
        //
        // unusable at `j = ZERO`: writing `prev(ZERO)` owes `ZERO != ZERO`, which is FALSE, not
        // merely unproved. Measured both ways — the identical shape with total `monus(j, ONE)`
        // in place of `prev(j)` instantiates fine, isolating the cause to a guarded operation
        // on a slot the guard does not cover.
        //
        // Dropping riding slots makes the predicate MORE faithful to what it asserts: whether
        // a recursion reaches a base depends on what shrinks, never on what an exponent does
        // alongside it.
        const slots = try self.controllingSlots(clause, params, head_app.args.len);

        // the predicate's parameters are the oper's AT THOSE SLOTS. A pred has no result sort,
        // so nothing else carries over.
        var kept_params: std.ArrayList(ast.Binder) = .empty;
        for (slots) |pos| if (pos < params.len) try kept_params.append(self.arena, params[pos]);
        const pred_params = kept_params.items;

        const head = try self.groundedCall(pred_name, try self.pickSlots(head_app.args, slots));

        // The body: ONE CONJUNCT PER CALL SITE, each a DISJUNCTION of that call grounded with
        // its argument hitting one of the terminating arms' patterns. This is what supplies the
        // recursion's BASE (user, 2026-11-24): at `k = TWO`, `sub(k, TWO) = ZERO` fires its
        // disjunct's base branch with NO recursive premise, so the chain bottoms out. An
        // earlier form conjoined the bare grounded calls and had a step with no base, which
        // made the obligation unprovable — measured, see the plan.
        //
        // The base patterns come from the TERMINATING arms' l-value arguments at the position
        // the call descends in. They are closed terms by the l-value rule, so comparing a
        // descent against one is always well-formed.
        var body: ?*const ast.Expr = null;
        for (calls.items) |c| {
            var conjunct = try self.groundedCall(pred_name, try self.pickSlots(c.args, slots));
            for (c.args, 0..) |arg, pos| {
                // a base branch belongs only to a slot the predicate still mentions
                var kept = false;
                for (slots) |k| if (k == pos) {
                    kept = true;
                    break;
                };
                if (!kept) continue;
                for (clauses, 0..) |other, other_i| {
                    if (!other.explicit) continue;
                    // only a TERMINATING arm contributes a base branch. The recursive arm's own
                    // l-value is `f(<params>)`, so without this it donates `sub(k, ONE) = k` —
                    // a branch that is not a base and would let the predicate escape its
                    // recursion.
                    if (other_i == rec) continue;
                    const oapp = findApplication(other.body, name) orelse continue;
                    if (pos >= oapp.args.len) continue;
                    const base = oapp.args[pos];
                    // only a CLOSED base pattern is a value to compare against; a bare
                    // parameter in that slot narrows nothing and contributes no branch.
                    if (base.* == .name) {
                        var is_param = false;
                        for (params) |p| if (p.name.name == base.name.name) {
                            is_param = true;
                            break;
                        };
                        if (is_param) continue;
                    }
                    conjunct = try self.binary(.or_op, pred_name, conjunct, try self.binary(.equal, pred_name, arg, base));
                }
            }
            body = if (body) |b| try self.binary(.and_op, pred_name, b, conjunct) else conjunct;
        }

        const defining = try self.binary(.iff, pred_name, head, body.?);
        try self.pending.append(self.arena, .{ .pred = .{ .local = .{
            .name = pred_name,
            .params = pred_params,
            // one clause, so no pairs: nothing to declare, exactly as a single-clause block.
            .consistency = null,
        } } });
        try self.stageDefinitionAxiom(pred_name, pred_params, defining, 0);
    }

    /// The TERMINATION obligation: `forall <params>; <base conditions negated> -> <f>Grounded(<params>)`.
    ///
    /// Stated over the DECLARATION'S PARAMETERS, not over any arm's variables. For `fib(n: Nat)`:
    ///
    ///     forall n: Nat; n != ZERO -> n != succ(ZERO) -> fibGrounded(n)
    ///
    /// and for `convolution(p: Poly, q: Poly, j: Nat, m: Nat)`, whose recursive arm matches
    /// `succ(m)`:
    ///
    ///     forall p: Poly; forall q: Poly; forall j: Nat; forall m: Nat;
    ///       m != ZERO -> convGrounded(p, q, j, m)
    ///
    /// **The parameters, not the recursive arm's pattern** — and that is load-bearing, not a
    /// style choice. Stating it at the pattern makes the obligation vacuous two ways over for
    /// an arm that matches: `succ(m) != ZERO` is trivially true, so the base arm narrows
    /// nothing; and `convGrounded(…, succ(m))` never claims anything at `ZERO`, so the
    /// predicate's recursion has no base to reach and the obligation is unprovable. Over the
    /// parameters both problems vanish — `m` ranges over the whole sort, so `m != ZERO` is a
    /// real condition and the conclusion is the universal statement induction can establish.
    ///
    /// The conditions are ANTECEDENTS rather than disjuncts of the predicate, and that too is
    /// load-bearing — two earlier drafts put them in the predicate and both died because
    /// instantiating at `ZERO` requires WRITING `sub(ZERO, TWO)`, whose guard is false, and
    /// 2b4m's guard discharge is per-term rather than flow-sensitive. As antecedents they do
    /// the opposite work: `n != ZERO -> n != succ(ZERO)` is exactly what makes `TWO <= n`
    /// derivable, so the `sub` terms become writable inside the author's proof.
    ///
    /// Each non-recursive arm contributes its condition NEGATED: a `when` guard verbatim under
    /// a `not`, or one disequation per argument slot its pattern narrows (`fib(ZERO)` gives
    /// `n != ZERO`; `convolution(p, q, j, ZERO)` gives `m != ZERO`, the other three slots being
    /// bare variables that narrow nothing).
    ///
    /// The obligation names NO ordering and NO induction principle. How to prove it is the
    /// author's choice (`peano.induction` for a one-step arm, strong induction for one reaching
    /// further back), which is the design's one load-bearing insight.
    fn terminationObligation(
        self: *Parser,
        name: Token,
        params: []const ast.Binder,
        clauses: []const Clause,
        rec: usize,
        pred_name: Token,
    ) ParseError!?*const ast.Expr {
        // The conclusion, at the parameters — but only at the CONTROLLING ones, since that is
        // the arity `stageGroundedPredicate` declares the predicate with. The two must agree.
        const rec_app_for_arity = findApplication(clauses[rec].body, name);
        const arity = if (rec_app_for_arity) |a| a.args.len else params.len;
        const slots = try self.controllingSlots(clauses[rec], params, arity);
        var args: std.ArrayList(*const ast.Expr) = .empty;
        for (slots) |pos| {
            if (pos >= params.len) continue;
            const node = try self.arena.create(ast.Expr);
            node.* = .{ .name = params[pos].name };
            try args.append(self.arena, node);
        }
        var body = try self.groundedCall(pred_name, args.items);

        // THE RECURSIVE ARM'S OWN GUARD, when it has one, is the whole antecedent (user,
        // 2026-11-24). `fib(k) = … when less_than(ONE, k)` yields
        //
        //     forall n: Nat; less_than(ONE, n) -> fibGrounded(n)
        //
        // which beats negating each base arm's condition three ways: ONE antecedent however
        // many base arms there are; it is the AUTHOR'S OWN TEXT rather than a derivation; and
        // it is directly usable — `less_than(ONE, k)` is what discharges `sub`'s guard, where
        // the negated-bases form made the proof derive that through constructor coverage.
        //
        // The guard is stated at the PARAMETERS like the rest of the obligation, so a guard
        // written in the arm's own variable names is substituted accordingly.
        if (clauses[rec].guard) |g| {
            const relocated = try self.substituteArmVarsForParams(g, name, clauses[rec], params);
            body = try self.binary(.implies, pred_name, relocated, body);
            var q = params.len;
            while (q > 0) {
                q -= 1;
                const one = try self.arena.alloc(ast.Binder, 1);
                one[0] = params[q];
                const node = try self.arena.create(ast.Expr);
                node.* = .{ .quant = .{ .q = .forall, .tok = pred_name, .binders = one, .body = body } };
                body = node;
            }
            return body;
        }

        // No guard on the recursive arm: fall back to negating each terminating arm's
        // condition. Both base forms stay legal (`fib(ZERO) = ZERO` and
        // `fib(n) = ZERO when n = ZERO`), so this path is reached by a block written in pattern
        // form throughout.
        //
        // antecedents, RIGHT to left so the written order is arm order (`->` is right-assoc).
        var i = clauses.len;
        while (i > 0) {
            i -= 1;
            if (i == rec) continue;
            const c = clauses[i];
            if (c.guard orelse antecedentOf(c.body)) |g| {
                const neg = try self.arena.create(ast.Expr);
                neg.* = .{ .not = .{ .tok = pred_name, .operand = g } };
                body = try self.binary(.implies, pred_name, neg, body);
                continue;
            }
            // a PATTERN arm: one disequation per slot it narrows, against the PARAMETER at
            // that position.
            const app = findApplication(c.body, name) orelse continue;
            var pos = app.args.len;
            while (pos > 0) {
                pos -= 1;
                if (pos >= params.len) continue;
                if (!narrowsSlot(app.args[pos], params[pos])) continue;
                const slot = try self.arena.create(ast.Expr);
                slot.* = .{ .name = params[pos].name };
                const ne = try self.binary(.not_equal, pred_name, slot, app.args[pos]);
                body = try self.binary(.implies, pred_name, ne, body);
            }
        }

        // quantify every parameter, at its declared sort, in declaration order.
        var k = params.len;
        while (k > 0) {
            k -= 1;
            const one = try self.arena.alloc(ast.Binder, 1);
            one[0] = params[k];
            const node = try self.arena.create(ast.Expr);
            node.* = .{ .quant = .{ .q = .forall, .tok = pred_name, .binders = one, .body = body } };
            body = node;
        }
        return body;
    }

    /// Which argument slots CONTROL the recursion: those whose parameter the recursive arm's
    /// own `when` guard mentions. `cappedRun(…) when n != ZERO` declares `n` to be what
    /// controls it; `monus(…) when i != ZERO and j != ZERO` declares both of its.
    ///
    /// Every other slot RIDES — it may change (an exponent walking up or down beside the
    /// controlling length) but termination does not depend on it, so the generated predicate
    /// drops it. Read off the GUARD rather than from "the argument differs from the head's":
    /// that was the first criterion and it is wrong, since a riding exponent written `succ(c)`
    /// differs from `c` while getting LARGER. The guard is the author's own statement of what
    /// shrinks, which is exactly the question being asked.
    ///
    /// Why it matters rather than being tidiness: transcribing a riding slot puts its
    /// arithmetic into the predicate, and if that arithmetic is GUARDED the predicate becomes
    /// uninstantiable where the guard fails — while the arm's guard only ever covers the slots
    /// it controls. `segment`'s riding exponent made
    ///
    ///     segmentGrounded(j, c, n) iff (segmentGrounded(prev(j), succ(c), prev(n)) or …)
    ///
    /// unusable at `j = ZERO`: writing `prev(ZERO)` owes `ZERO != ZERO`, which is FALSE, not
    /// merely unproved. Measured both ways — the identical shape with a TOTAL operation in
    /// place of `prev(j)` instantiates fine, isolating the cause to a guarded operation on a
    /// slot the guard does not cover.
    ///
    /// WITH NO GUARD (or a guard naming no parameter) the full arity is kept: a pattern-form
    /// block has no guard to read, and the degenerate `g(n) = s(g(n))` must keep generating
    /// `gGrounded(n) iff gGrounded(n)` — baseless, hence an obligation nothing can discharge,
    /// which is the behaviour to preserve.
    ///
    /// Shared by the generator and the obligation synthesizer, which must agree on the arity:
    /// they diverged in a first draft and the generated clause then failed its own arity check.
    fn controllingSlots(self: *Parser, clause: Clause, params: []const ast.Binder, arity: usize) ParseError![]const usize {
        var controlling: std.ArrayList(usize) = .empty;
        if (clause.guard) |g| {
            for (params, 0..) |p, pos| {
                if (pos >= arity) continue;
                if (!mentionsName(g, p.name.name)) continue;
                try controlling.append(self.arena, pos);
            }
        }
        if (controlling.items.len != 0) return controlling.items;
        var all: std.ArrayList(usize) = .empty;
        var pos: usize = 0;
        while (pos < arity) : (pos += 1) try all.append(self.arena, pos);
        return all.items;
    }

    /// The arguments at `slots`, in order — the projection a generated predicate applies at.
    fn pickSlots(self: *Parser, args: []const *const ast.Expr, slots: []const usize) ParseError![]const *const ast.Expr {
        var out: std.ArrayList(*const ast.Expr) = .empty;
        for (slots) |pos| if (pos < args.len) try out.append(self.arena, args[pos]);
        return out.items;
    }

    /// `<f>Grounded(args…)` — one application of the generated predicate.
    fn groundedCall(self: *Parser, pred_name: Token, args: []const *const ast.Expr) ParseError!*const ast.Expr {
        const node = try self.arena.create(ast.Expr);
        node.* = .{ .call = .{ .callee = pred_name, .args = try self.arena.dupe(*const ast.Expr, args) } };
        return node;
    }

    /// Synthesize one consistency obligation per unordered clause pair, in the canonical
    /// (lexicographic) order `ast.Consistency.pairAt` walks:
    ///
    ///     forall <binders>; (<cond_i> and <cond_j>) -> <arm_i> = <arm_j>
    ///
    /// DETERMINISTIC FROM SOURCE TEXT (user ruling) — no unification, no generated names, no
    /// choice. Each clause's condition is either its `when` guard verbatim, or, for a clause
    /// that PATTERN-MATCHES in an argument slot, an equation `<slot> = <pattern>` on a fresh
    /// POSITIONAL binder named for the slot (`arg1`, `arg2`, …).
    ///
    /// The binder must be positional and NOT the declared parameter name: `cpower(a, n: Nat)`
    /// has the clause `cpower(a, succ(n))`, whose clause variable SHADOWS the param, so
    /// `<param> = <pattern>` would generate the nonsense `n = succ(n)`.
    ///
    /// Sorts are left `inferred` exactly as `stageDefinitionAxiom` leaves a clause variable's:
    /// the parser cannot know them, and the elaborator settles them from the declarations.
    fn synthesizeObligations(self: *Parser, name: Token, params: []const ast.Binder, clauses: []const Clause) ParseError![]const *const ast.Expr {
        var out: std.ArrayList(*const ast.Expr) = .empty;
        var i: usize = 0;
        while (i < clauses.len) : (i += 1) {
            var j: usize = i + 1;
            while (j < clauses.len) : (j += 1) {
                try out.append(self.arena, try self.obligationFor(name, params, clauses[i], clauses[j]));
            }
        }
        return out.items;
    }

    /// The obligation relating two clauses. Collects each side's condition, conjoins them, and
    /// implies the equation between the two right-hand sides.
    fn obligationFor(self: *Parser, name: Token, params: []const ast.Binder, ci: Clause, cj: Clause) ParseError!*const ast.Expr {
        var binders: std.ArrayList(ast.Binder) = .empty;
        var conds: std.ArrayList(*const ast.Expr) = .empty;
        try self.conditionOf(name, params, ci, &binders, &conds);
        try self.conditionOf(name, params, cj, &binders, &conds);

        // The two arms' right-hand sides, equated — the agreed shape
        // `(conditions) -> rhs_i = rhs_j`.
        //
        // KNOWN LIMITATION, `when`-guarded blocks only: a clause VARIABLE that appears
        // nowhere but the guard and the dropped defining application has no sort the
        // ELABORATOR can infer, because its rule is argument-position only — `x = u` does not
        // pin `x` from `u: E` even though equality determines it. `swap` is the one such block
        // in std, and its obligation elaborates only once a named entry is compared. Fixing it
        // means teaching the elaborator to infer across equality, which is a separate change;
        // anchoring the clause's lhs as an extra conjunct also works but changes this shape and
        // breaks the tactic's two-conjunct recognition, so it is not the right trade.
        const li = lhsOf(ci.body) orelse return self.fail("a definition clause must be an equation (or `iff` for a predicate) for its consistency obligation to be stated", .{});
        const ri = rhsOf(ci.body).?;
        const rj = rhsOf(cj.body) orelse return self.fail("a definition clause must be an equation (or `iff` for a predicate) for its consistency obligation to be stated", .{});
        _ = li;
        var body = try self.binary(.equal, name, ri, rj);

        // conditions, left to right, conjoined into ONE flat antecedent (user ruling)
        if (conds.items.len > 0) {
            var cond = conds.items[0];
            for (conds.items[1..]) |c| cond = try self.binary(.and_op, name, cond, c);
            body = try self.binary(.implies, name, cond, body);
        }

        // quantify: the clause variables and positional slot binders, first-appearance order
        var k = binders.items.len;
        while (k > 0) {
            k -= 1;
            const one = try self.arena.alloc(ast.Binder, 1);
            one[0] = binders.items[k];
            const node = try self.arena.create(ast.Expr);
            node.* = .{ .quant = .{ .q = .forall, .tok = name, .binders = one, .body = body } };
            body = node;
        }
        return body;
    }

    /// One clause's condition, appended to `conds`, with any binders it introduces appended to
    /// `binders` (deduplicated by name, first-appearance order).
    ///
    /// Two shapes, which is what the two triviality routes correspond to:
    ///   - a `when` guard  -> the guard verbatim
    ///   - a positional pattern (`f(a, ZERO)`) -> `argN = ZERO` on a fresh positional binder
    /// A clause that writes the bare parameter in every slot and carries no guard contributes
    /// NO condition — it applies everywhere, which is exactly why overlapping it is a hazard.
    fn conditionOf(self: *Parser, name: Token, params: []const ast.Binder, c: Clause, binders: *std.ArrayList(ast.Binder), conds: *std.ArrayList(*const ast.Expr)) ParseError!void {
        // The clause's own variables come first, as stageDefinitionAxiom orders them — but a
        // DECLARED PARAM takes its declared sort, not `inferred`. The clause axiom can leave a
        // param inferred because it keeps the defining application (`at(sw(u, v), x)`), which
        // pins each sort by argument position; the obligation drops that application and keeps
        // only the two right-hand sides, so an inferred param there has nothing to pin it
        // ("cannot infer the sort of 'u'").
        var mentioned: std.ArrayList(ast.Binder) = .empty;
        try self.collectClauseVars(c.body, &mentioned);
        for (mentioned.items) |m| {
            var b = m;
            for (params) |prm| if (prm.name.name == m.name.name) {
                b = prm;
                break;
            };
            try addBinder(self.arena, binders, b);
        }

        if (c.guard orelse antecedentOf(c.body)) |g| {
            try conds.append(self.arena, g);
            return;
        }
        // positional patterns: find the clause's application of the DEFINED symbol and compare
        // each argument against the declared parameter at that position.
        const app = findApplication(c.body, name) orelse return;
        for (app.args, 0..) |arg, pos| {
            if (pos >= params.len) break;
            if (arg.* == .name and arg.name.name == params[pos].name.name) continue; // bare param: no condition
            const slot = try self.positionalBinder(name, pos);
            try addBinder(self.arena, binders, slot);
            const slot_ref = try self.arena.create(ast.Expr);
            slot_ref.* = .{ .name = slot.name };
            try conds.append(self.arena, try self.binary(.equal, name, slot_ref, arg));
        }
    }

    /// One arm's condition for the COVERAGE question, stated at the DECLARATION'S PARAMETERS —
    /// null when the arm is unconditional (it applies everywhere, so the block trivially
    /// covers).
    ///
    /// Differs from `conditionOf`, which serves `consistency:` and introduces fresh positional
    /// binders (`arg1`, `arg2`) because a pair's obligation relates two arms that may name their
    /// variables differently. Coverage is one statement over the parameters, so a pattern arm's
    /// condition is written against the parameter directly: `f(a, ZERO)` gives `n = ZERO` for
    /// the declaration `f(a, n)`, not `arg2 = ZERO`.
    fn coverageConditionOf(self: *Parser, name: Token, params: []const ast.Binder, c: Clause) ParseError!?*const ast.Expr {
        if (c.guard orelse antecedentOf(c.body)) |g| return g;
        const app = findApplication(c.body, name) orelse return null;
        var cond: ?*const ast.Expr = null;
        for (app.args, 0..) |arg, pos| {
            if (pos >= params.len) break;
            if (arg.* == .name and arg.name.name == params[pos].name.name) continue; // bare param narrows nothing
            const slot = try self.arena.create(ast.Expr);
            slot.* = .{ .name = params[pos].name };
            // A PATTERN BINDS ITS OWN VARIABLES, distinct from the parameters even when
            // spelled the same: `f(i, j, succ(k))` against the declaration `f(i, j, k)` means
            // "k is a successor of SOMETHING", not the false `k = succ(k)`. So the condition is
            // EXISTENTIAL over the pattern's free names.
            //
            // Getting this wrong produces an obligation that is not merely hard but FALSE,
            // which is the same shape of defect as the binder-rename hazard: a synthesized
            // statement that typechecks while asserting something nobody meant.
            // A PATTERN BINDS ITS OWN VARIABLES, distinct from the parameters even when spelled
            // identically: `f(i, j, succ(k))` against the declaration `f(i, j, k)` means "k is a
            // successor of SOMETHING", so the condition is `exists k'; k = succ(k')` — never the
            // false `k = succ(k)`. Getting this wrong yields an obligation that is not merely
            // hard but FALSE, the same shape of defect as the binder-rename hazard: a
            // synthesized statement that typechecks while asserting what nobody meant.
            //
            // The pattern's binders are RENAMED before the equation is built, so the parameter
            // reference on the left keeps its own name — renaming afterwards rewrites both sides
            // alike. The suffix is the slot index, so the spelling is a function of the
            // declaration and stable across runs. It must differ from the parameter's: the
            // obligation already quantifies `forall k`, and `exists k` inside it is rejected by
            // the no-shadowing rule.
            // A BARE NAME argument binds nothing: it is a CONSTANT the arm matches against
            // (`f(zed)`, `f(ZERO)`), so the condition is the plain equation `n = zed` with no
            // existential. Only names nested INSIDE an application are the pattern's own
            // binders — `succ(k)` binds `k`.
            //
            // This distinction cannot be made by spelling. `aata` declares
            // `const intZero = integer.ZERO`, a legal lower-case constant, and the style guide
            // prescribes lower-case for `pi`/`e`/`i`; `collectClauseVars` reads the lower-case
            // convention and so calls `intZero` a variable. Quantifying it produced
            // `exists intZero_at1; n = intZero_at1` — true but vacuous, which both broke
            // complementarity with the `n != intZero` guard (so the block wrongly appeared to
            // owe an obligation) and failed to elaborate. Reading the ARGUMENT'S SHAPE instead
            // of its name sidesteps the ambiguity entirely: the same ambiguity is what blocks
            // the l-value rule and what produced PAINPOINTS 16h.
            var pattern_vars: std.ArrayList(ast.Binder) = .empty;
            if (arg.* != .name) try self.collectClauseVars(arg, &pattern_vars);
            var pattern = arg;
            var fresh_binders: std.ArrayList(ast.Binder) = .empty;
            for (pattern_vars.items) |pv| {
                var fresh = pv;
                if (self.interner) |ip| {
                    const spelled = std.fmt.allocPrint(self.arena, "{s}_at{d}", .{ ip.stringBytes(pv.name.name), pos + 1 }) catch return error.OutOfMemory;
                    fresh.name.name = ip.internString(spelled) catch return error.OutOfMemory;
                    pattern = try self.renameFreeName(pattern, pv.name.name, fresh.name);
                }
                try fresh_binders.append(self.arena, fresh);
            }
            var eq = try self.binary(.equal, name, slot, pattern);
            var fb = fresh_binders.items.len;
            while (fb > 0) {
                fb -= 1;
                const one = try self.arena.alloc(ast.Binder, 1);
                one[0] = fresh_binders.items[fb];
                const node = try self.arena.create(ast.Expr);
                node.* = .{ .quant = .{ .q = .exists, .tok = name, .binders = one, .body = eq } };
                eq = node;
            }
            cond = if (cond) |have| try self.binary(.and_op, name, have, eq) else eq;
        }
        return cond;
    }

    /// The coverage obligation: the arms' conditions DISJOINED, quantified over the
    /// declaration's parameters.
    ///
    ///     forall n: Nat; n = ZERO or less_than(ONE, n)
    ///
    /// Deterministic from source text, like every other synthesized obligation — the author
    /// never writes it, so `--library` reports both sides when a named theorem states something
    /// else.
    fn coverageObligation(self: *Parser, name: Token, params: []const ast.Binder, conds: []const *const ast.Expr) ParseError!*const ast.Expr {
        var body = conds[0];
        for (conds[1..]) |c| body = try self.binary(.or_op, name, body, c);
        var i = params.len;
        while (i > 0) {
            i -= 1;
            const one = try self.arena.alloc(ast.Binder, 1);
            one[0] = params[i];
            const node = try self.arena.create(ast.Expr);
            node.* = .{ .quant = .{ .q = .forall, .tok = name, .binders = one, .body = body } };
            body = node;
        }
        return body;
    }

    /// A fresh binder for argument slot `pos`, named `argN` — a function of the DECLARATION
    /// alone, so it is stable under any clause's choice of variable names.
    fn positionalBinder(self: *Parser, name: Token, pos: usize) ParseError!ast.Binder {
        var tok = name;
        if (self.interner) |ip| {
            const slot_name = std.fmt.allocPrint(self.arena, "arg{d}", .{pos + 1}) catch return error.OutOfMemory;
            tok.name = ip.internString(slot_name) catch return error.OutOfMemory;
        }
        return .{ .name = tok, .sort = tok, .inferred = true };
    }

    /// Rewrite an arm's GUARD into the declaration's parameter names. The obligation is stated
    /// over the parameters, but a guard is written in whatever names the arm's l-value binds —
    /// `fib(k) = … when less_than(ONE, k)` binds `k` where the declaration says `n`.
    ///
    /// Positional: the arm's l-value argument at slot `i` corresponds to parameter `i`. Only a
    /// BARE-NAME argument is substituted; a closed base pattern binds nothing, and by the
    /// l-value rule those are the only two cases a recursive block admits.
    fn substituteArmVarsForParams(
        self: *Parser,
        guard: *const ast.Expr,
        name: Token,
        clause: Clause,
        params: []const ast.Binder,
    ) ParseError!*const ast.Expr {
        const app = findApplication(clause.body, name) orelse return guard;
        var out = guard;
        for (app.args, 0..) |arg, pos| {
            if (pos >= params.len) break;
            if (arg.* != .name) continue;
            if (arg.name.name == params[pos].name.name) continue;
            out = try self.renameFreeName(out, arg.name.name, params[pos].name);
        }
        return out;
    }

    /// `out` with every free `.name` leaf spelled `from` respelled as `to`. Structural, no
    /// capture analysis — a definition clause's guard has no binders of its own.
    fn renameFreeName(self: *Parser, e: *const ast.Expr, from: InternPool.StrId, to: Token) ParseError!*const ast.Expr {
        const node = try self.arena.create(ast.Expr);
        switch (e.*) {
            .name => |n| {
                if (n.name != from) return e;
                node.* = .{ .name = to };
            },
            .call => |c| {
                const args = try self.arena.alloc(*const ast.Expr, c.args.len);
                for (c.args, 0..) |a, i| args[i] = try self.renameFreeName(a, from, to);
                node.* = .{ .call = .{ .callee = c.callee, .args = args } };
            },
            .binary => |b| node.* = .{ .binary = .{
                .op = b.op,
                .tok = b.tok,
                .lhs = try self.renameFreeName(b.lhs, from, to),
                .rhs = try self.renameFreeName(b.rhs, from, to),
            } },
            .not => |n| node.* = .{ .not = .{ .tok = n.tok, .operand = try self.renameFreeName(n.operand, from, to) } },
            else => return e,
        }
        return node;
    }

    /// THE L-VALUE TEST for a recursive definition's clause argument: a bare PARAMETER, or a
    /// term with NO FREE VARIABLES.
    ///
    /// "Free variable" follows the same convention `collectClauseVars` reads — a lower-case
    /// single token that the declaration's parameter list does not claim is a clause variable;
    /// anything upper-case or qualified is a global by convention. So `ZERO` and
    /// `succ(succ(ZERO))` pass (closed), `k` passes (a parameter), and `succ(m)` fails for the
    /// free `m` inside it.
    fn argumentIsLegalLValue(self: *Parser, arg: *const ast.Expr, params: []const ast.Binder) bool {
        if (arg.* == .name) {
            for (params) |p| if (p.name.name == arg.name.name) return true;
        }
        var free: std.ArrayList(ast.Binder) = .empty;
        self.collectClauseVars(arg, &free) catch return false;
        return free.items.len == 0;
    }

    fn binary(self: *Parser, op: ast.Expr.BinOp, tok: Token, lhs: *const ast.Expr, rhs: *const ast.Expr) ParseError!*const ast.Expr {
        const node = try self.arena.create(ast.Expr);
        node.* = .{ .binary = .{ .op = op, .tok = tok, .lhs = lhs, .rhs = rhs } };
        return node;
    }

    /// One parsed definition clause, kept so the PAIRS can be synthesized. `guard` is the
    /// `when` condition when written; the positional condition (a constructor pattern in an
    /// argument slot) is recovered from `body` instead.
    /// `explicit` records whether the clause's LHS is the defined symbol (a rewrite — see
    /// `clauseIsExplicit`). It decides which well-formedness obligations the block owes:
    /// `consistency:` for explicit clauses, `existence:`/`uniqueness:` for implicit ones.
    /// What a definition block's well-formedness section declared: the explicit case's
    /// clause-pair `consistency:` list, and/or the implicit case's `existence:`/`uniqueness:`
    /// pair. A block is one or the other, never both — `parseWellformedness` errors if the
    /// declared kind does not match the clauses' shape.
    pub const Wellformedness = struct {
        consistency: ?ast.Consistency = null,
        determinacy: ?ast.Determinacy = null,
        termination: ?ast.Termination = null,
        totality: ?ast.Totality = null,
    };

    pub const Clause = struct {
        body: *const ast.Expr,
        guard: ?*const ast.Expr,
        explicit: bool = true,
    };

    fn fail(self: *Parser, comptime fmt: []const u8, args: anytype) ParseError {
        self.sink.add(self.file, self.tok.start, fmt, args) catch return error.OutOfMemory;
        return error.Recover;
    }

    fn expect(self: *Parser, tag: Token.Tag) ParseError!Token {
        if (self.tok.tag != tag) {
            return self.fail("expected '{s}', got '{s}'", .{ tag.spelling(), self.describe() });
        }
        return self.advance();
    }

    /// A step-label DEFINITION: `@name` (the `@` sigil is required — it marks a
    /// definition, distinct from the bare names that cite it). Returns a token
    /// spanning just the `name` (sans `@`) so it interns and resolves
    /// identically to those references.
    fn expectLabelDef(self: *Parser) ParseError!Token {
        switch (self.tok.tag) {
            .at_label => {
                const t = self.advance();
                // the stamped ids already exclude the `@` — carry them forward.
                return .{ .tag = .kebab_identifier, .start = t.start + 1, .end = t.end, .name = t.name, .qualifier = t.qualifier };
            },
            else => return self.fail("expected a step label '@name', got '{s}'", .{self.describe()}),
        }
    }

    /// A `[by ...]` reference / `unpack from` / `case` citation: a bare name
    /// (plain or kebab). References carry NO `@` — the sigil is for definitions.
    fn expectLabelRef(self: *Parser) ParseError!Token {
        return switch (self.tok.tag) {
            .identifier, .kebab_identifier => self.advance(),
            else => self.fail("expected a label reference, got '{s}'", .{self.describe()}),
        };
    }

    /// Enforce the by/using vocabulary partition at parse time: `by` admits only
    /// kernel-primitive rule words, `using` only accelerant / engine-generation words.
    /// Classified BY TEXT (this is the parser — strcmp is legal here, and the parse-only
    /// tools use `init` without an interner so the token isn't stamped): a KERNEL word (the
    /// pure primitives) requires `by`; everything else — accelerants, `instantiation`,
    /// `model`, and any unknown word — requires `using`. An unknown word therefore surfaces
    /// as "cite with `using`" if written after `by`; if written after `using` it passes here
    /// and the "unsupported by the demand prover" diagnostic fires later.
    fn checkKeyword(self: *Parser, kw: ast.Step.Claim.Kind, rule: Token) ParseError!void {
        const want: ast.Step.Claim.Kind = if (isKernelRule(self.text(rule))) .by else .using;
        if (kw == want) return;
        return switch (want) {
            .by => self.fail("'{s}' is a kernel rule; cite it with `by`, not `using`", .{self.text(rule)}),
            .using => self.fail("'{s}' is an accelerant; cite it with `using`, not `by`", .{self.text(rule)}),
        };
    }

    /// For error messages: identifiers show their text, everything else its spelling.
    fn describe(self: *const Parser) []const u8 {
        return switch (self.tok.tag) {
            .identifier, .kebab_identifier, .at_label => self.text(self.tok),
            else => self.tok.tag.spelling(),
        };
    }

    fn isTopLevelKeyword(tag: Token.Tag) bool {
        return switch (tag) {
            .keyword_sort, .keyword_const, .keyword_define, .keyword_oper, .keyword_pred, .keyword_fact, .keyword_axiom, .keyword_hole, .keyword_theorem, .keyword_theory, .keyword_forward, .keyword_model => true,
            else => false,
        };
    }

    /// THE LIBRARY HEADER RULE (`--library`, `.b4m` only). A library file's header is its
    /// INTERFACE: what it assumes (`axiom`, `hole`) and what it promises (`intheory`). All of
    /// it must be declared before any of it is used, so a reader learns both without reading a
    /// proof.
    ///
    /// The header admits `theory`, `intheory`, `axiom`, `hole`, `sort`, `oper`, `const`,
    /// `pred`, `define` and `fact`. The first `theorem`, `lemma` or `model` ends it; after
    /// that, `intheory`, `axiom` and `hole` are errors. Vocabulary — sorts, opers, consts,
    /// preds, defines, `fact` aliases, further `theory` declarations — stays legal anywhere,
    /// since none of it adds an assumption or a promise.
    ///
    /// `fact` is header vocabulary rather than a trigger: an alias is "a local name for the
    /// same thing, not a copy", so it is the same kind of declaration as the `sort`/`oper`
    /// aliases it sits among (91 of 151 std files open with such a block).
    fn checkHeaderStructure(self: *Parser, decl: ast.Decl, loc: u32) void {
        const kind: []const u8 = switch (decl) {
            .theorem => |t| switch (t) {
                .local => if (t.local.fact.exported) "theorem" else "lemma",
                .alias => return, // a `theorem X = ns.y` is a re-export; parsed as `fact`
            },
            .model => "model",
            .forward => "intheory",
            .axiom => |a| switch (a) {
                .local => "axiom",
                .alias => return,
            },
            .hole => "hole",
            else => return, // vocabulary: legal anywhere
        };
        if (std.mem.eql(u8, kind, "theorem") or std.mem.eql(u8, kind, "lemma") or
            std.mem.eql(u8, kind, "model"))
        {
            self.past_header = true;
            return;
        }
        if (!self.past_header) return;
        self.sink.add(self.file, loc, "`{s}` after the first proof: a library file's header declares everything it assumes and promises before any of it is used — move this above the first theorem/lemma/model (--library only)", .{kind}) catch {
            self.intern_oom = true;
        };
    }

    pub fn parseFile(self: *Parser) Allocator.Error!ast.File {
        var decls: std.ArrayList(ast.Decl) = .empty;
        while (self.tok.tag != .eof) {
            const decl_loc = self.tok.start;
            const decl = self.parseDecl() catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Recover => {
                    // skip to next top-level declaration keyword
                    while (self.tok.tag != .eof and !isTopLevelKeyword(self.tok.tag)) {
                        _ = self.advance();
                    }
                    continue;
                },
            };
            try decls.append(self.arena, decl);
            if (self.library_structure) self.checkHeaderStructure(decl, decl_loc);
            // a definition block staged its clause axioms — emit them right after the
            // declaration they belong to, so source order is preserved.
            for (self.pending.items) |extra| try decls.append(self.arena, extra);
            self.pending.clearRetainingCapacity();
        }
        if (self.intern_oom) return error.OutOfMemory;
        // Dead imports are an ERROR, not a warning (`no-warnings-hard-errors`): an import
        // nothing cites is either a leftover or — the case that motivated this — a MISSPELLED
        // path that `check` would otherwise accept in silence.
        for (self.unused_imports.keys(), self.unused_imports.values()) |ns, pending| {
            const ip = self.interner orelse break;
            self.sink.add(self.file, pending.at, "theory '{s}' ({s}) is never used — cite it, or remove it if the path is wrong", .{ ip.stringBytes(ns), ip.stringBytes(pending.path) }) catch return error.OutOfMemory;
        }
        // Likewise a non-`fact` alias nothing mentions: local vocabulary nothing speaks. A
        // `fact` alias is exempt — it is a re-export, so being unused HERE is its normal state.
        for (self.unused_aliases.keys(), self.unused_aliases.values()) |nm, pending| {
            const ip = self.interner orelse break;
            // the aggregator exemption, applied order-independently
            if (self.fact_namespaces.contains(pending.from)) continue;
            self.sink.add(self.file, pending.at, "{s} alias '{s}' is never used — remove it, or import the theory that owns it where you need it", .{ pending.kind, ip.stringBytes(nm) }) catch return error.OutOfMemory;
        }
        return .{ .decls = try decls.toOwnedSlice(self.arena) };
    }

    fn parseDecl(self: *Parser) ParseError!ast.Decl {
        switch (self.tok.tag) {
            .keyword_theory => {
                _ = self.advance();
                const ns = try self.expect(.identifier);
                _ = try self.expect(.import_arrow);
                const path = try self.expect(.string);
                // presumed dead until some qualifier names it (see `unused_imports`). A
                // re-import of a name already pending keeps the FIRST offset: the duplicate
                // is the redundant one.
                if (self.interner != null) {
                    const gop = try self.unused_imports.getOrPut(self.arena, ns.name);
                    if (!gop.found_existing) gop.value_ptr.* = .{ .at = ns.start, .path = path.name };
                }
                return .{ .import = .{ .ns = ns, .path = path } };
            },
            .keyword_forward => {
                _ = self.advance();
                return .{ .forward = .{ .name = try self.expect(.identifier) } };
            },
            .keyword_sort => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                // `sort N` root | `sort N = T` alias | `sort N = T where p` guarded.
                if (self.tok.tag != .equal) return .{ .sort = .{ .local = name } };
                _ = self.advance();
                const target = try self.expect(.identifier);
                if (self.tok.tag == .keyword_where) {
                    _ = self.advance();
                    // one or more qualifier predicates: `where p` | `where p and q and …`.
                    var guards: std.ArrayList(Token) = .empty;
                    while (true) {
                        try guards.append(self.arena, try self.expect(.identifier));
                        if (self.tok.tag == .keyword_and) {
                            _ = self.advance();
                            continue;
                        }
                        break;
                    }
                    return .{ .sort = .{ .guarded = .{ .name = name, .parent = target, .guards = try guards.toOwnedSlice(self.arena) } } };
                }
                try self.presumeAliasDead(name, "sort", target);
                return .{ .sort = .{ .alias = .{ .name = name, .target = target } } };
            },
            .keyword_const => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| {
                    try self.presumeAliasDead(name, "const", target);
                    return .{ .constant = .{ .alias = .{ .name = name, .target = target } } };
                }
                _ = try self.expect(.colon);
                return .{ .constant = .{ .local = .{ .name = name, .sort = try self.expect(.identifier) } } };
            },
            .keyword_define => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                // optional `(params)` — a parameterized define is a macro function
                // or predicate; no parens = a nullary term/prop abbreviation.
                const params = try self.parseDefineParams();
                _ = try self.expect(.equal);
                return .{ .define = .{ .name = name, .params = params, .value = try self.parseExpr() } };
            },
            .keyword_oper => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| {
                    try self.presumeAliasDead(name, "oper", target);
                    return .{ .func = .{ .alias = .{ .name = name, .target = target } } };
                }
                const params = try self.parseParams(false);
                // `=> Result`, not `: Result` — the colon is reserved for a DEFINITION
                // block (`func f(a: T) => U:` followed by its defining clauses). `=>` is
                // already the lambda arrow (`fun k: Nat => body`), so it reads the same way:
                // takes these, gives that.
                _ = try self.expect(.fat_arrow);
                const result = try self.expect(.identifier);
                var requires: ?*const ast.Expr = null;
                if (self.tok.tag == .keyword_requires) {
                    _ = self.advance();
                    requires = try self.parseExpr();
                }
                // `func f(a: T) => U:` opens a DEFINITION BLOCK (see parseDefinitionClauses).
                const fwf: Wellformedness = if (self.tok.tag == .colon) try self.parseDefinitionClauses(name, params) else .{};
                return .{ .func = .{ .local = .{ .name = name, .params = params, .result = result, .requires = requires, .consistency = fwf.consistency, .determinacy = fwf.determinacy, .termination = fwf.termination, .totality = fwf.totality } } };
            },
            .keyword_pred => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| {
                    try self.presumeAliasDead(name, "pred", target);
                    return .{ .pred = .{ .alias = .{ .name = name, .target = target } } };
                }
                const params = try self.parseParams(true);
                // `pred p(x: T):` opens a DEFINITION BLOCK — the declaration carries the
                // clauses that characterize it. Bare `pred p(x: T)` stays opaque.
                const pwf: Wellformedness = if (self.tok.tag == .colon) try self.parseDefinitionClauses(name, params) else .{};
                // A `pred` cannot be implicitly defined — it is total (so existence is free)
                // and determined pointwise by any condition on it (so uniqueness is free), and
                // `parseWellformedness` rejects the obligations on an explicit block. So there
                // is no determinacy to carry here.
                return .{ .pred = .{ .local = .{ .name = name, .params = params, .consistency = pwf.consistency } } };
            },
            .keyword_fact => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                // ALIAS-ONLY: `fact X = ns.y`. A bare `fact X: formula` is refused, because a
                // LOCAL claim always has a kind — see ast.Decl.fact.
                if (try self.parseAliasTail()) |target| {
                    try self.noteFactNamespace(target.qualifier);
                    return .{ .fact = .{ .name = name, .target = target } };
                }
                return self.fail("a 'fact' is a re-export and must name a target: `fact <name> = <namespace>.<name>`. A local claim has a kind — use `axiom` for this theory's own primitive, `theorem` for a proved result, or `hole` (optionally `cites \"...\"`) for an unproved one", .{});
            },
            .keyword_axiom => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                // an `axiom X = ns.y` RE-EXPORT is now spelled `fact X = ns.y`: the kind of
                // an alias is the TARGET's property, which the alias cannot know and nothing
                // checked. See ast.Decl.fact.
                if (self.tok.tag == .equal) {
                    return self.fail("a re-export is spelled `fact`, not `axiom`: write `fact <name> = <namespace>.<name>`. The alias cannot know its target's kind, so restating it was redundant and went stale", .{});
                }
                // an optional `(params)` makes it an axiom-SCHEMA (a parametric assumption
                // family) — recorded as Fact.params; "schema" is a downstream reading.
                const params = try self.parseOptSchemaParams();
                // `cites` belongs on a HOLE, not an axiom: an axiom is a theory's own
                // primitive, while a borrowed result is assumed on someone else's authority
                // and must stay visible as a hole.
                if (self.tok.tag == .keyword_cites) {
                    return self.fail("'cites' belongs on a hole, not an axiom: an axiom is a theory's own primitive, while a result borrowed from a source is assumed on external authority — write it as a cited hole, which stays disclosed but passes a strict check", .{});
                }
                _ = try self.expect(.colon);
                const formula = try self.parseExpr();
                if (self.tok.tag == .keyword_proof) {
                    return self.fail("an axiom does not carry a proof; declare it as a theorem", .{});
                }
                return .{ .axiom = .{ .local = .{ .name = name, .formula = formula, .params = params } } };
            },
            .keyword_hole => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                const params = try self.parseOptSchemaParams();
                // an optional `cites "locator"` makes this a CITED hole: assumed on external
                // authority, reported but not a strict-mode failure. See ast.Decl.hole.
                const cites: ?Token = if (self.tok.tag == .keyword_cites) blk: {
                    _ = self.advance();
                    break :blk try self.expect(.string);
                } else null;
                _ = try self.expect(.colon);
                if (self.tok.tag == .keyword_proof) {
                    return self.fail("a hole is a placeholder and carries no proof; once you prove it, make it a theorem", .{});
                }
                return .{ .hole = .{ .local = .{ .name = name, .formula = try self.parseExpr(), .params = params, .cites = cites } } };
            },
            // `theorem` and `lemma` are the SAME declaration: identical syntax, identical
            // proof obligation, identical kernel treatment (both intern as fact kind
            // `theorem`). A `lemma` only clears `Fact.exported`, which says another file may
            // not cite its name.
            .keyword_theorem, .keyword_lemma => {
                const exported = self.tok.tag == .keyword_theorem;
                const kw: []const u8 = if (exported) "theorem" else "lemma";
                _ = self.advance();
                const name = try self.expect(.identifier);
                // likewise `theorem X = ns.y` → `fact X = ns.y`.
                if (self.tok.tag == .equal) {
                    return self.fail("a re-export is spelled `fact`, not `{s}`: write `fact <name> = <namespace>.<name>`. The alias cannot know its target's kind, so restating it was redundant and went stale", .{kw});
                }
                // an optional `(params)` makes it a theorem-SCHEMA (proof re-checked per
                // instantiation) — recorded as Fact.params.
                const params = try self.parseOptSchemaParams();
                _ = try self.expect(.colon);
                const formula = try self.parseExpr();
                _ = try self.expect(.keyword_proof);
                const steps = try self.parseSteps(.keyword_qed);
                _ = try self.expect(.keyword_qed);
                return .{ .theorem = .{ .local = .{ .fact = .{ .name = name, .formula = formula, .params = params, .exported = exported }, .steps = steps } } };
            },
            .keyword_model => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                // no `= carrier [where guard]` header: the carrier is whatever the
                // source carrier maps to, and the guard is inferred from a predicated
                // target sort in the mappings.
                const m = try self.parseModelMappings();
                return .{ .model = .{ .name = name, .identifiers = m.identifiers, .obligations = m.obligations } };
            },
            else => return self.fail("expected a declaration, got '{s}'", .{self.describe()}),
        }
    }

    /// The mapping lines of a `model` block. Forms:
    ///   `<source> : <target>`                — a symbol/sort interpretation (→ `identifiers`)
    ///   `<source> : <target>(f1, f2, …)`     — CONST→refined-sort: PARENS base-fact witnesses
    ///                                           (`refined_sort`; one fact per target-sort guard)
    ///   `<source> : <target> -| <closure>`   — FUNC→refined-result: closure discharger
    ///                                           (`closed_operation`; single fact for now)
    ///   `<source> <- <localThm>`             — an axiom-obligation discharge (→ `obligations`)
    /// A `<-` whose SOURCE is a definition block's symbol discharges its whole clause set
    /// arm-for-arm, and its TARGET must likewise be a definition block (see ModelTask).
    /// A `<target>@<projected>` model-projection value is only valid on the `<-` form. The
    /// PARENS/`- |` witness clauses are only valid on the `:` form (a symbol map); which of
    /// them is legal for a given symbol (const vs func) is checked later, in ModelTask, where
    /// the symbol's KIND is resolved.
    fn parseModelMappings(self: *Parser) ParseError!struct { identifiers: []const ast.IdentMapping, obligations: []const ast.Mapping } {
        _ = try self.expect(.l_brace);
        // the `:` symbol/sort interpretations and the `<-` obligation discharges go to
        // SEPARATE lists — they resolve against different tables (idents vs facts).
        var identifiers: std.ArrayList(ast.IdentMapping) = .empty;
        var obligations: std.ArrayList(ast.Mapping) = .empty;
        while (self.tok.tag != .r_brace) {
            const source = try self.expect(.identifier);
            const is_symbol = switch (self.tok.tag) {
                .colon => true,
                .obligation_arrow => false,
                else => return self.fail("expected ':' (symbol/sort map) or '<-' (axiom-obligation discharge)", .{}),
            };
            _ = self.advance();
            const target = try self.expect(.identifier);

            if (!is_symbol) {
                // OBLIGATION: `src <- localThm` (+ optional `@projection`).
                var projection: ?Token = null;
                if (self.tok.tag == .at_label) {
                    const at = self.advance();
                    // stamped ids already exclude the `@` (and split a `ns.` qualifier).
                    projection = .{ .tag = .identifier, .start = at.start + 1, .end = at.end, .name = at.name, .qualifier = at.qualifier };
                }
                try obligations.append(self.arena, .{ .source = source, .target = target, .projection = projection });
                continue;
            }

            // SYMBOL map: `src : target` optionally with a guard-discharger witness clause.
            const mapping: ast.Mapping = .{ .source = source, .target = target, .projection = null };
            const im: ast.IdentMapping = switch (self.tok.tag) {
                // CONST → refined sort: `target(f1, f2, …)` — one base fact per target-sort guard.
                .l_paren => blk: {
                    _ = self.advance();
                    var dischargers: std.ArrayList(Token) = .empty;
                    while (true) {
                        try dischargers.append(self.arena, try self.expect(.identifier));
                        if (self.tok.tag == .comma) {
                            _ = self.advance();
                            continue;
                        }
                        break;
                    }
                    _ = try self.expect(.r_paren);
                    break :blk .{ .refined_sort = .{ .mapping = mapping, .dischargers = try dischargers.toOwnedSlice(self.arena) } };
                },
                // FUNC → refined result: `target -| closure1, closure2, …` (one closure fact
                // per guard predicate of the result's refined sort; comma list).
                .closure_turnstile => blk: {
                    _ = self.advance();
                    var closures: std.ArrayList(Token) = .empty;
                    while (true) {
                        try closures.append(self.arena, try self.expect(.identifier));
                        if (self.tok.tag == .comma) {
                            _ = self.advance();
                            continue;
                        }
                        break;
                    }
                    break :blk .{ .closed_operation = .{ .mapping = mapping, .closure_facts = try closures.toOwnedSlice(self.arena) } };
                },
                // `@`-projection is an obligation-only form; reject on a symbol map.
                .at_label => return self.fail("a '@'-projection value is only valid on a '<-' obligation discharge, not a ':' symbol map", .{}),
                else => .{ .basic = mapping },
            };
            try identifiers.append(self.arena, im);
        }
        _ = try self.expect(.r_brace);
        return .{ .identifiers = try identifiers.toOwnedSlice(self.arena), .obligations = try obligations.toOwnedSlice(self.arena) };
    }

    /// The alias tail `= target`, if `=` follows the name — returns the target token, else
    /// null (a local decl). Guard-free: only a SORT alias admits `where`, handled inline in
    /// the sort branch (a guarded sort is a distinct `Sort.guarded`, not an alias).
    fn parseAliasTail(self: *Parser) ParseError!?Token {
        if (self.tok.tag != .equal) return null;
        _ = self.advance();
        return try self.expect(.identifier);
    }

    /// An OPTIONAL `(params)` schema-parameter list — non-null makes the axiom/theorem/hole a
    /// SCHEMA (a parametric template). Absent = a plain fact.
    fn parseOptSchemaParams(self: *Parser) ParseError!?[]const ast.SchemaParam {
        if (self.tok.tag != .l_paren) return null;
        return try self.parseSchemaParams();
    }

    /// `( ident: sort, ... )` — absent or `()` means ZERO-ary.
    /// A DEFINITION BLOCK's clauses, staged onto `pending` as synthetic `axiom` decls.
    /// Called with the `:` still current, after the `pred`/`func` header is parsed.
    ///
    ///     pred isEvenPerm(g: Grp):
    ///       isEvenPerm(g) iff exists s: Seq; …
    ///
    ///     func add(a: Nat, b: Nat) => Nat:
    ///       add(ZERO, b) = b;
    ///       add(succ(k), b) = succ(add(k, b))
    ///
    /// Each clause is written EXACTLY as the axiom it becomes, so the desugaring is a
    /// wrapping, not a translation: universally quantify over the declaration's params and
    /// emit. A clause's own free variables beyond the params (`k` in `add(succ(k), b)`) are
    /// quantified too — collected in first-appearance order so the binder list is a
    /// function of the text, never of a hash walk.
    ///
    /// An optional Erlang-style `when <guard>` makes the clause conditional: the emitted
    /// formula becomes `guard -> clause`. Guards do NOT establish precedence — every clause
    /// states its own condition in full, because axioms have no order (see
    /// design/definition-wellformedness.md).
    fn parseDefinitionClauses(self: *Parser, name: Token, params: []const ast.Binder) ParseError!Wellformedness {
        _ = try self.expect(.colon);
        // Each clause is kept (not just staged) so the PAIRS can be synthesized below: a
        // consistency obligation relates two clauses, which needs both their guards and both
        // their equations.
        var clauses: std.ArrayList(Clause) = .empty;
        var arm: usize = 0;
        while (true) {
            const clause = try self.parseExpr();
            var formula = clause;
            var guard: ?*const ast.Expr = null;
            if (self.tok.tag == .keyword_when) {
                const when_tok = self.tok;
                _ = self.advance();
                guard = try self.parseExpr();
                const node = try self.arena.create(ast.Expr);
                node.* = .{ .binary = .{ .op = .implies, .tok = when_tok, .lhs = guard.?, .rhs = clause } };
                formula = node;
            }
            try clauses.append(self.arena, .{ .body = clause, .guard = guard, .explicit = clauseIsExplicit(clause, name) });
            try self.stageDefinitionAxiom(name, params, formula, arm);
            arm += 1;
            if (self.tok.tag != .semicolon) break;
            _ = self.advance();
        }
        // The clause list is TERMINATED by `.`, which separates it from the block's
        // WELL-FORMEDNESS declarations (`consistency:` today, `termination:` later). Without
        // the terminator a dropped `;` just ends the block, and the next clause reports as
        // "expected a declaration" at a line that looks fine — naming `;` or `.` here points
        // at the actual mistake.
        if (self.tok.tag != .dot) {
            return self.fail("expected ';' before the next clause or '.' to end the definition, got '{s}'", .{self.describe()});
        }
        _ = self.advance();
        return self.parseWellformedness(name, params, clauses.items);
    }

    /// A definition block's WELL-FORMEDNESS declarations, after the clause list's `.`:
    ///
    ///     consistency: <name | _> [, <name | _>]…
    ///
    /// One entry per unordered clause PAIR in canonical (lexicographic) order — `(0,1)`,
    /// `(0,2)`, … `(1,2)`, … A NAME points that pair at a theorem the author wrote; `_` says
    /// discharge it with `definition_consistency`. Every position is written out even when
    /// automatic, so a reader sees how many pairs exist and a miscount is an error rather than
    /// a silent default. See design/definition-wellformedness.md.
    ///
    /// `consistency` is a plain identifier, not a keyword: nothing in the corpus uses the name,
    /// and a block attribute does not need to be reserved vocabulary.
    fn parseWellformedness(self: *Parser, name: Token, params: []const ast.Binder, clauses: []const Clause) ParseError!Wellformedness {
        const arms = clauses.len;
        var found: ?ast.Consistency = null;
        var ex_tok: ?Token = null;
        var un_tok: ?Token = null;
        // Is ANY clause implicit? One is enough: the block then characterizes its symbol by a
        // property, and owes existence + uniqueness for the clause set as a whole. A block
        // mixing the two kinds is rejected below — nothing in the corpus does it, and the
        // obligations for a mixed block are not defined.
        var implicit_arms: usize = 0;
        for (clauses) |c| if (!c.explicit) {
            implicit_arms += 1;
        };
        if (implicit_arms != 0 and implicit_arms != arms) {
            return self.fail("definition '{s}' mixes explicit and implicit clauses ({d} of {d} are implicit) — an explicit clause rewrites its symbol, an implicit one characterizes it, and a block must be one or the other", .{ self.text(name), implicit_arms, arms });
        }
        const is_implicit = implicit_arms != 0;
        while (self.tok.tag == .identifier and std.mem.eql(u8, self.text(self.tok), "consistency")) {
            _ = self.advance();
            // `consistency(<theory>):` — the theory whose VACUITY SCHEMA a `_` entry's staged
            // proof cites. Optional, because a file owning its own constructors needs none.
            //
            // It exists because the alternative is to SNIFF it: `constructorTheory` reads the
            // theory off whether the author happened to qualify a clause token, so
            // `nrep(a, peano.ZERO)` found `peano` while the same definition written through
            // local aliases (`nrep(a, ZERO)`) found nothing and staged a proof that could not
            // cite the schema. Same mathematics, different behaviour by spelling — the naming
            // coupling [[accelerator-naming-couplings]] forbids. Stating it is the fix.
            var selector: ?Token = null;
            if (self.tok.tag == .l_paren) {
                _ = self.advance();
                selector = try self.expect(.identifier);
                _ = try self.expect(.r_paren);
            }
            _ = try self.expect(.colon);
            var entries: std.ArrayList(?Token) = .empty;
            while (true) {
                if (self.tok.tag == .identifier and std.mem.eql(u8, self.text(self.tok), "_")) {
                    _ = self.advance();
                    try entries.append(self.arena, null);
                } else {
                    try entries.append(self.arena, try self.expect(.identifier));
                }
                if (self.tok.tag != .comma) break;
                _ = self.advance();
            }
            const want = arms * (arms - 1) / 2;
            if (entries.items.len != want) {
                return self.fail("`consistency:` needs one entry per clause pair — {d} clause(s) make {d} pair(s), got {d}", .{ arms, want, entries.items.len });
            }
            if (found != null) return self.fail("a definition block declares `consistency:` at most once", .{});
            const list = try entries.toOwnedSlice(self.arena);
            const obligations = try self.synthesizeObligations(name, params, clauses);
            // A `_` entry has no theorem of the author's, so STAGE one: named by the pair's
            // mangle, stating the synthesized obligation, proved by the one tactic step. That
            // makes the entry real — `ParseTask` racks a ProveTask for any staged theorem with
            // no params, so the obligation is actually DISCHARGED rather than just declared.
            // A NAMED entry stages nothing; its own theorem is checked against the obligation.
            for (list, 0..) |entry, p| {
                if (entry != null) continue;
                if (p >= obligations.len) break;
                // The DECLARED selector wins; `constructorTheory`'s sniff is the fallback so
                // existing qualified-pattern blocks keep working unchanged.
                try self.stageConsistencyTheorem(name, obligations[p], p, arms, selector orelse constructorTheory(clauses, name));
            }
            found = .{ .arms = arms, .entries = list, .obligations = obligations };
        }

        // `totality(<theory>): <theorem>` — ONE entry, because coverage is a single statement
        // about the whole block rather than something per arm or per pair.
        var tot_theory: ?Token = null;
        var tot_theorem: ?Token = null;
        while (self.tok.tag == .identifier and std.mem.eql(u8, self.text(self.tok), "totality")) {
            if (tot_theorem != null) return self.fail("a definition block declares `totality:` at most once", .{});
            _ = self.advance();
            if (self.tok.tag == .l_paren) {
                _ = self.advance();
                tot_theory = try self.expect(.identifier);
                _ = try self.expect(.r_paren);
            }
            _ = try self.expect(.colon);
            tot_theorem = try self.expect(.identifier);
        }

        // `termination(<theory>): _, _, {thm, pred}` — positional over the ARMS. A `_` marks a
        // terminating arm (no recursive call); a `{thm, pred}` pair marks a recursive one and
        // names the theorem the author proves plus the predicate the checker generates.
        var term_theory: ?Token = null;
        var term_entries: std.ArrayList(?ast.Termination.Pair) = .empty;
        var saw_termination = false;
        while (self.tok.tag == .identifier and std.mem.eql(u8, self.text(self.tok), "termination")) {
            if (saw_termination) return self.fail("a definition block declares `termination:` at most once", .{});
            saw_termination = true;
            _ = self.advance();
            if (self.tok.tag == .l_paren) {
                _ = self.advance();
                term_theory = try self.expect(.identifier);
                _ = try self.expect(.r_paren);
            }
            _ = try self.expect(.colon);
            while (true) {
                if (self.tok.tag == .identifier and std.mem.eql(u8, self.text(self.tok), "_")) {
                    _ = self.advance();
                    try term_entries.append(self.arena, null);
                } else {
                    _ = try self.expect(.l_brace);
                    const thm = try self.expect(.identifier);
                    _ = try self.expect(.comma);
                    const prd = try self.expect(.identifier);
                    _ = try self.expect(.r_brace);
                    try term_entries.append(self.arena, .{ .theorem = thm, .predicate = prd });
                }
                if (self.tok.tag != .comma) break;
                _ = self.advance();
            }
            if (term_entries.items.len != arms) {
                return self.fail("`termination:` needs one entry per clause — {d} clause(s), got {d}", .{ arms, term_entries.items.len });
            }
        }

        // Each entry must MATCH its arm: `_` only where the arm does not recurse, a
        // `{thm, pred}` pair only where it does. Positional declarations drift silently
        // otherwise — an author who reorders the clauses would leave the recursive arm
        // unchecked and the obligation stated about a terminating one.
        var term_obligations: std.ArrayList(?*const ast.Expr) = .empty;
        if (saw_termination) {
            for (term_entries.items, clauses, 0..) |entry, c, i| {
                const rhs = clauseRhs(c.body);
                var calls: std.ArrayList(ast.Expr.Call) = .empty;
                if (rhs) |r| try collectRecursiveCalls(self.arena, r, name, &calls);
                const recurses = calls.items.len != 0;
                if (recurses and entry == null) {
                    return self.fail("`termination:` entry {d} is `_`, but clause {d} of '{s}' RECURSES — a recursive arm needs `{{theorem, predicate}}`", .{ i + 1, i, self.text(name) });
                }
                if (!recurses and entry != null) {
                    return self.fail("`termination:` entry {d} names a theorem, but clause {d} of '{s}' does not recurse — a terminating arm takes `_`", .{ i + 1, i, self.text(name) });
                }
                const pair = entry orelse {
                    try term_obligations.append(self.arena, null);
                    continue;
                };
                try self.stageGroundedPredicate(name, params, clauses, i, pair.predicate);
                try term_obligations.append(self.arena, try self.terminationObligation(name, params, clauses, i, pair.predicate));
            }
        }

        // The IMPLICIT case's pair. Both names are required, in either order, each once.
        while (self.tok.tag == .identifier) {
            const word = self.text(self.tok);
            const is_ex = std.mem.eql(u8, word, "existence");
            const is_un = std.mem.eql(u8, word, "uniqueness");
            if (!is_ex and !is_un) break;
            _ = self.advance();
            _ = try self.expect(.colon);
            const thm = try self.expect(.identifier);
            if (is_ex) {
                if (ex_tok != null) return self.fail("a definition block declares `existence:` at most once", .{});
                ex_tok = thm;
            } else {
                if (un_tok != null) return self.fail("a definition block declares `uniqueness:` at most once", .{});
                un_tok = thm;
            }
            if (self.tok.tag == .comma) _ = self.advance();
        }

        // An IMPLICIT block characterizes its symbol by a property it satisfies rather than
        // rewriting it away, so the clause silently asserts that such a value EXISTS and that
        // the property pins it DOWN. Both must be discharged, or the block is an assumption
        // wearing a definition's clothes — PAINPOINTS 16f derives `ZERO = ONE` from one that
        // was not.
        if (is_implicit) {
            if (ex_tok == null or un_tok == null) {
                return self.fail("definition '{s}' is IMPLICIT (its clause characterizes '{s}' rather than rewriting it) and must declare both `existence:` and `uniqueness:` after the clause list's `.`", .{ self.text(name), self.text(name) });
            }
        } else if (ex_tok != null or un_tok != null) {
            return self.fail("definition '{s}' is EXPLICIT (its clause rewrites '{s}' away), so `existence:`/`uniqueness:` do not apply — an explicit definition is eliminable and owes only `consistency:` across its clause pairs", .{ self.text(name), self.text(name) });
        }
        // Does this block RECURSE? A recursive one MUST declare `termination:`. Without it
        // nothing checks the recursion reaches a base case, and the author derives a
        // contradiction in six steps — measured, strict-green before this was enforced:
        //
        //     axiom sNoFixedPoint: forall a: N; s(a) != a
        //     oper g(n: N) => N:
        //       g(n) = s(g(n)).
        //     theorem absurd: Z != Z        // the clause at Z, plus sNoFixedPoint at g(Z)
        //
        // `g` asserts a value equal to its own successor, which no `N` has, so the clause is
        // inconsistent and everything follows. Requiring the declaration rejects `g` where it
        // is written, and the obligation the declaration names is what rules the recursion
        // sound.
        //
        // ENFORCED as of the `segment` migration (2026-11-25), which converted the last of the
        // 72 recursive `std` blocks. This and the l-value rule below were staged off together
        // while that ran; both are live now.
        var any_recursive = false;
        var rec_arm: usize = 0;
        for (clauses, 0..) |c, ci| {
            const rhs = clauseRhs(c.body) orelse continue;
            var calls: std.ArrayList(ast.Expr.Call) = .empty;
            collectRecursiveCalls(self.arena, rhs, name, &calls) catch return error.OutOfMemory;
            if (calls.items.len != 0) {
                if (!any_recursive) rec_arm = ci;
                any_recursive = true;
            }
        }
        if (any_recursive and !saw_termination) {
            return self.fail("definition '{s}' is RECURSIVE (a clause calls '{s}' on its right-hand side) and must declare `termination(<theory>): …` after the clause list's `.` — one entry per clause, `_` for a terminating arm and `{{theorem, predicate}}` for a recursive one. Without it nothing checks the recursion reaches a base case, and a definition like `g(n) = s(g(n))` is inconsistent", .{ self.text(name), self.text(name) });
        }
        if (saw_termination and !any_recursive) {
            return self.fail("definition '{s}' is not recursive, so `termination:` does not apply", .{self.text(name)});
        }
        if (any_recursive) {
            // ONE IMPLICIT ARM BANS RECURSION IN THE WHOLE BLOCK (user ruling 2026-11-24).
            // An implicit clause characterizes the value by a property rather than constructing
            // it, so a recursive one characterizes it by a property mentioning itself — with no
            // call sites to transcribe into a grounding predicate and nothing to ground the
            // recursion. There is no obligation to state, which is why this is a prohibition
            // rather than a gap.
            //
            // The ban is on the BLOCK, not on the implicit arm: an implicit arm anywhere means
            // the symbol is not eliminable, so no arm's recursion can be grounded, however the
            // recursive arms themselves are written. Tested per clause rather than deduced from
            // the all-explicit-or-all-implicit mixing check above — that check makes this
            // equivalent today, and this rule should not silently weaken if it ever relaxes.
            //
            // FREE: zero violations in `std` (the accessor-nested l-values like
            // `coeff(monomial(a, k), k) = a` are implicit but not recursive, which the RHS-only
            // `collectRecursiveCalls` already distinguishes).
            for (clauses) |c| {
                if (c.explicit) continue;
                return self.fail("definition '{s}' has an IMPLICIT clause (its left side does not rewrite '{s}' away) and the block is RECURSIVE — an implicit clause characterizes its value by a property, so the symbol is not eliminable and no arm's recursion can be grounded. Write every clause explicitly, or characterize the value without self-reference", .{ self.text(name), self.text(name) });
            }
            // THE L-VALUE RULE (user ruling 2026-11-24): every argument of every arm is a bare
            // parameter, or a term with NO FREE VARIABLES. One test, not two cases — a closed
            // term (`ZERO`, `succ(ZERO)`) is a value the generated predicate can compare a
            // descent against; `succ(m)` is a DESTRUCTURING that puts the descent on the left,
            // where the generator cannot read it. The RHS is unrestricted: whatever descent the
            // author wants lives there, and that is where the call sites are collected from.
            //
            // STILL STAGED OFF, and for a NEW reason — not the migration, which is complete.
            // `argumentIsLegalLValue` asks `collectClauseVars` whether an argument has free
            // variables, and that reads the LOWER-CASE convention, so a lower-case CONSTANT in
            // a base arm reads as a variable and the arm is rejected. Measured: `aata`'s
            // `multiple(intZero, r) = zero` (with `const intZero = integer.ZERO`) fails, and so
            // does a minimal `f(zed) = zed` against `const zed: N`. `std` escaped it only
            // because its zeros are spelled `ZERO`/`NAT_ZERO`.
            //
            // The style guide PRESCRIBES lower-case for `pi`/`e`/`i`, so this is not a corpus
            // wart to clean up — the rule needs a way to tell a constant from a variable, which
            // the single-pass parser has no declared-name table for. Two proxies already
            // misfired on the sibling binder-agreement check (spelling flags `intZero`;
            // "appears on the RHS" flags `NAT_ZERO`), so this wants a real fix, not a third
            // guess. The `termination:` requirement above is live regardless, and it is the one
            // that closes the soundness hole.
            // A clause's l-value argument that RENAMES a declared parameter silently corrupts
            // the generated predicate and opens a VACUOUS DISCHARGE of the termination
            // obligation. Measured, not theorised:
            //
            //   `f(j, ZERO)` against params `(i, k)` makes slot 0 read as a closed PATTERN, so
            //   the generator emits a base branch `i = j`, which the obligation restates at the
            //   parameters as `j = j`. TRUE, so the disjunct fires unconditionally, the
            //   predicate holds everywhere, and `[by reflexivity]` plus `tautology` discharges
            //   the obligation with NO INDUCTION AT ALL. That is exactly the vacuous route
            //   design/definition-wellformedness.md's soundness argument had searched for and not
            //   found.
            //
            // DETECTED VIA THE RECURSIVE ARM, which is the one clause whose argument names are
            // pinned: its l-value must be `f(<params>)` by the l-value rule, so any bare name
            // there that is not the slot's parameter IS a rename. A terminating arm cannot be
            // checked this way — `cmonus(NAT_ZERO, j)` and `f(j, Z)` are indistinguishable to
            // the parser, which has no declared-name table (it is single-pass, which is why
            // `collectClauseVars` leans on the lower-case convention) and cannot tell a
            // lower-case CONSTANT from a variable: `aata` declares `const intZero`, and the
            // style guide prescribes lower-case for `pi`/`e`/`i`. Two proxies were tried and
            // both misfired — spelling flags `intZero`, "appears on the RHS" flags `NAT_ZERO`.
            //
            // Checking the recursive arm alone suffices in practice: a block that renames in
            // its base arms but not its recursive one is possible, and would still generate a
            // reflexive branch. That residual is recorded rather than papered over, and the
            // narrowsSlot hardening below is the second line of defence.
            if (clauses.len != 0) {
                const rec_app = findApplication(clauses[rec_arm].body, name);
                if (rec_app) |app| for (app.args, 0..) |arg, pos| {
                    if (arg.* != .name) continue;
                    if (pos >= params.len) continue;
                    if (arg.name.name == params[pos].name.name) continue;
                    const ip = self.interner orelse continue;
                    return self.fail("definition '{s}' is RECURSIVE and its recursive clause writes argument {d} as '{s}' where the declaration names that parameter '{s}' — a recursive block's clauses must use the declared parameter names, because the termination check reads each base pattern by slot and a rename makes the generated predicate's base branch reflexive (provable by reflexivity, so the obligation would be vacuous)", .{ self.text(name), pos + 1, ip.stringBytes(arg.name.name), ip.stringBytes(params[pos].name.name) });
                };
            }
            if (false) for (clauses) |c| {
                const app = findApplication(c.body, name) orelse continue;
                for (app.args) |arg| {
                    if (self.argumentIsLegalLValue(arg, params)) continue;
                    return self.fail("definition '{s}' is RECURSIVE, so every argument on the left of every clause must be a parameter or a term with no free variables — this one destructures, which puts the descent where the termination check cannot read it. Write the pattern's descent on the RIGHT instead", .{self.text(name)});
                }
            };
        }

        // THE COVERAGE DEMAND. A multi-arm EXPLICIT block must either cover propositionally or
        // name a theorem. Implicit blocks are exempt: they characterize a value by a property
        // rather than by cases, so there are no arms to cover with — their obligations are
        // `existence:`/`uniqueness:`.
        var totality: ?ast.Totality = null;
        if (arms > 1 and clauses[0].explicit) {
            var conds: std.ArrayList(*const ast.Expr) = .empty;
            var all_conditioned = true;
            for (clauses) |c| {
                const cond = try self.coverageConditionOf(name, params, c);
                if (cond) |x| try conds.append(self.arena, x) else {
                    // an UNCONDITIONAL arm applies everywhere, so the block trivially covers.
                    all_conditioned = false;
                    break;
                }
            }
            if (all_conditioned and !conditionsCoverPropositionally(self.arena, conds.items)) {
                // REQUIRED. A block whose arms do not provably cover its domain must name the
                // proof that they do — otherwise it may leave the symbol UNDETERMINED
                // somewhere, which is what a definition exists to rule out and an axiom exists
                // to disclose. `monus`'s missing floor clause hid exactly there: its two arms
                // never overlapped, so every `consistency:` pair was vacuous while `i < j`
                // matched neither — undetermined precisely where the flooring was the point.
                //
                // Only blocks autodetection DECLINES reach here; 56 of the corpus's 62
                // applicable blocks are a base pattern beside its exact negation and owe
                // nothing.
                const thm = tot_theorem orelse return self.fail("definition '{s}' has {d} arms whose conditions do not provably cover its domain, so it may leave the symbol UNDETERMINED somewhere — declare `totality(<theory>): <theorem>` naming the proof that they do cover, or widen an arm's condition", .{ self.text(name), arms });
                totality = .{
                    .theory = tot_theory,
                    .theorem = thm,
                    .obligation = try self.coverageObligation(name, params, conds.items),
                };
            } else if (tot_theorem) |thm| {
                _ = thm;
                return self.fail("definition '{s}' already covers its domain by propositional logic (its arms' conditions are exhaustive), so `totality:` declares an obligation it does not owe", .{self.text(name)});
            }
        } else if (tot_theorem != null) {
            return self.fail("definition '{s}' does not need `totality:` — coverage is a statement about MULTIPLE explicit arms, and this block has {d} arm(s)", .{ self.text(name), arms });
        }

        const determ: ?ast.Determinacy = if (ex_tok != null and un_tok != null)
            .{ .existence = ex_tok.?, .uniqueness = un_tok.? }
        else
            null;
        const term: ?ast.Termination = if (saw_termination)
            .{
                .theory = term_theory,
                .entries = try term_entries.toOwnedSlice(self.arena),
                .obligations = try term_obligations.toOwnedSlice(self.arena),
            }
        else
            null;
        return .{ .consistency = found, .determinacy = determ, .termination = term, .totality = totality };
    }

    /// Wrap one clause in `forall` over the declaration's params plus any extra free
    /// variables it mentions, and stage it as an axiom.
    fn stageDefinitionAxiom(self: *Parser, name: Token, params: []const ast.Binder, clause: *const ast.Expr, arm: usize) ParseError!void {
        // The clause's free lower-case names, in FIRST-APPEARANCE order (a function of the
        // text, never of a traversal accident). A declared param among them is quantified at
        // its declared sort — a param the clause does not mention is NOT quantified (the axiom
        // is the clause exactly as written, `forall s; cycle(s, ZERO) = id`, with no vacuous
        // `forall k` for a citer to peel). Any other name (`k` in `add(s(k), b) = s(add(k, b))`)
        // is quantified with NO sort (`inferred`): the parser cannot know whether a lower-case
        // name is a clause variable or a global the file declares (`identityFn`), nor which sort
        // a variable has; the elaborator settles both from the declarations (ast.Binder.inferred).
        var mentioned: std.ArrayList(ast.Binder) = .empty;
        try self.collectClauseVars(clause, &mentioned);
        var binders: std.ArrayList(ast.Binder) = .empty;
        for (params) |p| for (mentioned.items) |m| if (m.name.name == p.name.name) {
            try binders.append(self.arena, p);
            break;
        };
        for (mentioned.items) |m| {
            var is_param = false;
            for (params) |p| if (p.name.name == m.name.name) {
                is_param = true;
                break;
            };
            if (!is_param) try binders.append(self.arena, m);
        }
        // NESTED single-binder quantifiers (innermost = last binder): a quantifier node shares
        // ONE sort across its binders, so `func cycle(s: Points, k: Nat)` must not become
        // `forall s, k: Points`; and an inferred binder is settled per node.
        var formula = clause;
        var i = binders.items.len;
        while (i > 0) {
            i -= 1;
            const one = try self.arena.alloc(ast.Binder, 1);
            one[0] = binders.items[i];
            const node = try self.arena.create(ast.Expr);
            node.* = .{ .quant = .{ .q = .forall, .tok = name, .binders = one, .body = formula } };
            formula = node;
        }
        // The emitted axiom's name is MANGLED — it cannot be the declaration's own, which
        // already names the pred/func (that collision is what `definition{…}` avoids). The
        // mangling is DETERMINISTIC in (symbol, arm), so `[by definition(N) f]` finds the
        // fact by re-mangling rather than searching, and `{}` cannot occur in a parsed
        // identifier, so a mangled name can never collide with a user's. `--axioms` reads
        // the marker to disclose a definition differently from a genuine assumption.
        var mangled = name;
        if (self.interner) |ip| {
            mangled.name = ip.definitionClauseName(self.arena, self.text(name), arm) catch {
                self.intern_oom = true;
                return;
            };
        }
        try self.pending.append(self.arena, .{ .axiom = .{ .local = .{ .name = mangled, .formula = formula } } });
    }

    /// Append every `.name` leaf of `e` that is not already bound (by the declaration's
    /// params, an inner quantifier, or an earlier find) to `out` as an INFERRED binder (no
    /// sort; the elaborator decides global-vs-variable and the variable's sort). Lower-case
    /// single-token names only: an upper-case or qualified name is a global (a const, another
    /// symbol) by convention, so a mistyped `ZER0` still reads as an unresolved reference.
    fn collectClauseVars(self: *Parser, e: *const ast.Expr, out: *std.ArrayList(ast.Binder)) ParseError!void {
        switch (e.*) {
            .name => |t| {
                if (t.qualifier != InternPool.StrId.none) return; // qualified: a global
                const txt = self.text(t);
                if (txt.len == 0 or !std.ascii.isLower(txt[0])) return; // ALLCAPS/Camel: a global
                for (out.items) |b| if (b.name.name == t.name) return; // already bound
                try out.append(self.arena, .{ .name = t, .sort = t, .inferred = true });
            },
            .call => |c| for (c.args) |a| try self.collectClauseVars(a, out),
            .binary => |b| {
                try self.collectClauseVars(b.lhs, out);
                try self.collectClauseVars(b.rhs, out);
            },
            .not => |n| try self.collectClauseVars(n.operand, out),
            // a quantifier binds its own; its body's other frees are still ours to catch.
            .quant => |q| try self.collectClauseVars(q.body, out),
            .lambda => |l| try self.collectClauseVars(l.body, out),
        }
    }

    /// `require_parens` is for `pred`: a predicate ALWAYS writes its signature's parens, so
    /// a zero-argument one is `pred base()` and bare `pred base` is an error. A `func` does
    /// not (its zero-arity form is `const`), and a nullary proposition is then written `base()`
    /// at every use — one spelling in all four positions (declaration, schema parameter,
    /// formula, schema argument).
    fn parseParams(self: *Parser, require_parens: bool) ParseError![]const ast.Binder {
        if (self.tok.tag != .l_paren) {
            if (require_parens) {
                return self.fail("a predicate writes its parameter list — a zero-argument predicate is 'name()', not a bare name", .{});
            }
            return &.{};
        }
        _ = self.advance();
        var params: std.ArrayList(ast.Binder) = .empty;
        while (self.tok.tag != .r_paren) {
            const name = try self.expect(.identifier);
            _ = try self.expect(.colon);
            const sort = try self.expect(.identifier);
            var guard: ?Token = null;
            if (self.tok.tag == .keyword_where) {
                _ = self.advance();
                guard = try self.expect(.identifier);
            }
            try params.append(self.arena, .{ .name = name, .sort = sort, .guard = guard });
            if (self.tok.tag != .comma) break;
            _ = self.advance();
        }
        _ = try self.expect(.r_paren);
        return params.toOwnedSlice(self.arena);
    }

    /// `(a, b, …)` — a define's params are bare NAMES. A sort annotation is a hard error: a
    /// define is a macro, its sorts are inferred from its body (a declared sort would be a
    /// second, possibly disagreeing, source).
    fn parseDefineParams(self: *Parser) ParseError![]const Token {
        if (self.tok.tag != .l_paren) return &.{};
        _ = self.advance();
        var params: std.ArrayList(Token) = .empty;
        while (self.tok.tag != .r_paren) {
            const name = try self.expect(.identifier);
            if (self.tok.tag == .colon) {
                return self.fail("define parameters take no sort — a define is a macro whose sorts are inferred from its body", .{});
            }
            try params.append(self.arena, name);
            if (self.tok.tag != .comma) break;
            _ = self.advance();
        }
        _ = try self.expect(.r_paren);
        return params.toOwnedSlice(self.arena);
    }

    /// `( x: Nat, prop(Nat), spec(Element, Element), f(Item) => Item )`
    ///
    /// THREE KINDS, no keyword — the token after the parameter NAME decides, on one-token
    /// lookahead (and `=>` after the `)` separates func from pred):
    ///
    ///     x: Nat                  VALUE   `:`
    ///     prop(Nat)   q()          PRED    `(` … `)`
    ///     f(Item) => Item         FUNC    `(` … `)` `=>`
    ///
    /// A PRED writes no result because it cannot have one (see `ast.SchemaParam`). This frees
    /// `->` to mean implication only — it used to mean BOTH, disambiguated purely by which
    /// parser function was on the stack — makes arity explicit, makes a nullary pred
    /// representable (`arg_sorts.len == 0` used to MEAN "value"), and kills the silent-kind
    /// change: `(prop: Nat)` is now unambiguously a VALUE param, and the predicate one meant is
    /// `prop(Nat)` — different shapes, not a missing arrow.
    ///
    /// A nullary pred is `q()`, never a bare `q`: a predicate always writes its parens, in
    /// every position (`pred q()` declares, `q()` is used in a formula and supplied as an
    /// argument). A BARE name here is an error — it would be ambiguous with a value param
    /// whose sort was forgotten.
    ///
    /// `x: Nat` is deliberately `parseParams`' own binder spelling, and `prop(Nat)` /
    /// `f(Item) => Item` read like the `pred` / `func` declarations they stand for.
    fn parseSchemaParams(self: *Parser) ParseError![]const ast.SchemaParam {
        _ = try self.expect(.l_paren);
        var params: std.ArrayList(ast.SchemaParam) = .empty;
        while (self.tok.tag != .r_paren) {
            const name = try self.expect(.identifier);
            const kind: ast.SchemaParam.Kind = if (self.tok.tag == .colon) blk: {
                _ = self.advance();
                break :blk .{ .value = try self.expect(.identifier) };
            } else if (self.tok.tag == .comma or self.tok.tag == .r_paren) {
                // A nullary pred parameter is `q()`, matching how one is declared and used.
                return self.fail("a schema parameter needs its kind: a value is 'x: Sort', a predicate 'q()' or 'q(Sort, …)', a function 'f(Sort) => Sort'", .{});
            } else blk: {
                _ = try self.expect(.l_paren);
                var sorts: std.ArrayList(Token) = .empty;
                while (self.tok.tag != .r_paren) {
                    try sorts.append(self.arena, try self.expect(.identifier));
                    if (self.tok.tag != .comma) break;
                    _ = self.advance();
                }
                _ = try self.expect(.r_paren);
                const args = try sorts.toOwnedSlice(self.arena);
                if (self.tok.tag != .fat_arrow) break :blk .{ .pred = args };
                _ = self.advance();
                break :blk .{ .func = .{ .args = args, .result = try self.expect(.identifier) } };
            };
            try params.append(self.arena, .{ .name = name, .kind = kind });
            if (self.tok.tag != .comma) break;
            _ = self.advance();
        }
        _ = try self.expect(.r_paren);
        return params.toOwnedSlice(self.arena);
    }

    fn parseSteps(self: *Parser, end: Token.Tag) ParseError![]const ast.Step {
        var steps: std.ArrayList(ast.Step) = .empty;
        while (self.tok.tag != end and self.tok.tag != .eof) {
            try steps.append(self.arena, try self.parseStep());
        }
        return steps.toOwnedSlice(self.arena);
    }

    fn parseStep(self: *Parser) ParseError!ast.Step {
        const label = try self.expectLabelDef();
        // `|` (not ':') delimits step labels: visually the Fitch proof gutter,
        // and it keeps ':' solely for sort ascription
        _ = try self.expect(.pipe);
        switch (self.tok.tag) {
            .keyword_assume => {
                _ = self.advance();
                const formula = try self.parseExpr();
                const steps = try self.parseBlock();
                return .{ .label = label, .body = .{ .assume = .{ .formula = formula, .steps = steps } } };
            },
            .keyword_fix => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                _ = try self.expect(.colon);
                const sort = try self.expect(.identifier);
                const steps = try self.parseBlock();
                return .{ .label = label, .body = .{ .fix = .{ .name = name, .sort = sort, .steps = steps } } };
            },
            .keyword_unpack => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                _ = try self.expect(.colon);
                const sort = try self.expect(.identifier);
                _ = try self.expect(.keyword_from);
                const from = try self.expectLabelRef();
                const steps = try self.parseBlock();
                return .{ .label = label, .body = .{ .unpack = .{ .name = name, .sort = sort, .from = from, .steps = steps } } };
            },
            else => {
                const formula = try self.parseExpr();
                // a `case` step states its goal, then eliminates a disjunction:
                //   label| GOAL
                //     case disj { arm* }
                if (self.tok.tag == .keyword_case) {
                    _ = self.advance();
                    const disj = try self.expectLabelRef();
                    const arms = try self.parseCaseArms();
                    return .{ .label = label, .body = .{ .case = .{ .goal = formula, .disj = disj, .arms = arms } } };
                }
                // the justification is a bracketed unit on its own line:
                //   label| formula
                //     [by rule refs...]
                _ = try self.expect(.l_bracket);
                // the justification keyword: `by` = kernel primitives (pure inference),
                // `using` = accelerants + `instantiation`/`model` (engine proof-generation).
                const kw: ast.Step.Claim.Kind = switch (self.tok.tag) {
                    .keyword_by => .by,
                    .keyword_using => .using,
                    else => return self.fail("expected 'by' or 'using', got '{s}'", .{self.describe()}),
                };
                _ = self.advance();
                // rule position admits `model` (the `using model(M)` citation rule) even
                // though it is a declaration keyword. `import` needs no such case — it is a
                // rule word ONLY (the declaration keyword is `theory`), so it arrives as a
                // plain identifier. `axiom`/`theorem` are NO LONGER rule words — fact
                // citations use `cite` (kind-agnostic); the keyword tokens here surface the
                // actionable diagnostic below.
                const rule = switch (self.tok.tag) {
                    .identifier, .keyword_model => self.advance(),
                    .keyword_axiom, .keyword_theorem => return self.fail("'{s}' is no longer a citation rule; cite a fact with `by cite <name>`", .{self.describe()}),
                    else => return self.fail("expected a rule name, got '{s}'", .{self.describe()}),
                };
                try self.checkKeyword(kw, rule);
                // `instantiation NAME(args)` cites a schema by name (always a plain
                // identifier). `specialize HEAD(args)` cites a forall-quantified
                // THEOREM/AXIOM by name OR a local `forall`-shaped STEP by its label
                // — so its head parses like a reference (plain OR kebab identifier).
                var schema: ?Token = null;
                if (std.mem.eql(u8, self.text(rule), "instantiation")) {
                    schema = try self.expect(.identifier);
                } else if (std.mem.eql(u8, self.text(rule), "specialize")) {
                    schema = try self.expectLabelRef();
                }
                // Theory-parameterized tactics take `(theory)`: the named
                // module whose scope their vocabulary + lemmas resolve against
                // (regardless of local aliases), reusing the `schema` token
                // slot. Bare (no parens) resolves against local scope.
                // `definition(N)` selects a definition block's CLAUSE — a numeral, not a
                // name, so it reuses the `schema` slot with a `.number` token. Bare
                // `definition p` means clause 0 (a predicate has exactly one).
                if (std.mem.eql(u8, self.text(rule), "definition") and self.tok.tag == .l_paren) {
                    _ = self.advance();
                    schema = try self.expect(.number);
                    _ = try self.expect(.r_paren);
                }
                if (isTheoryRule(self.text(rule)) and self.tok.tag == .l_paren) {
                    _ = self.advance();
                    schema = try self.expect(.identifier);
                    // `using import(I) thm` / `using arithmetic(I) …` NAME a namespace without
                    // writing an `I.` qualifier, so `stamp`'s dotted split never sees it. This
                    // is the corpus's main cross-file citation idiom (86 sites) — mark it used
                    // here or every file whose only use of an import is a citation fails.
                    _ = self.unused_imports.swapRemove(schema.?.name);
                    _ = try self.expect(.r_paren);
                }
                var args: []const *const ast.Expr = &.{};
                if (self.tok.tag == .l_paren) {
                    _ = self.advance();
                    var list: std.ArrayList(*const ast.Expr) = .empty;
                    while (true) {
                        try list.append(self.arena, try self.parseExpr());
                        if (self.tok.tag != .comma) break;
                        _ = self.advance();
                    }
                    _ = try self.expect(.r_paren);
                    args = try list.toOwnedSlice(self.arena);
                }
                // `fallback(<thm>)`: a contextual modifier (NOT a keyword — the
                // identifier `fallback` is otherwise ordinary), recognized only
                // here by text + `(`. Names a manual theorem to cite when the
                // arithmetic certifier chain declines, before the refs loop
                // would otherwise swallow the `fallback` identifier.
                var fallback: ?Token = null;
                if (std.mem.eql(u8, self.text(rule), "arithmetic") and
                    self.tok.tag == .identifier and std.mem.eql(u8, self.text(self.tok), "fallback"))
                {
                    _ = self.advance(); // `fallback`
                    _ = try self.expect(.l_paren);
                    fallback = try self.expect(.identifier);
                    _ = try self.expect(.r_paren);
                }
                // `[using model(M) definition(N) src.f]` — the transferred fact is a DEFINITION
                // BLOCK's clause, not a named theorem. The rule's own `(M)` already claimed the
                // `schema` slot, so the arm rides its own field. Recognized by TEXT before the
                // refs loop, which would otherwise swallow `definition` as the cited name.
                var definition_arm: ?usize = null;
                if (isTheoryRule(self.text(rule)) and self.tok.tag == .identifier and
                    std.mem.eql(u8, self.text(self.tok), "definition"))
                {
                    _ = self.advance();
                    var arm: usize = 0;
                    if (self.tok.tag == .l_paren) {
                        _ = self.advance();
                        const n = try self.expect(.number);
                        arm = std.fmt.parseInt(usize, self.text(n), 10) catch
                            return self.fail("`definition(N)` takes a clause NUMBER (zero-indexed)", .{});
                        _ = try self.expect(.r_paren);
                    }
                    definition_arm = arm;
                }
                // refs cite proof labels, which may be kebab-case
                var refs: std.ArrayList(Token) = .empty;
                while (self.tok.tag == .identifier or self.tok.tag == .kebab_identifier) {
                    try refs.append(self.arena, self.advance());
                    // `model(M) src.schema(pred)` / `import(I) sch(pred)`: a model- or
                    // import-cited SCHEMA takes its instantiation arguments right after the
                    // cited name. The rule's own `(M)` already went to `schema`, so these land
                    // in `args` — the same slot `instantiation NAME(args)` uses, so the engine
                    // sees one shape either way.
                    if (self.tok.tag == .l_paren and args.len == 0 and isTheoryRule(self.text(rule))) {
                        _ = self.advance();
                        var list: std.ArrayList(*const ast.Expr) = .empty;
                        while (true) {
                            try list.append(self.arena, try self.parseExpr());
                            if (self.tok.tag != .comma) break;
                            _ = self.advance();
                        }
                        _ = try self.expect(.r_paren);
                        args = try list.toOwnedSlice(self.arena);
                    }
                }
                _ = try self.expect(.r_bracket);
                return .{ .label = label, .body = .{ .claim = .{
                    .formula = formula,
                    .kind = kw,
                    .rule = rule,
                    .schema = schema,
                    .args = args,
                    .refs = try refs.toOwnedSlice(self.arena),
                    .fallback = fallback,
                    .definition_arm = definition_arm,
                } } };
            },
        }
    }

    fn parseBlock(self: *Parser) ParseError![]const ast.Step {
        _ = try self.expect(.l_brace);
        const steps = try self.parseSteps(.r_brace);
        _ = try self.expect(.r_brace);
        return steps;
    }

    /// `{ arm* }` where each arm is `label| assume <disjunct> { steps }` — the
    /// body of a `case`. Each arm is structurally an assume-block, labelled.
    fn parseCaseArms(self: *Parser) ParseError![]const ast.Step.CaseBlock.Arm {
        _ = try self.expect(.l_brace);
        var arms: std.ArrayList(ast.Step.CaseBlock.Arm) = .empty;
        while (self.tok.tag != .r_brace) {
            const label = try self.expectLabelDef();
            _ = try self.expect(.pipe);
            _ = try self.expect(.keyword_assume);
            const assumption = try self.parseExpr();
            const steps = try self.parseBlock();
            try arms.append(self.arena, .{ .label = label, .assumption = assumption, .steps = steps });
        }
        _ = try self.expect(.r_brace);
        return arms.toOwnedSlice(self.arena);
    }

    // --- expressions ---

    fn newExpr(self: *Parser, e: ast.Expr) ParseError!*const ast.Expr {
        const p = try self.arena.create(ast.Expr);
        p.* = e;
        return p;
    }

    /// Parse one expression. The grammar is the recursive-descent chain
    /// `expr(quant/lambda) → iff → implies → or → and → cmp → unary → primary`, with
    /// sub-expression recursion at four sites (quant/lambda body, `->`'s right side,
    /// call args, paren groups). Was native recursion over input nesting depth; now a
    /// CONTINUATION MACHINE — the same grammar functions CPS-converted onto explicit
    /// frames, preserving the exact token-consumption + `requireExplicit` order (note
    /// iff/or/and check the lhs BEFORE consuming their operator; implies checks AFTER).
    ///
    /// `iff` is the lowest-precedence boolean operator (below `->`); SURFACE sugar,
    /// desugared by elaboration to `(P -> Q) and (Q -> P)`. Like the other boolean
    /// ops, a *different* boolean operator as an operand must be parenthesized (so
    /// `A -> B iff C` errors, `(A -> B) iff C` is fine). `->` is right-associative
    /// (its rhs re-enters the full expr level, so quantifiers are legal there);
    /// or/and/iff chains are left-associative.
    ///
    /// Each iteration of the outer loop DESCENDS from `level`: pushes the `*_after_lhs`
    /// continuations for every precedence level the entry passes through (outermost
    /// first, so they pop innermost-first — the recursive return path), then runs the
    /// unary+primary entry inline. A primary that needs a sub-expression (call arg,
    /// paren) pushes its continuation and re-descends; an atom produces a value and
    /// falls into the APPLY loop, which pops continuations until one needs another
    /// descend or the stack drains (the parse result).
    pub fn parseExpr(self: *Parser) ParseError!*const ast.Expr {
        const Level = enum(u3) { expr = 0, implies = 1, or_lvl = 2, and_lvl = 3, cmp = 4, unary = 5 };
        const Frame = union(enum) {
            quant_done: struct { tok: Token, binders: []const ast.Binder },
            lambda_done: struct { tok: Token, binders: []const ast.Binder },
            iff_after_lhs,
            iff_after_rhs: struct { lhs: *const ast.Expr, tok: Token },
            implies_after_lhs,
            implies_after_rhs: struct { lhs: *const ast.Expr, tok: Token },
            or_after_lhs,
            or_after_rhs: struct { lhs: *const ast.Expr, tok: Token },
            and_after_lhs,
            and_after_rhs: struct { lhs: *const ast.Expr, tok: Token },
            cmp_after_lhs,
            cmp_after_rhs: struct { lhs: *const ast.Expr, op: ast.Expr.BinOp, tok: Token },
            unary_wrap: struct { nots: []const Token },
            call_arg: struct { callee: Token, args: std.ArrayList(*const ast.Expr) },
            paren_done,
        };
        var conts: std.ArrayList(Frame) = .empty;
        defer conts.deinit(self.arena);

        var level: Level = .expr;
        var value: *const ast.Expr = undefined;
        descend: while (true) {
            // -- DESCEND: entry code from `level` down to a primary --
            if (level == .expr) {
                switch (self.tok.tag) {
                    .keyword_forall, .keyword_exists => {
                        const tok = self.advance();
                        const binders = try self.parseBinders();
                        _ = try self.expect(.semicolon);
                        try conts.append(self.arena, .{ .quant_done = .{ .tok = tok, .binders = binders } });
                        continue :descend; // body: a full expr
                    },
                    .keyword_fun => {
                        const tok = self.advance();
                        const binders = try self.parseLambdaBinders();
                        _ = try self.expect(.fat_arrow);
                        try conts.append(self.arena, .{ .lambda_done = .{ .tok = tok, .binders = binders } });
                        continue :descend; // body: a full expr
                    },
                    else => {},
                }
            }
            if (@intFromEnum(level) <= 0) try conts.append(self.arena, .iff_after_lhs);
            if (@intFromEnum(level) <= 1) try conts.append(self.arena, .implies_after_lhs);
            if (@intFromEnum(level) <= 2) try conts.append(self.arena, .or_after_lhs);
            if (@intFromEnum(level) <= 3) try conts.append(self.arena, .and_after_lhs);
            if (@intFromEnum(level) <= 4) try conts.append(self.arena, .cmp_after_lhs);
            // unary: collect the `not` chain (wrapped inner-to-outer once the operand is built).
            var nots: std.ArrayList(Token) = .empty;
            while (self.tok.tag == .keyword_not) try nots.append(self.arena, self.advance());
            if (nots.items.len > 0) try conts.append(self.arena, .{ .unary_wrap = .{ .nots = nots.items } });
            // primary
            switch (self.tok.tag) {
                .identifier => {
                    const name = self.advance();
                    if (self.tok.tag != .l_paren) {
                        value = try self.newExpr(.{ .name = name });
                        // an atom: fall into APPLY below.
                    } else {
                        _ = self.advance();
                        // `p()` — a NULLARY application. A predicate always writes its
                        // parens (see `parseParams`), so a zero-argument proposition is
                        // `p()`, and the arg list is legitimately empty.
                        if (self.tok.tag == .r_paren) {
                            _ = self.advance();
                            value = try self.newExpr(.{ .call = .{ .callee = name, .args = &.{} } });
                        } else {
                            try conts.append(self.arena, .{ .call_arg = .{ .callee = name, .args = .empty } });
                            level = .expr;
                            continue :descend; // first argument
                        }
                    }
                },
                .l_paren => {
                    _ = self.advance();
                    try conts.append(self.arena, .paren_done);
                    level = .expr;
                    continue :descend; // the group
                },
                else => return self.fail("expected an expression, got '{s}'", .{self.describe()}),
            }

            // -- APPLY: feed `value` through continuations until one needs a sub-parse --
            while (conts.pop()) |fr| switch (fr) {
                .quant_done => |c| value = try self.newExpr(.{ .quant = .{
                    .q = if (c.tok.tag == .keyword_forall) .forall else .exists,
                    .tok = c.tok,
                    .binders = c.binders,
                    .body = value,
                } }),
                .lambda_done => |c| value = try self.newExpr(.{ .lambda = .{ .tok = c.tok, .binders = c.binders, .body = value } }),
                .iff_after_lhs => if (self.tok.tag == .keyword_iff) {
                    try self.requireExplicit(value, .iff); // lhs checked BEFORE consuming `iff`
                    const tok = self.advance();
                    try conts.append(self.arena, .{ .iff_after_rhs = .{ .lhs = value, .tok = tok } });
                    level = .implies;
                    continue :descend;
                },
                .iff_after_rhs => |c| {
                    try self.requireExplicit(value, .iff);
                    value = try self.newExpr(.{ .binary = .{ .op = .iff, .tok = c.tok, .lhs = c.lhs, .rhs = value } });
                    if (self.tok.tag == .keyword_iff) { // left-assoc chain continues
                        const tok = self.advance();
                        try conts.append(self.arena, .{ .iff_after_rhs = .{ .lhs = value, .tok = tok } });
                        level = .implies;
                        continue :descend;
                    }
                },
                .implies_after_lhs => if (self.tok.tag == .arrow) {
                    const tok = self.advance(); // consumed BEFORE the lhs check (original order)
                    try self.requireExplicit(value, .implies);
                    try conts.append(self.arena, .{ .implies_after_rhs = .{ .lhs = value, .tok = tok } });
                    // right-assoc; RHS may be a quantifier: `A -> forall x: Nat; prop(x)`.
                    level = .expr;
                    continue :descend;
                },
                .implies_after_rhs => |c| {
                    try self.requireExplicit(value, .implies);
                    value = try self.newExpr(.{ .binary = .{ .op = .implies, .tok = c.tok, .lhs = c.lhs, .rhs = value } });
                },
                .or_after_lhs => if (self.tok.tag == .keyword_or) {
                    try self.requireExplicit(value, .or_op);
                    const tok = self.advance();
                    try conts.append(self.arena, .{ .or_after_rhs = .{ .lhs = value, .tok = tok } });
                    level = .and_lvl;
                    continue :descend;
                },
                .or_after_rhs => |c| {
                    try self.requireExplicit(value, .or_op);
                    value = try self.newExpr(.{ .binary = .{ .op = .or_op, .tok = c.tok, .lhs = c.lhs, .rhs = value } });
                    if (self.tok.tag == .keyword_or) {
                        const tok = self.advance();
                        try conts.append(self.arena, .{ .or_after_rhs = .{ .lhs = value, .tok = tok } });
                        level = .and_lvl;
                        continue :descend;
                    }
                },
                .and_after_lhs => if (self.tok.tag == .keyword_and) {
                    try self.requireExplicit(value, .and_op);
                    const tok = self.advance();
                    try conts.append(self.arena, .{ .and_after_rhs = .{ .lhs = value, .tok = tok } });
                    level = .cmp;
                    continue :descend;
                },
                .and_after_rhs => |c| {
                    try self.requireExplicit(value, .and_op);
                    value = try self.newExpr(.{ .binary = .{ .op = .and_op, .tok = c.tok, .lhs = c.lhs, .rhs = value } });
                    if (self.tok.tag == .keyword_and) {
                        const tok = self.advance();
                        try conts.append(self.arena, .{ .and_after_rhs = .{ .lhs = value, .tok = tok } });
                        level = .cmp;
                        continue :descend;
                    }
                },
                .cmp_after_lhs => {
                    const op: ast.Expr.BinOp = switch (self.tok.tag) {
                        .equal => .equal,
                        .bang_equal => .not_equal,
                        else => continue,
                    };
                    const tok = self.advance();
                    try conts.append(self.arena, .{ .cmp_after_rhs = .{ .lhs = value, .op = op, .tok = tok } });
                    level = .unary;
                    continue :descend;
                },
                .cmp_after_rhs => |c| value = try self.newExpr(.{ .binary = .{ .op = c.op, .tok = c.tok, .lhs = c.lhs, .rhs = value } }),
                .unary_wrap => |c| {
                    var i: usize = c.nots.len;
                    while (i > 0) {
                        i -= 1;
                        value = try self.newExpr(.{ .not = .{ .tok = c.nots[i], .operand = value } });
                    }
                },
                .call_arg => |c| {
                    var args = c.args;
                    try args.append(self.arena, value);
                    if (self.tok.tag == .comma) {
                        _ = self.advance();
                        try conts.append(self.arena, .{ .call_arg = .{ .callee = c.callee, .args = args } });
                        level = .expr;
                        continue :descend; // next argument
                    }
                    _ = try self.expect(.r_paren);
                    value = try self.newExpr(.{ .call = .{ .callee = c.callee, .args = try args.toOwnedSlice(self.arena) } });
                },
                .paren_done => {
                    _ = try self.expect(.r_paren);
                    value = try self.markParen(value);
                },
            };
            return value; // continuations drained: the full expression
        }
    }

    /// `x, y: Nat`
    /// Lambda binders: COMMA-separated groups, each carrying its own sort —
    /// `fun i: Nat, v: Q => …`. A quantifier cannot share this parse because its
    /// binder list is terminated by `;`, which it uses to chain mixed sorts
    /// (`forall s: QSeq; forall k: Nat; …`); a lambda has one `=>` and no such
    /// escape, so before this a spec over two different sorts had NO lambda form
    /// at all (`schema(Nat, Q)` could only be instantiated at a bare predicate
    /// name). Same-sort grouping still works: `fun y, z: Element => …`, which is
    /// how every pre-existing caller writes it.
    fn parseLambdaBinders(self: *Parser) ParseError![]const ast.Binder {
        var all: std.ArrayList(ast.Binder) = .empty;
        while (true) {
            // one group: `a, b, c: Sort [where inH]`
            var names: std.ArrayList(Token) = .empty;
            try names.append(self.arena, try self.expect(.identifier));
            while (self.tok.tag == .comma) {
                // a comma continues THIS group only while a colon has not been
                // seen yet; once the group's sort is read, a comma starts a new
                // group instead (handled after the sort below).
                _ = self.advance();
                try names.append(self.arena, try self.expect(.identifier));
            }
            _ = try self.expect(.colon);
            const sort = try self.expect(.identifier);
            var guard: ?Token = null;
            if (self.tok.tag == .keyword_where) {
                _ = self.advance();
                guard = try self.expect(.identifier);
            }
            for (names.items) |name| {
                try all.append(self.arena, .{ .name = name, .sort = sort, .guard = guard });
            }
            if (self.tok.tag != .comma) break;
            _ = self.advance(); // next group
        }
        return all.items;
    }

    fn parseBinders(self: *Parser) ParseError![]const ast.Binder {
        var names: std.ArrayList(Token) = .empty;
        try names.append(self.arena, try self.expect(.identifier));
        while (self.tok.tag == .comma) {
            _ = self.advance();
            try names.append(self.arena, try self.expect(.identifier));
        }
        _ = try self.expect(.colon);
        const sort = try self.expect(.identifier);
        // inline refinement `x: S where inH` — an anonymous refined sort (bare
        // predicate name, applied to the binder variable).
        var guard: ?Token = null;
        if (self.tok.tag == .keyword_where) {
            _ = self.advance();
            guard = try self.expect(.identifier);
        }
        const binders = try self.arena.alloc(ast.Binder, names.items.len);
        for (names.items, binders) |name, *b| b.* = .{ .name = name, .sort = sort, .guard = guard };
        return binders;
    }

    /// Return a copy of `e` marked as parenthesized (for Binary/Not; other
    /// node kinds are returned unchanged since the paren rule never inspects
    /// them).
    fn markParen(self: *Parser, e: *const ast.Expr) ParseError!*const ast.Expr {
        return switch (e.*) {
            .binary => |b| self.newExpr(.{ .binary = .{ .op = b.op, .tok = b.tok, .lhs = b.lhs, .rhs = b.rhs, .paren = true } }),
            .not => |n| self.newExpr(.{ .not = .{ .tok = n.tok, .operand = n.operand, .paren = true } }),
            else => e,
        };
    }

    /// The mixed-boolean-operator paren rule: an operand of a boolean operator
    /// may not itself be a *different* boolean operator (and/or/->/not) unless
    /// parenthesized. Same-operator chains (`A or B or C`, `A -> B -> C`,
    /// `not not A`) stay legal; cross-operator nesting must be explicit.
    /// `=`/`!=` and atoms are not boolean operators and are always fine.
    fn requireExplicit(self: *Parser, operand: *const ast.Expr, outer: ast.Expr.BinOp) ParseError!void {
        const inner: ast.Expr.BinOp = switch (operand.*) {
            .binary => |b| switch (b.op) {
                .implies, .and_op, .or_op, .iff => if (b.paren) return else b.op,
                .equal, .not_equal => return, // comparisons aren't boolean ops
            },
            .not => |n| if (n.paren) return else {
                self.sink.add(self.file, n.tok.start, "parenthesize this 'not' where it meets '{s}': mixed boolean operators require explicit parentheses", .{@tagName(outer)}) catch return error.OutOfMemory;
                return error.Recover;
            },
            else => return,
        };
        if (inner == outer) return; // same-operator chain is fine
        const b = operand.binary;
        self.sink.add(self.file, b.tok.start, "parenthesize: '{s}' and '{s}' are different boolean operators and their nesting must be explicit", .{ @tagName(inner), @tagName(outer) }) catch return error.OutOfMemory;
        return error.Recover;
    }
};

// --- tests ---

const testing = std.testing;

fn expectExprDump(source: []const u8, expected: []const u8) !void {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const e = p.parseExpr() catch |err| {
        std.debug.print("parse failed: {t}; diagnostics:\n", .{err});
        for (sink.list.items) |d| std.debug.print("  @{d}: {s}\n", .{ d.offset, d.message });
        return err;
    };
    try testing.expectEqual(0, sink.list.items.len);

    var out: std.Io.Writer.Allocating = .init(arena);
    try ast.dumpExpr(arena, &out.writer, source, e);
    try testing.expectEqualStrings(expected, out.written());
}

fn expectParseError(source: []const u8) !void {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    _ = p.parseExpr() catch {
        try testing.expect(sink.list.items.len > 0);
        return;
    };
    std.debug.print("expected a parse error for: {s}\n", .{source});
    return error.ExpectedParseError;
}

test "precedence: same-operator chains parse; -> right-assoc; cmp is not a bool op" {
    // same-operator chains stay legal and unparenthesized
    try expectExprDump("a -> b -> c", "(implies a (implies b c))");
    try expectExprDump("a or b or c", "(or_op (or_op a b) c)");
    try expectExprDump("a and b and c", "(and_op (and_op a b) c)");
    try expectExprDump("not not a", "(not (not a))");
    // = / != are not boolean operators, so they mix with bool ops freely
    try expectExprDump("x = y and p", "(and_op (equal x y) p)");
    try expectExprDump("x != ZERO", "(not_equal x ZERO)");
    // `not` binds tighter than `=`, so this is (not x) = y, not not(x = y)
    try expectExprDump("not x = y", "(equal (not x) y)");
    // explicit parens resolve any mix
    try expectExprDump("(a -> b) -> c", "(implies (implies a b) c)");
    try expectExprDump("(a and b) or c", "(or_op (and_op a b) c)");
    try expectExprDump("(not a) and b", "(and_op (not a) b)");
    try expectExprDump("a -> (b and c)", "(implies a (and_op b c))");
}

test "conditionsCoverPropositionally recognizes the covering shapes, and only those" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    // Parse a file's definition-block guards by hand would be circular; build the conditions
    // directly as the parser does, over tokens whose `name` StrIds stand for `n`/`ZERO`/`p`.
    const n_tok: Token = .{ .tag = .identifier, .start = 0, .end = 1, .name = @enumFromInt(1), .qualifier = .none };
    const z_tok: Token = .{ .tag = .identifier, .start = 0, .end = 1, .name = @enumFromInt(2), .qualifier = .none };
    const one_tok: Token = .{ .tag = .identifier, .start = 0, .end = 1, .name = @enumFromInt(3), .qualifier = .none };
    const lt_tok: Token = .{ .tag = .identifier, .start = 0, .end = 1, .name = @enumFromInt(4), .qualifier = .none };

    const n = try arena.create(ast.Expr);
    n.* = .{ .name = n_tok };
    const z = try arena.create(ast.Expr);
    z.* = .{ .name = z_tok };
    const one = try arena.create(ast.Expr);
    one.* = .{ .name = one_tok };

    const n_eq_z = try arena.create(ast.Expr);
    n_eq_z.* = .{ .binary = .{ .op = .equal, .tok = n_tok, .lhs = n, .rhs = z } };
    const n_ne_z = try arena.create(ast.Expr);
    n_ne_z.* = .{ .binary = .{ .op = .not_equal, .tok = n_tok, .lhs = n, .rhs = z } };

    // 1. two-way complementarity — the dominant corpus shape
    try testing.expect(conditionsCoverPropositionally(arena, &.{ n_eq_z, n_ne_z }));

    // 2. a PREDICATE split: p(n) against not p(n)
    const p_args = try arena.alloc(*const ast.Expr, 1);
    p_args[0] = n;
    const p_of_n = try arena.create(ast.Expr);
    p_of_n.* = .{ .call = .{ .callee = lt_tok, .args = p_args } };
    const not_p = try arena.create(ast.Expr);
    not_p.* = .{ .not = .{ .tok = n_tok, .operand = p_of_n } };
    try testing.expect(conditionsCoverPropositionally(arena, &.{ p_of_n, not_p }));

    // 3. `swap`'s THREE-WAY split: x = A, x = B, (x != A and x != B)
    const n_eq_one = try arena.create(ast.Expr);
    n_eq_one.* = .{ .binary = .{ .op = .equal, .tok = n_tok, .lhs = n, .rhs = one } };
    const n_ne_one = try arena.create(ast.Expr);
    n_ne_one.* = .{ .binary = .{ .op = .not_equal, .tok = n_tok, .lhs = n, .rhs = one } };
    const neither = try arena.create(ast.Expr);
    neither.* = .{ .binary = .{ .op = .and_op, .tok = n_tok, .lhs = n_ne_z, .rhs = n_ne_one } };
    try testing.expect(conditionsCoverPropositionally(arena, &.{ n_eq_z, n_eq_one, neither }));

    // 4. THE GAP IT MUST REFUSE: `n = ZERO` beside `less_than(ONE, n)` says nothing at ONE.
    // Deciding that pair needs arithmetic, and a detector that reasons can be wrong.
    const lt_args = try arena.alloc(*const ast.Expr, 2);
    lt_args[0] = one;
    lt_args[1] = n;
    const one_lt_n = try arena.create(ast.Expr);
    one_lt_n.* = .{ .call = .{ .callee = lt_tok, .args = lt_args } };
    try testing.expect(!conditionsCoverPropositionally(arena, &.{ n_eq_z, one_lt_n }));

    // and a single unconditional arm covers nothing on its own evidence
    try testing.expect(!conditionsCoverPropositionally(arena, &.{n_eq_z}));
}

test "mixed boolean operators require explicit parentheses" {
    try expectParseError("a and b or c");
    try expectParseError("a or b and c");
    try expectParseError("not a and b");
    try expectParseError("a -> b and c");
    try expectParseError("a -> b or c");
    try expectParseError("a and b -> c");
    try expectParseError("a or b -> c");
    try expectParseError("not a or b");
}

test "quantifiers bind the rest; multiple binders share a sort" {
    try expectExprDump(
        "forall x, y: Nat; x = y -> y = x",
        "(forall x:Nat y:Nat (implies (equal x y) (equal y x)))",
    );
    try expectExprDump(
        "a -> exists w: Nat; succ(w) = a",
        "(implies a (exists w:Nat (equal (succ w) a)))",
    );
}

test "calls and lambdas" {
    try expectExprDump("add(succ(x), ZERO)", "(add (succ x) ZERO)");
    try expectExprDump("fun k: Nat => add(k, ZERO) = k", "(fun k:Nat (equal (add k ZERO) k))");
    // LAMBDA BINDERS ARE COMMA-SEPARATED GROUPS, each with its own sort. A quantifier chains
    // mixed sorts with `;` (`forall a: Nat; forall v: Q; …`); a lambda has only `=>`, so
    // without per-group sorts a spec over two different sorts had NO lambda form.
    try expectExprDump("fun y, z: Nat => p(y, z)", "(fun y:Nat z:Nat (p y z))");
    try expectExprDump("fun i: Nat, v: Q => p(i, v)", "(fun i:Nat v:Q (p i v))");
    try expectExprDump("fun a, b: Nat, v: Q => p(a, b, v)", "(fun a:Nat b:Nat v:Q (p a b v))");
}

test "declarations parse" {
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\oper div(a: Nat, b: Nat) => Nat requires b != ZERO
        \\pred even(n: Nat)
        \\axiom reflAx: forall x: Nat; x = x
        \\axiom induction(prop(Nat)):
        \\  prop(ZERO) -> (forall k: Nat; prop(k) -> prop(succ(k))) -> forall n: Nat; prop(n)
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);
    try testing.expectEqual(6, file.decls.len);

    const div = file.decls[2].func.local;
    try testing.expectEqualStrings("div", source[div.name.start..div.name.end]);
    try testing.expectEqual(2, div.params.len);
    try testing.expect(div.requires != null);

    const ind = file.decls[5].axiom.local;
    try testing.expectEqual(1, ind.params.?.len);
    // a PRED param: one argument sort, and no result token (its result is Prop, implicitly).
    try testing.expect(ind.params.?[0].kind == .pred);
    try testing.expectEqual(1, ind.params.?[0].argSorts().len);
    try testing.expectEqual(@as(?lexer.Token, null), ind.params.?[0].resultSort());
}

test "theorem with nested proof blocks and instantiate" {
    const source =
        \\theorem impExample: p() -> (q() -> p())
        \\proof
        \\  @outer | assume p() {
        \\    @inner | assume q() {
        \\      @got_p | p() [by hypothesis outer]
        \\    }
        \\    @qtop | q() -> p() [by discharge inner]
        \\  }
        \\  @done | p() -> (q() -> p()) [by discharge outer]
        \\qed
        \\theorem addZeroRight: forall n: Nat; add(n, ZERO) = n
        \\proof
        \\  @conc | forall n: Nat; add(n, ZERO) = n
        \\    [using instantiation induction((fun k: Nat => add(k, ZERO) = k)) base stepcase]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);
    try testing.expectEqual(2, file.decls.len);

    const thm = file.decls[0].theorem;
    try testing.expectEqual(2, thm.local.steps.len);
    const outer = thm.local.steps[0].body.assume;
    try testing.expectEqual(2, outer.steps.len);
    const inner = outer.steps[0].body.assume;
    try testing.expectEqual(1, inner.steps.len);
    const done = thm.local.steps[1].body.claim;
    try testing.expectEqualStrings("discharge", source[done.rule.start..done.rule.end]);
    try testing.expectEqual(1, done.refs.len);

    const inst = file.decls[1].theorem.local.steps[0].body.claim;
    try testing.expectEqualStrings("instantiation", source[inst.rule.start..inst.rule.end]);
    try testing.expectEqualStrings("induction", source[inst.schema.?.start..inst.schema.?.end]);
    try testing.expectEqual(1, inst.args.len);
    try testing.expect(inst.args[0].* == .lambda);
    try testing.expectEqual(2, inst.refs.len);
}

test "arithmetic fallback(<thm>) parses; fallback stays an ordinary identifier elsewhere" {
    const source =
        \\theorem t: forall a: Nat; p(a)
        \\proof
        \\  @c | forall a: Nat; p(a) [using arithmetic fallback(manualProof)]
        \\qed
        \\theorem u: q
        \\proof
        \\  @fallback | q [by hypothesis fallback]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);

    // the arithmetic claim carries fallback = `manualProof`, no refs
    const arith = file.decls[0].theorem.local.steps[0].body.claim;
    try testing.expectEqualStrings("arithmetic", source[arith.rule.start..arith.rule.end]);
    try testing.expect(arith.fallback != null);
    try testing.expectEqualStrings("manualProof", source[arith.fallback.?.start..arith.fallback.?.end]);
    try testing.expectEqual(0, arith.refs.len);

    // outside an arithmetic claim, `fallback` is a normal name: here a step
    // label cited as a hypothesis ref, with no fallback field set.
    const hyp = file.decls[1].theorem.local.steps[0].body.claim;
    try testing.expectEqualStrings("hypothesis", source[hyp.rule.start..hyp.rule.end]);
    try testing.expect(hyp.fallback == null);
    try testing.expectEqual(1, hyp.refs.len);
    try testing.expectEqualStrings("fallback", source[hyp.refs[0].start..hyp.refs[0].end]);
}

test "hole declaration parses as ast.Decl.hole; carrying a proof is an error" {
    const arena_alloc = std.testing.allocator;
    var arena_state: std.heap.ArenaAllocator = .init(arena_alloc);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    {
        const source = "pred p()\nhole aspirational: p()\n";
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, source, &sink);
        const file = try p.parseFile();
        try testing.expectEqual(0, sink.list.items.len);
        try testing.expectEqual(2, file.decls.len);
        try testing.expect(file.decls[1] == .hole);
        const h = file.decls[1].hole;
        try testing.expectEqualStrings("aspirational", source[h.local.name.start..h.local.name.end]);
    }
    {
        // a hole with a proof body is rejected (once proved, it's a theorem)
        const source = "pred p()\nhole bad: p()\nproof\n  @c | p() [by cite pa]\nqed\n";
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, source, &sink);
        _ = p.parseFile() catch {};
        try testing.expect(sink.list.items.len > 0);
    }
}

test "@label step definitions; the label name interns without the sigil; refs stay bare" {
    const source =
        \\pred p()
        \\theorem t: p()
        \\proof
        \\  @base | p() [by cite pAx]
        \\  @conc | p() [by symmetry base]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);
    const thm = file.decls[1].theorem;
    // the label token spans just `base` (no `@`), so it matches the bare ref
    try testing.expectEqualStrings("base", source[thm.local.steps[0].label.start..thm.local.steps[0].label.end]);
    const conc = thm.local.steps[1].body.claim;
    try testing.expectEqualStrings("symmetry", source[conc.rule.start..conc.rule.end]);
    // the reference is bare `base`, no sigil
    try testing.expectEqualStrings("base", source[conc.refs[0].start..conc.refs[0].end]);
}

test "fact citations use the kind-agnostic `cite` rule word" {
    const source =
        \\pred p()
        \\axiom pAx: p()
        \\theorem t1: p()
        \\proof
        \\  @conc | p() [by cite pAx]
        \\qed
        \\theorem t2: p()
        \\proof
        \\  @conc | p() [by cite t1]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);
    // `cite` cites both an axiom and a theorem — the kernel picks the arm by resolved kind.
    const c1 = file.decls[2].theorem.local.steps[0].body.claim;
    try testing.expectEqualStrings("cite", source[c1.rule.start..c1.rule.end]);
    try testing.expectEqual(1, c1.refs.len);
    const c2 = file.decls[3].theorem.local.steps[0].body.claim;
    try testing.expectEqualStrings("cite", source[c2.rule.start..c2.rule.end]);
}

test "`axiom`/`theorem` are NO LONGER citation rule words" {
    const source =
        \\pred p()
        \\axiom pAx: p()
        \\theorem t: p()
        \\proof
        \\  @c | p() [by axiom pAx]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    _ = try p.parseFile();
    try testing.expect(sink.list.items.len > 0);
    try testing.expect(std.mem.indexOf(u8, sink.list.items[0].message, "no longer a citation rule") != null);
}

test "consecutive claim steps: a following label is not swallowed as a ref" {
    const source =
        \\pred p()
        \\theorem t: p()
        \\proof
        \\  @a | p() [by cite x]
        \\  @b | p() [by modus_ponens a a]
        \\  @c | p() [by hypothesis b]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);
    const steps = file.decls[1].theorem.local.steps;
    try testing.expectEqual(3, steps.len);
    try testing.expectEqual(1, steps[0].body.claim.refs.len);
    try testing.expectEqual(2, steps[1].body.claim.refs.len);
    try testing.expectEqual(1, steps[2].body.claim.refs.len);
}

test "by/using keyword: records the kind + enforces the vocabulary partition" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    // a kernel rule under `by` and an accelerant under `using` both parse clean, and the
    // Claim records which keyword introduced the step.
    {
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena,
            \\pred p()
            \\theorem t: p()
            \\proof
            \\  @a | p() [by cite x]
            \\  @b | p() [using specialize head]
            \\qed
        , &sink);
        const file = try p.parseFile();
        try testing.expectEqual(0, sink.list.items.len);
        const steps = file.decls[1].theorem.local.steps;
        try testing.expectEqual(ast.Step.Claim.Kind.by, steps[0].body.claim.kind);
        try testing.expectEqual(ast.Step.Claim.Kind.using, steps[1].body.claim.kind);
    }
    // `using` on a KERNEL rule is rejected at parse.
    {
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, "pred p()\ntheorem t: p()\nproof\n  @a | p() [using axiom x]\nqed", &sink);
        _ = try p.parseFile();
        try testing.expect(sink.list.items.len >= 1);
    }
    // `by` on an ACCELERANT (here `model`, and a bare accelerant word) is rejected at parse.
    {
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, "pred p()\ntheorem t: p()\nproof\n  @a | p() [by tautology]\nqed", &sink);
        _ = try p.parseFile();
        try testing.expect(sink.list.items.len >= 1);
    }
}

test "ZERO-ary predicates write their parens; the bare form is rejected" {
    const source =
        \\pred q()
        \\pred r()
        \\axiom both: q() -> r()
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);
    try testing.expectEqual(3, file.decls.len);
    try testing.expectEqual(0, file.decls[0].pred.local.params.len);
    try testing.expectEqual(0, file.decls[1].pred.local.params.len);

    // a predicate ALWAYS writes its parameter list, so bare `pred p` is an error —
    // one spelling serves the declaration, a use, a schema parameter, and an argument.
    var bare_sink: Diagnostics.Sink = .init(arena);
    var bare: Parser = .init(arena, "pred p", &bare_sink);
    _ = bare.parseFile() catch {};
    try testing.expectEqual(1, bare_sink.list.items.len);
}

test "error recovery: two bad declarations yield two diagnostics" {
    const source =
        \\sort Nat
        \\axiom bad forall x: Nat; x = x
        \\const ZERO: Nat
        \\axiom worse: x =
        \\sort other
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    const file = try p.parseFile();
    try testing.expectEqual(2, sink.list.items.len);
    try testing.expectEqualStrings("expected ':', got 'forall'", sink.list.items[0].message);
    // recovery still parsed the good declarations
    try testing.expectEqual(3, file.decls.len);
}

test "deep nesting: the expression machine is not bounded by the C stack" {
    // ~100k-deep inputs of each recursion-driving shape (paren groups, right-assoc
    // implies chain, not chain). The recursive-descent parser this replaced overflowed
    // the C stack around ~10k frames on these; the continuation machine must not.
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const depth = 100_000;
    inline for (.{
        .{ "(", "p", ")" }, // ((((p))))
        .{ "p -> ", "p", "" }, // p -> p -> … -> p
        .{ "(not ", "p", ")" }, // (not (not … p))
    }) |shape| {
        var src: std.ArrayList(u8) = .empty;
        for (0..depth) |_| try src.appendSlice(arena, shape[0]);
        try src.appendSlice(arena, shape[1]);
        for (0..depth) |_| try src.appendSlice(arena, shape[2]);

        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, src.items, &sink);
        _ = try p.parseExpr();
        try testing.expectEqual(0, sink.list.items.len);
    }
}

test "an import no qualifier mentions is an error; a model block's qualifier counts as a use" {
    // The check is SYNTACTIC: `used` means some token carries the namespace as a `ns.`
    // qualifier. That is what makes a `model` block's mappings count without the parser
    // knowing anything about models — and why the six engine sites that resolve a qualifier
    // to a target need no instrumentation.
    const source =
        \\theory used_by_sort <<< "a.b4m"
        \\theory used_by_model <<< "b.b4m"
        \\theory dead <<< "c.b4m"
        \\sort G = used_by_sort.G
        \\model M {
        \\  used_by_model.G: G
        \\}
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var ip: InternPool = try .init(arena);
    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .initInterning(arena, source, &sink, &ip);
    _ = try p.parseFile();

    try testing.expectEqual(1, sink.list.items.len);
    try testing.expect(std.mem.indexOf(u8, sink.list.items[0].message, "'dead'") != null);
    try testing.expect(std.mem.indexOf(u8, sink.list.items[0].message, "never used") != null);
    // the PATH is in the message: a misspelled path is the costly form of this bug
    try testing.expect(std.mem.indexOf(u8, sink.list.items[0].message, "c.b4m") != null);
    // reported at the DECLARATION, not at end-of-file
    try testing.expectEqual(std.mem.indexOf(u8, source, "dead").?, sink.list.items[0].offset);
}

test "a theory-rule argument marks an import used: `using import(I) thm` writes no `I.` qualifier" {
    // 86 aata sites cite across a file boundary this way, and the namespace appears with NO
    // dot — so `stamp`'s dotted split never sees it and the `isTheoryRule` arm must mark it.
    // A CLI fixture cannot isolate this (the citer needs the imported SORT too, which marks
    // the import used via its qualifier), so the unit test is the only place it is guarded.
    const source =
        \\theory cited_only <<< "a.b4m"
        \\sort T
        \\theorem t: forall a: T; a = a
        \\proof
        \\  @conclusion |
        \\    forall a: T; a = a
        \\    [using import(cited_only) someFact]
        \\qed
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var ip: InternPool = try .init(arena);
    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .initInterning(arena, source, &sink, &ip);
    _ = try p.parseFile();
    // no unused-import diagnostic: the citation is the use.
    for (sink.list.items) |d| try testing.expect(std.mem.indexOf(u8, d.message, "never used") == null);
}

test "the unused-import check sleeps without an interner (fmt/lint/query parse this way)" {
    const source =
        \\theory dead <<< "c.b4m"
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .init(arena, source, &sink);
    _ = try p.parseFile();
    // ids are `.none` under plain `init`, so every qualifier would collide on one key;
    // the check is the engine's, not a formatter's.
    try testing.expectEqual(0, sink.list.items.len);
}

test "a definition block synthesizes one consistency obligation per clause pair" {
    // The obligation is DETERMINISTIC from source text (no unification, no generated names).
    // `f(a, ZERO)` / `f(a, succ(n))` matches in slot 2, so each clause's condition is an
    // equation on the POSITIONAL binder `arg2` — never on the declared param `n`, which the
    // step clause SHADOWS (`succ(n)` would otherwise generate the nonsense `n = succ(n)`).
    const source =
        \\sort N
        \\const Z: N
        \\oper s(a: N) => N
        \\oper f(a: N, n: N) => N:
        \\  f(a, Z) = a;
        \\  f(a, s(n)) = s(f(a, n)).
        \\  consistency: _
        \\  totality(peano): fCovers
        \\  termination(peano): _, {fIsGrounded, fGrounded}
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var ip: InternPool = try .init(arena);
    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .initInterning(arena, source, &sink, &ip);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);

    // find `f`'s declaration and its consistency record
    var cons: ?ast.Consistency = null;
    for (file.decls) |d| switch (d) {
        .func => |fu| switch (fu) {
            .local => |l| if (std.mem.eql(u8, ip.stringBytes(l.name.name), "f")) {
                cons = l.consistency;
            },
            .alias => {},
        },
        else => {},
    };
    const c = cons orelse return error.TestUnexpectedResult;

    // 2 clauses -> 1 pair -> 1 entry, 1 obligation
    try testing.expectEqual(@as(usize, 2), c.arms);
    try testing.expectEqual(@as(usize, 1), c.entries.len);
    try testing.expectEqual(@as(usize, 1), c.obligations.len);
    try testing.expect(c.entries[0] == null); // `_`

    // the obligation's SHAPE: forall … ; (cond and cond) -> rhs = rhs
    var e = c.obligations[0];
    var binders: usize = 0;
    while (e.* == .quant) : (binders += 1) e = e.quant.body;
    try testing.expect(binders > 0);
    try testing.expectEqual(ast.Expr.BinOp.implies, e.binary.op);
    try testing.expectEqual(ast.Expr.BinOp.and_op, e.binary.lhs.binary.op);
    try testing.expectEqual(ast.Expr.BinOp.equal, e.binary.rhs.binary.op);

    // each condition is `arg2 = <pattern>`, on the positional binder
    const c0 = e.binary.lhs.binary.lhs;
    const c1 = e.binary.lhs.binary.rhs;
    try testing.expectEqual(ast.Expr.BinOp.equal, c0.binary.op);
    try testing.expectEqualStrings("arg2", ip.stringBytes(c0.binary.lhs.name.name));
    try testing.expectEqualStrings("Z", ip.stringBytes(c0.binary.rhs.name.name));
    try testing.expectEqualStrings("arg2", ip.stringBytes(c1.binary.lhs.name.name));
    try testing.expectEqualStrings("s", ip.stringBytes(c1.binary.rhs.call.callee.name));

    // the consequent equates the two arms' RIGHT-hand sides: `a` and `s(f(a, n))`
    try testing.expectEqualStrings("a", ip.stringBytes(e.binary.rhs.binary.lhs.name.name));
    try testing.expectEqualStrings("s", ip.stringBytes(e.binary.rhs.binary.rhs.call.callee.name));
}

test "collectRecursiveCalls finds every self-call on the RHS, in order" {
    // fib's step arm calls TWICE at different arguments, which is why the collector exists:
    // one obligation per call would need both, and `findApplication` stops at the first.
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\const ONE: Nat
        \\oper succ(n: Nat) => Nat
        \\oper add(a: Nat, b: Nat) => Nat
        \\oper sub(a: Nat, b: Nat) => Nat
        \\oper fib(n: Nat) => Nat:
        \\  fib(n) = add(fib(sub(n, ONE)), fib(sub(n, succ(ONE)))).
        \\  termination(peano): {fibIsGrounded, fibGrounded}
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var ip: InternPool = try .init(arena);
    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .initInterning(arena, source, &sink, &ip);
    const file = try p.parseFile();

    var fib_name: ?Token = null;
    var clause: ?*const ast.Expr = null;
    for (file.decls) |d| switch (d) {
        .func => |fu| switch (fu) {
            .local => |l| if (std.mem.eql(u8, ip.stringBytes(l.name.name), "fib")) {
                fib_name = l.name;
            },
            .alias => {},
        },
        // the clause is staged as an axiom; its formula is what we walk. Take the FIRST one:
        // a `termination:` declaration also stages the generated predicate's own clause, so
        // keeping the last would walk `fibGrounded`'s body instead of `fib`'s.
        .axiom => |a| switch (a) {
            .local => |l| if (clause == null) {
                clause = l.formula;
            },
            else => {},
        },
        else => {},
    };
    const nm = fib_name orelse return error.TestUnexpectedResult;
    const cl = clause orelse return error.TestUnexpectedResult;

    // the staged axiom is `forall …; fib(n) = add(fib(…), fib(…))`; walk to the RHS
    // (the clause writes the DECLARED binder `n`: a recursive block may not rename it, since a
    // rename makes the generated predicate's base branch reflexive — see the binder-agreement
    // check in `parseWellformedness`)
    var body = cl;
    while (body.* == .quant) body = body.quant.body;
    const rhs = clauseRhs(body) orelse return error.TestUnexpectedResult;

    var calls: std.ArrayList(ast.Expr.Call) = .empty;
    try collectRecursiveCalls(arena, rhs, nm, &calls);
    // TWO calls, and neither is the LHS's own `fib(k)` — the RHS only
    try testing.expectEqual(@as(usize, 2), calls.items.len);
}

test "an ARROW-guarded clause states its condition like `when` does" {
    // The `monomial` family (5 blocks in std) writes its guard as a leading antecedent
    // rather than with `when`. The parser desugars `when` to exactly that shape, so the two
    // mean the same thing and the obligation must read both — otherwise those blocks could
    // not state an obligation at all ("a definition clause must be an equation").
    //
    // `monomial` is also an IMPLICIT definition (its clause characterizes the polynomial by
    // its coefficients rather than rewriting the symbol away), so the block owes
    // `existence:`/`uniqueness:` as well. That is orthogonal to what this test checks — the
    // arrow-guard reading of the CONSISTENCY obligation — but the block will not parse
    // without them.
    const source =
        \\sort R
        \\sort Nat
        \\const zeroR: R
        \\sort Poly
        \\oper coeff(p: Poly, i: Nat) => R
        \\axiom ex: forall a: R; forall k: Nat; exists r: Poly; coeff(r, k) = a
        \\axiom un: forall p, q: Poly; (forall i: Nat; coeff(p, i) = coeff(q, i)) -> p = q
        \\oper monomial(a: R, k: Nat) => Poly:
        \\  coeff(monomial(a, k), k) = a;
        \\  (not (i = k)) -> coeff(monomial(a, k), i) = zeroR.
        \\  consistency: _
        \\  existence: ex
        \\  uniqueness: un
    ;
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var ip: InternPool = try .init(arena);
    var sink: Diagnostics.Sink = .init(arena);
    var p: Parser = .initInterning(arena, source, &sink, &ip);
    const file = try p.parseFile();
    try testing.expectEqual(0, sink.list.items.len);

    var cons: ?ast.Consistency = null;
    for (file.decls) |d| switch (d) {
        .func => |fu| switch (fu) {
            .local => |l| if (std.mem.eql(u8, ip.stringBytes(l.name.name), "monomial")) {
                cons = l.consistency;
            },
            .alias => {},
        },
        else => {},
    };
    const c = cons orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), c.obligations.len);

    var e = c.obligations[0];
    while (e.* == .quant) e = e.quant.body;
    // `not (i = k) -> a = zeroR`, and the consequent is the two arms' right-hand sides read
    // THROUGH the arrow. Exactly ONE condition: clause 1 contributes its antecedent, while
    // clause 0 contributes NONE — its slot-2 argument is `k`, the declared parameter itself,
    // so that clause applies everywhere and constrains nothing. That asymmetry is the real
    // content of this definition (one index pinned, every other index zero).
    try testing.expectEqual(ast.Expr.BinOp.implies, e.binary.op);
    try testing.expect(e.binary.lhs.* == .not);
    try testing.expectEqual(ast.Expr.BinOp.equal, e.binary.rhs.binary.op);
    try testing.expectEqualStrings("a", ip.stringBytes(e.binary.rhs.binary.lhs.name.name));
    try testing.expectEqualStrings("zeroR", ip.stringBytes(e.binary.rhs.binary.rhs.name.name));
}
