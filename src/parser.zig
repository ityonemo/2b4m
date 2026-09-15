//! Recursive-descent parser for .bpa files.
//! Error recovery: on a parse error inside a declaration, record one diagnostic
//! and skip to the next top-level declaration keyword.
//!
//! Expression grammar (one unified Expr for terms and formulas):
//!   expr    := quant | lambda | implies
//!   quant   := ('forall'|'exists') binders ';' expr
//!   lambda  := 'fun' binders '=>' expr
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
fn isTheoryRule(name: []const u8) bool {
    return std.mem.eql(u8, name, "arithmetic") or
        std.mem.eql(u8, name, "polynomial") or
        std.mem.eql(u8, name, "polynomial_quantified") or
        std.mem.eql(u8, name, "extensionality") or
        std.mem.eql(u8, name, "extensionality_quantified") or
        std.mem.eql(u8, name, "model") or
        std.mem.eql(u8, name, "import");
}

pub const Parser = struct {
    arena: Allocator,
    source: []const u8,
    lex: lexer.Lexer,
    tok: Token,
    sink: *Diagnostics.Sink,
    /// When set, every non-reserved token the parser consumes is interned and
    /// carries its `StrId` (`Token.name`/`.qualifier`) — see `initInterning`.
    interner: ?*InternPool = null,
    /// Interning failure is remembered here (stamping happens inside the
    /// infallible `advance`) and surfaced as OutOfMemory when `parseFile` returns.
    intern_oom: bool = false,

    pub fn init(arena: Allocator, source: []const u8, sink: *Diagnostics.Sink) Parser {
        var lex: lexer.Lexer = .init(source);
        const first = lex.next();
        return .{ .arena = arena, .source = source, .lex = lex, .tok = first, .sink = sink };
    }

    /// Like `init`, but every non-reserved token is interned into `interner` as
    /// it is consumed, so the AST's tokens carry their `StrId`s. This is the
    /// ENGINE's parse entry: past parsing, names are integers — engine code
    /// never re-derives (or compares) name text from source. Parse-only tools
    /// (query/lint/fmt) keep plain `init`; their tokens' ids stay `.none`.
    pub fn initInterning(arena: Allocator, source: []const u8, sink: *Diagnostics.Sink, interner: *InternPool) Parser {
        var p = init(arena, source, sink);
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
                        self.sink.add(t.start, "only one level of namespace qualification is allowed", .{}) catch {
                            self.intern_oom = true;
                            return tok;
                        };
                    }
                    tok.qualifier = ip.internString(chars[0..i]) catch {
                        self.intern_oom = true;
                        return tok;
                    };
                    tok.name = ip.internString(chars[i + 1 ..]) catch {
                        self.intern_oom = true;
                        return tok;
                    };
                } else {
                    tok.name = ip.internString(chars) catch {
                        self.intern_oom = true;
                        return tok;
                    };
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
            .keyword_import => tok.name = InternPool.RuleStr.import.id(),
            else => {},
        }
        return tok;
    }

    fn text(self: *const Parser, t: Token) []const u8 {
        return self.source[t.start..t.end];
    }

    /// Report an error at the current token and begin recovery.
    fn fail(self: *Parser, comptime fmt: []const u8, args: anytype) ParseError {
        self.sink.add(self.tok.start, fmt, args) catch return error.OutOfMemory;
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
            .keyword_sort, .keyword_const, .keyword_define, .keyword_func, .keyword_pred, .keyword_axiom, .keyword_hole, .keyword_theorem, .keyword_import, .keyword_forward, .keyword_model => true,
            else => false,
        };
    }

    pub fn parseFile(self: *Parser) Allocator.Error!ast.File {
        var decls: std.ArrayList(ast.Decl) = .empty;
        while (self.tok.tag != .eof) {
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
        }
        if (self.intern_oom) return error.OutOfMemory;
        return .{ .decls = try decls.toOwnedSlice(self.arena) };
    }

    fn parseDecl(self: *Parser) ParseError!ast.Decl {
        switch (self.tok.tag) {
            .keyword_import => {
                _ = self.advance();
                const ns = try self.expect(.identifier);
                _ = try self.expect(.import_arrow);
                const path = try self.expect(.string);
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
                return .{ .sort = .{ .alias = .{ .name = name, .target = target } } };
            },
            .keyword_const => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| return .{ .constant = .{ .alias = .{ .name = name, .target = target } } };
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
            .keyword_func => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| return .{ .func = .{ .alias = .{ .name = name, .target = target } } };
                const params = try self.parseParams();
                _ = try self.expect(.colon);
                const result = try self.expect(.identifier);
                var requires: ?*const ast.Expr = null;
                if (self.tok.tag == .keyword_requires) {
                    _ = self.advance();
                    requires = try self.parseExpr();
                }
                return .{ .func = .{ .local = .{ .name = name, .params = params, .result = result, .requires = requires } } };
            },
            .keyword_pred => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| return .{ .pred = .{ .alias = .{ .name = name, .target = target } } };
                const params = try self.parseParams();
                return .{ .pred = .{ .local = .{ .name = name, .params = params } } };
            },
            .keyword_axiom => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| return .{ .axiom = .{ .alias = .{ .name = name, .target = target } } };
                // an optional `(params)` makes it an axiom-SCHEMA (a parametric assumption
                // family) — recorded as Fact.params; "schema" is a downstream reading.
                const params = try self.parseOptSchemaParams();
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
                _ = try self.expect(.colon);
                if (self.tok.tag == .keyword_proof) {
                    return self.fail("a hole is a placeholder and carries no proof; once you prove it, make it a theorem", .{});
                }
                return .{ .hole = .{ .local = .{ .name = name, .formula = try self.parseExpr(), .params = params } } };
            },
            .keyword_theorem => {
                _ = self.advance();
                const name = try self.expect(.identifier);
                if (try self.parseAliasTail()) |target| return .{ .theorem = .{ .alias = .{ .name = name, .target = target } } };
                // an optional `(params)` makes it a theorem-SCHEMA (proof re-checked per
                // instantiation) — recorded as Fact.params.
                const params = try self.parseOptSchemaParams();
                _ = try self.expect(.colon);
                const formula = try self.parseExpr();
                _ = try self.expect(.keyword_proof);
                const steps = try self.parseSteps(.keyword_qed);
                _ = try self.expect(.keyword_qed);
                return .{ .theorem = .{ .local = .{ .fact = .{ .name = name, .formula = formula, .params = params }, .steps = steps } } };
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
    fn parseParams(self: *Parser) ParseError![]const ast.Binder {
        if (self.tok.tag != .l_paren) return &.{};
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

    /// `( prop: Nat -> Prop, x: Nat, ... )`
    fn parseSchemaParams(self: *Parser) ParseError![]const ast.SchemaParam {
        _ = try self.expect(.l_paren);
        var params: std.ArrayList(ast.SchemaParam) = .empty;
        while (true) {
            const name = try self.expect(.identifier);
            _ = try self.expect(.colon);
            var sorts: std.ArrayList(Token) = .empty;
            try sorts.append(self.arena, try self.expect(.identifier));
            while (self.tok.tag == .arrow) {
                _ = self.advance();
                try sorts.append(self.arena, try self.expect(.identifier));
            }
            const result = sorts.pop().?;
            try params.append(self.arena, .{
                .name = name,
                .arg_sorts = try sorts.toOwnedSlice(self.arena),
                .result = result,
            });
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
                // though it is a declaration keyword. `axiom`/`theorem` are NO LONGER rule
                // words — fact citations use `cite` (kind-agnostic); the keyword tokens here
                // surface the actionable diagnostic below.
                const rule = switch (self.tok.tag) {
                    .identifier, .keyword_model, .keyword_import => self.advance(),
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
                if (isTheoryRule(self.text(rule)) and self.tok.tag == .l_paren) {
                    _ = self.advance();
                    schema = try self.expect(.identifier);
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
                // refs cite proof labels, which may be kebab-case
                var refs: std.ArrayList(Token) = .empty;
                while (self.tok.tag == .identifier or self.tok.tag == .kebab_identifier) {
                    try refs.append(self.arena, self.advance());
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
                        const binders = try self.parseBinders();
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
                        try conts.append(self.arena, .{ .call_arg = .{ .callee = name, .args = .empty } });
                        level = .expr;
                        continue :descend; // first argument
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
                self.sink.add(n.tok.start, "parenthesize this 'not' where it meets '{s}': mixed boolean operators require explicit parentheses", .{@tagName(outer)}) catch return error.OutOfMemory;
                return error.Recover;
            },
            else => return,
        };
        if (inner == outer) return; // same-operator chain is fine
        const b = operand.binary;
        self.sink.add(b.tok.start, "parenthesize: '{s}' and '{s}' are different boolean operators and their nesting must be explicit", .{ @tagName(inner), @tagName(outer) }) catch return error.OutOfMemory;
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
}

test "declarations parse" {
    const source =
        \\sort Nat
        \\const ZERO: Nat
        \\func div(a: Nat, b: Nat): Nat requires b != ZERO
        \\pred even(n: Nat)
        \\axiom reflAx: forall x: Nat; x = x
        \\axiom induction(prop: Nat -> Prop):
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
    try testing.expectEqual(1, ind.params.?[0].arg_sorts.len);
}

test "theorem with nested proof blocks and instantiate" {
    const source =
        \\theorem impExample: p -> (q -> p)
        \\proof
        \\  @outer | assume p {
        \\    @inner | assume q {
        \\      @got_p | p [by hypothesis outer]
        \\    }
        \\    @qtop | q -> p [by implies_intro inner]
        \\  }
        \\  @done | p -> (q -> p) [by implies_intro outer]
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
    try testing.expectEqualStrings("implies_intro", source[done.rule.start..done.rule.end]);
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
        const source = "pred p\nhole aspirational: p\n";
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
        const source = "pred p\nhole bad: p\nproof\n  @c | p [by cite pa]\nqed\n";
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, source, &sink);
        _ = p.parseFile() catch {};
        try testing.expect(sink.list.items.len > 0);
    }
}

test "@label step definitions; the label name interns without the sigil; refs stay bare" {
    const source =
        \\pred p
        \\theorem t: p
        \\proof
        \\  @base | p [by cite pAx]
        \\  @conc | p [by symmetry base]
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
        \\pred p
        \\axiom pAx: p
        \\theorem t1: p
        \\proof
        \\  @conc | p [by cite pAx]
        \\qed
        \\theorem t2: p
        \\proof
        \\  @conc | p [by cite t1]
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
        \\pred p
        \\axiom pAx: p
        \\theorem t: p
        \\proof
        \\  @c | p [by axiom pAx]
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
        \\pred p
        \\theorem t: p
        \\proof
        \\  @a | p [by cite x]
        \\  @b | p [by modus_ponens a a]
        \\  @c | p [by hypothesis b]
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
            \\pred p
            \\theorem t: p
            \\proof
            \\  @a | p [by cite x]
            \\  @b | p [using specialize head]
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
        var p: Parser = .init(arena, "pred p\ntheorem t: p\nproof\n  @a | p [using axiom x]\nqed", &sink);
        _ = try p.parseFile();
        try testing.expect(sink.list.items.len >= 1);
    }
    // `by` on an ACCELERANT (here `model`, and a bare accelerant word) is rejected at parse.
    {
        var sink: Diagnostics.Sink = .init(arena);
        var p: Parser = .init(arena, "pred p\ntheorem t: p\nproof\n  @a | p [by tautology]\nqed", &sink);
        _ = try p.parseFile();
        try testing.expect(sink.list.items.len >= 1);
    }
}

test "ZERO-ary predicates: bare and empty-paren forms" {
    const source =
        \\pred p
        \\pred q()
        \\axiom both: p -> q
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
