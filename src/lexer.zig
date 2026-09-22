//! Lexer for .bpa files. Zero-allocation: tokens are tag + byte range into the
//! source (style of std/zig/tokenizer.zig). `//` comments are skipped.

const std = @import("std");
const InternPool = @import("InternPool.zig");

pub const Token = struct {
    tag: Tag,
    start: u32,
    end: u32,
    /// Interned name for the stringy (non-reserved) tags, stamped by the PARSER
    /// as it consumes tokens — the lexer itself stays pure and leaves it `.none`.
    /// identifier/kebab_identifier: the name (for a `ns.`-qualified token, the
    /// part AFTER the dot); at_label: the label sans `@`; string: the contents
    /// sans quotes. Past parsing, engine code compares these ids — never text.
    name: InternPool.StrId = .none,
    /// The `ns` of a dot-qualified identifier/at_label (`peano.Nat` — one token;
    /// `qualifier` = `peano`, `name` = `Nat`). `.none` when unqualified.
    qualifier: InternPool.StrId = .none,

    pub const Tag = enum {
        identifier,
        /// an identifier containing a hyphen (`case-lt`, `h-eq`). Lexically a
        /// name, but a distinct tag so the parser can restrict declaration
        /// names to plain `.identifier` while proof labels/refs accept either.
        kebab_identifier,
        /// a proof step label written with the `@` sigil: `@lt-elim`. One token,
        /// `@` immediately followed by a (kebab-capable) name, no space. Marks a
        /// step DEFINITION; citations of the label stay bare (no `@`).
        at_label,
        /// A SYNTHETIC token (never lexed) whose `.name` is a resolved SYMBOL's InternPool
        /// Index — a sort/const/func/pred IDENTITY, not a name to look up. Delaboration
        /// (kernel term → AST) emits these so a term's symbols survive re-elaboration in any
        /// namespace — a schema instantiated at another file's symbols has synthetics
        /// mentioning names that file never declared. Elab applies the ambient model to it
        /// like any resolved name; `.qualifier == .universe` marks an EXACT identity (the
        /// parent/universe space, no model — a refined target sort's guard predicate).
        symbol,
        // declaration keywords
        keyword_import,
        keyword_forward,
        keyword_sort,
        keyword_const,
        keyword_define,
        keyword_definition,
        keyword_when,
        keyword_func,
        keyword_pred,
        keyword_axiom,
        keyword_hole,
        keyword_theorem,
        keyword_proof,
        keyword_qed,
        keyword_requires,
        keyword_where,
        keyword_model,
        // proof keywords
        keyword_assume,
        keyword_fix,
        keyword_unpack,
        keyword_from,
        keyword_by,
        /// `using` — the justification keyword for ACCELERANT steps (engine
        /// proof-generation: accelerants + `using instantiation` + `using model`),
        /// as opposed to `by` for the pure kernel primitives.
        keyword_using,
        keyword_case,
        // formula keywords
        keyword_forall,
        keyword_exists,
        keyword_not,
        keyword_and,
        keyword_or,
        keyword_iff,
        keyword_fun,
        // punctuation / operators
        colon,
        semicolon,
        comma,
        dot,
        l_paren,
        r_paren,
        l_brace,
        r_brace,
        arrow, // ->
        fat_arrow, // =>
        equal, // =
        bang_equal, // !=
        pipe, // | (step-label delimiter)
        l_bracket, // [ (justification opener)
        r_bracket, // ]
        /// import path: "peano.bpa" (no escapes)
        string,
        import_arrow, // <<<
        obligation_arrow, // <- (model axiom-obligation discharge)
        closure_turnstile, // -| (model func closure-discharge: `op -| closureFact`)
        /// only emitted when `keep_comments` is set (used by `bpa fmt`)
        comment,
        invalid,
        eof,

        /// Human-readable spelling for diagnostics ("expected ':', got 'forall'").
        pub fn spelling(tag: Tag) []const u8 {
            return switch (tag) {
                .identifier => "identifier",
                .kebab_identifier => "identifier",
                .at_label => "@label",
                .symbol => "symbol",
                .keyword_import => "import",
                .keyword_forward => "intheory",
                .keyword_sort => "sort",
                .keyword_const => "const",
                .keyword_define => "define",
                .keyword_definition => "definition",
                .keyword_when => "when",
                .keyword_func => "func",
                .keyword_pred => "pred",
                .keyword_axiom => "axiom",
                .keyword_hole => "hole",
                .keyword_theorem => "theorem",
                .keyword_proof => "proof",
                .keyword_qed => "qed",
                .keyword_requires => "requires",
                .keyword_where => "where",
                .keyword_model => "model",
                .keyword_assume => "assume",
                .keyword_fix => "fix",
                .keyword_unpack => "unpack",
                .keyword_from => "from",
                .keyword_by => "by",
                .keyword_using => "using",
                .keyword_case => "case",
                .keyword_forall => "forall",
                .keyword_exists => "exists",
                .keyword_not => "not",
                .keyword_and => "and",
                .keyword_or => "or",
                .keyword_iff => "iff",
                .keyword_fun => "fun",
                .colon => ":",
                .semicolon => ";",
                .comma => ",",
                .dot => ".",
                .l_paren => "(",
                .r_paren => ")",
                .l_brace => "{",
                .r_brace => "}",
                .arrow => "->",
                .fat_arrow => "=>",
                .equal => "=",
                .bang_equal => "!=",
                .pipe => "|",
                .l_bracket => "[",
                .r_bracket => "]",
                .string => "string",
                .import_arrow => "<<<",
                .obligation_arrow => "<-",
                .closure_turnstile => "-|",
                .comment => "comment",
                .invalid => "invalid token",
                .eof => "end of file",
            };
        }
    };
};

const keywords = std.StaticStringMap(Token.Tag).initComptime(.{
    .{ "import", .keyword_import },
    .{ "intheory", .keyword_forward },
    .{ "sort", .keyword_sort },
    .{ "const", .keyword_const },
    .{ "define", .keyword_define },
    .{ "definition", .keyword_definition },
    .{ "when", .keyword_when },
    .{ "func", .keyword_func },
    .{ "pred", .keyword_pred },
    .{ "axiom", .keyword_axiom },
    .{ "hole", .keyword_hole },
    .{ "theorem", .keyword_theorem },
    .{ "proof", .keyword_proof },
    .{ "qed", .keyword_qed },
    .{ "requires", .keyword_requires },
    .{ "where", .keyword_where },
    .{ "model", .keyword_model },
    .{ "assume", .keyword_assume },
    .{ "fix", .keyword_fix },
    .{ "unpack", .keyword_unpack },
    .{ "from", .keyword_from },
    .{ "by", .keyword_by },
    .{ "using", .keyword_using },
    .{ "case", .keyword_case },
    .{ "forall", .keyword_forall },
    .{ "exists", .keyword_exists },
    .{ "not", .keyword_not },
    .{ "and", .keyword_and },
    .{ "or", .keyword_or },
    .{ "iff", .keyword_iff },
    .{ "fun", .keyword_fun },
});

pub const Lexer = struct {
    source: []const u8,
    index: u32 = 0,
    /// emit `.comment` tokens instead of skipping them (for `bpa fmt`)
    keep_comments: bool = false,

    pub fn init(source: []const u8) Lexer {
        return .{ .source = source };
    }

    pub fn next(self: *Lexer) Token {
        const src = self.source;
        // skip whitespace and (unless kept) // comments
        while (self.index < src.len) {
            const c = src[self.index];
            if (c == ' ' or c == '\t' or c == '\n' or c == '\r') {
                self.index += 1;
            } else if (c == '/' and self.index + 1 < src.len and src[self.index + 1] == '/') {
                const comment_start = self.index;
                while (self.index < src.len and src[self.index] != '\n') self.index += 1;
                if (self.keep_comments) {
                    return .{ .tag = .comment, .start = comment_start, .end = self.index };
                }
            } else break;
        }
        const start = self.index;
        if (start >= src.len) return .{ .tag = .eof, .start = start, .end = start };

        const c = src[self.index];
        self.index += 1;
        const tag: Token.Tag = switch (c) {
            'a'...'z', 'A'...'Z', '_' => blk: {
                var saw_hyphen = false;
                while (self.index < src.len) : (self.index += 1) {
                    switch (src[self.index]) {
                        'a'...'z', 'A'...'Z', '0'...'9', '_' => {},
                        // kebab-case: '-' continues an identifier only when
                        // followed by an identifier character ('x->y' still
                        // lexes as arrow). Consequence, by design: there is no
                        // infix minus, ever.
                        '-' => {
                            if (self.index + 1 >= src.len) break;
                            switch (src[self.index + 1]) {
                                'a'...'z', 'A'...'Z', '0'...'9', '_' => saw_hyphen = true,
                                else => break,
                            }
                        },
                        // namespace access: '.' joins when followed by a
                        // letter/underscore, so `peano.Nat` is one token
                        // (resolved and validated by the elaborator)
                        '.' => {
                            if (self.index + 1 >= src.len) break;
                            switch (src[self.index + 1]) {
                                'a'...'z', 'A'...'Z', '_' => {},
                                else => break,
                            }
                        },
                        else => break,
                    }
                }
                // a keyword is never kebab (no keyword contains '-'); a name
                // with a hyphen becomes `.kebab_identifier` so the parser can
                // keep it out of declaration-name positions.
                if (keywords.get(src[start..self.index])) |kw| break :blk kw;
                break :blk if (saw_hyphen) .kebab_identifier else .identifier;
            },
            '@' => blk: {
                // `@name` step label: '@' then a (kebab-capable) identifier.
                // A lone '@' (not followed by an identifier char) is invalid.
                if (self.index >= src.len) break :blk .invalid;
                switch (src[self.index]) {
                    'a'...'z', 'A'...'Z', '_' => {},
                    else => break :blk .invalid,
                }
                while (self.index < src.len) : (self.index += 1) {
                    switch (src[self.index]) {
                        'a'...'z', 'A'...'Z', '0'...'9', '_' => {},
                        '-', '.' => {
                            // a hyphen joins a kebab name; a '.' joins a qualified
                            // projection tail (`@subgroup.opAssoc` — a model
                            // projection as a mapping value). Both only before a
                            // letter/underscore.
                            if (self.index + 1 >= src.len) break;
                            switch (src[self.index + 1]) {
                                'a'...'z', 'A'...'Z', '0'...'9', '_' => {},
                                else => break,
                            }
                        },
                        else => break,
                    }
                }
                break :blk .at_label;
            },
            ':' => .colon,
            ';' => .semicolon,
            '|' => .pipe,
            '[' => .l_bracket,
            ']' => .r_bracket,
            ',' => .comma,
            '.' => .dot,
            '(' => .l_paren,
            ')' => .r_paren,
            '{' => .l_brace,
            '}' => .r_brace,
            '-' => blk: {
                // `->` arrow, `-|` reverse turnstile (model closure-discharge), else invalid.
                if (self.index < src.len and src[self.index] == '>') {
                    self.index += 1;
                    break :blk .arrow;
                }
                if (self.index < src.len and src[self.index] == '|') {
                    self.index += 1;
                    break :blk .closure_turnstile;
                }
                break :blk .invalid;
            },
            '=' => self.ifNext('>', .fat_arrow, .equal),
            '!' => self.ifNext('=', .bang_equal, .invalid),
            '<' => blk: {
                if (self.index + 1 < src.len and src[self.index] == '<' and src[self.index + 1] == '<') {
                    self.index += 2;
                    break :blk .import_arrow;
                }
                // `<-` — model axiom-obligation discharge (distinct from `:` maps).
                if (self.index < src.len and src[self.index] == '-') {
                    self.index += 1;
                    break :blk .obligation_arrow;
                }
                break :blk .invalid;
            },
            '"' => blk: {
                while (self.index < src.len) : (self.index += 1) {
                    switch (src[self.index]) {
                        '"' => {
                            self.index += 1;
                            break :blk .string;
                        },
                        '\n' => break :blk .invalid, // unterminated
                        else => {},
                    }
                }
                break :blk .invalid;
            },
            else => .invalid,
        };
        return .{ .tag = tag, .start = start, .end = self.index };
    }

    fn ifNext(self: *Lexer, expected: u8, then: Token.Tag, otherwise: Token.Tag) Token.Tag {
        if (self.index < self.source.len and self.source[self.index] == expected) {
            self.index += 1;
            return then;
        }
        return otherwise;
    }
};

fn expectTags(source: []const u8, expected: []const Token.Tag) !void {
    var lexer: Lexer = .init(source);
    for (expected) |tag| {
        const tok = lexer.next();
        try std.testing.expectEqual(tag, tok.tag);
    }
    try std.testing.expectEqual(.eof, lexer.next().tag);
}

test "declarations lex to expected tags" {
    try expectTags("sort nat", &.{ .keyword_sort, .identifier });
    try expectTags("const zero: nat", &.{ .keyword_const, .identifier, .colon, .identifier });
    try expectTags(
        "func div(a: nat, b: nat): nat requires b != zero",
        &.{
            .keyword_func, .identifier, .l_paren,    .identifier,       .colon,
            .identifier,   .comma,      .identifier, .colon,            .identifier,
            .r_paren,      .colon,      .identifier, .keyword_requires, .identifier,
            .bang_equal,   .identifier,
        },
    );
}

test "operators disambiguate" {
    try expectTags("-> => = != and or |", &.{ .arrow, .fat_arrow, .equal, .bang_equal, .keyword_and, .keyword_or, .pipe });
    try expectTags("a=b", &.{ .identifier, .equal, .identifier });
    try expectTags("fun k: nat => k = k", &.{
        .keyword_fun, .identifier, .colon,      .identifier, .fat_arrow,
        .identifier,  .equal,      .identifier,
    });
}

test "comments are skipped" {
    try expectTags("// whole line\nsort nat // trailing\n// tail", &.{ .keyword_sort, .identifier });
}

test "byte ranges are exact" {
    var lexer: Lexer = .init("axiom bad forall");
    _ = lexer.next(); // axiom
    const bad = lexer.next();
    try std.testing.expectEqualStrings("bad", lexer.source[bad.start..bad.end]);
    const fa = lexer.next();
    try std.testing.expectEqual(@as(u32, 10), fa.start);
    try std.testing.expectEqual(.keyword_forall, fa.tag);
}

test "invalid characters produce invalid token" {
    try expectTags("sort $", &.{ .keyword_sort, .invalid });
    try expectTags("- !", &.{ .invalid, .invalid });
    // the old symbolic connectives are gone: bare slashes are invalid
    try expectTags("/ \\", &.{ .invalid, .invalid });
    // 'and'/'or' are keywords, but identifiers merely containing them are not
    try expectTags("and_intro orx", &.{ .identifier, .identifier });
}

test "imports: keyword, arrow, string, qualified names" {
    try expectTags("import peano <<< \"peano.bpa\"", &.{ .keyword_import, .identifier, .import_arrow, .string });
    try expectTags("peano.Nat", &.{.identifier});
    try expectTags("good(lib.NIL)", &.{ .identifier, .l_paren, .identifier, .r_paren });
    // '.' joins only before a letter/underscore; a lone '<' is invalid
    try expectTags("x. <", &.{ .identifier, .dot, .invalid });
    var lex: Lexer = .init("peano.add-zero");
    const tok = lex.next();
    try std.testing.expectEqualStrings("peano.add-zero", lex.source[tok.start..tok.end]);
}

test "kebab-case identifiers coexist with arrow" {
    // a hyphenated name is now its own tag, distinct from a plain identifier
    try expectTags("add-zero-left", &.{.kebab_identifier});
    try expectTags("plainname", &.{.identifier});
    try expectTags("eq2", &.{.identifier}); // digits alone are not kebab
    try expectTags("x->y", &.{ .identifier, .arrow, .identifier });
    try expectTags("Nat -> Prop", &.{ .identifier, .arrow, .identifier });
    // bare minus is not an operator
    try expectTags("a - b", &.{ .identifier, .invalid, .identifier });
    // keywords are never kebab (none contains '-')
    try expectTags("assume", &.{.keyword_assume});
    var lex: Lexer = .init("given-inductive-hypothesis| p");
    const tok = lex.next();
    try std.testing.expectEqual(Token.Tag.kebab_identifier, tok.tag);
    try std.testing.expectEqualStrings("given-inductive-hypothesis", lex.source[tok.start..tok.end]);
}

test "@label step-label sigil lexes as one token; lone @ is invalid" {
    // `@name` (kebab-capable) is a single at_label token, then the pipe
    try expectTags("@lt-elim |", &.{ .at_label, .pipe });
    try expectTags("@base | p", &.{ .at_label, .pipe, .identifier });
    var lex: Lexer = .init("@case-lt");
    const tok = lex.next();
    try std.testing.expectEqual(Token.Tag.at_label, tok.tag);
    try std.testing.expectEqualStrings("@case-lt", lex.source[tok.start..tok.end]);
    // a lone '@' with no following identifier is invalid
    try expectTags("@ x", &.{ .invalid, .identifier });
}
