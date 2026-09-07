//! `bpa fmt`: strictly a whitespace and indentation normalizer.
//!
//! It reflows the token stream — line structure, indent depth, spacing
//! between tokens — and nothing else. It never checks or rewrites names and
//! never enforces naming conventions. Because it is token-based it does not
//! require the file to parse; it formats whatever lexes.
//!
//! Canonical shape (each proof step is a label-led block, Fitch-ledger style):
//!   - declarations at column 0, one per line
//!   - `proof` / `qed` at column 0
//!   - a step's LABEL is `@name |`, alone on its line, indented two spaces per
//!     block depth. The `@` sigil marks a definition (citations stay bare); it
//!     sits at the left margin so labels form a scannable gutter column
//!   - the step's statement (or block header `fix …`/`assume …`/`case …`)
//!     goes on the NEXT line, +2 under the label
//!   - the `[by ...]` justification (and a `case`'s split) aligns WITH the
//!     statement, one column beneath the label
//!   - a block's inner steps indent one more level (+2 past the block header);
//!     the closing `}` aligns with the header
//!   - comments preserved: standalone comments keep their own line (at the
//!     current indent); trailing comments stay attached to their line
//!   - blank lines collapse to at most one, preserved where the author put
//!     them
//!   - the author's line breaks WITHIN a statement are preserved; the
//!     continuation is re-indented two spaces past the line it continues
//!     (fmt decides indentation, not where formulas break)

const std = @import("std");
const Allocator = std.mem.Allocator;
const lexer = @import("lexer.zig");
const Token = lexer.Token;
const Tag = Token.Tag;

pub fn format(arena: Allocator, source: []const u8) Allocator.Error![]const u8 {
    // tokenize fully (with comments) for one-token lookahead
    var toks: std.ArrayList(Token) = .empty;
    var lex: lexer.Lexer = .init(source);
    lex.keep_comments = true;
    while (true) {
        const t = lex.next();
        try toks.append(arena, t);
        if (t.tag == .eof) break;
    }

    var out: std.Io.Writer.Allocating = .init(arena);
    render(&out.writer, source, toks.items) catch return error.OutOfMemory;
    return out.toOwnedSlice();
}

fn render(w: *std.Io.Writer, source: []const u8, toks: []const Token) std.Io.Writer.Error!void {
    var depth: u32 = 0; // block depth inside a proof
    var in_proof = false;
    var in_bracket = false; // inside a [by ...] justification
    var line_empty = true; // nothing emitted on the current line yet
    var owner_indent: u32 = 0; // indent of the line being continued
    // the token after a step-label `|` opens the statement on its own line; it
    // becomes the OWNER of any wrapped continuation, so we re-anchor
    // `owner_indent` to its indent (not the label's) when it prints.
    var after_pipe = false;
    var prev_tag: Tag = .eof;
    var prev_end: u32 = 0;
    // Every block header (`fix`/`assume`/`unpack`/`case`) sits on a
    // label-continuation line (+2 past its label), so its body is one level
    // past that. Each open brace adds an extra indent level, undone at `}`.
    var extra_depth: u32 = 0; // extra indent levels currently in effect

    for (toks, 0..) |tok, i| {
        if (tok.tag == .eof) break;
        const text = source[tok.start..tok.end];
        const gap = newlineCount(source[prev_end..tok.start]);

        // where does this token want to go?
        const wants_new_line: bool, const indent: u32 = decide: {
            switch (tok.tag) {
                // inside [by ...], `axiom`/`theorem`/`model` are citations, not decls
                .keyword_import, .keyword_forward, .keyword_sort, .keyword_const, .keyword_define, .keyword_func, .keyword_pred, .keyword_axiom, .keyword_theorem, .keyword_hole, .keyword_model => {
                    if (in_bracket) break :decide .{ false, 0 };
                    break :decide .{ true, 0 };
                },
                .keyword_proof, .keyword_qed => break :decide .{ true, 0 },
                .comment => {
                    // standalone comments get their own line at context indent,
                    // aligned with the steps they annotate (so they carry the
                    // block's `extra_depth`, like labels/`[`/`case`/`}` do);
                    // trailing comments stay on the current line.
                    if (gap >= 1 or line_empty) break :decide .{ true, (depth + extra_depth) * 2 };
                    break :decide .{ false, 0 };
                },
                .identifier, .kebab_identifier, .at_label => {
                    // a step label: a (possibly kebab, possibly already
                    // `@`-sigiled) name directly before '|'
                    if (in_proof and i + 1 < toks.len and toks[i + 1].tag == .pipe) {
                        break :decide .{ true, (depth + extra_depth) * 2 };
                    }
                    break :decide .{ false, 0 };
                },
                .l_bracket => {
                    if (in_proof) break :decide .{ true, (depth + extra_depth) * 2 + 2 };
                    break :decide .{ false, 0 };
                },
                // `case` starts on its own line under the goal it justifies,
                // aligned with the goal statement (like a `[by ...]` line).
                .keyword_case => {
                    if (in_proof) break :decide .{ true, (depth + extra_depth) * 2 + 2 };
                    break :decide .{ false, 0 };
                },
                // a `}` aligns with the block header that opened it (which sits
                // one extra level in, on a label-continuation line), so it keeps
                // this block's still-in-effect extra level.
                .r_brace => break :decide .{ true, (depth - 1 + extra_depth) * 2 },
                else => break :decide .{ false, 0 },
            }
        };

        // a non-structural token on a fresh source line continues its
        // statement: keep the author's break, re-indent to owner + 2
        const continues = !wants_new_line and gap >= 1 and prev_tag != .eof;
        if ((wants_new_line or continues) and !line_empty) {
            try w.writeAll("\n");
            line_empty = true;
        }
        if (line_empty) {
            if (wants_new_line) {
                // author blank lines survive (collapsed to one)
                if (gap >= 2 and prev_tag != .eof) try w.writeAll("\n");
                try w.splatByteAll(' ', indent);
                owner_indent = indent;
            } else {
                const line_indent = owner_indent + 2;
                try w.splatByteAll(' ', line_indent);
                // the statement opener directly after a `|` becomes the owner of
                // its own continuations, so re-anchor here (a plain wrapped line
                // keeps the existing owner).
                if (after_pipe) owner_indent = line_indent;
            }
            after_pipe = false;
        } else if (needSpace(prev_tag, tok.tag)) {
            try w.writeAll(" ");
        }
        // a step label is emitted with the `@` sigil. `.at_label` text already
        // carries it; a bare name before `|` gets one prepended. This makes fmt
        // idempotent whether the source uses `@name |` or the old `name |`.
        const bare_label = (tok.tag == .identifier or tok.tag == .kebab_identifier) and
            in_proof and i + 1 < toks.len and toks[i + 1].tag == .pipe;
        if (bare_label) try w.writeAll("@");
        try w.writeAll(text);
        line_empty = false;

        // state transitions and forced line ends
        switch (tok.tag) {
            .keyword_proof => {
                in_proof = true;
                depth = 1;
                try w.writeAll("\n");
                line_empty = true;
            },
            .keyword_qed => {
                in_proof = false;
                depth = 0;
                extra_depth = 0;
                try w.writeAll("\n");
                line_empty = true;
            },
            .pipe => {
                // a step label sits alone on its line; the statement (or block
                // header) it introduces starts on the next line, indented +2 as
                // a continuation. `|` is only ever the step-label delimiter. That
                // next line owns any further continuations, so flag it.
                if (in_proof) {
                    try w.writeAll("\n");
                    line_empty = true;
                    after_pipe = true;
                }
            },
            .l_brace => {
                // in a proof, every block header (`fix …`, `assume …`,
                // `case …`) sits on a label-continuation line, one level (+2)
                // past its label; its body is one level past THAT, so the brace
                // carries an extra indent level (undone at its matching `}`). A
                // top-level `{` (a `model … { … }` declaration body), by contrast,
                // opens at column 0 — its closing `}` returns to column 0, so it
                // gets NO extra_depth (only depth, keeping the r_brace math at 0).
                depth += 1;
                if (in_proof) extra_depth += 1;
                try w.writeAll("\n");
                line_empty = true;
            },
            .r_brace => {
                if (in_proof) extra_depth -= 1;
                depth -= 1;
                try w.writeAll("\n");
                line_empty = true;
            },
            .l_bracket => in_bracket = true,
            .r_bracket => {
                in_bracket = false;
                try w.writeAll("\n");
                line_empty = true;
            },
            .comment => {
                try w.writeAll("\n");
                line_empty = true;
            },
            else => {},
        }

        prev_tag = tok.tag;
        prev_end = tok.end;
    }
    if (!line_empty) try w.writeAll("\n");
}

fn newlineCount(s: []const u8) u32 {
    var n: u32 = 0;
    for (s) |c| {
        if (c == '\n') n += 1;
    }
    return n;
}

/// spacing between two adjacent tokens on the same line
fn needSpace(prev: Tag, cur: Tag) bool {
    switch (cur) {
        .r_paren, .r_bracket, .comma, .dot, .colon, .semicolon => return false,
        // a step label reads `label |` — a space separates the tag from its pipe
        .pipe => return true,
        // `model(Instance)` cites with no space, like `arithmetic(peano)` —
        // `model` is a keyword here, not an identifier, so admit it explicitly.
        .l_paren => return prev != .identifier and prev != .kebab_identifier and prev != .l_paren and prev != .keyword_model,
        else => {},
    }
    switch (prev) {
        .l_paren, .l_bracket, .pipe => return prev == .pipe, // 'label| formula'
        else => return true,
    }
}

// --- tests ---

const testing = std.testing;

fn expectFmt(input: []const u8, expected: []const u8) !void {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const got = try format(arena_state.allocator(), input);
    try testing.expectEqualStrings(expected, got);
    // idempotency: formatting is a fixpoint
    const again = try format(arena_state.allocator(), got);
    try testing.expectEqualStrings(expected, again);
}

test "declarations normalize to one per line at column 0" {
    try expectFmt(
        "sort   Nat\n  const ZERO:Nat\nfunc succ( n:Nat ):Nat\naxiom a:forall b:Nat ;succ(b)!=ZERO\n",
        "sort Nat\nconst ZERO: Nat\nfunc succ(n: Nat): Nat\naxiom a: forall b: Nat; succ(b) != ZERO\n",
    );
}

test "a `hole` declaration is top-level: resets to column 0" {
    try expectFmt(
        "pred p\n  hole h: p\n",
        "pred p\nhole h: p\n",
    );
}

test "proof steps: label alone on its line; statement and justification aligned; block body +4" {
    try expectFmt(
        \\pred p
        \\theorem t: p -> p
        \\proof
        \\  outer| assume p {   inner| p
        \\  [by hypothesis outer]  }
        \\  conclusion| p -> p [by implies_intro outer]
        \\qed
        \\
    ,
        \\pred p
        \\theorem t: p -> p
        \\proof
        \\  @outer |
        \\    assume p {
        \\      @inner |
        \\        p
        \\        [by hypothesis outer]
        \\    }
        \\  @conclusion |
        \\    p -> p
        \\    [by implies_intro outer]
        \\qed
        \\
    );
}

test "case: arms nest one level under `case`, closing brace aligns with it" {
    try expectFmt(
        \\pred p
        \\pred q
        \\theorem t: q
        \\proof
        \\  d| p or q [by cite e]
        \\  r| q
        \\  case d {
        \\  a| assume p { c| q [by hypothesis a] }
        \\  b| assume q { c| q [by hypothesis b] }
        \\  }
        \\qed
        \\
    ,
        \\pred p
        \\pred q
        \\theorem t: q
        \\proof
        \\  @d |
        \\    p or q
        \\    [by cite e]
        \\  @r |
        \\    q
        \\    case d {
        \\      @a |
        \\        assume p {
        \\          @c |
        \\            q
        \\            [by hypothesis a]
        \\        }
        \\      @b |
        \\        assume q {
        \\          @c |
        \\            q
        \\            [by hypothesis b]
        \\        }
        \\    }
        \\qed
        \\
    );
}

test "comments: standalone keeps its line at indent, trailing stays attached" {
    try expectFmt(
        \\// header
        \\pred p
        \\theorem t: p
        \\proof
        \\// why
        \\  conclusion| p // trailing
        \\  [by cite missing]
        \\qed
        \\
    ,
        \\// header
        \\pred p
        \\theorem t: p
        \\proof
        \\  // why
        \\  @conclusion |
        \\    p // trailing
        \\    [by cite missing]
        \\qed
        \\
    );
}

test "blank lines collapse to one and survive where placed" {
    try expectFmt(
        "sort Nat\n\n\n\nconst ZERO: Nat\n",
        "sort Nat\n\nconst ZERO: Nat\n",
    );
}

test "standalone comment inside a nested block aligns with the steps (carries extra_depth)" {
    // a comment inside a `fix` block must indent to the block's step level, not
    // the shallower `depth*2` that ignores the brace's extra level.
    try expectFmt(
        \\pred p(a: Nat)
        \\theorem t: forall a: Nat; p(a)
        \\proof
        \\  g| fix a: Nat {
        \\  // why this step
        \\  s| p(a) [by cite e]
        \\  }
        \\  conclusion| forall a: Nat; p(a) [by forall_intro g]
        \\qed
        \\
    ,
        \\pred p(a: Nat)
        \\theorem t: forall a: Nat; p(a)
        \\proof
        \\  @g |
        \\    fix a: Nat {
        \\      // why this step
        \\      @s |
        \\        p(a)
        \\        [by cite e]
        \\    }
        \\  @conclusion |
        \\    forall a: Nat; p(a)
        \\    [by forall_intro g]
        \\qed
        \\
    );
}

test "wrapped formula continuation inside a nested block re-indents to owner + 2" {
    // the continuation of a multi-line formula indents two past the FORMULA
    // line (its owner), not two past the label — inside nested proof blocks the
    // owner is the formula, which sits at label + 2.
    try expectFmt(
        \\pred p(a: Nat, b: Nat)
        \\theorem t: forall a: Nat; p(a, a)
        \\proof
        \\  g| fix a: Nat {
        \\  s| forall b: Nat;
        \\  p(a, b)
        \\  [by cite e]
        \\  }
        \\  conclusion| forall a: Nat; p(a, a) [by forall_intro g]
        \\qed
        \\
    ,
        \\pred p(a: Nat, b: Nat)
        \\theorem t: forall a: Nat; p(a, a)
        \\proof
        \\  @g |
        \\    fix a: Nat {
        \\      @s |
        \\        forall b: Nat;
        \\          p(a, b)
        \\        [by cite e]
        \\    }
        \\  @conclusion |
        \\    forall a: Nat; p(a, a)
        \\    [by forall_intro g]
        \\qed
        \\
    );
}

test "author line breaks within statements survive; continuation re-indents to +2" {
    try expectFmt(
        \\axiom induction(prop: Nat -> Prop):
        \\      prop(ZERO) -> forall n: Nat; prop(n)
        \\theorem t: forall n: Nat.
        \\ is_zero(n)
        \\proof
        \\  conclusion| forall n: Nat; is_zero(n)
        \\    [by instantiate induction((fun k: Nat => is_zero(k))) base step]
        \\qed
        \\
    ,
        \\axiom induction(prop: Nat -> Prop):
        \\  prop(ZERO) -> forall n: Nat; prop(n)
        \\theorem t: forall n: Nat.
        \\  is_zero(n)
        \\proof
        \\  @conclusion |
        \\    forall n: Nat; is_zero(n)
        \\    [by instantiate induction((fun k: Nat => is_zero(k))) base step]
        \\qed
        \\
    );
}
