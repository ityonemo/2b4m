//! `2b4m index <file.b4m>` — print a file's HEADER: every line up to, but not including,
//! the first `theorem`, `lemma` or `model`.
//!
//! That boundary is the one `--library` enforces (see the parser's `checkHeaderStructure`):
//! a library file's header declares everything it ASSUMES (`axiom`, `hole`) and PROMISES
//! (`intheory`) before any of it is used. So the header IS the file's interface, and this
//! command is how you read one without opening the proofs — the output is the answer to
//! "what does this file give me, and what does it rest on?".
//!
//! `.b4m` only. A literate `.md` has no enforced header (its prose drives its declaration
//! order), and `literate.extract` blanks prose while keeping line positions, so an `.md`
//! index would be mostly blank padding.
//!
//! A file with NO proof is entirely header: its whole contents are its interface, which
//! matches `check` treating a declarations-only file as a legitimate dependency.

const std = @import("std");

/// The declaration keywords that END the header. Matched at column 0 only — a nested
/// occurrence inside a proof cannot reach here (the first one already stopped the scan),
/// and a mention in a comment or a string never starts a line at column 0 as a bare word.
const TRIGGERS = [_][]const u8{ "theorem", "lemma", "model" };

/// Is `line` a top-level declaration of one of the header-ending kinds?
fn isTrigger(line: []const u8) bool {
    for (TRIGGERS) |kw| {
        if (!std.mem.startsWith(u8, line, kw)) continue;
        // the keyword must be the whole word: `theorem foo` yes, `theoremish` no
        if (line.len == kw.len) return true;
        const c = line[kw.len];
        if (!std.ascii.isAlphanumeric(c) and c != '_') return true;
    }
    return false;
}

/// `source`'s header: everything before the first line that opens a `theorem`, `lemma` or
/// `model`, with trailing newlines stripped. Returns a slice OF `source` — no allocation.
pub fn header(source: []const u8) []const u8 {
    var cut: usize = source.len;
    var at: usize = 0;
    while (at < source.len) {
        const nl = std.mem.indexOfScalarPos(u8, source, at, '\n') orelse source.len;
        if (isTrigger(source[at..nl])) {
            cut = at;
            break;
        }
        at = nl + 1;
    }
    return std.mem.trimEnd(u8, source[0..cut], "\n");
}

const testing = std.testing;

test "index: the header stops at the first theorem" {
    const src =
        \\sort Nat
        \\const ZERO: Nat
        \\intheory foo
        \\
        \\theorem foo: ZERO = ZERO
        \\proof
        \\qed
        \\
    ;
    try testing.expectEqualStrings("sort Nat\nconst ZERO: Nat\nintheory foo", header(src));
}

test "index: `lemma` and `model` also end the header" {
    try testing.expectEqualStrings("sort Nat", header("sort Nat\nlemma h: x\n"));
    try testing.expectEqualStrings("sort Nat", header("sort Nat\nmodel M {\n}\n"));
}

test "index: a file with no proof is entirely header" {
    // its whole contents are its interface, trailing newline stripped
    try testing.expectEqualStrings("sort Nat\nconst ZERO: Nat", header("sort Nat\nconst ZERO: Nat\n"));
}

test "index: a trigger word must stand alone at column 0" {
    // `theoremFoo` is an identifier, not the keyword; an INDENTED `theorem` is inside a
    // proof body or a comment, never a top-level declaration.
    try testing.expectEqualStrings("sort theoremFoo", header("sort theoremFoo\n"));
    try testing.expectEqualStrings("// the theorem below", header("// the theorem below\n"));
    try testing.expectEqualStrings("sort Nat\n  theorem x", header("sort Nat\n  theorem x\n"));
}

test "index: no trailing newline in the output, however many the header has" {
    try testing.expectEqualStrings("sort Nat", header("sort Nat\n\n\ntheorem t: x\n"));
    try testing.expectEqualStrings("sort Nat", header("sort Nat\n\n\n"));
}
