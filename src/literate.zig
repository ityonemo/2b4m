//! Literate 2b4m: `2b4m check foo.md` checks the proofs embedded in a Markdown
//! document. Only ```` ```2b4m ```` fenced blocks are code; everything else is
//! prose.
//!
//! The extraction is a MASK, not a copy: every line outside a `2b4m` block —
//! prose, blank lines, the fence lines themselves — is replaced by an empty
//! line, and the *contents* of `2b4m` blocks are kept verbatim in place. So the
//! result has the SAME byte and line offsets as the original `.md`, which means
//! error locations (`file.md:line:col`) map straight back to the document with
//! zero offset bookkeeping. All `2b4m` blocks share one scope (they concatenate
//! into a single logical file), so a later block can cite an earlier one.

const std = @import("std");
const Allocator = std.mem.Allocator;
const fmt = @import("fmt.zig");

/// Mask `source` (a Markdown document) to 2b4m code: keep the lines inside
/// ```` ```2b4m ```` fences, blank everything else, preserving line count and
/// every byte offset. The returned buffer has the same length as `source`
/// except where content is dropped (replaced by nothing but the newline).
pub fn extract(arena: Allocator, source: []const u8) Allocator.Error![]const u8 {
    var out: std.ArrayList(u8) = .empty;
    try out.ensureTotalCapacity(arena, source.len);

    var in_block = false;
    var i: usize = 0;
    while (i < source.len) {
        // find the end of this line (inclusive of the trailing '\n' if present)
        const line_start = i;
        var line_end = i;
        while (line_end < source.len and source[line_end] != '\n') line_end += 1;
        const has_nl = line_end < source.len;
        const line = source[line_start..line_end];

        if (isFenceOpen(line)) {
            // the ```2b4m fence line itself is not code — blank it, enter block
            in_block = true;
        } else if (in_block and isFenceClose(line)) {
            // closing ``` — blank it, leave block
            in_block = false;
        } else if (in_block) {
            // inside a 2b4m block: keep the line verbatim
            try out.appendSlice(arena, line);
        }
        // (else: prose / blank / non-2b4m fence — emit nothing but the newline)

        if (has_nl) try out.append(arena, '\n');
        i = line_end + @intFromBool(has_nl);
    }
    return out.items;
}

/// Format a literate `.md` document: reformat the 2b4m inside each ```` ```2b4m ````
/// fenced block with `fmt.format`, leaving ALL prose, blank lines, and fence
/// lines byte-for-byte verbatim. The inverse of the situation `extract` is built
/// for — here the prose is preserved and the code is rewritten, whereas `extract`
/// masks the prose and preserves the code. Byte offsets shift (that's the point:
/// the code is reflowed), so this is for `fmt`, never for error mapping.
///
/// Each block is formatted independently (a block is a self-contained chunk of
/// declarations/one proof; `fmt.format` handles a partial file). A block whose
/// content does not lex is left verbatim rather than dropped, so a malformed
/// block never silently loses content.
pub fn formatLiterate(arena: Allocator, source: []const u8) Allocator.Error![]const u8 {
    var out: std.ArrayList(u8) = .empty;
    try out.ensureTotalCapacity(arena, source.len);

    var block: std.ArrayList(u8) = .empty; // accumulates the current block's content
    var in_block = false;

    var i: usize = 0;
    while (i < source.len) {
        const line_start = i;
        var line_end = i;
        while (line_end < source.len and source[line_end] != '\n') line_end += 1;
        const has_nl = line_end < source.len;
        const line = source[line_start..line_end];

        if (!in_block and isFenceOpen(line)) {
            // emit the opening fence verbatim, start collecting the block
            in_block = true;
            block.clearRetainingCapacity();
            try out.appendSlice(arena, line);
            if (has_nl) try out.append(arena, '\n');
        } else if (in_block and isFenceClose(line)) {
            // block done: format its collected content, emit, then the fence
            const formatted = fmt.format(arena, block.items) catch block.items;
            try out.appendSlice(arena, formatted);
            in_block = false;
            try out.appendSlice(arena, line);
            if (has_nl) try out.append(arena, '\n');
        } else if (in_block) {
            // inside a block: buffer the content line (with its newline) for fmt
            try block.appendSlice(arena, line);
            if (has_nl) try block.append(arena, '\n');
        } else {
            // prose / blank / non-2b4m fence: verbatim
            try out.appendSlice(arena, line);
            if (has_nl) try out.append(arena, '\n');
        }
        i = line_end + @intFromBool(has_nl);
    }

    // an unterminated block (no closing fence): flush its buffered content
    // verbatim so nothing is lost.
    if (in_block) try out.appendSlice(arena, block.items);

    return out.items;
}

/// A ```` ```2b4m ```` opening fence: ``` (or more backticks) immediately
/// followed by the info string `2b4m` (and nothing else but trailing spaces).
fn isFenceOpen(line: []const u8) bool {
    const rest = fenceRest(line) orelse return false;
    const info = std.mem.trim(u8, rest, " \t");
    return std.mem.eql(u8, info, "2b4m");
}

/// A closing fence: a run of backticks with no info string.
fn isFenceClose(line: []const u8) bool {
    const rest = fenceRest(line) orelse return false;
    return std.mem.trim(u8, rest, " \t").len == 0;
}

/// If `line` (after optional leading spaces) starts with a run of >= 3
/// backticks, return the text after that run; else null.
fn fenceRest(line: []const u8) ?[]const u8 {
    var s: usize = 0;
    while (s < line.len and (line[s] == ' ' or line[s] == '\t')) s += 1;
    var ticks: usize = 0;
    while (s + ticks < line.len and line[s + ticks] == '`') ticks += 1;
    if (ticks < 3) return null;
    return line[s + ticks ..];
}

// -- tests -----------------------------------------------------------------

const testing = std.testing;

test "extract keeps 2b4m block content, blanks prose, preserves offsets" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();

    const md =
        \\# Title
        \\
        \\Some prose.
        \\
        \\```2b4m
        \\sort Nat
        \\const Z: Nat
        \\```
        \\
        \\more prose
        \\
    ;
    const got = try extract(a, md);
    // the mask preserves NEWLINE count (so line numbers map), though prose
    // bytes are dropped (columns only matter inside 2b4m blocks, kept verbatim).
    try testing.expectEqual(
        std.mem.count(u8, md, "\n"),
        std.mem.count(u8, got, "\n"),
    );
    // the 2b4m lines survive, on their original line numbers
    const expect =
        \\
        \\
        \\
        \\
        \\
        \\sort Nat
        \\const Z: Nat
        \\
        \\
        \\
        \\
    ;
    try testing.expectEqualStrings(expect, got);
}

test "ignores non-2b4m fences" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    const md =
        \\```
        \\not checked
        \\```
        \\```zig
        \\also not
        \\```
        \\```2b4m
        \\sort Nat
        \\```
        \\
    ;
    const got = try extract(a, md);
    try testing.expectEqualStrings(
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\sort Nat
        \\
        \\
    , got);
}

test "formatLiterate reflows 2b4m blocks and leaves prose verbatim" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();

    // prose (including a deliberately mis-indented heading and trailing spaces),
    // then a 2b4m block whose steps are written on one line and under-indented.
    const md =
        \\#   Title
        \\
        \\Some   prose   with   inner   spaces.
        \\
        \\```2b4m
        \\theorem t: a
        \\proof
        \\@conclusion | a [by cite h]
        \\qed
        \\```
        \\
        \\more prose
        \\
    ;
    const got = try formatLiterate(a, md);
    // prose lines survive byte-for-byte; only the 2b4m block is reflowed to the
    // canonical three-line-per-step form.
    const expect =
        \\#   Title
        \\
        \\Some   prose   with   inner   spaces.
        \\
        \\```2b4m
        \\theorem t: a
        \\proof
        \\  @conclusion |
        \\    a
        \\    [by cite h]
        \\qed
        \\```
        \\
        \\more prose
        \\
    ;
    try testing.expectEqualStrings(expect, got);
}

test "formatLiterate ignores non-2b4m fences" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    // a plain fence and a zig fence must pass through untouched, even though
    // their contents would be mangled if treated as 2b4m source.
    const md =
        \\```
        \\@not a step | but looks like one
        \\```
        \\
        \\```zig
        \\const x=1;
        \\```
        \\
    ;
    const got = try formatLiterate(a, md);
    try testing.expectEqualStrings(md, got);
}

test "formatLiterate flushes an unterminated 2b4m block verbatim" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    // no closing fence: rather than reflow a half-parsed block, emit it as-is so
    // the (broken) document round-trips instead of losing bytes.
    const md =
        \\intro
        \\
        \\```2b4m
        \\sort Nat
        \\const Z: Nat
    ;
    const got = try formatLiterate(a, md);
    try testing.expectEqualStrings(md, got);
}
