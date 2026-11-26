//! `2b4m query instance <file> <hash>` — decode a `Schema{<hash>}` back into the
//! instantiation it names.
//!
//! THE PROBLEM. A schema instance is NAMED by hashing its arguments
//! (`Schema.instanceHash`), so a `--trace-facts` line or a bug report carries
//!
//!     [prove] task#11 = induction{2e5cfa07d7a3de11} in ns#36 (model#0)
//!
//! and that hash identifies the instance only in the sense that two identical instantiations
//! collide and two different ones (almost surely) do not. The preimage —
//! `(schema_name, params, args)` — lives on the IN-FLIGHT task, and nothing maps
//! `name -> payload`, so once the run ends the association is gone.
//!
//! THE APPROACH: RE-RUN AND MATCH ON THE NAME, never on a recomputed hash.
//!
//! The plan this implements (SCHEMA-HASH-DECODE-PLAN.md) proposed re-derivation: enumerate
//! candidate instantiations, recompute `instanceHash` for each, report the matches. That is
//! the right instinct — store nothing, no side table to keep in sync — but recomputing the
//! hash means reproducing, exactly:
//!
//!   - SIX per-accelerant `termHash` recipes, five identical and `Specialize` mixing in an
//!     arg count plus a head-local flavour (`Specialize.zig:245`);
//!   - `freeFvarParams`' extension of the parameter list under a model (`Prove.zig:1812`);
//!   - `hashEntity`'s reserved-slot rule, where a non-named Item hashes its raw value
//!     (`Schema.zig:91`);
//!   - and the model-transfer asymmetry, the hash being over `args` while `args_source` is
//!     also retained.
//!
//! Every one of those is a way to compute a DIFFERENT number and report "no match" on a hash
//! that does decode — a confidently wrong answer, which is worse than no tool. So this does
//! not recompute anything: it re-runs the check and compares the queried hash against the
//! name the ENGINE minted. The hashing is then correct by construction, because the engine
//! did it. The four hazards above do not apply; they are the engine's business and it already
//! handles them.
//!
//! What this costs is a full check per query, which the plan explicitly allows ("a slow linear
//! search is acceptable — the error path does not need to be fast").
//!
//! And it degrades honestly: no match means "no instantiation in this run hashes to that",
//! which is information — a stale hash from an edited file, or a different model.
//!
//! NOTE this module does CHECK, unlike its siblings under `query/` (which never elaborate).
//! It has to: a hash exists only as a product of elaboration, so there is nothing to read
//! without running the prover.

const std = @import("std");
const Allocator = std.mem.Allocator;
const root = @import("../root.zig");
const diagnostics = @import("../diagnostics.zig");
const Context = @import("../Context.zig");

pub const Result = struct {
    text: []const u8,
    ok: bool,
};

/// Decode `hash` against `path`. `hash` may be a bare `2e5cfa07d7a3de11` or the full
/// `induction{2e5cfa07d7a3de11}` spelling, since those are what a reader has to hand.
pub fn instance(
    io: std.Io,
    arena: Allocator,
    path: []const u8,
    hash: []const u8,
    theorem: ?[]const u8,
    read_ctx: ?*anyopaque,
    read_fn: Context.ReadFileFn,
    std_root: []const u8,
) !Result {
    const wanted = normalize(hash);
    if (wanted.len == 0) {
        return .{ .text = "error: empty hash — pass `<hash>` or `Schema{<hash>}`\n", .ok = false };
    }

    // The ordinary STRICT check, with the decode flag set: a ProveTask reports its own
    // instance when the name matches (`ProveTask.decodeInstance`). Default `Verify` otherwise,
    // so every synthetic is minted by the code that always mints it — a decode that ran under
    // `--fast` could miss an instance whose task was admitted rather than produced.
    //
    // `theorem` MATTERS, and that is not obvious: WHICH instances exist is a function of what
    // the run demanded, so a hash minted by `check <file> <thm>` need not appear in a
    // whole-file check at all. Pass the same theorem the hash came from.
    const loaded = try root.loadProject(io, arena, &.{.{ .path = path, .theorem = theorem }}, read_ctx, read_fn, .custom, .{ .decode_instance = wanted }, std_root);

    const files = try arena.dupe(diagnostics.FileSrc, loaded.files);
    files[@intFromEnum(loaded.root_file)].path = path;
    if (loaded.sink.list.items.len > 0) {
        var out: std.Io.Writer.Allocating = .init(arena);
        loaded.sink.render(&out.writer, files) catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = false };
    }

    const found = loaded.context.decoded_instances.items;
    if (found.len == 0) {
        // Honest degradation, and the two likely causes are worth naming: a reader holding a
        // hash from an older run of an edited file, or one minted under a model this check
        // never reached.
        const msg = try std.fmt.allocPrint(arena,
            \\no instantiation in this run hashes to '{s}'
            \\  WHICH instances exist depends on what the run demanded, so pass the same
            \\  theorem the hash came from: `query instance <file> <hash> [theorem]`.
            \\  An ACCELERANT-minted name (`specialize{{A}}{{B}}`) also varies with WORKER
            \\  INTERLEAVING on a multi-theorem run: its inner hash covers the prover's
            \\  hygienic fvars, whose numbering follows the demand schedule. Re-run the
            \\  original check with `-j1 --sync-io` to get a reproducible one. A declared
            \\  schema's hash (`induction{{…}}`) is stable either way.
            \\
        , .{wanted});
        return .{ .text = msg, .ok = false };
    }

    var out: std.Io.Writer.Allocating = .init(arena);
    const w = &out.writer;
    for (found, 0..) |text, i| {
        if (i != 0) w.writeAll("\n") catch return error.OutOfMemory;
        w.writeAll(text) catch return error.OutOfMemory;
    }
    return .{ .text = try out.toOwnedSlice(), .ok = true };
}

/// Accept either spelling: a bare hash, or the full `Schema{hash}` as a trace line prints it.
/// Returns the bare instance hash in both cases, so `decodeInstance` has one comparison to make.
///
/// THE LAST brace group, not the first. An ACCELERANT mints a synthetic schema already named
/// `specialize{A}` (a `termHash` of its head formula, `common.zig:1373`), and `instanceHash`
/// then wraps THAT name, so the instance is `specialize{A}{B}` — two groups, of which only the
/// outer `{B}` is the instance hash. Taking the first group yielded `A}{B` and never matched
/// anything, which is how this was found.
fn normalize(hash: []const u8) []const u8 {
    const trimmed = std.mem.trim(u8, hash, " \t\r\n");
    if (std.mem.endsWith(u8, trimmed, "}")) {
        if (std.mem.lastIndexOfScalar(u8, trimmed[0 .. trimmed.len - 1], '{')) |open| {
            return trimmed[open + 1 .. trimmed.len - 1];
        }
    }
    return trimmed;
}

const testing = std.testing;

test "normalize accepts a bare hash and the full Schema{hash} spelling" {
    try testing.expectEqualStrings("2e5cfa07d7a3de11", normalize("2e5cfa07d7a3de11"));
    try testing.expectEqualStrings("2e5cfa07d7a3de11", normalize("induction{2e5cfa07d7a3de11}"));
    // A DOUBLE-HASH accelerant name: the synthetic schema is itself `tautology{aaa}`, so only
    // the OUTER group is the instance hash.
    try testing.expectEqualStrings("bbb", normalize("tautology{aaa}{bbb}"));
    // whitespace from a copy-paste out of a log
    try testing.expectEqualStrings("abc", normalize("  abc\n"));
}
