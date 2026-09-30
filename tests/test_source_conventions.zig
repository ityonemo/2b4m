//! SOURCE-CONVENTION gates — invariants the language cannot express, checked by reading the
//! source. Zig has no field privacy, so a lock discipline that says "touch this map only
//! through an accessor" is enforceable only by convention plus a test like this one.
//!
//! Each gate names the defect it prevents. A gate that fires is not style pedantry: it is the
//! exact shape of a bug that has already happened here.

const std = @import("std");

/// The Context side tables guarded by `side_lock`. An access DURING proving must go through an
/// accessor that takes the lock: these are hashmaps, they REHASH on growth, and an unguarded
/// read racing a concurrent publish walks freed metadata. One such read segfaulted on
/// 2026-09-29 (`inheritAxioms`); auditing found four more reach-past accesses.
const guarded_tables = [_][]const u8{
    "accelerated",
    "axiom_origin",
    "axiom_taint",
    "hole_taint",
    "model_discharged",
    "model_define_targets",
    "holes_reached",
    "expand_linted",
    "fact_trace",
};

/// Files allowed to touch those tables directly:
///   Context.zig — owns them; its accessors are what everyone else must use.
///   root.zig    — the REPORTING reads, which run after quiescence with no task publishing.
///                 Unguarded by design, documented at the `side_lock` declaration.
const allowed_direct = [_][]const u8{ "Context.zig", "root.zig" };

const receivers = [_][]const u8{ "self.", "ctx.", "context." };

test "Context side tables are reached only through their accessors" {
    const gpa = std.testing.allocator;
    var threaded: std.Io.Threaded = .init(gpa, .{});
    defer threaded.deinit();
    const io = threaded.io();

    var offenders: std.ArrayList(u8) = .empty;
    defer offenders.deinit(gpa);

    var dir = try std.Io.Dir.cwd().openDir(io, "src", .{ .iterate = true });
    defer dir.close(io);

    var walker = try dir.walk(gpa);
    defer walker.deinit();

    while (try walker.next(io)) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.basename, ".zig")) continue;

        var allowed = false;
        for (allowed_direct) |ok| if (std.mem.eql(u8, entry.basename, ok)) {
            allowed = true;
        };
        if (allowed) continue;

        const source = try dir.readFileAlloc(io, entry.path, gpa, .limited(8 << 20));
        defer gpa.free(source);

        var line_no: usize = 1;
        var it = std.mem.splitScalar(u8, source, '\n');
        while (it.next()) |line| : (line_no += 1) {
            // comments may name a table freely — that is how the discipline is explained.
            const code = if (std.mem.indexOf(u8, line, "//")) |c| line[0..c] else line;
            for (guarded_tables) |table| {
                for (receivers) |recv| {
                    const needle = try std.fmt.allocPrint(gpa, "{s}{s}.", .{ recv, table });
                    defer gpa.free(needle);
                    if (std.mem.indexOf(u8, code, needle) != null) {
                        const note = try std.fmt.allocPrint(gpa, "  src/{s}:{d}: `{s}` touched directly\n", .{ entry.path, line_no, table });
                        defer gpa.free(note);
                        try offenders.appendSlice(gpa, note);
                    }
                }
            }
        }
    }

    if (offenders.items.len != 0) {
        std.debug.print(
            \\
            \\A Context side table guarded by `side_lock` is accessed directly:
            \\
            \\{s}
            \\Add or use an accessor on Context that takes `side_lock`. See the LOCK ORDER note
            \\at the `side_lock` declaration in src/Context.zig: these maps rehash on growth, so
            \\an unguarded read racing a publish walks freed metadata.
            \\
        , .{offenders.items});
        return error.UnguardedSideTableAccess;
    }
}
