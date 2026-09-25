//! Diagnostics: collected as data during checking, rendered late as
//! `path:line:col: error: message`. Multi-file: each diagnostic carries the FILE its offset
//! indexes into, passed explicitly at `add`.
//!
//! The file is a PARAMETER, never ambient state. It used to be a `current_file` field that
//! each task set on entry, which worked only because one task ran at a time: "I am the last
//! writer before my own `add`s" is an invariant several workers destroy silently — worker A
//! sets file 3, B sets 7, A's diagnostic renders against B's source. `render` CLAMPS a
//! past-the-end offset, so that misdirection degrades to a merely mislocated message rather
//! than a crash, which makes it invisible to the goldens. Passing the file removes the
//! invariant instead of documenting it.

const std = @import("std");

pub const FileSrc = struct {
    path: []const u8,
    source: []const u8,
};

pub const Diagnostic = struct {
    /// index into the driver's file list
    file: u32,
    /// byte offset into that file's source
    offset: u32,
    message: []const u8,
};

pub const Sink = struct {
    arena: std.mem.Allocator,
    list: std.ArrayList(Diagnostic) = .empty,

    pub fn init(arena: std.mem.Allocator) Sink {
        return .{ .arena = arena };
    }

    /// Record a diagnostic at `offset` in `file`. `file` indexes the driver's file list and
    /// MUST be the file `offset` refers to — see the note at the top on why it is explicit.
    pub fn add(self: *Sink, file: u32, offset: u32, comptime fmt: []const u8, args: anytype) !void {
        const msg = try std.fmt.allocPrint(self.arena, fmt, args);
        try self.list.append(self.arena, .{ .file = file, .offset = offset, .message = msg });
    }

    /// Render all diagnostics, ordered by (file, byte offset). Identical duplicates collapse:
    /// the demand model re-runs a step's read pass and its process pass, so a diagnostic keyed
    /// to the same (file, offset, message) can be recorded twice (e.g. an accelerant producer
    /// diagnosing on both passes) — the user should see it once.
    pub fn render(self: *Sink, w: *std.Io.Writer, files: []const FileSrc) !void {
        std.mem.sort(Diagnostic, self.list.items, {}, lessThan);
        var prev: ?Diagnostic = null;
        for (self.list.items) |d| {
            if (prev) |p| {
                if (p.file == d.file and p.offset == d.offset and std.mem.eql(u8, p.message, d.message)) continue;
            }
            prev = d;
            const f = files[d.file];
            // CLAMP: an offset is only meaningful against the file it was recorded for, and a
            // demand-engine bug can pair one with another (shorter) file — `findLineColumn`
            // would then index out of bounds and PANIC, turning a diagnosable defect into a
            // crash. Clamping degrades such a bug to a merely mislocated message.
            const off = @min(d.offset, @as(u32, @intCast(f.source.len)));
            const loc = std.zig.findLineColumn(f.source, off);
            try w.print("{s}:{d}:{d}: error: {s}\n", .{ f.path, loc.line + 1, loc.column + 1, d.message });
        }
    }

    fn lessThan(_: void, a: Diagnostic, b: Diagnostic) bool {
        if (a.file != b.file) return a.file < b.file;
        return a.offset < b.offset;
    }
};

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;

test "render: an offset past its file's end is CLAMPED, not a panic" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var sink: Sink = .init(arena);
    // an offset from a LONGER file, recorded against a short one (a demand-engine mispairing).
    const files = [_]FileSrc{.{ .path = "/t/short.b4m", .source = "sort Nat\n" }};
    try sink.add(0, 9_999, "stale offset", .{});
    var out: std.Io.Writer.Allocating = .init(arena);
    try sink.render(&out.writer, &files);
    // renders (no crash) and names the right file.
    try testing.expect(std.mem.indexOf(u8, out.written(), "/t/short.b4m") != null);
    try testing.expect(std.mem.indexOf(u8, out.written(), "stale offset") != null);
}

test "render: an in-range offset still reports its true line and column" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var sink: Sink = .init(arena);
    const files = [_]FileSrc{.{ .path = "/t/a.b4m", .source = "sort Nat\nconst Z: Nat\n" }};
    try sink.add(0, 9, "second line", .{}); // the 'c' of `const`
    var out: std.Io.Writer.Allocating = .init(arena);
    try sink.render(&out.writer, &files);
    try testing.expect(std.mem.indexOf(u8, out.written(), "/t/a.b4m:2:1:") != null);
}
