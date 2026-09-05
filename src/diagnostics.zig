//! Diagnostics: collected as data during checking, rendered late as
//! `path:line:col: error: message`. Multi-file: each diagnostic is stamped
//! with the file being processed (`Sink.current_file`, set by the driver).

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
    /// stamped onto every added diagnostic; the driver sets this before
    /// processing each file (and the elaborator swaps it while elaborating a
    /// schema defined in another file)
    current_file: u32 = 0,

    pub fn init(arena: std.mem.Allocator) Sink {
        return .{ .arena = arena };
    }

    pub fn add(self: *Sink, offset: u32, comptime fmt: []const u8, args: anytype) !void {
        const msg = try std.fmt.allocPrint(self.arena, fmt, args);
        try self.list.append(self.arena, .{ .file = self.current_file, .offset = offset, .message = msg });
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
            const loc = std.zig.findLineColumn(f.source, d.offset);
            try w.print("{s}:{d}:{d}: error: {s}\n", .{ f.path, loc.line + 1, loc.column + 1, d.message });
        }
    }

    fn lessThan(_: void, a: Diagnostic, b: Diagnostic) bool {
        if (a.file != b.file) return a.file < b.file;
        return a.offset < b.offset;
    }
};
