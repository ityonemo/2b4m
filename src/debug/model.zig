//! `2b4m debug model <file> [Name]` — a model's mapping surface, and what it LEAVES OUT.
//!
//! The reason this exists: an incomplete model does not report as an incomplete model. Omit
//! one `<-` discharge and the failure surfaces as a sort mismatch inside the SOURCE theory's
//! own proof — a file the author may never have opened (see PAINPOINTS.md, "An incomplete
//! model discharge reports as a bare sort mismatch").
//! The diagnostics now name the cause at the failure site; this is the other half, the
//! up-front checklist: for each source theory the model draws on, what does that theory
//! DECLARE, and which of those does this model not mention?
//!
//! Pure over the AST, like `taint`/`outline`: parse the file, parse each source theory it
//! names, compare by name. It never elaborates, so it reports the SURFACE a model covers, not
//! the obligation set a particular citation forces — that set is "whatever the proof actually
//! cited" and is only known at elaboration (see design/model-design.md). So an unmapped entry
//! here is not necessarily an error: a model need only cover what the theorems it transfers
//! reach, and `std` is full of deliberately partial models. It is a checklist to read when a
//! transfer fails, and the thing to diff when a transfer that used to work stops.
//!
//! Cross-file reads go through the caller's `ReadFileFn`, reusing the loader's `std/`-prefix
//! resolution — the same hook `query whereis` uses.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");
const Token = lexer.Token;

pub const Result = struct {
    text: []const u8,
    ok: bool,
};

pub const ReadFileFn = *const fn (ctx: ?*anyopaque, arena: Allocator, path: []const u8) anyerror![]const u8;

/// The source-theory bucket for UNQUALIFIED mappings — a theory declared in the same file as
/// the model. Not a legal identifier, so it can never collide with a real namespace name.
const local_ns = "<this file>";

/// One thing a source theory declares. `alias_target` is the qualified name this declaration
/// re-exports (`sort F = field_order.OrderedField`), else null for a root declaration.
///
/// The distinction matters for the unmapped report. Aliasing is identity-by-origin: `F` and
/// `field_order.OrderedField` are the SAME entity, so a model that maps the origin has
/// already mapped the alias and must not map it twice. Listing an alias as "unmapped" would
/// be a false positive — and `std` re-exports heavily, so it would be the common case.
const Entry = struct {
    name: []const u8,
    alias_target: ?[]const u8,
};

/// What a source theory declares, by kind — the surface a model may interpret or discharge.
/// `idents` are mapped with `:` (sorts, consts, opers, preds); `facts` are discharged with
/// `<-` (axioms, and holes, which are assumptions too).
const Surface = struct {
    idents: []const Entry,
    facts: []const Entry,
};

pub fn model(
    arena: Allocator,
    path: []const u8,
    source: []const u8,
    name: ?[]const u8,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    std_root: []const u8,
) Allocator.Error!Result {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);

    var p: parser.Parser = .init(arena, source, sink);
    const file = try p.parseFile();

    var out: std.Io.Writer.Allocating = .init(arena);
    const w = &out.writer;

    if (sink.list.items.len > 0) {
        const files = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
        sink.render(w, &files) catch return error.OutOfMemory;
        return .{ .text = try out.toOwnedSlice(), .ok = false };
    }

    var q: Query = .{
        .arena = arena,
        .read_ctx = read_ctx,
        .read_fn = read_fn,
        .std_root = std_root,
        .path = path,
        .source = source,
        .out = w,
    };

    const ok = q.render(file, name) catch return error.OutOfMemory;
    return .{ .text = try out.toOwnedSlice(), .ok = ok };
}

const Query = struct {
    arena: Allocator,
    read_ctx: ?*anyopaque,
    read_fn: ReadFileFn,
    std_root: []const u8,
    path: []const u8,
    source: []const u8,
    out: *std.Io.Writer,

    fn render(self: *Query, file: ast.File, want: ?[]const u8) !bool {
        var found = false;
        var any = false;
        for (file.decls) |decl| {
            const m = switch (decl) {
                .model => |mo| mo,
                else => continue,
            };
            const mname = self.text(m.name);
            if (want) |n| {
                if (!std.mem.eql(u8, n, mname)) continue;
            }
            found = true;
            if (any) try self.out.writeAll("\n");
            any = true;
            try self.one(file, m, mname);
        }
        if (want) |n| {
            if (!found) {
                try self.out.print("error: no model '{s}' in {s}\n", .{ n, self.path });
                return false;
            }
        } else if (!found) {
            try self.out.print("{s}: no models\n", .{self.path});
        }
        return true;
    }

    /// One model block: its mappings grouped by source theory, then the unmapped remainder.
    fn one(self: *Query, file: ast.File, m: @FieldType(ast.Decl, "model"), mname: []const u8) !void {
        const loc = std.zig.findLineColumn(self.source, m.name.start);
        try self.out.print("model {s}  ({s}:{d})\n", .{ mname, self.path, loc.line + 1 });

        // Collect every source qualifier this model names, in first-seen order. An
        // UNQUALIFIED source (`Thing: Part`) models a theory declared in THIS file, which is
        // the `local_ns` sentinel: it needs no path resolution and no second parse, and its
        // declared surface is the file we already have.
        var theories: std.ArrayList([]const u8) = .empty;
        for (m.identifiers) |im| try self.noteQualifier(&theories, self.mappingOf(im).source);
        for (m.obligations) |ob| try self.noteQualifier(&theories, ob.source);

        if (theories.items.len == 0) {
            try self.out.writeAll("  (maps nothing)\n");
            return;
        }

        // Every source name the model mentions, FULLY QUALIFIED (`field_order.add`). The
        // unmapped report matches against this whole set rather than one theory's slice,
        // because an alias's origin usually lives in a DIFFERENT theory.
        var mapped_idents: std.ArrayList([]const u8) = .empty;
        var mapped_facts: std.ArrayList([]const u8) = .empty;
        for (m.identifiers) |im| try mapped_idents.append(self.arena, self.text(self.mappingOf(im).source));
        for (m.obligations) |ob| try mapped_facts.append(self.arena, self.text(ob.source));

        // Everything the model names as a TARGET, plus the guard dischargers it nominates.
        // These are the model's own vocabulary, not source entities awaiting a mapping — and
        // in a same-file model the file declares BOTH theories, so without this the target
        // side reports as unmapped source.
        var targets: std.ArrayList([]const u8) = .empty;
        for (m.identifiers) |im| {
            try targets.append(self.arena, self.text(self.mappingOf(im).target));
            switch (im) {
                .basic => {},
                .refined_sort => |r| for (r.dischargers) |d| try targets.append(self.arena, self.text(d)),
                .closed_operation => |c| for (c.closure_facts) |f| try targets.append(self.arena, self.text(f)),
            }
        }
        for (m.obligations) |ob| try targets.append(self.arena, self.text(ob.target));
        // A target that is a REFINED sort (`sort Part = Thing where inPart`) carries its
        // guard predicate, which is the model's vocabulary too — reached through the sort
        // rather than named on a mapping line.
        for (file.decls) |d| {
            const srt = switch (d) {
                .sort => |srt| srt,
                else => continue,
            };
            const g = switch (srt) {
                .guarded => |g| g,
                else => continue,
            };
            if (!contains(targets.items, self.text(g.name))) continue;
            for (g.guards) |gu| try targets.append(self.arena, self.text(gu));
        }

        for (theories.items) |ns| {
            const is_local = std.mem.eql(u8, ns, local_ns);
            const resolved = if (is_local) self.path else findImportPath(self.source, self.path, ns, self.std_root, self.arena) catch null;
            if (is_local) {
                try self.out.print("\n  from this file  ({s})\n", .{self.path});
            } else {
                try self.out.print("\n  from {s}", .{ns});
                if (resolved) |rp| try self.out.print("  <<< {s}", .{rp});
                try self.out.writeAll("\n");
            }

            for (m.identifiers) |im| {
                const mp = self.mappingOf(im);
                const tail = self.qualifiedTail(mp.source, ns) orelse continue;
                try self.out.print("    {s}: {s}", .{ tail, self.text(mp.target) });
                try self.guardNote(im);
                try self.out.writeAll("\n");
            }
            for (m.obligations) |ob| {
                const tail = self.qualifiedTail(ob.source, ns) orelse continue;
                if (ob.projection) |pj| {
                    try self.out.print("    {s} <- {s}@{s}\n", .{ tail, self.text(ob.target), self.text(pj) });
                } else {
                    try self.out.print("    {s} <- {s}\n", .{ tail, self.text(ob.target) });
                }
            }

            // The checklist: what the theory declares that this model never mentions.
            const rp = resolved orelse {
                try self.out.writeAll("    (cannot resolve this theory's path; no unmapped report)\n");
                continue;
            };
            const surf = self.surfaceOf(rp) catch |e| {
                try self.out.print("    (cannot read {s}: {t}; no unmapped report)\n", .{ rp, e });
                continue;
            };
            try self.report("unmapped", ns, surf.idents, mapped_idents.items, targets.items, ":");
            try self.report("undischarged", ns, surf.facts, mapped_facts.items, targets.items, "<-");
        }
    }

    /// List what `ns` declares that the model never mentions — skipping aliases whose ORIGIN
    /// it does mention, since those are the same entity already mapped.
    fn report(
        self: *Query,
        label: []const u8,
        ns: []const u8,
        declared: []const Entry,
        mapped: []const []const u8,
        targets: []const []const u8,
        op: []const u8,
    ) !void {
        // A definition block (`oper f(...): <clauses>`) declares one axiom PER CLAUSE, all
        // under the operator's name, so a name can repeat here. Collapse repeats and say how
        // many clauses are owed — listing `segment` twice reads like a bug, not like arity.
        var missing: std.ArrayList([]const u8) = .empty;
        var clauses: std.ArrayList(u32) = .empty;
        for (declared) |d| {
            const qualified = if (std.mem.eql(u8, ns, local_ns))
                d.name
            else
                try std.fmt.allocPrint(self.arena, "{s}.{s}", .{ ns, d.name });
            if (contains(mapped, qualified)) continue;
            if (contains(targets, d.name)) continue;
            if (d.alias_target) |t| {
                if (contains(mapped, t)) continue;
            }
            if (indexOfName(missing.items, d.name)) |i| {
                clauses.items[i] += 1;
            } else {
                try missing.append(self.arena, d.name);
                try clauses.append(self.arena, 1);
            }
        }
        if (missing.items.len == 0) return;
        try self.out.print("    — {d} {s} ({s}):", .{ missing.items.len, label, op });
        for (missing.items, clauses.items, 0..) |n, c, i| {
            try self.out.print("{s} {s}", .{ if (i == 0) "" else ",", n });
            if (c > 1) try self.out.print(" x{d}", .{c});
        }
        try self.out.writeAll("\n");
    }

    /// A guarded mapping nominates its dischargers ON the `:` line — a refined-sort target
    /// takes `TGT(baseFact…)`, a closed operation takes `F -| closureFact…`. Those facts are
    /// part of what the model owes, so print them rather than only flagging the guard.
    fn guardNote(self: *Query, im: ast.IdentMapping) !void {
        switch (im) {
            .basic => {},
            .refined_sort => |r| try self.nominated("refined sort", r.dischargers),
            .closed_operation => |c| try self.nominated("closed operation", c.closure_facts),
        }
    }

    fn nominated(self: *Query, kind: []const u8, facts: []const Token) !void {
        try self.out.print("   [guarded {s}:", .{kind});
        for (facts, 0..) |f, i| {
            try self.out.print("{s} {s}", .{ if (i == 0) "" else ",", self.text(f) });
        }
        try self.out.writeAll("]");
    }

    fn mappingOf(self: *Query, im: ast.IdentMapping) ast.Mapping {
        _ = self;
        return switch (im) {
            .basic => |mp| mp,
            .refined_sort => |r| r.mapping,
            .closed_operation => |c| c.mapping,
        };
    }

    /// The qualifier of a `ns.name` source token, or null when unqualified.
    fn qualifierOf(self: *Query, tok: Token) ?[]const u8 {
        const t = self.text(tok);
        const dot = std.mem.indexOfScalar(u8, t, '.') orelse return null;
        return t[0..dot];
    }

    /// The `name` half of `ns.name`, but only when the qualifier is `ns`. For `local_ns`
    /// (a theory in this same file) the source is unqualified and IS the name.
    fn qualifiedTail(self: *Query, tok: Token, ns: []const u8) ?[]const u8 {
        const t = self.text(tok);
        const dot = std.mem.indexOfScalar(u8, t, '.') orelse
            return if (std.mem.eql(u8, ns, local_ns)) t else null;
        if (std.mem.eql(u8, ns, local_ns)) return null;
        if (!std.mem.eql(u8, t[0..dot], ns)) return null;
        return t[dot + 1 ..];
    }

    fn noteQualifier(self: *Query, list: *std.ArrayList([]const u8), tok: Token) !void {
        const ns = self.qualifierOf(tok) orelse local_ns;
        if (contains(list.items, ns)) return;
        try list.append(self.arena, ns);
    }

    /// Parse a source theory and collect what it declares, by kind.
    fn surfaceOf(self: *Query, file_path: []const u8) !Surface {
        const src = try self.read_fn(self.read_ctx, self.arena, file_path);
        const sink = try self.arena.create(diagnostics.Sink);
        sink.* = .init(self.arena);
        var p: parser.Parser = .init(self.arena, src, sink);
        const f = try p.parseFile();

        var idents: std.ArrayList(Entry) = .empty;
        var facts: std.ArrayList(Entry) = .empty;
        for (f.decls) |d| {
            const bucket: *std.ArrayList(Entry), const name: Token = switch (d) {
                .sort => |s| .{ &idents, ast.sortName(s) },
                .constant => |c| .{ &idents, ast.constantName(c) },
                .func => |fu| .{ &idents, ast.funcName(fu) },
                .pred => |pr| .{ &idents, ast.predName(pr) },
                .axiom, .hole => |a| .{ &facts, ast.axiomName(a) },
                else => continue,
            };
            const target: ?[]const u8 = if (ast.aliasOf(&d)) |al| tokenText(src, al.target) else null;
            try bucket.append(self.arena, .{ .name = tokenText(src, name), .alias_target = target });
        }
        return .{ .idents = idents.items, .facts = facts.items };
    }

    fn text(self: *const Query, t: Token) []const u8 {
        return self.source[t.start..t.end];
    }
};

fn indexOfName(hay: []const []const u8, needle: []const u8) ?usize {
    for (hay, 0..) |h, i| {
        if (std.mem.eql(u8, h, needle)) return i;
    }
    return null;
}

fn contains(hay: []const []const u8, needle: []const u8) bool {
    for (hay) |h| {
        if (std.mem.eql(u8, h, needle)) return true;
    }
    return false;
}

fn tokenText(source: []const u8, t: Token) []const u8 {
    return source[t.start..t.end];
}

/// Resolve theory namespace `ns` to its file path (loader's rule: `std/…` under std_root,
/// else relative to the declaring file's dir). Same rule as `query whereis`.
fn findImportPath(source: []const u8, path: []const u8, ns: []const u8, std_root: []const u8, arena: Allocator) !?[]const u8 {
    var lex: lexer.Lexer = .init(source);
    var prev: Token = .{ .tag = .eof, .start = 0, .end = 0 };
    var import_ns: ?[]const u8 = null;
    while (true) {
        const t = lex.next();
        if (t.tag == .eof) break;
        if (prev.tag == .keyword_theory and t.tag == .identifier) {
            import_ns = source[t.start..t.end];
        } else if (t.tag == .string and import_ns != null) {
            if (std.mem.eql(u8, import_ns.?, ns)) {
                const quoted = source[t.start..t.end];
                const raw = quoted[1 .. quoted.len - 1];
                if (std.mem.startsWith(u8, raw, "std/"))
                    return try std.fs.path.resolve(arena, &.{ std_root, raw["std/".len..] });
                return try std.fs.path.resolve(arena, &.{ std.fs.path.dirname(path) orelse ".", raw });
            }
            import_ns = null;
        }
        prev = t;
    }
    return null;
}
