//! The unit-test RIG: a Context + Engine + Site stood up in memory so a test can build terms
//! and call an accelerant's internals directly. Test infrastructure only — nothing in
//! production depends on this file.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("../InternPool.zig");
const term = @import("../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const SymId = term.SymId;
const Site = @import("Site.zig");
const kernel = @import("../kernel.zig");
const testing = std.testing;
const Context = @import("../Context.zig");
const Engine = @import("../Engine.zig");

/// A unit-test RIG: a real Context over one inline ring theory (`Int` with ZERO/add/mul/neg),
/// its symbols FETCHED through the engine, and a standalone `Site` whose pool the tests build
/// goal terms in. Shared by the tactic unit tests and Prove's own.
pub const Rig = struct {
    ctx: *Context,
    eng: *Engine,
    h: *Engine.Handle,
    site: *Site,
    file: InternPool.Index,
    ns: InternPool.Index,
    int: term.SortId,
    zero: term.SymId,
    add: term.SymId,
    mul: term.SymId,
    neg: term.SymId,
    succ: term.SymId,

    pub const source =
        \\sort Int
        \\const ZERO: Int
        \\oper add(a: Int, b: Int) => Int
        \\oper mul(a: Int, b: Int) => Int
        \\oper neg(a: Int) => Int
        \\oper succ(a: Int) => Int
    ;

    pub fn init(arena: std.mem.Allocator, io: std.Io) !Rig {
        const FetchTask = @import("../Engine/FetchTask.zig");
        const ctx = try FetchTask.fixtureCtx(arena, io, "/t/ring.b4m", source);
        const file = try ctx.fileIndex("/t/ring.b4m");
        const ns = try ctx.interner.namespace(.universe, file);
        const eng = try arena.create(Engine);
        eng.* = Engine.init(arena, ctx, ctx.io);
        for ([_][]const u8{ "Int", "ZERO", "add", "mul", "neg", "succ" }) |n| {
            _ = try eng.rack(try FetchTask.new(arena, .{ .file = file, .name = try ctx.interner.internString(n), .loc = 0 }));
        }
        try eng.run();
        try testing.expectEqual(@as(usize, 0), ctx.sink.list.items.len);
        const h = try arena.create(Engine.Handle);
        h.* = .{ .engine = eng, .self_index = @enumFromInt(0) };
        const pool = try arena.create(term.Pool);
        pool.* = .init(arena, ctx.gpa);
        const site = try arena.create(Site);
        site.* = .{
            .ctx = ctx,
            .h = h,
            .pool = pool,
            .source = source,
            .file = file,
            .ns = ns,
            .model = .universe,
            .self_key = null,
            .fresh_counter = try arena.create(u32),
            .ordinal_step = try arena.create(std.ArrayList(kernel.StepId)),
            .low_steps = try arena.create(std.ArrayList(kernel.Step)),
            .source_formulas = try arena.create(std.ArrayList(TermId)),
            .holes_used = try arena.create(std.ArrayList(InternPool.StrId)),
            .axioms_used = try arena.create(std.ArrayList(InternPool.Index)),
        };
        site.fresh_counter.* = 0;
        @constCast(site.ordinal_step).* = .empty;
        @constCast(site.low_steps).* = .empty;
        @constCast(site.source_formulas).* = .empty;
        site.holes_used.* = .empty;
        site.axioms_used.* = .empty;
        return .{
            .ctx = ctx,
            .eng = eng,
            .h = h,
            .site = site,
            .file = file,
            .ns = ns,
            .int = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "Int"))),
            .zero = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "ZERO"))),
            .add = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "add"))),
            .mul = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "mul"))),
            .neg = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "neg"))),
            .succ = @enumFromInt(@intFromEnum(try lookup(ctx, ns, "succ"))),
        };
    }

    fn lookup(ctx: *Context, ns: InternPool.Index, name: []const u8) !InternPool.Index {
        return ctx.idents.lookup(ctx.io, .{ .namespace = ns, .name = try ctx.interner.internString(name) }).?.done;
    }

    /// A free variable of the ring sort.
    pub fn v(self: Rig, name: []const u8) !TermId {
        return self.site.pool.add(.{ .fvar = .{ .name = try self.ctx.interner.internString(name), .sort = self.int } });
    }
    pub fn a2(self: Rig, sym: term.SymId, x: TermId, y: TermId) !TermId {
        return self.site.pool.addApp(.app, sym, &.{ x, y });
    }
    pub fn a1(self: Rig, sym: term.SymId, x: TermId) !TermId {
        return self.site.pool.addApp(.app, sym, &.{x});
    }
    pub fn eq(self: Rig, l: TermId, r: TermId) !TermId {
        return self.site.pool.add(.{ .eq = .{ .lhs = l, .rhs = r } });
    }
};
