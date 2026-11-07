//! The unit-test RIG: a Context + Engine + Prove stood up in memory so a test can build terms
//! and call an accelerant's internals directly. Test infrastructure only — nothing in
//! production depends on this file.

const std = @import("std");
const Allocator = std.mem.Allocator;
const InternPool = @import("../../../InternPool.zig");
const term = @import("../../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const SymId = term.SymId;
const Prove = @import("../Prove.zig");
const testing = std.testing;
const Context = @import("../../../Context.zig");
const Engine = @import("../../../Engine.zig");

/// A unit-test RIG: a real Context over one inline ring theory (`Int` with ZERO/add/mul/neg),
/// its symbols FETCHED through the engine, and a standalone `Prove` whose pool the tests build
/// goal terms in. Shared by the polynomial unit tests here and the op-reader tests in Prove.
pub const Rig = struct {
    ctx: *Context,
    eng: *Engine,
    h: *Engine.Handle,
    prove: *Prove,
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
        \\func add(a: Int, b: Int) => Int
        \\func mul(a: Int, b: Int) => Int
        \\func neg(a: Int) => Int
        \\func succ(a: Int) => Int
    ;

    pub fn init(arena: std.mem.Allocator, io: std.Io) !Rig {
        const FetchTask = @import("../../FetchTask.zig");
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
        const prove = try Prove.init(ctx, h, source, file, ns);
        return .{
            .ctx = ctx,
            .eng = eng,
            .h = h,
            .prove = prove,
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
        return self.prove.pool.add(.{ .fvar = .{ .name = try self.ctx.interner.internString(name), .sort = self.int } });
    }
    pub fn a2(self: Rig, sym: term.SymId, x: TermId, y: TermId) !TermId {
        return self.prove.pool.addApp(.app, sym, &.{ x, y });
    }
    pub fn a1(self: Rig, sym: term.SymId, x: TermId) !TermId {
        return self.prove.pool.addApp(.app, sym, &.{x});
    }
    pub fn eq(self: Rig, l: TermId, r: TermId) !TermId {
        return self.prove.pool.add(.{ .eq = .{ .lhs = l, .rhs = r } });
    }
};
