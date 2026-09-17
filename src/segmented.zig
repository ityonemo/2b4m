//! A NON-MOVING append-only store: `Segmented(T)`.
//!
//! WHY THIS EXISTS: the InternPool's reads are lock-free BY DESIGN (see
//! `InternPool.write_mutex`) — a reader takes no lock, so it never coordinates with a
//! concurrent writer. That is only sound if an element, once appended, never MOVES. A plain
//! `ArrayList` reallocates on growth and copies its elements, so a reader holding a pointer
//! (or, worse, a SLICE — `InternPool.sortData` hands out `qualifiers` as a live slice into
//! `extra`) into the old buffer is left pointing at freed memory the instant another thread
//! appends. That is the "CONCURRENCY PREREQUISITE (NOT yet satisfied)" the pool's own header
//! calls out; this file satisfies it.
//!
//! THE STRUCTURE: a table of exponentially-growing BLOCKS. Element `i` lives in block
//! `b = log2(i/first_len + 1)` at a fixed offset within it. A block is allocated once and
//! never resized, never copied, never freed (the store is append-only and arena-backed), so
//! `&get(i)` is stable for the life of the pool. Growth allocates a NEW block and publishes
//! its pointer into the block table; existing blocks are untouched, which is exactly the
//! property a lock-free reader needs.
//!
//! Exponential (rather than fixed-size) blocks keep the block table tiny — 32 entries
//! addresses 2^32 elements from a small first block — so `get` is an index, a shift and two
//! loads with no allocation-size bookkeeping.
//!
//! SLICES ACROSS A BOUNDARY: a run appended contiguously may still straddle two blocks, and
//! a `[]T` cannot span them. `appendSliceContiguous` therefore PADS to the next block when a
//! run would straddle, so any run appended through it is guaranteed sliceable by
//! `sliceContiguous`. The padding is dead space (a few words, bounded by the run length) —
//! the price of handing out stable slices without copying. Callers that never slice (plain
//! `append`) pay nothing.

const std = @import("std");
const Allocator = std.mem.Allocator;

/// Number of elements in the first block. Each later block DOUBLES: 1024, 2048, 4096, …
/// so block `b` holds `first_len << b` elements starting at `first_len * (2^b - 1)`.
const first_len_log2 = 10;
const first_len: u32 = 1 << first_len_log2;

/// The block table's fixed capacity. Doubling from `first_len`, 32 blocks address
/// `first_len * (2^32 - 1)` elements — far past what a u32 index can name, so the table
/// never grows and a reader never sees it move.
const max_blocks = 32;

pub fn Segmented(comptime T: type) type {
    return struct {
        const Self = @This();

        /// Pointers to each allocated block. Only entries `< block_count` are live. The
        /// table itself is a fixed inline array, so appending a block never moves the
        /// table — a reader walking it races nothing but the count.
        blocks: [max_blocks][*]T = undefined,
        /// How many blocks are allocated.
        block_count: u32 = 0,
        /// Number of elements appended — the store's logical length.
        len: u32 = 0,

        pub const empty: Self = .{};

        /// Which block holds element `i`, and its offset within that block.
        ///
        /// Block `b` spans `first_len << b` elements based at `first_len * (2^b - 1)`, so
        /// `i / first_len + 1` lands in the power-of-two bucket `2^b` and the block is that
        /// value's bit-length minus one — one shift and one `@clz`.
        fn locate(i: u32) struct { block: u32, offset: u32 } {
            const bucket = (i >> first_len_log2) + 1;
            const block: u32 = 31 - @clz(bucket);
            return .{ .block = block, .offset = i - baseOf(block) };
        }

        /// The index of block `b`'s first element: `first_len * (2^b - 1)`.
        fn baseOf(b: u32) u32 {
            return first_len * ((@as(u32, 1) << @intCast(b)) - 1);
        }

        /// How many elements block `b` holds.
        fn blockLen(b: u32) u32 {
            return first_len << @intCast(b);
        }

        /// Element `i` by value. Lock-free: reads only an existing block, which never moves.
        pub fn get(self: *const Self, i: u32) T {
            const spot = locate(i);
            return self.blocks[spot.block][spot.offset];
        }

        /// A STABLE pointer to element `i`. Valid for the life of the store — this is the
        /// whole point of the type.
        pub fn at(self: *const Self, i: u32) *T {
            const spot = locate(i);
            return &self.blocks[spot.block][spot.offset];
        }

        /// Overwrite element `i` (the store is append-only in LENGTH, but an element may be
        /// patched in place — e.g. back-patching a payload after its children are known).
        pub fn set(self: *Self, i: u32, value: T) void {
            self.at(i).* = value;
        }

        /// Ensure block coverage for at least `n` more elements.
        fn ensureUnused(self: *Self, arena: Allocator, n: u32) Allocator.Error!void {
            while (self.len + n > self.capacity()) try self.addBlock(arena);
        }

        /// Total elements the allocated blocks cover — the base of the first UNallocated
        /// block, since block bases are exactly the running totals.
        fn capacity(self: *const Self) u32 {
            return baseOf(self.block_count);
        }

        fn addBlock(self: *Self, arena: Allocator) Allocator.Error!void {
            if (self.block_count >= max_blocks) return error.OutOfMemory;
            const b = self.block_count;
            const mem = try arena.alloc(T, blockLen(b));
            self.blocks[b] = mem.ptr;
            // publish the pointer BEFORE the count: a reader that sees the new count must
            // already see a valid pointer. (Single-threaded today; ordering is free and
            // makes the invariant explicit for when workers land.)
            @atomicStore(u32, &self.block_count, b + 1, .release);
        }

        /// Iterate every element in order. The store is append-only, so a walk started at a
        /// given `len` stays valid even if another thread appends behind it.
        pub const Iterator = struct {
            store: *const Self,
            i: u32 = 0,
            end: u32,
            pub fn next(it: *Iterator) ?T {
                if (it.i >= it.end) return null;
                defer it.i += 1;
                return it.store.get(it.i);
            }
        };

        pub fn iterator(self: *const Self) Iterator {
            return .{ .store = self, .end = self.len };
        }

        /// Append one element; returns its index.
        pub fn append(self: *Self, arena: Allocator, value: T) Allocator.Error!u32 {
            try self.ensureUnused(arena, 1);
            const i = self.len;
            const spot = locate(i);
            self.blocks[spot.block][spot.offset] = value;
            self.len = i + 1;
            return i;
        }

        /// Append `values` so they are CONTIGUOUS — skipping ahead when the run would
        /// straddle a block boundary. Returns the start index, from which
        /// `sliceContiguous(start, values.len)` is valid. Use this for any run a caller will
        /// later slice; `append` is fine for standalone elements.
        ///
        /// Blocks DOUBLE in size, so a run bigger than the current block always fits in a
        /// later one: this walks forward, skipping each too-small block's tail, until it
        /// reaches one with room (the corpus serializes 200k-word terms as single runs). The
        /// skipped elements are dead space — the price of stable slices without copying.
        pub fn appendSliceContiguous(self: *Self, arena: Allocator, values: []const T) Allocator.Error!u32 {
            const n: u32 = @intCast(values.len);
            if (n == 0) return self.len;
            const start = while (true) {
                const spot = locate(self.len);
                if (spot.block >= self.block_count) { // the block isn't allocated yet
                    try self.addBlock(arena);
                    continue;
                }
                const room = blockLen(spot.block) - spot.offset;
                if (room >= n) break self.len;
                self.len += room; // skip this block's tail; the next one is twice as big
            };
            const spot = locate(start);
            @memcpy(self.blocks[spot.block][spot.offset..][0..n], values);
            self.len = start + n;
            return start;
        }

        /// A slice of `len` elements from `start`. Only valid when the run was appended via
        /// `appendSliceContiguous` (or is otherwise known not to straddle) — asserted here.
        pub fn sliceContiguous(self: *const Self, start: u32, len: u32) []const T {
            if (len == 0) return &.{};
            const spot = locate(start);
            std.debug.assert(spot.offset + len <= blockLen(spot.block)); // caller must not straddle
            return self.blocks[spot.block][spot.offset..][0..len];
        }
    };
}

test "segmented: append and read back across many blocks" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u32) = .empty;
    const n = 100_000; // spans many blocks
    for (0..n) |i| {
        const idx = try s.append(arena, @intCast(i * 3));
        try std.testing.expectEqual(@as(u32, @intCast(i)), idx);
    }
    try std.testing.expectEqual(@as(u32, n), s.len);
    for (0..n) |i| try std.testing.expectEqual(@as(u32, @intCast(i * 3)), s.get(@intCast(i)));
}

test "segmented: an element's ADDRESS is stable across growth (the whole point)" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u32) = .empty;
    _ = try s.append(arena, 42);
    const p0 = s.at(0);
    // grow far past the first block — an ArrayList would have reallocated many times.
    for (0..200_000) |i| _ = try s.append(arena, @intCast(i));
    try std.testing.expectEqual(p0, s.at(0)); // same address
    try std.testing.expectEqual(@as(u32, 42), p0.*); // and the value survived
}

test "segmented: a contiguous run is sliceable even when it would straddle a block" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u32) = .empty;
    // fill to 8 short of the first block boundary, then append a 32-run: it must not straddle.
    for (0..first_len - 8) |i| _ = try s.append(arena, @intCast(i));
    var run: [32]u32 = undefined;
    for (&run, 0..) |*v, i| v.* = @intCast(1000 + i);
    const start = try s.appendSliceContiguous(arena, &run);
    const got = s.sliceContiguous(start, run.len);
    try std.testing.expectEqualSlices(u32, &run, got);
    // and the padded-over region did not corrupt the earlier data
    for (0..first_len - 8) |i| try std.testing.expectEqual(@as(u32, @intCast(i)), s.get(@intCast(i)));
}

test "segmented: every index maps into its block, especially at boundaries" {
    // `locate` is the load-bearing arithmetic: an off-by-one at a block boundary corrupts
    // silently rather than crashing, so pin the exact boundaries plus a dense prefix.
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u32) = .empty;
    const n = first_len * 8; // spans blocks 0..3
    for (0..n) |i| _ = try s.append(arena, @intCast(i));
    for (0..n) |i| try std.testing.expectEqual(@as(u32, @intCast(i)), s.get(@intCast(i)));

    // each block's first and last index resolves inside that block
    const S = Segmented(u32);
    var b: u32 = 0;
    while (b < 4) : (b += 1) {
        const base = S.baseOf(b);
        const last = base + S.blockLen(b) - 1;
        try std.testing.expectEqual(b, S.locate(base).block);
        try std.testing.expectEqual(@as(u32, 0), S.locate(base).offset);
        try std.testing.expectEqual(b, S.locate(last).block);
        try std.testing.expectEqual(S.blockLen(b) - 1, S.locate(last).offset);
    }
}

test "segmented: a run that fits exactly does not pad; one that overruns does" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u32) = .empty;
    for (0..first_len - 4) |i| _ = try s.append(arena, @intCast(i));
    // exactly fills block 0: no padding, so it starts right where we are.
    const exact = [_]u32{ 1, 2, 3, 4 };
    const at_exact = try s.appendSliceContiguous(arena, &exact);
    try std.testing.expectEqual(@as(u32, first_len - 4), at_exact);
    try std.testing.expectEqualSlices(u32, &exact, s.sliceContiguous(at_exact, exact.len));
    // the next run begins block 1 with no padding needed
    const next = [_]u32{ 9, 9 };
    const at_next = try s.appendSliceContiguous(arena, &next);
    try std.testing.expectEqual(@as(u32, first_len), at_next);
    try std.testing.expectEqualSlices(u32, &next, s.sliceContiguous(at_next, next.len));
}

test "segmented: a run far LARGER than the first block still lands contiguous" {
    // The corpus serializes very deep terms as single runs (term.zig round-trips a
    // 200k-node term), so a contiguous run routinely dwarfs the first block. Blocks double,
    // so the append walks forward until one has room.
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u32) = .empty;
    const big = try arena.alloc(u32, 200_000);
    for (big, 0..) |*v, i| v.* = @intCast(i);
    const start = try s.appendSliceContiguous(arena, big);
    try std.testing.expectEqualSlices(u32, big, s.sliceContiguous(start, @intCast(big.len)));

    // and a second one after it, so the walk-forward works from a non-empty store
    const start2 = try s.appendSliceContiguous(arena, big);
    try std.testing.expect(start2 >= start + big.len);
    try std.testing.expectEqualSlices(u32, big, s.sliceContiguous(start2, @intCast(big.len)));
}

test "segmented: byte element type (string_bytes shape)" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var s: Segmented(u8) = .empty;
    const a = try s.appendSliceContiguous(arena, "hello");
    const b = try s.appendSliceContiguous(arena, "world");
    try std.testing.expectEqualStrings("hello", s.sliceContiguous(a, 5));
    try std.testing.expectEqualStrings("world", s.sliceContiguous(b, 5));
}
