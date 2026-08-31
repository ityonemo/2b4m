//! The interned entity pool — a uniform, deduplicated store for the denotations bpa's
//! checker works with (types/sorts/symbols/statements/models/files), modeled on the Zig
//! compiler's `InternPool` (src/InternPool.zig in the zig tree).
//!
//! This is the SKELETON (first slice of the data-model rebuild). It proves the core
//! mechanism against ONE interned kind — `file` — where deduplication is the whole
//! point: the same resolved path interns to the SAME `Index` (the job the Context's
//! hand-rolled `by_path` map does today, generalized). Later kinds (sort, symbol,
//! statement, model) are added as `Key`/`Tag` variants on this same machinery.
//!
//! THE THREE-TIER SHAPE (Zig's design, adopted):
//!   * `Index` — a dense `enum(u32)` handle. Low values are RESERVED for well-known
//!     entries (like a builtin `Prop` sort would be); dynamic entries follow.
//!   * `Key` — the ERGONOMIC tagged union you construct with and match on. This is the
//!     public face: `get(key) -> Index`, `keyOf(index) -> Key`.
//!   * `Item {tag, data}` + `extra` — the PACKED storage. `data` is either an inline
//!     payload, another `Index`, or an offset into `extra` (the variable-length spill).
//!     You never touch this directly; `get`/`keyOf` are the only bridge.
//!
//! DEDUP: always-intern. `get` hashes the key, structurally compares against existing
//! entries, and returns the existing `Index` on a match (else appends). Two keys that
//! are structurally equal collapse to one `Index` — which for `file` means one id per
//! physical file, shared across every importer.
//!
//! `extra` ENCODING is reflection-based (`addExtra(anytype)` / `extraData(T)`): a payload
//! struct's fields are serialized field-by-field as `u32` (enum-cast for ids, bit-cast
//! for scalars) and read back the same way — so a new variable-length kind is a payload
//! struct + one `keyOf` case, no hand-written pack/unpack.

const std = @import("std");

const InternPool = @This();

/// A string id IS a pool `Index` (the `.string` kind) — so a string, a file, and every
/// future entity share ONE id space, distinguished only by their item `tag`. Kept as a
/// public alias because the name `StrId` reads clearly across the codebase (a `StrId`
/// value is understood to name a string, even though the type is the general `Index`).
pub const StrId = Index;

/// The packed store: one `Item` per interned entity, indexed by `@intFromEnum(Index)`.
items: std.MultiArrayList(Item) = .empty,
/// Variable-length payload spill. An `Item.data` may be an offset into here; the run of
/// `u32`s starting there decodes (via reflection) into a payload struct.
extra: std.ArrayList(u32) = .empty,
/// Raw byte store for `.string` items. An interned string's bytes live here as a
/// contiguous run (its `String` payload in `extra` records the offset + length).
string_bytes: std.ArrayList(u8) = .empty,
/// Dedup map: structural key hash -> Index. `void` value; the Index is recovered by
/// re-deriving the key from the stored item (adapter context compares against `items`).
map: std.HashMapUnmanaged(Index, void, MapContext, std.hash_map.default_max_load_percentage) = .empty,

arena: std.mem.Allocator,

/// A dense handle into the pool. Non-exhaustive: low values are reserved for well-known
/// entries, `_` covers dynamically-interned ones. (No reserved entries yet — the shape is
/// fixed so e.g. a `Prop` sort can claim index 0 later.)
pub const Index = enum(u32) { _ };

/// The packed storage form. `tag` discriminates; `data` is interpreted per the tag's doc
/// (inline value, an `Index`, or an offset into `extra`).
pub const Item = struct {
    tag: Tag,
    data: u32,
};

/// One kind per interned entity family. Each variant documents how to read `Item.data`.
pub const Tag = enum(u8) {
    /// An interned string (identifier/path). `data` is an offset into `extra` decoding to
    /// `String` (byte offset + length into `string_bytes`).
    string,
    /// A source file, identified by its resolved-path string. `data` is an offset into
    /// `extra` decoding to `File` (the path's string `Index`).
    file,
};

/// The ERGONOMIC view — what callers build and match on. One variant per `Tag`.
pub const Key = union(enum) {
    /// A string's bytes. Interned by CONTENT: equal bytes collapse to one `Index`.
    string: []const u8,
    file: File,

    /// A source file's interned payload: its resolved-path string id. Identity IS the
    /// path — two importers of the same file get the same `Index`.
    pub const File = struct { path: StrId };

    /// `.string` storage payload: where the bytes live in `string_bytes`.
    const String = struct { off: u32, len: u32 };
};

// -- the dedup map's hashing/equality, computed over the ergonomic Key ----------------

const MapContext = struct {
    pool: *const InternPool,

    pub fn hash(ctx: MapContext, index: Index) u64 {
        return hashKey(ctx.pool.keyOf(index));
    }
    pub fn eql(ctx: MapContext, a: Index, b: Index) bool {
        return keyEql(ctx.pool.keyOf(a), ctx.pool.keyOf(b));
    }
};

/// Adapter so we can look up / insert by a Key we haven't stored yet (getOrPutAdapted).
const KeyAdapter = struct {
    pool: *const InternPool,

    pub fn hash(_: KeyAdapter, key: Key) u64 {
        return hashKey(key);
    }
    pub fn eql(ctx: KeyAdapter, key: Key, index: Index) bool {
        return keyEql(key, ctx.pool.keyOf(index));
    }
};

fn hashKey(key: Key) u64 {
    var h = std.hash.Wyhash.init(0);
    std.hash.autoHash(&h, std.meta.activeTag(key));
    switch (key) {
        .string => |bytes| h.update(bytes), // identity IS the bytes
        .file => |f| std.hash.autoHash(&h, f.path),
    }
    return h.final();
}

fn keyEql(a: Key, b: Key) bool {
    if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
    return switch (a) {
        .string => std.mem.eql(u8, a.string, b.string),
        .file => a.file.path == b.file.path,
    };
}

pub fn init(arena: std.mem.Allocator) InternPool {
    return .{ .arena = arena };
}

/// Intern a key: return the existing `Index` if a structurally-equal entry exists, else
/// append a new packed `Item` (+ `extra`) and record it. The always-intern entry point.
pub fn get(self: *InternPool, key: Key) std.mem.Allocator.Error!Index {
    const gop = try self.map.getOrPutContextAdapted(self.arena, key, KeyAdapter{ .pool = self }, MapContext{ .pool = self });
    if (gop.found_existing) return gop.key_ptr.*;

    const index: Index = @enumFromInt(self.items.len);
    switch (key) {
        .string => |bytes| {
            const bytes_off: u32 = @intCast(self.string_bytes.items.len);
            try self.string_bytes.appendSlice(self.arena, bytes);
            const off = try self.addExtra(Key.String{ .off = bytes_off, .len = @intCast(bytes.len) });
            try self.items.append(self.arena, .{ .tag = .string, .data = off });
        },
        .file => |f| {
            const off = try self.addExtra(Key.File{ .path = f.path });
            try self.items.append(self.arena, .{ .tag = .file, .data = off });
        },
    }
    gop.key_ptr.* = index;
    return index;
}

/// Reconstruct the ergonomic `Key` from an `Index` — the inverse of `get`'s packing.
pub fn keyOf(self: *const InternPool, index: Index) Key {
    const item = self.items.get(@intFromEnum(index));
    return switch (item.tag) {
        .string => {
            const s = self.extraData(Key.String, item.data);
            return .{ .string = self.string_bytes.items[s.off .. s.off + s.len] };
        },
        .file => .{ .file = self.extraData(Key.File, item.data) },
    };
}

/// Number of interned entries.
pub fn count(self: *const InternPool) usize {
    return self.items.len;
}

// -- string convenience (the StrId façade rests on these) -----------------------------

/// Intern bytes as a string, returning its `StrId` (== a pool `Index`). Content-deduped.
pub fn internString(self: *InternPool, bytes: []const u8) std.mem.Allocator.Error!StrId {
    return self.get(.{ .string = bytes });
}

/// The bytes of an interned string. Asserts `id` names a `.string` item.
pub fn stringBytes(self: *const InternPool, id: StrId) []const u8 {
    std.debug.assert(self.items.get(@intFromEnum(id)).tag == .string);
    return self.keyOf(id).string;
}

// -- reflection-based `extra` encoding ------------------------------------------------
// A payload struct is serialized field-by-field as `u32`: enum fields by their integer
// tag, integer fields by bit-cast. Reading reverses it. Field ORDER is the contract.

/// Append `payload`'s fields to `extra` as a run of `u32`; return the start offset.
fn addExtra(self: *InternPool, payload: anytype) std.mem.Allocator.Error!u32 {
    const T = @TypeOf(payload);
    const fields = @typeInfo(T).@"struct".fields;
    const off: u32 = @intCast(self.extra.items.len);
    try self.extra.ensureUnusedCapacity(self.arena, fields.len);
    inline for (fields) |field| {
        const v = @field(payload, field.name);
        self.extra.appendAssumeCapacity(encodeField(v));
    }
    return off;
}

/// Decode a `T` payload from `extra` starting at `off` — the inverse of `addExtra`.
fn extraData(self: *const InternPool, comptime T: type, off: u32) T {
    const fields = @typeInfo(T).@"struct".fields;
    var result: T = undefined;
    inline for (fields, 0..) |field, i| {
        @field(result, field.name) = decodeField(field.type, self.extra.items[off + i]);
    }
    return result;
}

fn encodeField(v: anytype) u32 {
    return switch (@typeInfo(@TypeOf(v))) {
        .@"enum" => @intFromEnum(v),
        .int => @bitCast(v),
        else => @compileError("InternPool extra: unsupported field type " ++ @typeName(@TypeOf(v))),
    };
}

fn decodeField(comptime T: type, raw: u32) T {
    return switch (@typeInfo(T)) {
        .@"enum" => @enumFromInt(raw),
        .int => @bitCast(raw),
        else => @compileError("InternPool extra: unsupported field type " ++ @typeName(T)),
    };
}

test "strings intern by content and round-trip their bytes" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = .init(arena_state.allocator());

    const add = try pool.internString("add");
    const zero = try pool.internString("zero");
    const add2 = try pool.internString("add");

    try std.testing.expectEqual(add, add2); // DEDUP: equal bytes collapse to one Index
    try std.testing.expect(add != zero);
    try std.testing.expectEqualStrings("add", pool.stringBytes(add));
    try std.testing.expectEqualStrings("zero", pool.stringBytes(zero));
    try std.testing.expectEqual(@as(usize, 2), pool.count()); // only two strings stored
}

test "file interns by path: same path -> same Index, distinct paths -> distinct" {
    var arena_state: std.heap.ArenaAllocator = .init(std.testing.allocator);
    defer arena_state.deinit();
    var pool: InternPool = .init(arena_state.allocator());

    const p_int = try pool.internString("std/integer.bpa");
    const p_nat = try pool.internString("std/peano.bpa");

    const a = try pool.get(.{ .file = .{ .path = p_int } });
    const b = try pool.get(.{ .file = .{ .path = p_nat } });
    const a2 = try pool.get(.{ .file = .{ .path = p_int } }); // second importer, same file

    try std.testing.expectEqual(a, a2); // DEDUP: same path collapses to one Index
    try std.testing.expect(a != b); // distinct paths are distinct entities

    // round-trip: the Index reconstructs the original key (path StrId)
    try std.testing.expectEqual(p_int, pool.keyOf(a).file.path);
    try std.testing.expectEqual(p_nat, pool.keyOf(b).file.path);
    // a file entity's Index is distinct from its path's string Index (one id space)
    try std.testing.expect(@intFromEnum(a) != @intFromEnum(p_int));
}
