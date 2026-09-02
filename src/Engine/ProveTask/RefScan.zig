//! RefScan — the READ PASS's name enumeration (Step 8, W2).
//!
//! Given one proof step, enumerate every GLOBAL name candidate it references — the set
//! the read pass must resolve (IdentKV/FactKV: done → use, in_flight → suspend, absent →
//! rack a fetch) before the step can be truth-checked. See memory
//! `provetask-step-walk-design`.
//!
//! CLASSIFICATION (mirrors the eager resolvers' domains):
//!   - `axiom`/`theorem` justification refs are FACT-domain names — always global (a
//!     local step label never shadows a theorem citation; same as the eager
//!     resolveStatementRef, which never consulted labels).
//!   - Every other rule's refs (modus_ponens, intros/elims, hypothesis, predicate, an
//!     unpack's `from`, a case's `disj`) are LOCAL-ONLY step/block labels: resolved
//!     against LocalStepKV at process time; a miss there is an ERROR, not a fetch — so
//!     they are NOT enumerated here.
//!   - Names inside expressions (claim formulas, assume hypotheses, case goals/arm
//!     assumptions) are IDENT-domain candidates — except proof-local binders
//!     (LocalIdentKV: fix eigenvariables, unpack witnesses) and EXPRESSION-local binders
//!     (quantifier/lambda binders, tracked transiently during the expr walk).
//!   - Binder SORT tokens (fix/unpack sorts, quantifier binder sorts) and binder GUARD
//!     preds (`x: G where inH`) are IDENT-domain candidates.
//!   - A DOTTED token `ns.name` is a QUALIFIED reference: `ns` is itself an IDENT-domain
//!     candidate (an import), and the base name resolves in the imported namespace. The
//!     scanner splits on the FIRST dot only (deeper qualification errors at elaboration).
//!
//! The scan is PURE enumeration — no KV lookups, no racking, no diagnostics. It is
//! deliberately idempotent and cheap: the read pass re-runs it on every resume.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const Walk = @import("Walk.zig");

/// One global name candidate a step references.
pub const Ref = struct {
    /// the namespace qualifier (an import's local name), or null for a bare name
    ns: ?StrId,
    name: StrId,
    domain: Domain,
    /// source offset of the referencing token (for diagnostics)
    loc: u32,

    pub const Domain = enum {
        /// an axiom/theorem citation — resolved via FactKV (a ProveTask produces it)
        fact,
        /// a sort/const/func/pred/import — resolved via IdentKV (a FetchTask produces it)
        ident,
    };
};

arena: Allocator,
interner: *InternPool,
source: []const u8,
/// consulted to SKIP proof-local binders (fix eigenvariables, unpack witnesses)
walk: *const Walk,

out: std.ArrayList(Ref) = .empty,
seen: std.AutoHashMapUnmanaged(SeenKey, void) = .empty,
/// expression-local binders (quantifier/lambda), innermost-last; mark/truncate scoping
expr_locals: std.ArrayList(StrId) = .empty,

const SeenKey = struct { ns: StrId, name: StrId, domain: Ref.Domain };
const Scanner = @This();

pub fn init(arena: Allocator, interner: *InternPool, source: []const u8, walk: *const Walk) Scanner {
    return .{ .arena = arena, .interner = interner, .source = source, .walk = walk };
}

/// Enumerate `step`'s global name candidates (deduped, in first-appearance order).
/// The returned slice is arena-allocated and valid until the next `scanStep` on this
/// scanner (internal buffers are reused across calls).
pub fn scanStep(self: *Scanner, step: *const ast.Step) Allocator.Error![]const Ref {
    self.out.clearRetainingCapacity();
    self.seen.clearRetainingCapacity();
    self.expr_locals.clearRetainingCapacity();
    switch (step.body) {
        .claim => |c| {
            try self.scanExpr(c.formula);
            switch (ruleDomain(self.source[c.rule.start..c.rule.end])) {
                .fact => for (c.refs) |r| try self.addTok(r, .fact),
                .local => {}, // local-only labels: LocalStepKV at process time, no fetch
            }
            for (c.args) |a| try self.scanExpr(a);
        },
        .assume => |blk| try self.scanExpr(blk.formula),
        .fix => |blk| try self.addTok(blk.sort, .ident),
        .unpack => |blk| try self.addTok(blk.sort, .ident), // `from` is a local step ref
        .case => |c| {
            try self.scanExpr(c.goal); // `disj` is a local step ref
            // arm assumptions are scanned when their synthesized assume steps walk
        },
    }
    return self.out.items;
}

/// Enumerate a bare FORMULA's global candidates (a theorem's goal / an axiom's asserted
/// proposition — the "step -1" read pass that runs before any proof step walks).
pub fn scanFormula(self: *Scanner, e: *const ast.Expr) Allocator.Error![]const Ref {
    self.out.clearRetainingCapacity();
    self.seen.clearRetainingCapacity();
    self.expr_locals.clearRetainingCapacity();
    try self.scanExpr(e);
    return self.out.items;
}

/// Which resolution domain a rule's refs live in. Only axiom/theorem citations are
/// global facts; everything else cites local steps/blocks (including accelerant names,
/// which hard-error as unsupported at process time — their refs never fetch).
fn ruleDomain(rule: []const u8) enum { fact, local } {
    if (std.mem.eql(u8, rule, "axiom") or std.mem.eql(u8, rule, "theorem")) return .fact;
    return .local;
}

fn scanExpr(self: *Scanner, e: *const ast.Expr) Allocator.Error!void {
    switch (e.*) {
        .name => |tok| try self.addNameTok(tok),
        .call => |c| {
            try self.addNameTok(c.callee);
            for (c.args) |a| try self.scanExpr(a);
        },
        .binary => |b| {
            try self.scanExpr(b.lhs);
            try self.scanExpr(b.rhs);
        },
        .not => |n| try self.scanExpr(n.operand),
        .quant => |q| try self.scanBinderBody(q.binders, q.body),
        .lambda => |l| try self.scanBinderBody(l.binders, l.body),
    }
}

/// Quantifier/lambda: binder sorts + guards are global candidates; binder NAMES become
/// expression-local for the body (shadowing proof-locals and globals alike).
fn scanBinderBody(self: *Scanner, binders: []const ast.Binder, body: *const ast.Expr) Allocator.Error!void {
    const mark = self.expr_locals.items.len;
    for (binders) |b| {
        try self.addTok(b.sort, .ident);
        if (b.guard) |g| try self.addTok(g, .ident);
        try self.expr_locals.append(self.arena, try self.intern(b.name));
    }
    try self.scanExpr(body);
    self.expr_locals.shrinkRetainingCapacity(mark);
}

/// An expression NAME position: skip expression-local and proof-local binders; the rest
/// are global ident candidates.
fn addNameTok(self: *Scanner, tok: lexer.Token) Allocator.Error!void {
    const text = self.source[tok.start..tok.end];
    if (std.mem.indexOfScalar(u8, text, '.') == null) {
        const name = try self.interner.internString(text);
        for (self.expr_locals.items) |b| if (b == name) return; // expr-local binder
        if (self.walk.findIdent(name) != null) return; // proof-local binder
    }
    try self.addTok(tok, .ident);
}

/// Record a (possibly dotted) token as a global candidate in `domain`, deduped. For a
/// dotted `ns.base`: the ns is ALSO recorded as an ident candidate (the import must
/// resolve), and the base carries the qualifier.
fn addTok(self: *Scanner, tok: lexer.Token, domain: Ref.Domain) Allocator.Error!void {
    const text = self.source[tok.start..tok.end];
    if (std.mem.indexOfScalar(u8, text, '.')) |i| {
        const ns = try self.interner.internString(text[0..i]);
        const base = try self.interner.internString(text[i + 1 ..]);
        try self.add(.{ .ns = null, .name = ns, .domain = .ident, .loc = tok.start });
        try self.add(.{ .ns = ns, .name = base, .domain = domain, .loc = tok.start });
    } else {
        const name = try self.interner.internString(text);
        try self.add(.{ .ns = null, .name = name, .domain = domain, .loc = tok.start });
    }
}

fn add(self: *Scanner, ref: Ref) Allocator.Error!void {
    const key = SeenKey{ .ns = ref.ns orelse .none, .name = ref.name, .domain = ref.domain };
    const gop = try self.seen.getOrPut(self.arena, key);
    if (gop.found_existing) return;
    try self.out.append(self.arena, ref);
}

fn intern(self: *Scanner, tok: lexer.Token) Allocator.Error!StrId {
    return self.interner.internString(self.source[tok.start..tok.end]);
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../../parser.zig");
const Diagnostics = @import("../../diagnostics.zig");

/// Drive a Walk over `source`'s (last-decl) theorem with a driver whose read pass runs
/// the scanner and records, per step label, the scanned global candidates as
/// "domain:name" / "domain:ns.name" strings.
fn scanAll(arena: Allocator, source: []const u8) !*ScanRecorder {
    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const sink = try arena.create(Diagnostics.Sink);
    sink.* = .init(arena);
    var p: parser.Parser = .init(arena, source, sink);
    const parsed = try p.parseFile();
    try testing.expectEqual(@as(usize, 0), sink.list.items.len);
    const steps = parsed.decls[parsed.decls.len - 1].theorem.steps;

    const rec = try arena.create(ScanRecorder);
    rec.* = .{ .arena = arena, .interner = interner, .source = source };
    var walk = Walk.init(arena, interner, source, sink);
    const result = try walk.drive(steps, rec);
    try testing.expect(result == .done);
    return rec;
}

const ScanRecorder = struct {
    arena: Allocator,
    interner: *InternPool,
    source: []const u8,
    /// per processed step: label -> list of "domain:name" strings, in scan order
    scans: std.ArrayList(struct { label: []const u8, refs: []const []const u8 }) = .empty,

    pub fn readPass(self: *ScanRecorder, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!?@import("../../Engine.zig").TaskIndex {
        _ = block;
        var scanner = Scanner.init(self.arena, self.interner, self.source, w);
        const refs = try scanner.scanStep(step);
        var rendered: std.ArrayList([]const u8) = .empty;
        for (refs) |r| {
            const domain = @tagName(r.domain);
            const s = if (r.ns) |ns|
                try std.fmt.allocPrint(self.arena, "{s}:{s}.{s}", .{ domain, self.interner.stringBytes(ns), self.interner.stringBytes(r.name) })
            else
                try std.fmt.allocPrint(self.arena, "{s}:{s}", .{ domain, self.interner.stringBytes(r.name) });
            try rendered.append(self.arena, s);
        }
        try self.scans.append(self.arena, .{
            .label = self.source[step.label.start..step.label.end],
            .refs = rendered.items,
        });
        return null;
    }

    pub fn process(self: *ScanRecorder, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!bool {
        _ = self;
        _ = w;
        _ = step;
        _ = block;
        return true;
    }

    pub fn caseConclude(self: *ScanRecorder, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!bool {
        _ = self;
        _ = w;
        _ = step;
        _ = block;
        return true;
    }

    pub fn exitBlock(self: *ScanRecorder, w: *Walk, block: Walk.BlockOrdinal) Allocator.Error!void {
        _ = self;
        _ = w;
        _ = block;
    }

    fn refsOf(self: *const ScanRecorder, label: []const u8) []const []const u8 {
        for (self.scans.items) |s| {
            if (std.mem.eql(u8, s.label, label)) return s.refs;
        }
        return &.{};
    }

    fn expectRefs(self: *const ScanRecorder, label: []const u8, expected: []const []const u8) !void {
        const got = self.refsOf(label);
        try testing.expectEqual(expected.len, got.len);
        for (expected, got) |e, g| try testing.expectEqualStrings(e, g);
    }
};

test "scan: globals enumerated; proof-local and expr-local binders skipped; dedup" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rec = try scanAll(arena,
        \\theorem t: Q
        \\proof
        \\  @outer |
        \\    fix n: Nat {
        \\      @inner |
        \\        forall k: Nat; le(add(k, n), n)
        \\        [by axiom axLe]
        \\    }
        \\  @concl |
        \\    Q
        \\    [by theorem outer]
        \\qed
    );
    // @outer (the fix step): its sort is a global candidate.
    try rec.expectRefs("outer", &.{"ident:Nat"});
    // @inner: Nat once (deduped: binder sort + nothing else), le + add global idents;
    // k (expr-local) and n (proof-local fix binder) are SKIPPED; the axiom ref is a fact.
    try rec.expectRefs("inner", &.{ "ident:Nat", "ident:le", "ident:add", "fact:axLe" });
    // @concl: Q is a global ident; `outer` is a theorem-rule ref -> fact domain — but it
    // is ALSO enumerated (fact refs are always global candidates; a local label never
    // shadows a citation).
    try rec.expectRefs("concl", &.{ "ident:Q", "fact:outer" });
}

test "scan: kernel-rule refs are local-only (not enumerated); qualified names split" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rec = try scanAll(arena,
        \\theorem t: P
        \\proof
        \\  @imp |
        \\    peano.impPQ
        \\    [by axiom peano.axImp]
        \\  @p |
        \\    P
        \\    [by axiom axP]
        \\  @q |
        \\    Q
        \\    [by modus_ponens imp p]
        \\qed
    );
    // @imp: the formula names a qualified ident (import `peano` + base in its namespace);
    // the citation is a qualified FACT.
    try rec.expectRefs("imp", &.{ "ident:peano", "ident:peano.impPQ", "fact:peano.axImp" });
    // @q: modus_ponens refs (imp, p) are LOCAL-only labels — not enumerated; only the
    // formula's Q is a global candidate.
    try rec.expectRefs("q", &.{"ident:Q"});
}
