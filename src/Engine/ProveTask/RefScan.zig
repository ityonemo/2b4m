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
        /// a schema name in a `using instantiation` step — resolved via IdentKV (a FetchTask
        /// mints the .schema locator); the instantiate handler then demands the instance FACT.
        schema,
        /// a model name in a `using model(M) …` step — resolved via IdentKV (a ModelTask
        /// builds M's overlay); the model-cite handler then demands the TRANSFERRED FACT.
        model,
    };
};

arena: Allocator,
interner: *InternPool,
source: []const u8,
/// consulted to SKIP proof-local binders (fix eigenvariables, unpack witnesses)
walk: *const Walk,
/// SCHEMA PARAM NAMES to skip while scanning a schema body/steps (they resolve via the
/// instance's schema_args, not as globals); empty for an ordinary proof. Set by the
/// instance ProveTask before scanning its schema body/steps.
schema_params: []const StrId = &.{},

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
            switch (ruleDomain(c.rule.name, c.kind)) {
                .fact => for (c.refs) |r| try self.addTok(r, .fact),
                .instantiate => if (c.schema) |s| try self.addTok(s, .schema), // the schema
                // NAME (its `c.refs` are LOCAL premise labels — not enumerated)
                .model => if (c.schema) |s| try self.addTok(s, .model), // the model NAME (the
                // `(M)` selector lands in c.schema); the transferred fact ref is demanded by
                // the cite handler once M resolves.
                .accelerant => {
                    // an accelerant HEAD (specialize's `c.schema`): a GLOBAL theorem/axiom
                    // citation UNLESS it's a live local step (then resolved locally at process
                    // time). EXCEPTION: for a THEORY-parameterized accelerant (polynomial…),
                    // `c.schema` is the theory SELECTOR (an import), not a fact head — the outer
                    // proof needn't resolve it at all (the generated schema's steps cite the
                    // theory's lemmas qualified by it, and the INSTANCE ProveTask demands those).
                    if (c.schema) |s| {
                        if (!self.isTheorySelector(c.rule.name) and self.walk.findStep(s.name) == null) {
                            try self.addTok(s, .fact);
                        }
                    }
                    // simplify's refs are its rewrite RULES — a mix of global axioms/theorems
                    // and local equation steps; a ref that is NOT a live local step is a global
                    // fact the producer will `resolveFactRef`, so demand it here. (For
                    // specialize/tautology every ref IS a live local step → skipped, unchanged.)
                    for (c.refs) |r| {
                        if (r.qualifier != InternPool.Index.none or self.walk.findStep(r.name) == null) {
                            try self.addTok(r, .fact);
                        }
                    }
                },
                .local => {}, // local-only labels: LocalStepKV at process time, no fetch
            }
            // assoc / assoc_commut take their equation LEMMAS as ARGS (not refs) — a bare-name
            // arg that isn't a live local step is a GLOBAL fact the producer resolves, so demand
            // it here. Every OTHER accelerant's args are VALUE terms (scanned as idents below).
            if (self.lemmaArgAccelerant(c)) {
                for (c.args) |a| {
                    if (a.* == .name and
                        (a.name.qualifier != InternPool.Index.none or self.walk.findStep(a.name.name) == null))
                    {
                        try self.addTok(a.name, .fact);
                    }
                }
            } else {
                for (c.args) |a| try self.scanExpr(a);
            }
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

/// Which resolution domain a rule's refs live in. Axiom/theorem citations are global facts;
/// `instantiate` names a global schema (in `c.schema`); everything else cites local
/// steps/blocks (including accelerant names, which hard-error as unsupported at process
/// time — their refs never fetch). Dispatch is on the RESERVED rule-word StrId the parser
/// stamped — integer comparison, no strcmp past parsing.
fn ruleDomain(rule: StrId, kind: ast.Step.Claim.Kind) enum { fact, instantiate, model, accelerant, local } {
    if (InternPool.RuleStr.of(rule)) |word| return switch (word) {
        .axiom, .theorem => .fact,
        .instantiation => .instantiate,
        .model => .model,
        else => .local,
    };
    // a non-reserved word under `using` is an accelerant (its HEAD may be a global fact).
    return if (kind == .using) .accelerant else .local;
}

/// True when the claim is an `assoc`/`assoc_commut` (or `_quantified`) accelerant, whose ARGS
/// are equation-lemma NAMES (global facts) rather than value terms — so the read pass demands
/// them in the `.fact` domain. Matched by interned rule name (integer compare, no strcmp).
/// True for a THEORY-parameterized accelerant whose `c.schema` is a theory SELECTOR (an
/// import namespace), not a fact head — so the read pass must NOT demand `c.schema` as a fact.
/// Matched by interned rule name (integer compare, no strcmp past parsing). Mirrors the
/// parser's `isTheoryRule` (minus `model`, which is dispatched as its own RuleStr domain).
fn isTheorySelector(self: *Scanner, rule: StrId) bool {
    inline for (.{ "polynomial", "polynomial_quantified", "ext", "ext_quantified" }) |nm| {
        const id = self.interner.internString(nm) catch return false;
        if (rule == id) return true;
    }
    return false;
}

fn lemmaArgAccelerant(self: *Scanner, c: ast.Step.Claim) bool {
    if (c.kind != .using) return false;
    inline for (.{ "assoc", "assoc_quantified", "assoc_commut", "assoc_commut_quantified" }) |nm| {
        const id = self.interner.internString(nm) catch return false;
        if (c.rule.name == id) return true;
    }
    return false;
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
        try self.expr_locals.append(self.arena, b.name.name);
    }
    try self.scanExpr(body);
    self.expr_locals.shrinkRetainingCapacity(mark);
}

/// An expression NAME position: skip expression-local and proof-local binders (only a
/// BARE name can be one — a qualified token never shadows); the rest are global ident
/// candidates.
fn addNameTok(self: *Scanner, tok: lexer.Token) Allocator.Error!void {
    if (tok.qualifier == InternPool.Index.none) {
        const name = tok.name;
        for (self.expr_locals.items) |b| if (b == name) return; // expr-local binder
        if (self.walk.findIdent(name) != null) return; // proof-local binder
        for (self.schema_params) |p| if (p == name) return; // schema parameter
    }
    try self.addTok(tok, .ident);
}

/// Record a (possibly qualified) stamped token as a global candidate in `domain`, deduped.
/// For a qualified `ns.base`: the ns is ALSO recorded as an ident candidate (the import
/// must resolve), and the base carries the qualifier.
fn addTok(self: *Scanner, tok: lexer.Token, domain: Ref.Domain) Allocator.Error!void {
    if (tok.qualifier != InternPool.Index.none) {
        try self.add(.{ .ns = null, .name = tok.qualifier, .domain = .ident, .loc = tok.start });
        try self.add(.{ .ns = tok.qualifier, .name = tok.name, .domain = domain, .loc = tok.start });
    } else {
        try self.add(.{ .ns = null, .name = tok.name, .domain = domain, .loc = tok.start });
    }
}

fn add(self: *Scanner, ref: Ref) Allocator.Error!void {
    const key = SeenKey{ .ns = ref.ns orelse .none, .name = ref.name, .domain = ref.domain };
    const gop = try self.seen.getOrPut(self.arena, key);
    if (gop.found_existing) return;
    try self.out.append(self.arena, ref);
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
    var p: parser.Parser = .initInterning(arena, source, sink, interner);
    const parsed = try p.parseFile();
    try testing.expectEqual(@as(usize, 0), sink.list.items.len);
    const steps = parsed.decls[parsed.decls.len - 1].theorem.local.steps;

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

test "scan: instantiate emits the schema name (schema domain); its refs are local; args scanned" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rec = try scanAll(arena,
        \\theorem t: P
        \\proof
        \\  @c |
        \\    P
        \\    [using instantiation foo(bar) premiseStep]
        \\qed
    );
    // @c: the schema `foo` is a .schema candidate; the arg `bar` is a global ident; the
    // ref `premiseStep` is a LOCAL premise label (not enumerated). Formula P is an ident.
    try rec.expectRefs("c", &.{ "ident:P", "schema:foo", "ident:bar" });
}

test "scan: a qualified schema name splits into import + schema base" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rec = try scanAll(arena,
        \\theorem t: P
        \\proof
        \\  @c |
        \\    P
        \\    [using instantiation lib.foo(bar)]
        \\qed
    );
    // qualified schema: import `lib` (ident) + base `foo` in its namespace (schema).
    try rec.expectRefs("c", &.{ "ident:P", "ident:lib", "schema:lib.foo", "ident:bar" });
}
