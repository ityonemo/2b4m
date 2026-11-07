//! The `arithmetic` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
//! `Accelerant.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../../ast.zig");
const lexer = @import("../../../lexer.zig");
const InternPool = @import("../../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const kernel = @import("../../../kernel.zig");
const Engine = @import("../../../Engine.zig");
const Walk = @import("../Walk.zig");
const RefScan = @import("../RefScan.zig");
const Elab = @import("../Elab.zig");
const Schema = @import("../Schema.zig");
const Accelerant = @import("../Accelerant.zig");
const EqCert = @import("../EqCert.zig");
const polycanon = @import("polycanon.zig");
const rewrite = @import("rewrite.zig");
const presburger = @import("presburger.zig");
const smt = @import("../smt.zig");
const farkas = @import("farkas.zig");
const FactKV = @import("../../../FactKV.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const tokName = Prove.tokName;
const testing = std.testing;
const common = @import("common.zig");
const ac = @import("ac.zig");
const testrig = @import("testrig.zig");
const Symbols = @import("symbols.zig").Symbols;

pub const schema_slot: Accelerant.SchemaSlot = .theory_selector;
pub const premise_shape: Accelerant.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

/// Phase 1: the decision binds its well-known operator symbols by name — `add` for the
/// mul/order certs, `nonneg` to pick the ℕ-vs-ℤ fragment — even when the goal itself does not
/// mention them (a pure-succ order goal, a ground `mul`). Demand every well-known name DECLARED
/// in this file so the producer's ident lookups find them done; an absent name is skipped (no
/// fetch, no error). Without `nonneg` resolved a ℕ goal is read over ℤ and
/// `less_than(a, add(a, succ(b)))` decides FALSE — which is what the trusted path once did.
pub fn read(self: @This(), prove: *Prove, w: *const Walk, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    _ = self;
    _ = w;
    const loc = c.rule.start;
    const wk = [_][]const u8{ "add", "mul", "succ", "prev", "ZERO", "ONE", "neg", "sub", "less_than", "nonneg" };
    const fid = prove.ctx.fileOf(prove.file).?;
    var refs: std.ArrayList(RefScan.Ref) = .empty;
    for (wk) |name| {
        const nid = prove.ctx.interner.internString(name) catch return error.OutOfMemory;
        const decl = prove.ctx.declOf(fid, nid) orelse continue; // not declared here → skip
        if (decl.* == .define) continue; // a define is a macro, not an identifier to fetch (`define ONE = succ(ZERO)`)
        try refs.append(prove.ctx.arena, .{ .ns = null, .name = nid, .domain = .ident, .loc = loc });
    }
    // the Cooper induction path instantiates the `induction` schema — demand its `.schema`
    // locator so the producer's schema lookup finds it `done`. Only when THIS file declares
    // `induction` as a schema (a parameterized axiom); a bare re-export or a theory-qualified
    // name is left to the ordinary resolver (the induction path declines if it can't resolve).
    const induction_id = prove.ctx.interner.internString("induction") catch return error.OutOfMemory;
    if (c.schema == null) if (prove.ctx.declOf(fid, induction_id)) |d| {
        if (ast.factOf(d)) |f| if (f.params != null) {
            try refs.append(prove.ctx.arena, .{ .ns = null, .name = induction_id, .domain = .schema, .loc = loc });
        };
    };
    return Prove.resolveRefs(prove.ctx, prove.h, prove.file, prove.ns, prove.model, prove.self_key, refs.items);
}

pub fn decide(self: @This(), prove: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    return common.decideFused(self, prove, w, e, goal, c);
}

pub fn certify(self: @This(), prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    _ = self;
    return produceArithmetic(prove, w, goal, c);
}

/// A well-known symbol's name text (for the head-name reads that build `Symbols`).
fn symName(prove: *const Prove, sym: term.SymId) []const u8 {
    return prove.ctx.interner.stringBytes(prove.ctx.interner.nameOf(@enumFromInt(@intFromEnum(sym))));
}

/// Build the arithmetic `Symbols` by reading the goal's (and premises') operator head-NAMES
/// — like `readPolyOps`. An absent symbol stays null (shrinking the fragment), matching the
/// old `wellKnownSym` semantics. `c.schema` only qualifies the emitted lemma CITES; symbols
/// come off the terms.
fn readArithSymbols(prove: *Prove, goal: TermId, premises: []const TermId) Error!Symbols {
    var s: Symbols = .{};
    try collectArithSyms(prove, goal, &s);
    for (premises) |p| try collectArithSyms(prove, p, &s);
    // Fill any core operator ABSENT from the goal by IDENT lookup (best-effort, no
    // fetch/suspend) — the old scope-based `wellKnownSym`. A pure-succ order goal like
    // `less_than(succ(ZERO), succ(succ(ZERO)))` has no `add`, but the order cert needs it for
    // `lessThanIntro`'s `add(a, succ(d)) = b`. Absent (not a top-level ident) → stays null.
    if (s.add == null) s.add = resolveArithSym(prove, "add", .func);
    if (s.mul == null) s.mul = resolveArithSym(prove, "mul", .func);
    if (s.succ == null) s.succ = resolveArithSym(prove, "succ", .func);
    if (s.prev == null) s.prev = resolveArithSym(prove, "prev", .func);
    if (s.zero == null) s.zero = resolveArithSym(prove, "ZERO", .constant);
    if (s.one == null) s.one = resolveArithSym(prove, "ONE", .constant);
    if (s.neg == null) s.neg = resolveArithSym(prove, "neg", .func);
    if (s.sub == null) s.sub = resolveArithSym(prove, "sub", .func);
    if (s.less_than == null) s.less_than = resolveArithSym(prove, "less_than", .pred);

    const anchor = s.succ orelse s.add orelse s.zero orelse s.one orelse s.mul orelse s.sub orelse s.neg;
    if (anchor) |sym| s.nat = @enumFromInt(@intFromEnum(prove.ctx.interner.symResult(@enumFromInt(@intFromEnum(sym)))));
    // A well-known `nonneg` predicate: its PRESENCE in scope is the theory's request to
    // constrain its variables nonneg (ℕ binds it; ℤ/ℚ don't). Read as x ≥ 0 by the engine +
    // injected per free var below. Resolved by IDENT lookup (best-effort, no fetch/suspend) —
    // it's a top-level alias, resolved in the read pass; absent → pure ℤ.
    if (resolveArithNonneg(prove)) |nn| s.nonneg = nn;
    return s;
}

/// Resolve the well-known `nonneg` predicate symbol in this proof's namespace, or null.
fn resolveArithNonneg(prove: *Prove) ?term.SymId {
    return resolveArithSym(prove, "nonneg", .pred);
}

/// Resolve a well-known arithmetic symbol by NAME in this proof's namespace (a `done` IdentKV
/// entry of the given kind), or null. No fetch/suspend — a top-level alias/decl is resolved in
/// the read pass; an absent name reads as unresolved. This is the demand-framework equivalent
/// of the old scope-based `wellKnownSym`.
fn resolveArithSym(prove: *Prove, name: []const u8, comptime kind: enum { func, pred, constant }) ?term.SymId {
    const nid = prove.ctx.interner.internString(name) catch return null;
    const state = prove.ctx.idents.lookup(prove.ctx.io, .{ .namespace = prove.ns, .name = nid }) orelse return null;
    const ix = switch (state) {
        .done => |x| prove.ctx.interner.applyModel(prove.model, x),
        .in_flight => return null,
    };
    return switch (prove.ctx.interner.keyOf(ix)) {
        .func => if (kind == .func) @enumFromInt(@intFromEnum(ix)) else null,
        .pred => if (kind == .pred) @enumFromInt(@intFromEnum(ix)) else null,
        .constant => if (kind == .constant) @enumFromInt(@intFromEnum(ix)) else null,
        else => null,
    };
}

/// Collect a `nonneg(v)` guard for each distinct free var of the arithmetic sort in `id`
/// (dedup by name) into `out` — the ℕ theory's per-variable x ≥ 0 the pure-ℤ engine needs.
fn collectArithNonneg(prove: *Prove, id: TermId, nat: term.SortId, nn: term.SymId, seen: *std.AutoHashMapUnmanaged(StrId, void), out: *std.ArrayList(TermId)) Error!void {
    // collect one `nonneg(x)` per distinct nat-sorted fvar. Iterative work-stack; the `seen` dedup
    // makes emission order-independent. NOTE the original emits the fvar's `nonneg` on FIRST sight
    // in traversal order — dedup by name means the SET is identical regardless of stack order.
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = prove.pool.get(cur);
        switch (node) {
            .fvar => |v| {
                if (v.sort != nat) continue;
                const gop = seen.getOrPut(prove.ctx.arena, v.name) catch return error.OutOfMemory;
                if (gop.found_existing) continue;
                try out.append(prove.ctx.arena, try prove.pool.addApp(.pred, nn, &.{cur}));
            },
            else => try prove.pool.pushChildren(&stack, wa, node),
        }
    }
}

fn collectArithSyms(prove: *Prove, id: TermId, s: *Symbols) Error!void {
    // resolve the arithmetic vocabulary by well-known name over the whole term. Iterative work-
    // stack; field-setting is order-independent (a name maps to one sym).
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, id);
    while (stack.pop()) |cur| {
        const node = prove.pool.get(cur);
        switch (node) {
            .app, .pred => |a| {
                const name = symName(prove, a.sym);
                if (std.mem.eql(u8, name, "ZERO")) s.zero = a.sym //
                else if (std.mem.eql(u8, name, "ONE")) s.one = a.sym //
                else if (std.mem.eql(u8, name, "succ")) s.succ = a.sym //
                else if (std.mem.eql(u8, name, "prev")) s.prev = a.sym //
                else if (std.mem.eql(u8, name, "add")) s.add = a.sym //
                else if (std.mem.eql(u8, name, "mul")) s.mul = a.sym //
                else if (std.mem.eql(u8, name, "neg")) s.neg = a.sym //
                else if (std.mem.eql(u8, name, "sub")) s.sub = a.sym //
                else if (std.mem.eql(u8, name, "less_than")) s.less_than = a.sym //
                else if (std.mem.eql(u8, name, "nonneg")) s.nonneg = a.sym;
                try prove.pool.pushChildren(&stack, wa, node);
            },
            .eq, .not, .bin, .quant => try prove.pool.pushChildren(&stack, wa, node),
            else => {},
        }
    }
}

/// Does the term `id` mention the symbol `want` anywhere?
fn usesSym(prove: *Prove, want: term.SymId, id: TermId) bool {
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), prove.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, id) catch return true; // OOM conservative
    while (stack.pop()) |cur| {
        const node = prove.pool.get(cur);
        switch (node) {
            .app, .pred => |ap| if (ap.sym == want) return true,
            else => {},
        }
        prove.pool.pushChildren(&stack, a, node) catch return true;
    }
    return false;
}

/// A cite token for a well-known lemma named `name`, qualified by the theory selector
/// `c.schema` (bare when absent) — the generated ProveTask resolves + kernel-checks it. No
/// facts.lookup here.
fn wkCite(prove: *Prove, name: []const u8, c: ast.Step.Claim) Error!lexer.Token {
    const nid = prove.ctx.interner.internString(name) catch return error.OutOfMemory;
    return .{
        .tag = .identifier,
        .start = c.rule.start,
        .end = c.rule.start,
        .name = nid,
        .qualifier = if (c.schema) |sel| sel.name else InternPool.Index.none,
    };
}

/// Resolve a cited premise `ref` (an equation or `less_than` atom) to its formula + how the
/// cert cites it (a LOCAL step restated by hypothesis, or a GLOBAL fact cited by name). Only
/// LOCAL refs are schema antecedents; a GLOBAL premise is cited inside the cert.
const ArithPremise = struct {
    formula: TermId,
    local: bool,
    /// LOCAL: the restated-hypothesis label (a schema antecedent). GLOBAL: unused.
    hyp: StrId,
    /// GLOBAL: the cite token + kind. LOCAL: unused.
    head: lexer.Token,
    is_axiom: bool,
};

fn resolveArithPremise(prove: *Prove, w: *const Walk, ref: lexer.Token) Error!ArithPremise {
    const is_local = ref.qualifier == InternPool.Index.none and w.findStep(Prove.tokName(ref)) != null;
    if (is_local) {
        const sref = try prove.resolveStepRef(w, ref);
        return .{
            .formula = prove.producerPremiseFormula(sref),
            .local = true,
            .hyp = try common.premiseHypLabel(prove, ref),
            .head = ref,
            .is_axiom = false,
        };
    }
    const fact = try prove.resolveFactRef(ref);
    const formula = try prove.pool.copyIn(prove.ctx.interner, prove.ctx.interner.keyOf(fact).fact.formula);
    return .{
        .formula = formula,
        .local = false,
        .hyp = undefined,
        .head = ref,
        .is_axiom = prove.ctx.interner.keyOf(fact).fact.kind == .axiom,
    };
}

/// The arithmetic certificate emitter: a growable step list plus the shared builder. Mirrors
/// the old `emitStep`/`newBlock` API onto `ast.Step`s the kernel re-checks.
const ArithCert = struct {
    p: *Prove,
    b: *Accelerant.Builder,
    c: ast.Step.Claim,

    /// A claim step `@label | <formula> [by <rule> args refs]`; refs are label StrIds.
    pub fn claim(self: *ArithCert, block: *std.ArrayList(ast.Step), formula: TermId, rule: []const u8, args: []const *const ast.Expr, refs: []const StrId) Error!StrId {
        const toks = try self.p.ctx.arena.alloc(lexer.Token, refs.len);
        for (refs, toks) |r, *o| o.* = self.b.tok(r);
        const label = try self.p.freshNamed("arith");
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(formula), .by, try common.internStrRt(self.p, rule), args, toks));
        return label;
    }

    /// Cite a well-known lemma by name (qualified by the theory selector); returns the cite
    /// step's label (its formula = the lemma's `forall …` statement). The word "axiom" is a
    /// placeholder — the kernel picks the arm by the RESOLVED fact's kind.
    pub fn citeLemma(self: *ArithCert, block: *std.ArrayList(ast.Step), name: []const u8, formula: TermId) Error!StrId {
        const head = try wkCite(self.p, name, self.c);
        const label = try self.p.freshNamed("arith-lemma");
        const refs = try self.p.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = head;
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(formula), .by, try self.p.internStr("axiom"), &.{}, refs));
        return label;
    }

    /// Cite a GLOBAL user premise (arith premise) by its own head token.
    pub fn citeGlobalPremise(self: *ArithCert, block: *std.ArrayList(ast.Step), prem: ArithPremise) Error!StrId {
        const label = try self.p.freshNamed("arith-prem");
        const refs = try self.p.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = prem.head;
        const word: []const u8 = if (prem.is_axiom) "axiom" else "theorem";
        try block.append(self.p.ctx.arena, try self.b.claimStep(label, try self.b.termExpr(prem.formula), .by, try common.internStrRt(self.p, word), &.{}, refs));
        return label;
    }

    /// `apply_at` the fact at `label` (formula `cur`) at each binding, appending steps;
    /// returns the final label + opened formula.
    pub fn elimChain(self: *ArithCert, block: *std.ArrayList(ast.Step), label: StrId, cur: TermId, bindings: []const TermId) Error!struct { label: StrId, formula: TermId } {
        var cur_label = label;
        var cur_formula = cur;
        for (bindings) |val| {
            const qn = self.p.pool.get(cur_formula);
            const opened = try self.p.pool.open(qn.quant.body, val);
            const arg1 = try self.p.ctx.arena.alloc(*const ast.Expr, 1);
            arg1[0] = try self.b.termExpr(val);
            cur_label = try self.claim(block, opened, "apply_at", arg1, &.{cur_label});
            cur_formula = opened;
        }
        return .{ .label = cur_label, .formula = cur_formula };
    }

    /// A `fix name: sort { steps }` block step (returns the step + label).
    pub fn fixStep(self: *ArithCert, label_prefix: []const u8, name: StrId, sort: SortId, steps: []const ast.Step) Error!struct { step: ast.Step, label: StrId } {
        const fix_label = try self.p.freshNamed(label_prefix);
        const bname = self.b.tok(try common.displayName(self.p, name));
        return .{ .step = .{ .label = self.b.tok(fix_label), .body = .{ .fix = .{ .name = bname, .sort = self.b.sortTok(sort), .steps = steps } } }, .label = fix_label };
    }
};

/// `[using arithmetic (theory)? refs… (fallback(thm))?]` — the entry producer for both the
/// bare `arithmetic` and the `arithmetic_quantified` alias (same body; the goal shape drives
/// the ∀-peel). See `buildArithmetic`.
pub fn produceArithmetic(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    if (c.args.len != 0) return prove.fail(c.rule.start, "arithmetic takes no arguments", .{});
    return buildArithmetic(prove, w, goal, c);
}

/// The arithmetic core: DECIDE the goal from its cited premises (+ injected nonneg guards),
/// then walk the certifier chain (equation/order/exists → premise-combination → Farkas →
/// Cooper), first that certifies wins, emitting its cert as the synthetic schema's proof.
/// A declined-but-valid goal with `fallback(thm)` emits the fallback path; else a terminal
/// error. STRICT ONLY — never a trusted verdict.
/// The diagnostic for a refuted `arithmetic` goal. Shared by the DECISION GATE (which runs in
/// both modes) and the strict certifier path, because both refute on the same `decideMixed`
/// verdict and a reader deserves the same message either way — the gate used to carry only the
/// two degenerate branches, so running it in strict (e884a17) silently downgraded every
/// countermodel to "the statement is false" and broke three goldens.
///
/// Three shapes, in order of what they can tell you:
///   - an abstracted opaque subterm (`mul(a, b)`, `f(x)`) is in the countermodel: the goal
///     needs more than linear arithmetic, and its atom values are not independently
///     realizable, so naming the subterm beats inventing numbers;
///   - no values and no opaques: nothing to show, the statement is just false;
///   - otherwise: the falsifying assignment, with the abstraction's params (p1, p2, …) mapped
///     back to the CALLER's own variable names and sorted for stability.
fn arithCountermodelFail(
    prove: *Prove,
    loc: u32,
    cm: anytype,
    abs: common.FvarAbstraction,
) Error!?Accelerant.Synthetic {
    for (cm.values) |a| if (a.term) |offending|
        return prove.fail(loc, "arithmetic: '{s}' is outside linear arithmetic", .{try prove.renderTerm(offending)});
    if (cm.values.len == 0 and cm.opaques.len == 0)
        return prove.fail(loc, "arithmetic: the statement is false", .{});
    const Shown = struct { name: []const u8, value: i128 };
    const shown = try prove.ctx.arena.alloc(Shown, cm.values.len);
    for (cm.values, shown) |a, *out| {
        var orig = a.name;
        for (abs.names, abs.origs) |pn, on| if (pn == a.name) {
            orig = on;
        };
        out.* = .{ .name = prove.ctx.interner.stringBytes(try common.displayName(prove, orig)), .value = a.value };
    }
    std.mem.sort(Shown, shown, {}, struct {
        fn lessThan(_: void, x: Shown, y: Shown) bool {
            return std.mem.lessThan(u8, x.name, y.name);
        }
    }.lessThan);
    var msg: std.Io.Writer.Allocating = .init(prove.ctx.arena);
    var count: usize = 0;
    for (shown) |a| {
        msg.writer.print("{s}{s} := {d}", .{ if (count > 0) ", " else "", a.name, a.value }) catch return error.OutOfMemory;
        count += 1;
    }
    for (cm.opaques) |lit| {
        msg.writer.print("{s}{s} := {s}", .{ if (count > 0) ", " else "", try prove.renderTerm(lit.atom), if (lit.value) "true" else "false" }) catch return error.OutOfMemory;
        count += 1;
    }
    return prove.fail(loc, "arithmetic: false at {s}", .{msg.written()});
}

fn buildArithmetic(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    // `--fast` declines to EMIT the certificate; the DECISION still runs. (It did run until
    // `4d84393` restored per-word admit and inserted an early return here, collapsing it away —
    // which let `--fast` accept `succ(ZERO) = succ(succ(ZERO))` and `add(a, succ(b)) < a`, both
    // plainly false.) The decision admits on exactly ONE outcome: the goal is TRUE.
    //
    //   FALSE                     -> fail, with strict's own diagnostic.
    //   TRUE (certifiable or not) -> admit. Certifiability is a fact about our CERTIFIER
    //                                strategies, not about the goal, so `--fast` accepts both
    //                                and never consults `fallback(...)` — a fallback supplies a
    //                                CERTIFICATE, which `--fast` is not building.
    //   SHAPE IT CANNOT HANDLE    -> fail. Nothing was adjudicated, so admitting would invent
    //                                a verdict; strict reports the same gap.
    //
    // The admit point is after the decision below, before the certifier chain — which exists
    // only to BUILD a certificate. The well-known idents the decision needs (`nonneg` above
    // all, which picks the ℕ-vs-ℤ fragment) are demanded in the read pass by
    // `demandArithIdents`, for trusted steps as well as untrusted — without that the decision
    // here would read a ℕ goal over ℤ. See design/acceleration.md.
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // resolve cited premises (local steps / global facts).
    const prems = try prove.ctx.arena.alloc(ArithPremise, c.refs.len);
    for (c.refs, prems) |r, *out| out.* = try resolveArithPremise(prove, w, r);
    const prem_formulae = try prove.ctx.arena.alloc(TermId, prems.len);
    for (prems, prem_formulae) |p, *out| out.* = p.formula;

    const symbols = try readArithSymbols(prove, goal, prem_formulae);

    // ABSTRACT genuinely-free caller-local fvars (an enclosing `fix`) into value params — so
    // the cert steps, premises and schema body all speak the param names. (The ∀-goal's own
    // binders are NOT free here; they are peeled into eigenvariables by each cert path.)
    var local_pf: std.ArrayList(TermId) = .empty;
    for (prems) |p| if (p.local) try local_pf.append(prove.ctx.arena, p.formula);
    const ag = try common.abstractGoal(prove, &b, goal, local_pf.items, &.{});
    const abs = ag.abs;
    const goal_p = ag.goal_p;
    for (prems, prem_formulae) |*p, *pf| {
        p.formula = try common.substFvarsToParams(prove, p.formula, abs);
        pf.* = p.formula;
    }

    // THE DECISION — under `--fast`, the whole of the check. Same inputs as the strict decide
    // below (abstracted goal, param-substituted premises, injected `nonneg` guards), so the two
    // modes always agree on the goal's truth.
    // THE DECISION GATE, run in BOTH modes. Strict must apply every gate `--fast` applies and
    // then additionally emit and kernel-check the certificate; a gate that runs only under
    // `--fast` lets the two modes DISAGREE, which is the invariant's whole point. This block
    // used to be wrapped in `if (prove.admit_mode)`, so strict skipped it and fell straight
    // through to the certifier — and `--fast` could then REJECT a step strict accepted (the
    // mirror of the 2026-10-26 sweep, which only probed the other direction).
    //
    // Only the ADMIT differs by mode: on `.valid`, `--fast` is done and strict goes on to
    // build the certificate.
    {
        const peel = try arithPeel(prove, goal_p);
        var dprems: std.ArrayList(TermId) = .empty;
        try dprems.appendSlice(prove.ctx.arena, prem_formulae);
        if (symbols.nonneg) |nn| if (symbols.nat) |nat| {
            var seen: std.AutoHashMapUnmanaged(StrId, void) = .empty;
            try collectArithNonneg(prove, peel.body, nat, nn, &seen, &dprems);
            for (prem_formulae) |pf| try collectArithNonneg(prove, pf, nat, nn, &seen, &dprems);
        };
        switch (try smt.decideMixed(prove.ctx.arena, prove.pool, symbols, dprems.items, peel.body)) {
            .valid => {
                if (prove.admit_mode) {
                    prove.admit_ok = true;
                    return null;
                }
                // strict: decided TRUE, now go build the certificate below.
            },
            .countermodel => |cm| {
                // Does this refutation rest on an ABSTRACTED OPAQUE SUBTERM (`sumTo(succ(k))`,
                // `mul(a, b)`)? Then the decision adjudicated NOTHING: it replaced the subterm
                // with a fresh variable free to range, so the "countermodel" is an artifact of
                // that abstraction rather than a falsifying assignment — a cited premise may
                // well pin the subterm's value, which is exactly how `examples/gauss.b4m` is
                // true and certifiable while the decision cannot see it.
                var abstained = false;
                for (cm.values) |a| if (a.term != null) {
                    abstained = true;
                };
                // THE INVARIANT IS ONE-DIRECTIONAL.
                //   - `--fast` must NEVER reject what strict can certify: a certificate is
                //     kernel-checked proof the statement is true, so rejecting it is simply
                //     wrong. `--fast` is the WEAKER check; on an abstention it accepts.
                //   - `--fast` MAY accept what strict rejects — strict rejects for want of a
                //     CERTIFICATE, which is a fact about the certifier's reach, not about the
                //     statement.
                //   - Neither mode may accept something FALSE: a genuine countermodel (nothing
                //     opaque in it) is a real refutation and rejects in both.
                if (!abstained) return arithCountermodelFail(prove, c.rule.start, cm, abs);
                if (prove.admit_mode) {
                    prove.admit_ok = true;
                    return null;
                }
                // strict: fall through to the certifier, which may prove what we could not decide.
            },
            .too_many_atoms => |n| return prove.fail(c.rule.start, "arithmetic: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
            .too_large => return prove.fail(c.rule.start, "arithmetic: decision exceeded the work limit", .{}),
            .overflow => return prove.fail(c.rule.start, "arithmetic: coefficient overflow", .{}),
        }
    }

    // build the cert into a fresh step list. Try each certifier in order — every path is
    // kernel-checked, so we CERTIFY FIRST and only run the decision procedure for a good error
    // when all decline. (The decision gate would otherwise need the theory's per-variable
    // `nonneg` guard for a ℕ order goal — resolvable only by an ident fetch — while the cert
    // itself, e.g. an order goal whose difference is a literal `succ`-tower, never needs it.)
    var cert: ArithCert = .{ .p = prove, .b = &b, .c = c };
    var body_steps: std.ArrayList(ast.Step) = .empty;
    var proved_prop: TermId = goal_p; // the eigen-closed prop the wrapped cert concludes
    var certified = false;
    if (try arithEquationCert(prove, &cert, &body_steps, goal_p, &proved_prop, prems, symbols)) {
        certified = true;
    } else if (try arithFarkasCert(prove, &cert, &body_steps, goal_p, &proved_prop, symbols)) {
        certified = true;
    } else if (try arithCooperCert(prove, &cert, &body_steps, goal_p, &proved_prop, symbols)) {
        certified = true;
    } else if (try arithMixedCert(prove, &cert, &body_steps, goal_p, &proved_prop, prems, symbols)) {
        certified = true;
    }

    if (!certified) {
        if (c.fallback) |fb| return buildArithFallback(prove, w, &b, fb, goal_p, prems, abs, c);
        // DECIDE to produce a good error: a genuine non-consequence names the countermodel; a
        // valid-but-uncertifiable goal reports the fragment gap. Strip the ∀-Nat prefix +
        // inject the theory's per-variable `nonneg` guard (when it binds one) so a ℕ order
        // goal decides true.
        const decide_peel = try arithPeel(prove, goal_p);
        var decide_prems: std.ArrayList(TermId) = .empty;
        try decide_prems.appendSlice(prove.ctx.arena, prem_formulae);
        if (symbols.nonneg) |nn| if (symbols.nat) |nat| {
            var seen: std.AutoHashMapUnmanaged(StrId, void) = .empty;
            try collectArithNonneg(prove, decide_peel.body, nat, nn, &seen, &decide_prems);
            for (prem_formulae) |pf| try collectArithNonneg(prove, pf, nat, nn, &seen, &decide_prems);
        };
        const verdict = smt.decideMixed(prove.ctx.arena, prove.pool, symbols, decide_prems.items, decide_peel.body) catch return error.OutOfMemory;
        switch (verdict) {
            .valid => {
                // every link declined; name each one's reason (the farkas link needs the order
                // predicate, the others decline on shape).
                const farkas_reason: []const u8 = if (symbols.less_than == null) "theory lacks symbol 'less_than'" else "form not in certification scope";
                return prove.fail(c.rule.start, "'arithmetic' is valid but no certifier could prove it here:\n  - equation/order/exists: form not in certification scope\n  - mixed-skeleton: form not in certification scope\n  - farkas: {s}\n  - cooper: form not in certification scope\nuse --fast to accept the accelerated verdict", .{farkas_reason});
            },
            .countermodel => |cm| return arithCountermodelFail(prove, c.rule.start, cm, abs),
            .too_many_atoms => |n| return prove.fail(c.rule.start, "arithmetic: {d} distinct atoms exceeds the limit of {d}", .{ n, smt.atom_limit }),
            .too_large => return prove.fail(c.rule.start, "arithmetic: decision exceeded the work limit", .{}),
            .overflow => return prove.fail(c.rule.start, "arithmetic: coefficient overflow", .{}),
        }
    }
    // certified on our own: a `fallback(thm)` is redundant (strict; --draft suppresses).
    if (c.fallback) |fb| {
        if (!prove.ctx.verify.draft) return prove.fail(fb.start, "'arithmetic' certifies this goal on its own — the fallback '{s}' is unnecessary; drop `fallback({s})`", .{ prove.text(fb), prove.text(fb) });
    }

    // package with the cert's ACTUAL conclusion (`proved_prop`), not the raw `goal_p`: the
    // ∀-re-generalization shell (wrapArithForall) re-quantifies at the eigenvariables' fresh
    // names, so `proved_prop` is alpha-equal to `goal_p` but its binder hints match the proof's
    // final `generalize` steps. Declaring the schema body from `proved_prop` keeps the stated
    // schema and the emitted proof's conclusion byte-identical (a hint mismatch would surface as
    // "claims forall b1 but derives forall …", the cooper_witness bug).
    return try packageArith(prove, w, &b, "arithmetic", proved_prop, prems, abs, body_steps.items, c);
}

/// Package the emitted cert `body_steps` (proving the param-substituted `goal_p`) as the
/// synthetic schema: body = `localPrem0 -> … -> goal_p` wrapped in `assume` blocks for the
/// LOCAL premises; params from the abstracted caller-locals; deterministic hash name.
fn packageArith(prove: *Prove, w: *const Walk, b: *Accelerant.Builder, comptime prefix: []const u8, goal_p: TermId, prems: []const ArithPremise, abs: common.FvarAbstraction, body_steps: []const ast.Step, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    // LOCAL premises become schema antecedents (restated by hypothesis, discharged at the
    // call site) in ref order; GLOBAL premises are cited inside the cert (not antecedents).
    var local_cites: std.ArrayList(EqCert.RuleCite) = .empty;
    var local_formulae: std.ArrayList(TermId) = .empty;
    for (prems) |p| if (p.local) {
        try local_cites.append(prove.ctx.arena, .{ .local = .{ .hyp = p.hyp } });
        try local_formulae.append(prove.ctx.arena, p.formula);
    };

    const kept = try common.keptPremises(prove, local_cites.items, local_formulae.items, body_steps);
    const kept_refs = try common.keptRefTokens(prove, w, c.refs, local_cites.items, body_steps);
    const inner_prop = try common.impliesChain(prove, goal_p, kept);
    const steps = try common.wrapSimplifyPremises(prove, b, local_cites.items, local_formulae.items, goal_p, body_steps);

    const body_expr = try b.termExpr(inner_prop);
    const params = try prove.ctx.arena.alloc(ast.SchemaParam, abs.names.len);
    for (abs.names, abs.sorts, params) |name, sort, *pp| {
        pp.* = .{ .name = b.tok(name), .kind = .{ .value = b.sortTok(sort) } };
    }

    const hash = Schema.termHash(prove.ctx.interner, prove.pool, inner_prop);
    const name = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, prefix ++ "{{{x}}}", .{hash}));
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = abs.args,
        .premises = kept_refs,
        .seen = b.seen.items,
        .fvar_binds = try common.fvarBinds(prove, w, abs),
    };
}

/// `fallback(thm)` path: the certifier chain declined (or the goal isn't in the certifiable
/// fragment) but the goal is an INSTANCE of the manually-proven theorem `fb`. Emit the cert:
/// cite `fb`, apply_at at the inferred witnesses, then modus_ponens each `->` antecedent
/// against the matching cited ref. Every step kernel-checked. Fast-path when `fb`'s statement
/// α-equals the goal (cite it directly). Packages the synthetic schema.
fn buildArithFallback(prove: *Prove, w: *const Walk, b: *Accelerant.Builder, fb: lexer.Token, goal_p: TermId, prems: []const ArithPremise, abs: common.FvarAbstraction, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    const fact = try prove.resolveFactRef(fb);
    const key = prove.ctx.interner.keyOf(fact).fact;
    const formula = try prove.pool.copyIn(prove.ctx.interner, key.formula);
    const is_axiom = key.kind == .axiom;
    var cert: ArithCert = .{ .p = prove, .b = b, .c = c };
    var block: std.ArrayList(ast.Step) = .empty;

    // FAST PATH: fb IS the goal (α-equal) — cite it directly.
    if (prove.pool.alphaEq(formula, goal_p)) {
        const word: []const u8 = if (is_axiom) "axiom" else "theorem";
        const label = try prove.freshNamed("arith-fallback");
        const refs = try prove.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = fb;
        try block.append(prove.ctx.arena, try b.claimStep(label, try b.termExpr(goal_p), .by, try common.internStrRt(prove, word), &.{}, refs));
        return try packageArith(prove, w, b, "arithmetic", goal_p, prems, abs, block.items, c);
    }

    // SPECIALIZE PATH: peel fb's ∀ prefix into pattern fvars, split leading `->` antecedents.
    var pattern: std.ArrayList(term.Node.Fvar) = .empty;
    var f = formula;
    while (true) {
        const node = prove.pool.get(f);
        if (node == .quant and node.quant.q == .forall) {
            const fv: term.Node.Fvar = .{ .name = try prove.freshNamed("fallback-var"), .sort = node.quant.sort };
            try pattern.append(prove.ctx.arena, fv);
            f = try prove.pool.open(node.quant.body, try prove.pool.add(.{ .fvar = fv }));
        } else break;
    }
    var antecedents: std.ArrayList(TermId) = .empty;
    while (true) {
        const node = prove.pool.get(f);
        if (node == .bin and node.bin.op == .implies) {
            try antecedents.append(prove.ctx.arena, node.bin.lhs);
            f = node.bin.rhs;
        } else break;
    }
    // infer each pattern var by matching the consequent against the goal.
    var binds: std.AutoHashMapUnmanaged(StrId, TermId) = .empty;
    if (!try arithMatchPattern(prove, pattern.items, f, goal_p, &binds)) {
        return prove.fail(fb.start, "fallback theorem '{s}' does not prove this goal (its conclusion does not match, even after specialization)", .{prove.text(fb)});
    }
    const witnesses = try prove.ctx.arena.alloc(TermId, pattern.items.len);
    for (pattern.items, witnesses) |pv, *out| {
        out.* = binds.get(pv.name) orelse
            return prove.fail(fb.start, "fallback theorem '{s}' does not prove this goal (variable unconstrained by the conclusion)", .{prove.text(fb)});
    }

    // resolve each antecedent (at the witnesses) to a matching cited ref.
    const ant_labels = try prove.ctx.arena.alloc(StrId, antecedents.items.len);
    for (antecedents.items, ant_labels) |ant_raw, *out_label| {
        var ant = ant_raw;
        for (pattern.items, witnesses) |pv, wit| ant = try prove.pool.substFvar(ant, pv.name, wit);
        var matched: ?StrId = null;
        for (prems) |p| {
            if (prove.pool.alphaEq(p.formula, ant)) {
                matched = if (p.local) p.hyp else try cert.citeGlobalPremise(&block, p);
                break;
            }
        }
        out_label.* = matched orelse
            return prove.fail(fb.start, "fallback theorem '{s}' needs a hypothesis '{s}' — supply it as a ref to the arithmetic step", .{ prove.text(fb), try prove.renderTerm(ant) });
    }

    // emit: cite fb, apply_at at each witness, modus_ponens each antecedent.
    const word: []const u8 = if (is_axiom) "axiom" else "theorem";
    const cite_label = try prove.freshNamed("arith-fallback");
    const cite_refs = try prove.ctx.arena.alloc(lexer.Token, 1);
    cite_refs[0] = fb;
    try block.append(prove.ctx.arena, try b.claimStep(cite_label, try b.termExpr(formula), .by, try common.internStrRt(prove, word), &.{}, cite_refs));
    const elim = try cert.elimChain(&block, cite_label, formula, witnesses);
    var cur_label = elim.label;
    var cur_formula = elim.formula;
    for (ant_labels) |al| {
        const imp = prove.pool.get(cur_formula).bin;
        cur_label = try cert.claim(&block, imp.rhs, "modus_ponens", &.{}, &.{ cur_label, al });
        cur_formula = imp.rhs;
    }
    return try packageArith(prove, w, b, "arithmetic", goal_p, prems, abs, block.items, c);
}

/// First-order match: bind each `pattern` fvar (by name) so substituting yields `target`. Iterative
/// parallel two-tree walk (was native recursion) over a work-stack of `(pat, target)` pairs that
/// must ALL match (a conjunction — stack order irrelevant; the `binds` re-encounter check is
/// order-independent). Scratch on ctx.gpa; OOM → no match.
fn arithMatchPattern(prove: *Prove, pattern: []const term.Node.Fvar, pat: TermId, target: TermId, binds: *std.AutoHashMapUnmanaged(StrId, TermId)) Error!bool {
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList([2]TermId) = .empty;
    try stack.append(wa, .{ pat, target });
    while (stack.pop()) |pair| {
        const p = pair[0];
        const t = pair[1];
        const pn = prove.pool.get(p);
        if (pn == .fvar) {
            const bound = for (pattern) |pv| {
                if (pv.name == pn.fvar.name) break true;
            } else false;
            if (bound) {
                if (binds.get(pn.fvar.name)) |prev| {
                    if (!prove.pool.alphaEq(prev, t)) return false;
                } else binds.put(prove.ctx.arena, pn.fvar.name, t) catch return error.OutOfMemory;
                continue;
            }
            const tn = prove.pool.get(t);
            if (!(tn == .fvar and tn.fvar.name == pn.fvar.name and tn.fvar.sort == pn.fvar.sort)) return false;
            continue;
        }
        const tn = prove.pool.get(t);
        if (std.meta.activeTag(pn) != std.meta.activeTag(tn)) return false;
        switch (pn) {
            .bvar => if (pn.bvar != tn.bvar) return false,
            .fvar => unreachable,
            .app => |a| {
                if (a.sym != tn.app.sym or a.args.len != tn.app.args.len) return false;
                for (prove.pool.args(a), prove.pool.args(tn.app)) |x, y| try stack.append(wa, .{ x, y });
            },
            .pred => |a| {
                if (a.sym != tn.pred.sym or a.args.len != tn.pred.args.len) return false;
                for (prove.pool.args(a), prove.pool.args(tn.pred)) |x, y| try stack.append(wa, .{ x, y });
            },
            .eq => |pp| {
                try stack.append(wa, .{ pp.lhs, tn.eq.lhs });
                try stack.append(wa, .{ pp.rhs, tn.eq.rhs });
            },
            .not => |tt| try stack.append(wa, .{ tt, tn.not }),
            .bin => |bb| {
                if (bb.op != tn.bin.op) return false;
                try stack.append(wa, .{ bb.lhs, tn.bin.lhs });
                try stack.append(wa, .{ bb.rhs, tn.bin.rhs });
            },
            .quant => |q| {
                if (!(q.q == tn.quant.q and q.sort == tn.quant.sort)) return false;
                try stack.append(wa, .{ q.body, tn.quant.body });
            },
        }
    }
    return true;
}

/// The Farkas certifier — order-composition / infeasibility over the difference-logic edges.
/// (Not exercised by the target fixtures; declines for now — a follow-up port.)
/// A proved strict-order hypothesis `less_than(lo, hi)`: its endpoints (as terms) and the label
/// of the step proving it (a restated `->` antecedent, or a derived scaled/summed edge).
const OrderHyp = struct { lo: TermId, hi: TermId, ref: StrId };

/// The Farkas certifier over the difference-logic fragment. A goal
/// `forall v..; H1 -> … -> Hn -> C` whose Hi are strict-order atoms `less_than(s, t)` is
/// certified by composing them with `lessThanTransitive`. Three conclusion shapes:
///   (a) order composition `less_than(s, t)` (s != t): fold a path s < … < t;
///   (b) prove-loop `less_than(x, x)`: fold a cycle;
///   (c) INFEASIBILITY of an arbitrary conclusion: fold a cycle to `less_than(x, x)`, contradict
///       with `lessThanIrreflexive`, then `ex_falso`.
/// Stage 1 (scaling) lifts a hypothesis by a literal coefficient via
/// `multiplicationPreservesOrder`; stage 2 (sum) combines two edges over distinct variables via
/// `additionPreservesOrder`. Declines (false) on any out-of-fragment shape.
fn arithFarkasCert(prove: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, symbols_in: Symbols) Error!bool {
    var symbols = symbols_in;
    const less_than = symbols.less_than orelse return false;

    // 1. peel the ∀ prefix into eigenvariables; the body is `H1 -> … -> Hn -> C`.
    const peel = try arithPeel(prove, goal_p);

    // A pure-order fixture (only `less_than` + a bare sort in scope, no arithmetic op) leaves
    // `symbols.nat` unanchored; recover it from the quantified eigenvariables' sort so the order
    // lemmas (`lessThanTransitive`/`lessThanIrreflexive`) can be built.
    if (symbols.nat == null and peel.eigen.len != 0) symbols.nat = peel.eigen[0].sort;
    if (symbols.nat == null) return false;
    if ((try arithLemmaFormula(prove, "lessThanTransitive", symbols)) == null) return false;

    // 2. peel the `->` antecedent chain — each must be a strict-order atom — recording each as a
    //    difference-logic edge (nodes = distinct endpoint terms) with the label that will restate
    //    it by hypothesis inside its assume block. `residual[k]` = the formula proved inside
    //    assume[k] (the conclusion of the remaining chain).
    var edges: std.ArrayList(farkas.Edge) = .empty;
    var hyps: std.ArrayList(OrderHyp) = .empty;
    var node_ids: std.ArrayList(TermId) = .empty;
    var blk_labels: std.ArrayList(StrId) = .empty; // the assume-block label per antecedent
    var ante_formulae: std.ArrayList(TermId) = .empty;
    var body = peel.body;
    while (true) {
        const node = prove.pool.get(body);
        if (node != .bin or node.bin.op != .implies) break;
        const ante = node.bin.lhs;
        const an = prove.pool.get(ante);
        if (an != .pred or !ac.symIs(an.pred.sym, less_than) or an.pred.args.len != 2) return false;
        const args = prove.pool.args(an.pred);
        const blk_label = try prove.freshNamed("given-order");
        const restate_label = try prove.freshNamed("order-hyp"); // the OrderHyp ref (the fold cites this)
        try edges.append(prove.ctx.arena, .{
            .lo = try farkasNodeId(prove, &node_ids, args[0]),
            .hi = try farkasNodeId(prove, &node_ids, args[1]),
        });
        try hyps.append(prove.ctx.arena, .{ .lo = args[0], .hi = args[1], .ref = restate_label });
        try blk_labels.append(prove.ctx.arena, blk_label);
        try ante_formulae.append(prove.ctx.arena, ante);
        body = node.bin.rhs;
    }
    if (edges.items.len == 0) return false; // nothing to combine: not Farkas
    const base_count = edges.items.len;

    // the fold + derived-edge steps live in an INNER block that runs inside the innermost assume
    // (where every antecedent hypothesis is in scope).
    var inner: std.ArrayList(ast.Step) = .empty;

    // 2b. COEFFICIENT SCALING: derive `less_than(mul(k,lo), mul(k,hi))` edges for each literal k
    //     the conclusion / hypotheses mention.
    var literals: std.ArrayList(usize) = .empty;
    try collectFarkasScaleLiterals(prove, symbols, body, &literals);
    for (hyps.items[0..base_count]) |h| {
        try collectFarkasScaleLiterals(prove, symbols, h.lo, &literals);
        try collectFarkasScaleLiterals(prove, symbols, h.hi, &literals);
    }
    if (literals.items.len != 0) {
        if (!try emitFarkasScaledEdges(prove, cert, &inner, symbols, literals.items, base_count, &edges, &hyps, &node_ids)) return false;
    }

    // 2c. SUM PATH: if the conclusion is `less_than(add(_,_), add(_,_))` no single edge proves,
    //     derive a summed edge from a pair of base hypotheses.
    if (symbols.add != null) {
        const cn0 = prove.pool.get(body);
        const wants_sum = cn0 == .pred and ac.symIs(cn0.pred.sym, less_than) and cn0.pred.args.len == 2 and
            isFarkasAddSum(prove, symbols, prove.pool.args(cn0.pred)[0]);
        if (wants_sum and base_count >= 2) {
            if (!try emitFarkasSumEdge(prove, cert, &inner, symbols, body, base_count, &edges, &hyps, &node_ids)) return false;
        }
    }

    // 3. prove the conclusion `body` from the order edges, dispatching on its shape.
    const concl_label = (try emitFarkasConclusion(prove, cert, &inner, symbols, less_than, body, edges.items, hyps.items, &node_ids)) orelse return false;

    // 4. wrap `inner` in nested assume blocks (innermost antecedent first): each block restates
    //    its hypothesis, runs the (progressively) exported proof, and `discharge` exports
    //    `H_k -> … -> C`. Mirrors `wrapSimplifyPremises`.
    _ = concl_label;
    var carry_steps = inner.items;
    var carry_formula = body; // the conclusion proved inside the current level
    var k = base_count;
    while (k > 0) {
        k -= 1;
        const blk_label = blk_labels.items[k];
        const restate_label = hyps.items[k].ref;
        var blk_body = try std.ArrayList(ast.Step).initCapacity(prove.ctx.arena, carry_steps.len + 1);
        // restate the assumption (label = the OrderHyp `ref` the fold cites) via `hypothesis`
        // citing the enclosing assume block.
        blk_body.appendAssumeCapacity(try cert.b.claimStep(restate_label, try cert.b.termExpr(ante_formulae.items[k]), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, blk_label)));
        blk_body.appendSliceAssumeCapacity(carry_steps);

        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, try cert.b.assumeStep(blk_label, try cert.b.termExpr(ante_formulae.items[k]), blk_body.items));
        const exported = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = ante_formulae.items[k], .rhs = carry_formula } });
        _ = try cert.claim(&lvl, exported, "discharge", &.{}, &.{blk_label});
        carry_formula = exported;
        carry_steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }

    // 5. wrap in the ∀ fix/generalize shell.
    const wrapped = try wrapArithForall(prove, cert, peel.eigen, peel.body, carry_steps);
    try out.appendSlice(prove.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Intern a term as an abstract Farkas node identity (by structural order).
fn farkasNodeId(prove: *Prove, list: *std.ArrayList(TermId), t: TermId) Error!usize {
    for (list.items, 0..) |x, i| {
        if (prove.pool.termOrder(x, t) == .eq) return i;
    }
    try list.append(prove.ctx.arena, t);
    return list.items.len - 1;
}

/// Prove the Farkas conclusion `body`, returning the label of a step proving it (or null to
/// decline). (a)/(b): if `body` is an order atom `less_than(s, t)`, compose a chain s < … < t
/// (a cycle when s == t). (c): otherwise fold ANY cycle to `less_than(x, x)`, contradict with
/// `lessThanIrreflexive`, and `ex_falso` proves the (arbitrary) conclusion.
fn emitFarkasConclusion(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: Symbols, less_than: term.SymId, body: TermId, edges: []const farkas.Edge, hyps: []const OrderHyp, node_ids: *std.ArrayList(TermId)) Error!?StrId {
    const cn = prove.pool.get(body);
    const is_order = cn == .pred and ac.symIs(cn.pred.sym, less_than) and cn.pred.args.len == 2;

    if (is_order) {
        const cargs = prove.pool.args(cn.pred);
        const from = try farkasNodeId(prove, node_ids, cargs[0]);
        const to = try farkasNodeId(prove, node_ids, cargs[1]);
        if (try farkas.compose(prove.ctx.arena, edges, from, to)) |path| {
            return try emitFarkasFold(prove, cert, block, symbols, path.chain, hyps);
        }
        // no direct chain: fall through to the infeasibility cap.
    }

    // (c) INFEASIBILITY CAP.
    if ((try arithLemmaFormula(prove, "lessThanIrreflexive", symbols)) == null) return null;
    const refutation = (try farkas.refute(prove.ctx.arena, edges, null)) orelse return null;
    const cycle_label = try emitFarkasFold(prove, cert, block, symbols, refutation.chain, hyps);
    const cnode = node_ids.items[refutation.node];

    // cite lessThanIrreflexive, apply_at at cnode → `not less_than(cnode, cnode)`; ex_falso
    // against the folded `less_than(cnode, cnode)` proves the (arbitrary) `body`.
    const irr_stmt = (try arithLemmaFormula(prove, "lessThanIrreflexive", symbols)).?;
    const irr_label = try cert.citeLemma(block, "lessThanIrreflexive", irr_stmt);
    const not_lt = try cert.elimChain(block, irr_label, irr_stmt, &.{cnode});
    return try cert.claim(block, body, "ex_falso", &.{}, &.{ cycle_label, not_lt.label });
}

/// Fold an order chain (edge indices, each hi linking to the next lo) into a single proof
/// `less_than(chain-first-lo, chain-last-hi)` by composing consecutive hypotheses with
/// `lessThanTransitive`. Returns the label of that proof (the sole hypothesis for a one-edge
/// chain).
fn emitFarkasFold(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: Symbols, chain: []const usize, hyps: []const OrderHyp) Error!StrId {
    var acc_label = hyps[chain[0]].ref;
    const acc_lo = hyps[chain[0]].lo;
    var acc_hi = hyps[chain[0]].hi;

    const tr_stmt = (try arithLemmaFormula(prove, "lessThanTransitive", symbols)).?;
    for (chain[1..]) |idx| {
        const next = hyps[idx];
        // lessThanTransitive(acc_lo, acc_hi, next.hi):
        //   less_than(acc_lo,acc_hi) -> less_than(acc_hi,next.hi) -> less_than(acc_lo,next.hi)
        const tr_label = try cert.citeLemma(block, "lessThanTransitive", tr_stmt);
        const elim = try cert.elimChain(block, tr_label, tr_stmt, &.{ acc_lo, acc_hi, next.hi });
        const inner = prove.pool.get(elim.formula).bin.rhs; // less_than(acc_hi,next.hi) -> less_than(acc_lo,next.hi)
        const mp1 = try cert.claim(block, inner, "modus_ponens", &.{}, &.{ elim.label, acc_label });
        const concl = prove.pool.get(inner).bin.rhs; // less_than(acc_lo, next.hi)
        acc_label = try cert.claim(block, concl, "modus_ponens", &.{}, &.{ mp1, next.ref });
        acc_hi = next.hi;
    }
    return acc_label;
}

/// If `t` is a ground successor tower `succ^k(ZERO)`, return k, else 0.
fn farkasLiteral(prove: *Prove, symbols: Symbols, t: TermId) usize {
    var k: usize = 0;
    var cur = t;
    while (true) {
        const node = prove.pool.get(cur);
        if (node == .app and ac.symIs(node.app.sym, symbols.succ) and node.app.args.len == 1) {
            k += 1;
            cur = prove.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and ac.symIs(node.app.sym, symbols.zero) and node.app.args.len == 0) return k;
        return 0;
    }
}

/// Scan `t` for `mul(<literal>, x)` subterms, collecting distinct literal coefficients k >= 2.
fn collectFarkasScaleLiterals(prove: *Prove, symbols: Symbols, t: TermId, out: *std.ArrayList(usize)) Error!void {
    // collect the distinct scale literals k>=2 from `mul(k, _)` subterms. Iterative work-stack; the
    // `out` dedup makes order-independent.
    var scratch: std.heap.ArenaAllocator = .init(prove.ctx.gpa);
    defer scratch.deinit();
    const wa = scratch.allocator();
    var stack: std.ArrayList(TermId) = .empty;
    try stack.append(wa, t);
    while (stack.pop()) |cur| {
        const node = prove.pool.get(cur);
        switch (node) {
            .app, .pred => |a| {
                if (ac.symIs(a.sym, symbols.mul) and a.args.len == 2) {
                    const args = prove.pool.args(a);
                    const k = farkasLiteral(prove, symbols, args[0]);
                    if (k >= 2) {
                        for (out.items) |x| {
                            if (x == k) break;
                        } else try out.append(prove.ctx.arena, k);
                    }
                }
                try prove.pool.pushChildren(&stack, wa, node);
            },
            .eq, .not, .bin, .quant => try prove.pool.pushChildren(&stack, wa, node),
            else => {},
        }
    }
}

/// Is `t` an `add(_, _)` application?
fn isFarkasAddSum(prove: *Prove, symbols: Symbols, t: TermId) bool {
    const node = prove.pool.get(t);
    return node == .app and ac.symIs(node.app.sym, symbols.add) and node.app.args.len == 2;
}

/// For each base hypothesis and literal k, emit a SCALED edge `less_than(mul(k,lo), mul(k,hi))`
/// via `multiplicationPreservesOrder` (k = succ(c), so apply_at at c = succ^{k-1}(ZERO)),
/// appending it to `edges`/`hyps`/`node_ids`. Returns false (declines) if the lemma or the
/// mul/succ/zero symbols are absent.
fn emitFarkasScaledEdges(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: Symbols, literals: []const usize, base_count: usize, edges: *std.ArrayList(farkas.Edge), hyps: *std.ArrayList(OrderHyp), node_ids: *std.ArrayList(TermId)) Error!bool {
    const succ = symbols.succ orelse return false;
    const zero_sym = symbols.zero orelse return false;
    const mpo_stmt = (try arithLemmaFormula(prove, "multiplicationPreservesOrder", symbols)) orelse return false;
    const zero = try prove.pool.addApp(.app, zero_sym, &.{});

    for (literals) |k| {
        // c = succ^{k-1}(ZERO), so succ(c) = k.
        var c = zero;
        for (0..k - 1) |_| c = try prove.pool.addApp(.app, succ, &.{c});
        for (0..base_count) |bi| {
            const h = hyps.items[bi];
            // multiplicationPreservesOrder(h.lo, h.hi, c):
            //   less_than(h.lo,h.hi) -> less_than(mul(succ(c),h.lo), mul(succ(c),h.hi))
            const mpo_label = try cert.citeLemma(block, "multiplicationPreservesOrder", mpo_stmt);
            const elim = try cert.elimChain(block, mpo_label, mpo_stmt, &.{ h.lo, h.hi, c });
            const concl = prove.pool.get(elim.formula).bin.rhs; // the scaled order atom
            const scaled_label = try cert.claim(block, concl, "modus_ponens", &.{}, &.{ elim.label, h.ref });
            const scaled = prove.pool.get(concl).pred;
            const sargs = prove.pool.args(scaled);
            try edges.append(prove.ctx.arena, .{
                .lo = try farkasNodeId(prove, node_ids, sargs[0]),
                .hi = try farkasNodeId(prove, node_ids, sargs[1]),
            });
            try hyps.append(prove.ctx.arena, .{ .lo = sargs[0], .hi = sargs[1], .ref = scaled_label });
        }
    }
    return true;
}

/// The conclusion is `less_than(add(A,B), add(C,D))`. Find base hypotheses proving A<C and B<D,
/// derive the summed edge `less_than(add(A,B), add(C,D))`, and append it. Returns false
/// (declines) when the matching hypotheses or the needed lemmas are absent.
fn emitFarkasSumEdge(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), symbols: Symbols, body: TermId, base_count: usize, edges: *std.ArrayList(farkas.Edge), hyps: *std.ArrayList(OrderHyp), node_ids: *std.ArrayList(TermId)) Error!bool {
    const add = symbols.add orelse return false;
    const less_than = symbols.less_than orelse return false;
    const cargs = prove.pool.args(prove.pool.get(body).pred);
    const lhs_args = prove.pool.args(prove.pool.get(cargs[0]).app); // [A, B]
    const rhs_args = prove.pool.args(prove.pool.get(cargs[1]).app); // [C, D]
    const a = lhs_args[0];
    const bb = lhs_args[1];
    const cc = rhs_args[0];
    const dd = rhs_args[1];
    // find base hyps A<C and B<D.
    var ha: ?OrderHyp = null;
    var hb: ?OrderHyp = null;
    for (hyps.items[0..base_count]) |h| {
        if (prove.pool.termOrder(h.lo, a) == .eq and prove.pool.termOrder(h.hi, cc) == .eq) ha = h;
        if (prove.pool.termOrder(h.lo, bb) == .eq and prove.pool.termOrder(h.hi, dd) == .eq) hb = h;
    }
    const first = ha orelse return false;
    const second = hb orelse return false;

    const apo_stmt = (try arithLemmaFormula(prove, "additionPreservesOrder", symbols)) orelse return false;
    const comm_stmt = (try arithLemmaFormula(prove, "addIsCommutative", symbols)) orelse return false;
    const tr_stmt = (try arithLemmaFormula(prove, "lessThanTransitive", symbols)) orelse return false;

    const p = first.lo;
    const q = first.hi;
    const r = second.lo;
    const s = second.hi;

    // lift p<q by c:=r via additionPreservesOrder → add(r,p) < add(r,q).
    const apo1_label = try cert.citeLemma(block, "additionPreservesOrder", apo_stmt);
    const apo1 = try cert.elimChain(block, apo1_label, apo_stmt, &.{ p, q, r });
    const lifted1 = prove.pool.get(apo1.formula).bin.rhs; // less_than(add(r,p), add(r,q))
    const rp_lt_rq = try cert.claim(block, lifted1, "modus_ponens", &.{}, &.{ apo1.label, first.ref });

    // commute add(r,p)=add(p,r), add(r,q)=add(q,r); rewrite both.
    const pr = try prove.pool.addApp(.app, add, &.{ p, r });
    const rq = try prove.pool.addApp(.app, add, &.{ r, q });
    const qr = try prove.pool.addApp(.app, add, &.{ q, r });
    const eq_rp = try emitFarkasCommEq(cert, block, comm_stmt, r, p); // add(r,p)=add(p,r)
    const eq_rq = try emitFarkasCommEq(cert, block, comm_stmt, r, q); // add(r,q)=add(q,r)
    const pr_lt_rq_f = try prove.pool.addApp(.pred, less_than, &.{ pr, rq });
    const pr_lt_rq = try cert.claim(block, pr_lt_rq_f, "rewrite", &.{}, &.{ eq_rp, rp_lt_rq });
    const pr_lt_qr_f = try prove.pool.addApp(.pred, less_than, &.{ pr, qr });
    const pr_lt_qr = try cert.claim(block, pr_lt_qr_f, "rewrite", &.{}, &.{ eq_rq, pr_lt_rq });

    // lift r<s by c:=q via additionPreservesOrder → add(q,r) < add(q,s).
    const apo2_label = try cert.citeLemma(block, "additionPreservesOrder", apo_stmt);
    const apo2 = try cert.elimChain(block, apo2_label, apo_stmt, &.{ r, s, q });
    const lifted2 = prove.pool.get(apo2.formula).bin.rhs; // less_than(add(q,r), add(q,s))
    const qr_lt_qs = try cert.claim(block, lifted2, "modus_ponens", &.{}, &.{ apo2.label, second.ref });

    // chain add(p,r) < add(q,r) < add(q,s) via lessThanTransitive.
    const qs = try prove.pool.addApp(.app, add, &.{ q, s });
    const tr_label = try cert.citeLemma(block, "lessThanTransitive", tr_stmt);
    const chain = try cert.elimChain(block, tr_label, tr_stmt, &.{ pr, qr, qs });
    const chain_inner = prove.pool.get(chain.formula).bin.rhs;
    const chain2 = try cert.claim(block, chain_inner, "modus_ponens", &.{}, &.{ chain.label, pr_lt_qr });
    const summed_f = prove.pool.get(chain_inner).bin.rhs; // less_than(add(p,r), add(q,s))
    const summed_label = try cert.claim(block, summed_f, "modus_ponens", &.{}, &.{ chain2, qr_lt_qs });

    try edges.append(prove.ctx.arena, .{
        .lo = try farkasNodeId(prove, node_ids, pr),
        .hi = try farkasNodeId(prove, node_ids, qs),
    });
    try hyps.append(prove.ctx.arena, .{ .lo = pr, .hi = qs, .ref = summed_label });
    return true;
}

/// Emit `add(x,y) = add(y,x)` via addIsCommutative(x, y). Returns the equation step's label.
fn emitFarkasCommEq(cert: *ArithCert, block: *std.ArrayList(ast.Step), comm_stmt: TermId, x: TermId, y: TermId) Error!StrId {
    const comm_label = try cert.citeLemma(block, "addIsCommutative", comm_stmt);
    const elim = try cert.elimChain(block, comm_label, comm_stmt, &.{ x, y });
    return elim.label;
}

/// The MIXED-D2 certifier: a goal whose boolean structure mixes propositional atoms with
/// linear/order (theory) atoms. Peel the ∀ prefix + strip the leading `->` premises (surfaced
/// as local hypotheses), then prove the residual body by a propositional-skeleton proof
/// (excluded-middle split + `common_conclusion` per atom, like the tautology cert) whose leaves are
/// discharged EITHER propositionally (an assumed literal) OR by the arithmetic equation/order
/// certs (a theory atom, closed from the branch's assumed theory literals). Every step is
/// kernel-checked. Declines (false) when `smt.decideMixed` doesn't confirm validity, when the
/// atom count exceeds the limit, or when a theory leaf can't be discharged.
/// Is `body` a skeleton the mixed certifier can decompose into atoms — i.e. quantifier-free?
/// A bare atom counts (see `arithMixedCert`); a quantifier does not, its binders having been
/// peeled into eigenvariables before the body is examined.
fn mixedCertShape(prove: *const Prove, body: TermId) bool {
    return prove.pool.get(body) != .quant;
}

fn arithMixedCert(prove: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const peel = try arithPeel(prove, goal_p);
    // strip the body's leading `->` antecedents into local hypotheses (assume blocks); each
    // becomes a theory/prop premise available to the skeleton + theory leaves.
    var body = peel.body;
    var strip_assumes: std.ArrayList(TermId) = .empty; // the stripped antecedents, in order
    while (true) {
        const node = prove.pool.get(body);
        if (node != .bin or node.bin.op != .implies) break;
        try strip_assumes.append(prove.ctx.arena, node.bin.lhs);
        body = node.bin.rhs;
    }
    // the body must be a SKELETON the atom decomposition can handle: any quantifier-free
    // proposition. A boolean combination is the motivating case, but a BARE atom belongs here
    // too — the equation certifier proves an equation by REWRITING, which cannot always
    // connect goal to premise (`sub(y,x) = succ(d)` from `add(x, succ(d)) = y`: the premise
    // rule fires on a term the goal does not contain), while the skeleton decides it
    // semantically. Gating on `bin`/`not` refused exactly that and declined the whole chain —
    // the pre-refactor engine's mixed certifier had no such gate (std/integer/divides.b4m:1073).
    if (!mixedCertShape(prove, body)) return false;

    // collect the atoms (premises + stripped antecedents + body); decide validity.
    var decide_prems: std.ArrayList(TermId) = .empty;
    for (prems) |p| try decide_prems.append(prove.ctx.arena, p.formula);
    try decide_prems.appendSlice(prove.ctx.arena, strip_assumes.items);
    if (symbols.nonneg) |nn| if (symbols.nat) |nat| {
        var seen: std.AutoHashMapUnmanaged(StrId, void) = .empty;
        try collectArithNonneg(prove, body, nat, nn, &seen, &decide_prems);
        for (decide_prems.items[0 .. prems.len + strip_assumes.items.len]) |pf| try collectArithNonneg(prove, pf, nat, nn, &seen, &decide_prems);
    };
    const verdict = smt.decideMixed(prove.ctx.arena, prove.pool, symbols, decide_prems.items, body) catch return error.OutOfMemory;
    if (verdict != .valid) return false;

    // the skeleton's atoms (premises + stripped + body); over-cap declines.
    var atoms: std.ArrayList(TermId) = .empty;
    for (prems) |p| try smt.collectAtoms(prove.ctx.arena, prove.pool, &atoms, p.formula);
    for (strip_assumes.items) |a| try smt.collectAtoms(prove.ctx.arena, prove.pool, &atoms, a);
    try smt.collectAtoms(prove.ctx.arena, prove.pool, &atoms, body);
    if (atoms.items.len > smt.atom_limit) return false;

    const assignment = try prove.ctx.arena.alloc(?bool, atoms.items.len);
    @memset(assignment, null);
    const lit_blocks = try prove.ctx.arena.alloc(?StrId, atoms.items.len);
    @memset(lit_blocks, null);

    // the stripped antecedents each get an assume-block (restated hypothesis); the cited
    // premises (LOCAL restated / GLOBAL cited) provide their labels directly.
    var mixed: MixedAst = .{
        .p = prove,
        .cert = cert,
        .body = body,
        .atoms = atoms.items,
        .assignment = assignment,
        .lit_blocks = lit_blocks,
        .symbols = symbols,
    };

    // emit the cited-premise + stripped-antecedent hypotheses so their theory atoms are
    // available to the leaves, then the skeleton proof. We build inside the ∀-`fix` shell
    // (via wrapArithForall) after assembling the body proof.
    var body_steps: std.ArrayList(ast.Step) = .empty;
    // GLOBAL cited premises: cite them; LOCAL cited premises: restated hyp label lives in the
    // schema-antecedent wrapper (packageArith). Register both as leaf-usable premises.
    for (prems) |p| {
        const label = if (p.local) p.hyp else try cert.citeGlobalPremise(&body_steps, p);
        try mixed.premise_labels.append(prove.ctx.arena, .{ .formula = p.formula, .label = label });
    }
    // stripped antecedents become assume blocks wrapping the rest; emit the skeleton inside the
    // innermost. Build the skeleton first, then nest the assume blocks outward.
    var inner: std.ArrayList(ast.Step) = .empty;
    // restate each stripped antecedent's hypothesis inside its block (labels created here).
    const strip_labels = try prove.ctx.arena.alloc(StrId, strip_assumes.items.len);
    const strip_blocks = try prove.ctx.arena.alloc(StrId, strip_assumes.items.len);
    for (strip_assumes.items, strip_labels, strip_blocks) |a, *lbl, *blk| {
        lbl.* = try prove.freshNamed("mixed-hyp");
        blk.* = try prove.freshNamed("mixed-assume");
        try mixed.premise_labels.append(prove.ctx.arena, .{ .formula = a, .label = lbl.* });
    }
    if (!try mixed.deriveGoal(&inner)) return false;

    // nest the stripped antecedents' assume blocks (innermost = last antecedent), exporting
    // `a_i -> …` out through each with discharge.
    var wrapped_body = inner.items;
    var residual = body;
    var i = strip_assumes.items.len;
    while (i > 0) {
        i -= 1;
        var blk_body: std.ArrayList(ast.Step) = .empty;
        try blk_body.append(prove.ctx.arena, try cert.b.claimStep(strip_labels[i], try cert.b.termExpr(strip_assumes.items[i]), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, strip_blocks[i])));
        try blk_body.appendSlice(prove.ctx.arena, wrapped_body);
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, try cert.b.assumeStep(strip_blocks[i], try cert.b.termExpr(strip_assumes.items[i]), blk_body.items));
        residual = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = strip_assumes.items[i], .rhs = residual } });
        _ = try cert.claim(&lvl, residual, "discharge", &.{}, &.{strip_blocks[i]});
        wrapped_body = lvl.items;
    }
    try body_steps.appendSlice(prove.ctx.arena, wrapped_body);

    // re-generalize under the ∀ eigenvariables.
    const wrapped = try wrapArithForall(prove, cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(prove.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// The mixed-skeleton certificate emitter (D2): a propositional excluded-middle/common_conclusion
/// skeleton over the goal's atoms whose leaves are discharged EITHER by an assumed literal
/// (propositional) OR by the arithmetic equation/order certs (a theory atom, closed from the
/// branch's assumed theory literals). Mirrors `common.TautAst` but adds theory-leaf discharge.
const MixedAst = struct {
    p: *Prove,
    cert: *ArithCert,
    body: TermId,
    atoms: []const TermId,
    assignment: []?bool,
    /// per atom: the assume-block LABEL whose hypothesis is the (positive/negative) literal
    lit_blocks: []?StrId,
    symbols: Symbols,
    /// premises (cited + stripped antecedents) usable as theory-leaf rewrite rules: formula +
    /// the label of a step/hypothesis proving it.
    premise_labels: std.ArrayList(struct { formula: TermId, label: StrId }) = .empty,

    pub fn pool(self: *const MixedAst) *term.Pool {
        return self.p.pool;
    }

    pub fn eval(self: *const MixedAst, f: TermId) ?bool {
        return smt.eval(self.pool(), self.atoms, self.assignment, f);
    }

    /// Is `atom` a theory (linear/order) atom the arithmetic certs can discharge?
    pub fn isTheory(self: *const MixedAst, atom: TermId) bool {
        return switch (self.pool().get(atom)) {
            .eq => true,
            .pred => |pr| ac.symIs(pr.sym, self.symbols.less_than),
            else => false,
        };
    }

    /// The assume-block label whose hypothesis is the literal for a propositional atom `f`.
    pub fn litBlock(self: *const MixedAst, f: TermId) StrId {
        for (self.atoms, self.lit_blocks) |a, blk| {
            if (self.pool().alphaEq(a, f)) return blk.?;
        }
        unreachable;
    }

    /// The theory literals assumed TRUE on the current branch (assigned atoms + always-true
    /// premises), as `ArithPremise`s the equation/order certs use as rewrite rules. Each needs
    /// a citable step label: an assigned atom cites its split assume-block hypothesis (restated
    /// into `block`); a premise cites its own label.
    pub fn theoryPremises(self: *MixedAst, block: *std.ArrayList(ast.Step)) Error![]const ArithPremise {
        var out: std.ArrayList(ArithPremise) = .empty;
        // premises whose formula is a theory atom (or a conjunction of them — restate atoms).
        for (self.premise_labels.items) |pl| {
            if (self.isTheory(pl.formula)) {
                try out.append(self.p.ctx.arena, .{ .formula = pl.formula, .local = true, .hyp = pl.label, .head = undefined, .is_axiom = false });
            }
        }
        // atoms assigned TRUE that are theory atoms: restate their literal hypothesis.
        for (self.atoms, self.assignment) |a, v| {
            if (v != true) continue;
            if (!self.isTheory(a)) continue;
            const restated = try self.p.freshNamed("mixed-theory");
            try block.append(self.p.ctx.arena, try self.cert.b.claimStep(restated, try self.cert.b.termExpr(a), .by, try self.p.internStr("hypothesis"), &.{}, try common.oneRef(self.p, self.cert.b, self.litBlock(a))));
            try out.append(self.p.ctx.arena, .{ .formula = a, .local = true, .hyp = restated, .head = undefined, .is_axiom = false });
        }
        return out.items;
    }

    /// Prove `self.body` in `block`. A refuted premise closes by `ex_falso`; a true goal derives
    /// structurally (theory leaves via the arith certs); a fully-decided branch that is
    /// theory-UNSAT derives a theory contradiction; otherwise split on the first unassigned
    /// atom via excluded-middle + `common_conclusion`.
    pub fn deriveGoal(self: *MixedAst, block: *std.ArrayList(ast.Step)) Error!bool {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        const Frame = union(enum) {
            expand: *std.ArrayList(ast.Step),
            arm_right: struct { idx: usize, right: *OpenBlock },
            finish: struct { block: *std.ArrayList(ast.Step), idx: usize, atom: TermId, not_atom: TermId, lem: StrId, left: *OpenBlock, right: *OpenBlock },
        };
        var work: std.ArrayList(Frame) = .empty;
        var failed = false;
        try work.append(sa, .{ .expand = block });

        while (work.pop()) |frame| {
            if (failed) continue; // a leaf/theory discharge failed; drain, then return false.
            switch (frame) {
                .expand => |blk| {
                    // a premise assumed false on this branch → ex_falso (rare; premises are true).
                    const refuted_idx: ?usize = for (self.premise_labels.items, 0..) |pl, i| {
                        if (self.eval(pl.formula) == false) break i;
                    } else null;
                    if (refuted_idx) |ri| {
                        const pl = self.premise_labels.items[ri];
                        if (try self.deriveFalse(blk, pl.formula)) |refuted| {
                            _ = try self.cert.claim(blk, self.body, "ex_falso", &.{}, &.{ pl.label, refuted });
                        } else failed = true;
                        continue;
                    }
                    if (self.eval(self.body) == true) {
                        if ((try self.deriveTrue(blk, self.body)) == null) failed = true;
                        continue;
                    }
                    // find the first unassigned atom.
                    const unassigned = for (self.assignment, 0..) |v, i| {
                        if (v == null) break i;
                    } else null;
                    if (unassigned == null) {
                        // fully decided, body false, no premise refuted: theory-UNSAT branch.
                        if (!try self.deriveTheoryContradiction(blk)) failed = true;
                        continue;
                    }
                    const idx = unassigned.?;
                    const atom = self.atoms[idx];
                    const not_atom = try self.pool().add(.{ .not = atom });
                    const disj = try self.pool().add(.{ .bin = .{ .op = .or_op, .lhs = atom, .rhs = not_atom } });
                    const lem = try self.emitLem(blk, atom, not_atom, disj);

                    const left = try sa.create(OpenBlock);
                    left.* = try self.openBlock();
                    const right = try sa.create(OpenBlock);
                    right.* = try self.openBlock();

                    try work.append(sa, .{ .finish = .{ .block = blk, .idx = idx, .atom = atom, .not_atom = not_atom, .lem = lem, .left = left, .right = right } });
                    try work.append(sa, .{ .arm_right = .{ .idx = idx, .right = right } });
                    self.assignment[idx] = true;
                    self.lit_blocks[idx] = left.label;
                    try work.append(sa, .{ .expand = &left.body });
                },
                .arm_right => |a| {
                    self.assignment[a.idx] = false;
                    self.lit_blocks[a.idx] = a.right.label;
                    try work.append(sa, .{ .expand = &a.right.body });
                },
                .finish => |c| {
                    try self.finishBlock(c.block, c.left, c.atom);
                    try self.finishBlock(c.block, c.right, c.not_atom);
                    self.assignment[c.idx] = null;
                    self.lit_blocks[c.idx] = null;
                    _ = try self.cert.claim(c.block, self.body, "common_conclusion", &.{}, &.{ c.lem, c.left.label, c.right.label });
                },
            }
        }
        return !failed;
    }

    /// A fully-decided theory-UNSAT branch: for each theory atom assigned FALSE, try to PROVE
    /// it (positively) from the true theory literals via the equation/order cert; on success,
    /// `ex_falso` the proof against the atom's assumed-false hypothesis, closing the branch to any
    /// goal. Returns false if no such contradiction can be built.
    pub fn deriveTheoryContradiction(self: *MixedAst, block: *std.ArrayList(ast.Step)) Error!bool {
        for (self.atoms, self.assignment) |a, v| {
            if (v != false) continue;
            if (!self.isTheory(a)) continue;
            var probe: std.ArrayList(ast.Step) = .empty;
            const tp = try self.theoryPremises(&probe);
            if (!try arithBodyEqCert(self.p, self.cert, &probe, a, tp, self.symbols)) continue;
            const proof = try arithLastLabel(self.p, probe.items);
            try block.appendSlice(self.p.ctx.arena, probe.items);
            // restate the assumed-false literal `not a` as a step (the assume-block hypothesis),
            // then `ex_falso` the positive proof against it (ex_falso wants s1 = P, s2 = not P).
            const not_a = try self.pool().add(.{ .not = a });
            const neg_ref = try self.emit(block, not_a, "hypothesis", &.{self.litBlock(a)});
            _ = try self.cert.claim(block, self.body, "ex_falso", &.{}, &.{ proof, neg_ref });
            return true;
        }
        return false;
    }

    const OpenBlock = struct { label: StrId, body: std.ArrayList(ast.Step) = .empty };

    pub fn openBlock(self: *MixedAst) Error!OpenBlock {
        return .{ .label = try self.p.freshNamed("mixed") };
    }

    pub fn finishBlock(self: *MixedAst, parent: *std.ArrayList(ast.Step), blk: *OpenBlock, formula: TermId) Error!void {
        try parent.append(self.p.ctx.arena, try self.cert.b.assumeStep(blk.label, try self.cert.b.termExpr(formula), blk.body.items));
    }

    pub fn hyp(self: *MixedAst, blk: *OpenBlock, formula: TermId) Error!StrId {
        const label = try self.p.freshNamed("mixed");
        try blk.body.append(self.p.ctx.arena, try self.cert.b.claimStep(label, try self.cert.b.termExpr(formula), .by, try self.p.internStr("hypothesis"), &.{}, try common.oneRef(self.p, self.cert.b, blk.label)));
        return label;
    }

    pub fn emit(self: *MixedAst, block: *std.ArrayList(ast.Step), formula: TermId, rule: []const u8, refs: []const StrId) Error!StrId {
        const toks = try self.p.ctx.arena.alloc(lexer.Token, refs.len);
        for (refs, toks) |r, *o| o.* = self.cert.b.tok(r);
        const label = try self.p.freshNamed("mixed");
        try block.append(self.p.ctx.arena, try self.cert.b.claimStep(label, try self.cert.b.termExpr(formula), .by, try common.internStrRt(self.p, rule), &.{}, toks));
        return label;
    }

    /// `atom or not atom` classically: contradiction on the negated disjunction, double_negation.
    pub fn emitLem(self: *MixedAst, block: *std.ArrayList(ast.Step), atom: TermId, not_atom: TermId, disj: TermId) Error!StrId {
        const not_disj = try self.pool().add(.{ .not = disj });
        const not_not = try self.pool().add(.{ .not = not_disj });
        var outer = try self.openBlock();
        const hyp_outer = try self.hyp(&outer, not_disj);
        var innerb = try self.openBlock();
        const hyp_inner = try self.hyp(&innerb, atom);
        const or_left = try self.emit(&innerb.body, disj, "either_left", &.{hyp_inner});
        try self.finishBlock(&outer.body, &innerb, atom);
        const derived_not = try self.emit(&outer.body, not_atom, "contradiction", &.{ innerb.label, or_left, hyp_outer });
        const or_right = try self.emit(&outer.body, disj, "either_right", &.{derived_not});
        try self.finishBlock(block, &outer, not_disj);
        const nn = try self.emit(block, not_not, "contradiction", &.{ outer.label, or_right, hyp_outer });
        return self.emit(block, disj, "double_negation", &.{nn});
    }

    /// Prove `f` (evaluates true) in `block`; return its label, or null on a theory-leaf
    /// discharge failure.
    pub fn deriveTrue(self: *MixedAst, block: *std.ArrayList(ast.Step), f: TermId) Error!?StrId {
        return self.deriveStructural(.true, block, f);
    }

    /// Prove `not f` (f evaluates false) in `block`; return its label, or null on failure.
    pub fn deriveFalse(self: *MixedAst, block: *std.ArrayList(ast.Step), f: TermId) Error!?StrId {
        return self.deriveStructural(.false, block, f);
    }

    const Mode = enum { true, false };

    /// The shared iterative engine behind `deriveTrue`/`deriveFalse` (was mutual native recursion
    /// over formula structure). Same post-order worklist as `common.TautAst.deriveStructural`, but a
    /// theory-leaf discharge can FAIL: on failure a leaf sets `failed`, the loop drains without
    /// emitting, and the entry returns null. Otherwise byte-identical step vocabulary + order.
    pub fn deriveStructural(self: *MixedAst, root_mode: Mode, root_block: *std.ArrayList(ast.Step), root_f: TermId) Error!?StrId {
        var scratch: std.heap.ArenaAllocator = .init(self.pool().gpa);
        defer scratch.deinit();
        const sa = scratch.allocator();

        const Frame = union(enum) {
            expand: struct { mode: Mode, block: *std.ArrayList(ast.Step), f: TermId },
            combine_and: struct { block: *std.ArrayList(ast.Step), f: TermId },
            combine_or_left: struct { block: *std.ArrayList(ast.Step), f: TermId },
            combine_or_right: struct { block: *std.ArrayList(ast.Step), f: TermId },
            combine_true_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId },
            combine_true_implies_absurd: struct { block: *std.ArrayList(ast.Step), f: TermId, blk: *OpenBlock, ante: TermId, conseq: TermId, hyp: StrId },
            combine_false_and: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, side: TermId, left_false: bool },
            combine_false_or: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, lhs: TermId, rhs: TermId },
            combine_false_implies: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId, rhs: TermId },
            combine_false_not: struct { block: *std.ArrayList(ast.Step), f: TermId, nf: TermId },
        };
        var work: std.ArrayList(Frame) = .empty;
        var results: std.ArrayList(StrId) = .empty;
        var failed = false;
        try work.append(sa, .{ .expand = .{ .mode = root_mode, .block = root_block, .f = root_f } });

        while (work.pop()) |frame| {
            if (failed) continue; // a theory leaf failed; drain without emitting.
            switch (frame) {
                .expand => |e| switch (e.mode) {
                    .true => switch (self.pool().get(e.f)) {
                        .bin => |bin| switch (bin.op) {
                            .and_op => {
                                try work.append(sa, .{ .combine_and = .{ .block = e.block, .f = e.f } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.lhs } });
                            },
                            .or_op => {
                                if (self.eval(bin.lhs) == true) {
                                    try work.append(sa, .{ .combine_or_left = .{ .block = e.block, .f = e.f } });
                                    try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.lhs } });
                                } else {
                                    try work.append(sa, .{ .combine_or_right = .{ .block = e.block, .f = e.f } });
                                    try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.rhs } });
                                }
                            },
                            .implies => {
                                const blk = try sa.create(OpenBlock);
                                blk.* = try self.openBlock();
                                if (self.eval(bin.rhs) == true) {
                                    try work.append(sa, .{ .combine_true_implies = .{ .block = e.block, .f = e.f, .blk = blk, .ante = bin.lhs } });
                                    try work.append(sa, .{ .expand = .{ .mode = .true, .block = &blk.body, .f = bin.rhs } });
                                } else {
                                    const h = try self.hyp(blk, bin.lhs);
                                    try work.append(sa, .{ .combine_true_implies_absurd = .{ .block = e.block, .f = e.f, .blk = blk, .ante = bin.lhs, .conseq = bin.rhs, .hyp = h } });
                                    try work.append(sa, .{ .expand = .{ .mode = .false, .block = &blk.body, .f = bin.lhs } });
                                }
                            },
                        },
                        .not => |inner| try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = inner } }),
                        else => {
                            // an atom assigned true. THEORY atom: discharge via arith cert; a
                            // failure bails the whole cert. Propositional: restate its assumption.
                            if (self.isTheory(e.f)) {
                                const tp = try self.theoryPremises(e.block);
                                if (!try arithBodyEqCert(self.p, self.cert, e.block, e.f, tp, self.symbols)) {
                                    failed = true;
                                } else {
                                    try results.append(sa, try arithLastLabel(self.p, e.block.items));
                                }
                            } else {
                                try results.append(sa, try self.emit(e.block, e.f, "hypothesis", &.{self.litBlock(e.f)}));
                            }
                        },
                    },
                    .false => switch (self.pool().get(e.f)) {
                        .bin => |bin| switch (bin.op) {
                            .and_op => {
                                const left_false = self.eval(bin.lhs) == false;
                                const side = if (left_false) bin.lhs else bin.rhs;
                                const nf = try self.pool().add(.{ .not = e.f });
                                try work.append(sa, .{ .combine_false_and = .{ .block = e.block, .f = e.f, .nf = nf, .side = side, .left_false = left_false } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = side } });
                            },
                            .or_op => {
                                const nf = try self.pool().add(.{ .not = e.f });
                                try work.append(sa, .{ .combine_false_or = .{ .block = e.block, .f = e.f, .nf = nf, .lhs = bin.lhs, .rhs = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bin.lhs } });
                            },
                            .implies => {
                                const nf = try self.pool().add(.{ .not = e.f });
                                try work.append(sa, .{ .combine_false_implies = .{ .block = e.block, .f = e.f, .nf = nf, .rhs = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .false, .block = e.block, .f = bin.rhs } });
                                try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = bin.lhs } });
                            },
                        },
                        .not => |inner| {
                            const nf = try self.pool().add(.{ .not = e.f });
                            try work.append(sa, .{ .combine_false_not = .{ .block = e.block, .f = e.f, .nf = nf } });
                            try work.append(sa, .{ .expand = .{ .mode = .true, .block = e.block, .f = inner } });
                        },
                        else => {
                            const nf = try self.pool().add(.{ .not = e.f });
                            try results.append(sa, try self.emit(e.block, nf, "hypothesis", &.{self.litBlock(e.f)}));
                        },
                    },
                },
                .combine_and => |c| {
                    const right = results.pop().?;
                    const left = results.pop().?;
                    const rule: []const u8 = if (self.p.isBiconditionalShape(c.f)) "make_equivalence" else "both";
                    try results.append(sa, try self.emit(c.block, c.f, rule, &.{ left, right }));
                },
                .combine_or_left => |c| {
                    const l = results.pop().?;
                    try results.append(sa, try self.emit(c.block, c.f, "either_left", &.{l}));
                },
                .combine_or_right => |c| {
                    const r = results.pop().?;
                    try results.append(sa, try self.emit(c.block, c.f, "either_right", &.{r}));
                },
                .combine_true_implies => |c| {
                    _ = results.pop().?;
                    try self.finishBlock(c.block, c.blk, c.ante);
                    try results.append(sa, try self.emit(c.block, c.f, "discharge", &.{c.blk.label}));
                },
                .combine_true_implies_absurd => |c| {
                    const refuted = results.pop().?;
                    _ = try self.emit(&c.blk.body, c.conseq, "ex_falso", &.{ c.hyp, refuted });
                    try self.finishBlock(c.block, c.blk, c.ante);
                    try results.append(sa, try self.emit(c.block, c.f, "discharge", &.{c.blk.label}));
                },
                .combine_false_and => |c| {
                    const refuted = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    const elim = try self.emit(&blk.body, c.side, if (c.left_false) "and_lhs" else "and_rhs", &.{h});
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, elim, refuted }));
                },
                .combine_false_or => |c| {
                    const not_right = results.pop().?;
                    const not_left = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    var left = try self.openBlock();
                    _ = try self.hyp(&left, c.lhs);
                    try self.finishBlock(&blk.body, &left, c.lhs);
                    var right = try self.openBlock();
                    const rh = try self.hyp(&right, c.rhs);
                    _ = try self.emit(&right.body, c.lhs, "ex_falso", &.{ rh, not_right });
                    try self.finishBlock(&blk.body, &right, c.rhs);
                    const conc = try self.emit(&blk.body, c.lhs, "common_conclusion", &.{ h, left.label, right.label });
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, conc, not_left }));
                },
                .combine_false_implies => |c| {
                    const not_conseq = results.pop().?;
                    const ante = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    const conseq = try self.emit(&blk.body, c.rhs, "modus_ponens", &.{ h, ante });
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, conseq, not_conseq }));
                },
                .combine_false_not => |c| {
                    const truth = results.pop().?;
                    var blk = try self.openBlock();
                    const h = try self.hyp(&blk, c.f);
                    try self.finishBlock(c.block, &blk, c.f);
                    try results.append(sa, try self.emit(c.block, c.nf, "contradiction", &.{ blk.label, truth, h }));
                },
            }
        }
        if (failed) return null;
        return results.items[0];
    }
};

/// The Cooper certifier (period-1 witness). Peel the goal's ∀ prefix into `fix` blocks; the
/// body must be `exists y; disj`. Trace the Cooper elimination, reconstruct each boundary
/// witness as a term, and prove the body at the first witness whose opened disjunction has a
/// provable arm (equation/order under the fix vars), lifting through the or-intro path with an
/// `witness`. Wraps in the `fix`/`generalize` shell. Declines on period>1 (induction —
/// not ported) or a nested/multi-var shape.
fn arithCooperCert(prove: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, symbols: Symbols) Error!bool {
    if (symbols.nat == null) return false;
    const peel = try arithPeel(prove, goal_p);
    const bn = prove.pool.get(peel.body);
    if (bn != .quant or bn.quant.q != .exists) return false;

    const traced = presburger.trace(prove.ctx.arena, prove.pool, symbols, &.{}, peel.body) catch return error.OutOfMemory;
    if (traced != .replay) return false;
    const replay = traced.replay;
    if (replay.period != 1) return arithCooperInduction(prove, cert, out, peel, goal_p, proved_prop, symbols);

    // reconstruct candidate boundary witnesses as terms.
    var candidates: std.ArrayList(TermId) = .empty;
    for (replay.disjuncts) |d| {
        const bw = switch (d) {
            .minus_inf => continue,
            .boundary => |x| x,
        };
        if (try arithBuildWitness(prove, replay, replay.boundaries[bw.b_index], bw.j, peel.eigen, symbols)) |wtn| {
            try candidates.append(prove.ctx.arena, wtn);
        }
    }

    // prove `exists y; disj` at the first candidate that closes an arm.
    var body_steps: std.ArrayList(ast.Step) = .empty;
    const ok = try arithEmitExistsWitness(prove, cert, &body_steps, peel.body, candidates.items, &.{}, symbols);
    if (!ok) return false;
    const wrapped = try wrapArithForall(prove, cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(prove.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Cooper layer 3 (period > 1): synthesize an induction on the single fixed variable to
/// certify a period-D `forall x; exists y; body`. Predicate P(k) = body[x:=k]; base P(ZERO)
/// and step `forall k; P(k) -> P(succ(k))` are proved by the witness search (the step unpacks
/// the IH witness and case-splits its disjunction, shifting the witness per residue arm using
/// the arm equation as a rewrite premise), then the `induction` schema is instantiated at P.
/// Declines (returns false) on a multi-fixed-variable goal or a missing symbol/lemma; every
/// emitted step is kernel-checked (an `instantiation induction(…)` step the generated
/// ProveTask re-demands + the kernel re-checks). The instance concludes `forall n; P(n)` =
/// the goal, so no ∀-re-generalization shell is needed.
fn arithCooperInduction(prove: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), peel: ArithPeel, goal_p: TermId, proved_prop: *TermId, symbols: Symbols) Error!bool {
    if (peel.eigen.len != 1) return false; // layer 3 = single induction variable
    const nat = symbols.nat orelse return false;
    const zero = symbols.zero orelse return false;
    const succ = symbols.succ orelse return false;
    // the `induction` schema must be declared in this proof's namespace (a parameterized
    // axiom) for the instantiation step to resolve.
    const induction_id = try common.internStrRt(prove, "induction");
    if (resolveArithSchema(prove, induction_id) == null) return false;

    // P as a body closed over the induction variable: P(t) = open(p_closed, t).
    const x = peel.eigen[0];
    const p_closed = try prove.pool.close(peel.body, x.name);
    const zero_t = try prove.pool.addApp(.app, zero, &.{});

    // --- base case: P(ZERO) --------------------------------------------------------------
    const p_zero = try prove.pool.open(p_closed, zero_t);
    const base_candidates = try arithWitnessCandidates(prove, symbols, null);
    var base_steps: std.ArrayList(ast.Step) = .empty;
    if (!try arithEmitExistsWitness(prove, cert, &base_steps, p_zero, base_candidates, &.{}, symbols)) return false;
    // the base's exists proof ends in a claim step proving `p_zero`; its label is citable.
    const base_cite = try arithLastLabel(prove, base_steps.items);

    // --- step: forall k; P(k) -> P(succ(k)) ----------------------------------------------
    const k: term.Node.Fvar = .{ .name = try prove.freshNamed("k"), .sort = nat };
    const k_id = try prove.pool.add(.{ .fvar = .{ .name = k.name, .sort = nat } });
    const p_k = try prove.pool.open(p_closed, k_id);
    const succ_k = try prove.pool.addApp(.app, succ, &.{k_id});
    const p_succ_k = try prove.pool.open(p_closed, succ_k);
    const step_impl = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = p_k, .rhs = p_succ_k } });

    // the IH existential var y0; the IH body (disjunction) opened at y0.
    const ihn = prove.pool.get(p_k);
    if (ihn != .quant or ihn.quant.q != .exists) return false;
    const y0: term.Node.Fvar = .{ .name = try prove.freshNamed("y"), .sort = ihn.quant.sort };
    const y0_id = try prove.pool.add(.{ .fvar = .{ .name = y0.name, .sort = y0.sort } });
    const ih_body = try prove.pool.open(ihn.quant.body, y0_id);

    // labels for the step's block structure (all `#`-mangled, collision-free).
    const ih_label = try prove.freshNamed("inductive-hypothesis");
    const step_candidates = try arithWitnessCandidates(prove, symbols, y0_id);

    // inside the unpack: restate the IH body (disjunction) by hypothesis, then case-split it,
    // each arm proving P(succ(k)) via the witness search using the arm equation as a premise.
    var unpack_body: std.ArrayList(ast.Step) = .empty;
    const ih_body_label = try prove.freshNamed("ih-disjunct");
    const unpack_block_label = try prove.freshNamed("with-witness");
    try unpack_body.append(prove.ctx.arena, try cert.b.claimStep(ih_body_label, try cert.b.termExpr(ih_body), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, unpack_block_label)));
    if ((try arithEmitInductionCases(prove, cert, &unpack_body, ih_body, ih_body_label, p_succ_k, step_candidates, symbols)) == null) return false;

    // the unpack block: `unpack y from <ih>` — draws the existential witness y0 out of the IH.
    const unpack_step: ast.Step = .{ .label = cert.b.tok(unpack_block_label), .body = .{ .unpack = .{
        .name = cert.b.tok(try common.displayName(prove, y0.name)),
        .sort = cert.b.sortTok(y0.sort),
        .from = cert.b.tok(ih_label),
        .steps = unpack_body.items,
    } } };

    // the assume P(k) block: restate the IH, then unpack + case-split, exporting P(succ(k)).
    var assume_body: std.ArrayList(ast.Step) = .empty;
    const assume_block_label = try prove.freshNamed("given-ih");
    try assume_body.append(prove.ctx.arena, try cert.b.claimStep(ih_label, try cert.b.termExpr(p_k), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, assume_block_label)));
    try assume_body.append(prove.ctx.arena, unpack_step);
    // export P(succ(k)) out of the unpack (unpacked).
    _ = try cert.claim(&assume_body, p_succ_k, "unpacked", &.{}, &.{unpack_block_label});
    const assume_step = try cert.b.assumeStep(assume_block_label, try cert.b.termExpr(p_k), assume_body.items);

    // the fix k block: assume P(k), conclude P(succ(k)), export the implication.
    var fix_body: std.ArrayList(ast.Step) = .empty;
    try fix_body.append(prove.ctx.arena, assume_step);
    _ = try cert.claim(&fix_body, step_impl, "discharge", &.{}, &.{assume_block_label});
    const fixr = try cert.fixStep("cooper-step-fix", k.name, nat, fix_body.items);
    const step_forall = try closeForallVar(prove, step_impl, k.name, nat);

    // assemble `out`: base steps, then the fix block, then the step's generalize, then the
    // induction instantiation. (base + step labels must precede the instantiation cite.)
    try out.appendSlice(prove.ctx.arena, base_steps.items);
    try out.append(prove.ctx.arena, fixr.step);
    const step_cite = try cert.claim(out, step_forall, "generalize", &.{}, &.{fixr.label});

    // --- instantiate the `induction` schema at P -----------------------------------------
    // build the predicate arg `fun x => P(x)` as a lambda AST expr (binder trims to the
    // eigenvar's display name, so the delaborated body's refs bind to it — single eigenvar,
    // no collision). The generated ProveTask re-demands the instance; the kernel re-checks it.
    const lambda_arg = try arithInductionLambda(prove, cert.b, p_closed, x, nat);
    const args = try prove.ctx.arena.alloc(*const ast.Expr, 1);
    args[0] = lambda_arg;
    const inst_label = try prove.freshNamed("cooper-induction");
    const refs = try prove.ctx.arena.alloc(lexer.Token, 2);
    refs[0] = cert.b.tok(base_cite);
    refs[1] = cert.b.tok(step_cite);
    try out.append(prove.ctx.arena, .{ .label = cert.b.tok(inst_label), .body = .{ .claim = .{
        .formula = try cert.b.termExpr(goal_p),
        .kind = .using,
        .rule = cert.b.tok(try common.internStrRt(prove, "instantiation")),
        .schema = try wkCite(prove, "induction", cert.c),
        .args = args,
        .refs = refs,
    } } });
    proved_prop.* = goal_p;
    return true;
}

/// Candidate existential witnesses for the induction base/step: constant towers around ZERO
/// (`succ^0..3(ZERO)`, and over ℤ `prev^1..3(ZERO)`) and, in the step, the shifted IH witness
/// `y0` (`y0`, `succ(y0)`, `succ(succ(y0))`, and over ℤ `prev`-shifts). One of these proves the
/// residue-class arm at succ(k) (the bounded realization of the arbitrary-period shift table).
fn arithWitnessCandidates(prove: *Prove, symbols: Symbols, ih_witness: ?TermId) Error![]const TermId {
    var out: std.ArrayList(TermId) = .empty;
    const zero = symbols.zero orelse return out.items;
    const zero_t = try prove.pool.addApp(.app, zero, &.{});
    for ([_]i128{ 0, 1, 2, 3, -1, -2, -3 }) |off| {
        if (try ac.buildArithTowerSigned(prove, off, zero_t, symbols)) |w| try out.append(prove.ctx.arena, w);
    }
    if (ih_witness) |y0| {
        for ([_]i128{ 0, 1, 2, -1, -2 }) |off| {
            if (try ac.buildArithTowerSigned(prove, off, y0, symbols)) |w| try out.append(prove.ctx.arena, w);
        }
    }
    return out.items;
}

/// Prove `goal` (= P(succ(k))) by an `common_conclusion` over `disj` (the IH witness disjunction at
/// y0). Each arm assumes one disjunct — an equation over k, y0 — restates it by hypothesis,
/// and proves `goal` by the witness search using that equation as a rewrite premise. Returns
/// the concluding `common_conclusion` step's label, or null if any arm fails.
///
/// A right-nested `or` was handled by prove-recursion on the rhs; now an iterative
/// descend-then-unwind over the spine: DESCEND emits each level's left arm and seeds its
/// right-arm body (the next level's target block); UNWIND (innermost→outermost) wraps each
/// right body as its assume block and claims the level's `common_conclusion` — the same emission
/// order the recursion produced. Scratch stacks on the pool's GPA; the right bodies are
/// scratch-heap-allocated so their pointers stay stable across levels.
fn arithEmitInductionCases(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), disj: TermId, disj_label: StrId, goal: TermId, candidates: []const TermId, symbols: Symbols) Error!?StrId {
    const root = prove.pool.get(disj);
    if (root != .bin or root.bin.op != .or_op) return null;

    var scratch: std.heap.ArenaAllocator = .init(prove.pool.gpa);
    defer scratch.deinit();
    const sa = scratch.allocator();

    const Level = struct {
        block: *std.ArrayList(ast.Step), // where this level's assume/common_conclusion steps land
        rhs: TermId,
        disj_label: StrId,
        left_label: StrId,
        right_label: StrId,
        right_body: *std.ArrayList(ast.Step),
    };
    var levels: std.ArrayList(Level) = .empty;

    var cur_disj = disj;
    var cur_label = disj_label;
    var cur_block = block;
    while (true) {
        const node = prove.pool.get(cur_disj); // an `or` (root check above / descend condition below)
        // left arm: assume the lhs disjunct, prove goal at some witness using it as a premise.
        const left_label = try prove.freshNamed("arm-left");
        const left_hyp = try prove.freshNamed("arm-hyp");
        var left_body: std.ArrayList(ast.Step) = .empty;
        try left_body.append(prove.ctx.arena, try cert.b.claimStep(left_hyp, try cert.b.termExpr(node.bin.lhs), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, left_label)));
        const lprem = try prove.ctx.arena.dupe(ArithPremise, &.{.{ .formula = node.bin.lhs, .local = true, .hyp = left_hyp, .head = undefined, .is_axiom = false }});
        if (!try arithEmitExistsWitness(prove, cert, &left_body, goal, candidates, lprem, symbols)) return null;
        try cur_block.append(prove.ctx.arena, try cert.b.assumeStep(left_label, try cert.b.termExpr(node.bin.lhs), left_body.items));

        // right arm: the rhs disjunct (possibly itself an `or`, descended into).
        const right_label = try prove.freshNamed("arm-right");
        const right_hyp = try prove.freshNamed("arm-hyp");
        const right_body = try sa.create(std.ArrayList(ast.Step));
        right_body.* = .empty;
        try right_body.append(prove.ctx.arena, try cert.b.claimStep(right_hyp, try cert.b.termExpr(node.bin.rhs), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, right_label)));
        try levels.append(sa, .{ .block = cur_block, .rhs = node.bin.rhs, .disj_label = cur_label, .left_label = left_label, .right_label = right_label, .right_body = right_body });

        const rn = prove.pool.get(node.bin.rhs);
        if (rn == .bin and rn.bin.op == .or_op) {
            cur_disj = node.bin.rhs;
            cur_label = right_hyp;
            cur_block = right_body;
            continue;
        }
        const rprem = try prove.ctx.arena.dupe(ArithPremise, &.{.{ .formula = node.bin.rhs, .local = true, .hyp = right_hyp, .head = undefined, .is_axiom = false }});
        if (!try arithEmitExistsWitness(prove, cert, right_body, goal, candidates, rprem, symbols)) return null;
        break;
    }

    // unwind: close each level's right assume + common_conclusion, innermost first; the outermost
    // level's common_conclusion label (the last popped) is the result.
    var result: StrId = undefined;
    while (levels.pop()) |lvl| {
        try lvl.block.append(prove.ctx.arena, try cert.b.assumeStep(lvl.right_label, try cert.b.termExpr(lvl.rhs), lvl.right_body.items));
        result = try cert.claim(lvl.block, goal, "common_conclusion", &.{}, &.{ lvl.disj_label, lvl.left_label, lvl.right_label });
    }
    return result;
}

/// Build the induction predicate arg `fun x: Nat => P(x)` as a lambda AST expr. The binder is
/// named by the eigenvar's display name (trimmed of the `#` mangle); the body delaborates
/// `p_closed` opened at the eigenvar, whose free-var refs trim to the same name and so re-bind
/// to the lambda binder (single eigenvar ⇒ no display collision).
fn arithInductionLambda(prove: *Prove, b: *Accelerant.Builder, p_closed: TermId, x: term.Node.Fvar, nat: term.SortId) Error!*const ast.Expr {
    const x_id = try prove.pool.add(.{ .fvar = .{ .name = x.name, .sort = nat } });
    const p_open = try prove.pool.open(p_closed, x_id);
    const body = try b.termExpr(p_open);
    const bname = try common.displayName(prove, x.name);
    const binders = try prove.ctx.arena.alloc(ast.Binder, 1);
    binders[0] = .{ .name = b.tok(bname), .sort = b.sortTok(nat) };
    const e = try prove.ctx.arena.create(ast.Expr);
    e.* = .{ .lambda = .{ .tok = b.tok(InternPool.Index.none), .binders = binders, .body = body } };
    return e;
}

/// Resolve a schema by NAME in this proof's namespace (a `proven` FactKV `.schema` locator),
/// or null. A schema is a fact-with-params, so it lives in the FACT table.
fn resolveArithSchema(prove: *Prove, name: StrId) ?InternPool.Index {
    const state = prove.ctx.facts.lookup(prove.ctx.io, .{ .namespace = prove.ns, .name = name }) orelse return null;
    const ix = switch (state) {
        .proven => |x| x,
        .in_flight => return null,
    };
    return if (prove.ctx.interner.keyOf(ix) == .schema) ix else null;
}

/// Close `body` (mentioning fvar `name`) into `forall name; …`.
fn closeForallVar(prove: *Prove, body: TermId, name: StrId, sort: term.SortId) Error!TermId {
    const closed = try prove.pool.close(body, name);
    return prove.pool.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = name, .body = closed } });
}

/// Prove `exists y; disj` in `block` at one of `candidates`: open the body at the witness,
/// prove a provable arm of the (possibly disjunctive) instance, lift through the or-intro
/// path, and emit `witness`. Returns false if no candidate closes.
fn arithEmitExistsWitness(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), exists_body: TermId, candidates: []const TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const en = prove.pool.get(exists_body);
    if (en != .quant or en.quant.q != .exists) return false;
    for (candidates) |wtn| {
        const instance = try prove.pool.open(en.quant.body, wtn);
        // try each arm of the right/left or-nest.
        var arm_steps: std.ArrayList(ast.Step) = .empty;
        const found = (try arithProveDisjArm(prove, cert, &arm_steps, instance, prems, symbols)) orelse continue;
        try block.appendSlice(prove.ctx.arena, arm_steps.items);
        // lift the arm through the or-intro path (innermost first).
        var arm_label = found.label;
        var arm_formula = found.formula;
        var pi = found.path.len;
        while (pi > 0) {
            pi -= 1;
            const disj = try arithDisjAt(prove, instance, found.path[0..pi]);
            const rule: []const u8 = if (found.path[pi]) "either_right" else "either_left";
            arm_label = try cert.claim(block, disj, rule, &.{}, &.{arm_label});
            arm_formula = disj;
        }
        // witness at the witness.
        const arg1 = try prove.ctx.arena.alloc(*const ast.Expr, 1);
        arg1[0] = try cert.b.termExpr(wtn);
        const label = try prove.freshNamed("arith");
        const refs = try prove.ctx.arena.alloc(lexer.Token, 1);
        refs[0] = cert.b.tok(arm_label);
        try block.append(prove.ctx.arena, try cert.b.claimStep(label, try cert.b.termExpr(exists_body), .by, try prove.internStr("witness"), arg1, refs));
        return true;
    }
    return false;
}

const ArithArm = struct { label: StrId, formula: TermId, path: []const bool };

/// Prove one arm of a right/left `or`-nest `instance` via the equation/order body cert; return
/// the arm's step label + formula + the or-intro path to it, or null if no arm is provable.
fn arithProveDisjArm(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), instance: TermId, prems: []const ArithPremise, symbols: Symbols) Error!?ArithArm {
    var path: std.ArrayList(bool) = .empty;
    var cur = instance;
    while (true) {
        const node = prove.pool.get(cur);
        if (node == .bin and node.bin.op == .or_op) {
            var probe: std.ArrayList(ast.Step) = .empty;
            if (try arithBodyEqCert(prove, cert, &probe, node.bin.lhs, prems, symbols)) {
                try block.appendSlice(prove.ctx.arena, probe.items);
                const label = try arithLastLabel(prove, probe.items);
                try path.append(prove.ctx.arena, false);
                return .{ .label = label, .formula = node.bin.lhs, .path = try prove.ctx.arena.dupe(bool, path.items) };
            }
            try path.append(prove.ctx.arena, true);
            cur = node.bin.rhs;
            continue;
        }
        var probe: std.ArrayList(ast.Step) = .empty;
        if (try arithBodyEqCert(prove, cert, &probe, cur, prems, symbols)) {
            try block.appendSlice(prove.ctx.arena, probe.items);
            const label = try arithLastLabel(prove, probe.items);
            return .{ .label = label, .formula = cur, .path = try prove.ctx.arena.dupe(bool, path.items) };
        }
        return null;
    }
}

/// Descend `instance` (a right/left `or`-nest) along `path` (false=left, true=right).
fn arithDisjAt(prove: *Prove, instance: TermId, path: []const bool) Error!TermId {
    var cur = instance;
    for (path) |go_right| {
        const node = prove.pool.get(cur);
        cur = if (go_right) node.bin.rhs else node.bin.lhs;
    }
    return cur;
}

/// Reconstruct a boundary witness `boundaries[i] + j` (a linear form over the fix vars) as a
/// term: coeff 0 → a constant tower over ZERO; coeff 1 on the single eigenvariable → a tower
/// over it. Higher coeff / 2+ vars → null. Port of the old `buildWitness`.
fn arithBuildWitness(prove: *Prove, replay: presburger.Replay, dump: presburger.LinearDump, j: i128, fix_vars: []const term.Node.Fvar, symbols: Symbols) Error!?TermId {
    var fix_index: ?usize = null;
    for (dump.coeffs, 0..) |co, id| {
        if (co == 0) continue;
        if (co != 1) return null;
        const pos = std.mem.indexOfScalar(u32, replay.free_ids, @intCast(id)) orelse return null;
        if (fix_index != null) return null;
        fix_index = pos;
    }
    // A witness that is exactly a fixed eigenvariable (`y := x` for `exists y; x = y or …`, the
    // left arm reflexive) is fine: the proof pool is locally nameless and hash-consed, so
    // `witness(x)` closes only the existential slot and the instance re-checks as written.
    const offset = dump.konst + j;
    const base = if (fix_index) |pos| blk: {
        if (pos >= fix_vars.len) return null;
        break :blk try prove.pool.add(.{ .fvar = fix_vars[pos] });
    } else blk: {
        const zero = symbols.zero orelse return null;
        break :blk try prove.pool.addApp(.app, zero, &.{});
    };
    return try ac.buildArithTowerSigned(prove, offset, base, symbols);
}

/// Peel `goal`'s ∀ prefix into fresh eigenvariables (outermost first); return the body + the
/// eigenvariables (for the `fix`/`generalize` re-generalization shell). Used by each
/// arithmetic certifier so a `forall …; body` goal skeletonizes to `body` at fixed vars.
const ArithPeel = struct { body: TermId, eigen: []const term.Node.Fvar, opened: []const TermId };

fn arithPeel(prove: *Prove, goal: TermId) Error!ArithPeel {
    var eigen: std.ArrayList(term.Node.Fvar) = .empty;
    var opened: std.ArrayList(TermId) = .empty;
    var body = goal;
    while (true) {
        const node = prove.pool.get(body);
        if (node != .quant or node.quant.q != .forall) break;
        const hint = prove.ctx.interner.stringBytes(node.quant.hint);
        const fv: term.Node.Fvar = .{ .name = try prove.freshNamed(if (hint.len > 0) hint else "q"), .sort = node.quant.sort };
        body = try prove.pool.open(node.quant.body, try prove.pool.add(.{ .fvar = fv }));
        try eigen.append(prove.ctx.arena, fv);
        try opened.append(prove.ctx.arena, body);
    }
    return .{ .body = body, .eigen = eigen.items, .opened = opened.items };
}

/// Wrap `inner` steps (proving `body`) in nested `fix` blocks for `eigen` (outermost first),
/// concluding each level with `generalize`. Returns the wrapped steps + the eigen-closed
/// prop the outermost `generalize` proves (the schema body must use THIS prop, so its
/// binder hints match the fix blocks). (Same shell as `wrapSimplifyForall`.)
const WrappedArith = struct { steps: []const ast.Step, prop: TermId };

fn wrapArithForall(prove: *Prove, cert: *ArithCert, eigen: []const term.Node.Fvar, body: TermId, inner: []const ast.Step) Error!WrappedArith {
    if (eigen.len == 0) return .{ .steps = inner, .prop = body };
    var steps = inner;
    var prop = body;
    var i: usize = eigen.len;
    while (i > 0) {
        i -= 1;
        const fv = eigen[i];
        const fixr = try cert.fixStep("arith-fix", fv.name, fv.sort, steps);
        const closed = try prove.pool.close(prop, fv.name);
        prop = try prove.pool.add(.{ .quant = .{ .q = .forall, .sort = fv.sort, .hint = fv.name, .body = closed } });
        var lvl: std.ArrayList(ast.Step) = .empty;
        try lvl.append(prove.ctx.arena, fixr.step);
        _ = try cert.claim(&lvl, prop, "generalize", &.{}, &.{fixr.label});
        steps = try lvl.toOwnedSlice(prove.ctx.arena);
    }
    return .{ .steps = steps, .prop = prop };
}

/// The EQUATION / ORDER cert. Peels the goal's ∀ prefix, then certifies the body:
///   - an equation `s = t`: canonicalize both sides to a shared normal form (the ring
///     `Polynomial` path when `mul` is present; else an additive AC + inverse-elimination
///     path), emit the `EqCert` join;
///   - an order atom `less_than(s, t)`: find the difference `d` with `add(s, succ(d)) = t`
///     an additive identity, prove that equation, and cite `lessThanIntro` (`add(a,succ(d))=b
///     -> less_than(a,b)`).
/// Wraps the body proof in the `fix`/`generalize` shell. Returns false (declines) on any
/// shape/normal-form mismatch — the caller tries the next certifier.
fn arithEquationCert(prove: *Prove, cert: *ArithCert, out: *std.ArrayList(ast.Step), goal_p: TermId, proved_prop: *TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const peel = try arithPeel(prove, goal_p);
    var body_steps: std.ArrayList(ast.Step) = .empty;
    const ok = try arithBodyEqCert(prove, cert, &body_steps, peel.body, prems, symbols);
    if (!ok) return false;
    const wrapped = try wrapArithForall(prove, cert, peel.eigen, peel.body, body_steps.items);
    try out.appendSlice(prove.ctx.arena, wrapped.steps);
    proved_prop.* = wrapped.prop;
    return true;
}

/// Certify one (∀-free) equation/order body into `block`; returns false if out of scope.
///
/// The EXISTS case is a witness search: `exists y; inner` tries constant witnesses
/// succ^k(ZERO), k=0..33, proving `inner[y:=witness]` by the equation/order cert, then
/// `witness` (the old arithCertCore C2c). Handles e.g. `exists y; add(y,y) =
/// succ(succ(ZERO))` (witness y=1). A NESTED exists recursed; now an explicit backtracking
/// frame stack — one frame per open exists level, `k` its next witness index; a child frame
/// lives for exactly one parent witness attempt (child exhausted → pop → parent advances).
/// On a leaf success the leaf steps + one `witness` per level (innermost→outermost,
/// each citing the previous last label) flatten into `block` — the same step sequence the
/// recursive appendSlice chain produced. Scratch on the pool's GPA.
fn arithBodyEqCert(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), body: TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const node = prove.pool.get(body);
    if (node == .eq) {
        return arithEmitEquation(prove, cert, block, node.eq.lhs, node.eq.rhs, prems, symbols);
    }
    if (node == .pred and ac.symIs(node.pred.sym, symbols.less_than) and node.pred.args.len == 2) {
        return arithEmitOrder(prove, cert, block, body, prems, symbols);
    }
    if (node != .quant or node.quant.q != .exists) return false;

    const zero = symbols.zero orelse return false;
    const zero_t = try prove.pool.addApp(.app, zero, &.{});

    var scratch: std.heap.ArenaAllocator = .init(prove.pool.gpa);
    defer scratch.deinit();
    const sa = scratch.allocator();

    const Frame = struct {
        formula: TermId, // the `exists y; inner` this level proves
        inner: TermId, // its quant body
        k: usize = 0, // next witness index (0..34)
        witness: TermId = undefined, // current attempt's witness (set before descending)
    };
    var stack: std.ArrayList(Frame) = .empty;
    try stack.append(sa, .{ .formula = body, .inner = node.quant.body });

    while (stack.items.len > 0) {
        const f = &stack.items[stack.items.len - 1];
        if (f.k >= 34) {
            // exhausted: this level fails; the parent advances to its next witness.
            _ = stack.pop();
            continue;
        }
        const witness = (try ac.buildArithTowerSigned(prove, @intCast(f.k), zero_t, symbols)) orelse {
            // tower construction failing stops the search at this level (the recursive `break`).
            _ = stack.pop();
            continue;
        };
        f.k += 1;
        f.witness = witness;
        const instance = try prove.pool.open(f.inner, witness);
        const in = prove.pool.get(instance);
        if (in == .quant and in.quant.q == .exists) {
            // nested exists: a child frame for this attempt. (f is invalidated by the append.)
            try stack.append(sa, .{ .formula = instance, .inner = in.quant.body });
            continue;
        }
        // leaf attempt into a fresh probe (discarded on failure, like the recursive version).
        var probe: std.ArrayList(ast.Step) = .empty;
        const ok = if (in == .eq)
            try arithEmitEquation(prove, cert, &probe, in.eq.lhs, in.eq.rhs, prems, symbols)
        else if (in == .pred and ac.symIs(in.pred.sym, symbols.less_than) and in.pred.args.len == 2)
            try arithEmitOrder(prove, cert, &probe, instance, prems, symbols)
        else
            false;
        if (!ok) continue; // next witness at this level
        // SUCCESS: flatten — the leaf steps, then one witness per level innermost first
        // (accumulated in `probe`), the whole sequence + the root's witness into `block`.
        var inst_label = try arithLastLabel(prove, probe.items);
        var i = stack.items.len;
        while (i > 0) {
            i -= 1;
            const fr = stack.items[i];
            const out: *std.ArrayList(ast.Step) = if (i == 0) blk: {
                try block.appendSlice(prove.ctx.arena, probe.items);
                break :blk block;
            } else &probe;
            const arg1 = try prove.ctx.arena.alloc(*const ast.Expr, 1);
            arg1[0] = try cert.b.termExpr(fr.witness);
            const label = try prove.freshNamed("arith");
            const refs = try prove.ctx.arena.alloc(lexer.Token, 1);
            refs[0] = cert.b.tok(inst_label);
            try out.append(prove.ctx.arena, try cert.b.claimStep(label, try cert.b.termExpr(fr.formula), .by, try prove.internStr("witness"), arg1, refs));
            inst_label = label;
        }
        return true;
    }
    return false;
}

/// Emit a proof of the equation `s = t` into `block`; false if it can't join. Dispatches on
/// whether the goal has `mul` (ring `Polynomial` canonicalizer) or is additive-only (AC +
/// inverse elimination), plus a PREMISE-COMBINATION fallback (goal = ±1·premise). The cited
/// premises join as ground rewrite rules where their sides occur literally.
pub fn arithEmitEquation(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    if (prove.pool.alphaEq(s, t)) {
        _ = try cert.claim(block, try prove.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } }), "reflexivity", &.{}, &.{});
        return true;
    }
    const eq_goal = try prove.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });

    // build the ring/additive rule set (well-known lemmas cited by name) + premise rules.
    var rules: std.ArrayList(rewrite.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    const have_mul = symbols.mul != null and (usesSym(prove, symbols.mul.?, s) or usesSym(prove, symbols.mul.?, t));
    const qualifier: StrId = if (cert.c.schema) |sel| sel.name else InternPool.Index.none;
    if (have_mul) {
        // FIRST try the ring `Polynomial` canonicalizer (distribution/fold + AC) — handles
        // symbolic ring identities like `mul(2, n) = add(n, n)`. If the NFs disagree it may
        // still be a GROUND numeric identity (`mul(2, 2) = 4`) the ring form can't evaluate —
        // fall through to the additive path (which carries the mul RECURSION rules).
        if (try polycanon.readPolyOps(prove, eq_goal)) |ops| {
            const pr = try polycanon.polyRules(prove, ops, qualifier, cert.c.rule.start);
            if (try polycanon.polyCanon(prove, pr, s)) |rs| {
                if (try polycanon.polyCanon(prove, pr, t)) |rt| {
                    if (prove.pool.alphaEq(rs.nf, rt.nf)) {
                        var ec: EqCert = .{ .b = cert.b, .pool = prove.pool, .rules = pr.rules, .cites = pr.cites, .fresh_ctx = prove, .freshFn = common.eqCertFresh };
                        _ = try ec.emitJoin(block, s, t, rs, rt);
                        return true;
                    }
                }
            }
        }
    }
    // additive path: elimination + succ/mul RECURSION pre-rules, then AC-sort + inverse-cancel.
    const add_sym = symbols.add orelse return false;
    try pushAdditiveElim(prove, &rules, &cites, symbols, qualifier, cert.c.rule.start);
    // PREMISE ground rules: a cited equation premise `P_l = P_r` joins the normalizer as a
    // ground rewrite `P_l -> P_r`, firing where `P_l` occurs literally (e.g. the Cooper
    // induction-step arm rewrites the fixed var by its case hypothesis `k = add(y0, y0)`). A
    // prove-embedding rule (`P_l` a subterm of `P_r`) would loop — skip it.
    try pushPremiseRules(prove, &rules, &cites, prems);
    const pre_count = rules.items.len;
    const sort: term.SortId = @enumFromInt(@intFromEnum(prove.termSort(s)));
    try ac.pushACTriple(prove, &rules, &cites, add_sym, sort, "addIsAssociative", "addIsCommutative", "addLeftSwap", cert.c.rule.start);
    const assoc_idx = pre_count;
    const comm_idx = pre_count + 1;
    const swap_idx = pre_count + 2;
    const pre_rules = rules.items[0..pre_count];

    const s_pre = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, pre_rules, s, 1000) catch |e| switch (e) {
        error.Limit => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    const t_pre = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, pre_rules, t, 1000) catch |e| switch (e) {
        error.Limit => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    // pre-normalization alone may already agree (pure numerals / leafless towers where the
    // AC sort is a no-op) — join directly, skipping acPlan (which declines on leafless sums).
    if (prove.pool.alphaEq(s_pre.nf, t_pre.nf)) {
        var ec: EqCert = .{ .b = cert.b, .pool = prove.pool, .rules = rules.items, .cites = cites.items, .fresh_ctx = prove, .freshFn = common.eqCertFresh };
        _ = try ec.emitJoin(block, s, t, s_pre, t_pre);
        return true;
    }
    // canonicalize each side to a fixpoint: AC-sort + bubble-cancel inverse pairs + re-normalize,
    // repeating until stable (arithCanon carries `symbols` so its cancelInverses has neg/zero).
    const rs = (try arithCanon(prove, symbols, rules.items, pre_rules, assoc_idx, comm_idx, swap_idx, s_pre)) orelse return false;
    const rt = (try arithCanon(prove, symbols, rules.items, pre_rules, assoc_idx, comm_idx, swap_idx, t_pre)) orelse return false;
    if (prove.pool.alphaEq(rs.nf, rt.nf)) {
        var ec: EqCert = .{ .b = cert.b, .pool = prove.pool, .rules = rules.items, .cites = cites.items, .fresh_ctx = prove, .freshFn = common.eqCertFresh };
        _ = try ec.emitJoin(block, s, t, rs, rt);
        return true;
    }
    // PREMISE COMBINATION: goal = ±1·(an equality premise). Certify via addCancelLeft.
    return arithPremiseCombination(prove, cert, block, s, t, prems, symbols);
}

/// Canonicalize `start` (with its initial pre-normalize `Result`) to a fixpoint by alternating
/// AC-sort (`acPlan`) and pre-rule normalize (elim + adjacent inverse-cancel + ZERO-drop),
/// concatenating every trace. The sort places an inverse pair adjacent so the next normalize's
/// addNegRight/Left cancels it. Returns the final `Result` (NF + full trace), null on decline.
fn arithCanon(prove: *Prove, symbols: Symbols, rules: []const rewrite.Rule, pre_rules: []const rewrite.Rule, assoc_idx: usize, comm_idx: usize, swap_idx: usize, pre: rewrite.Result) Error!?rewrite.Result {
    // the pre-rules float succ/prev to the root (`succ(add(…))`), so both the AC sort and the
    // inverse-cancel work UNDER that tower: acPlan strips it, cancelInverses parses it.
    var nf = pre.nf;
    var trace: std.ArrayList(rewrite.Rewrite) = .empty;
    try trace.appendSlice(prove.ctx.arena, pre.trace);
    var iter: usize = 0;
    while (iter < 6) : (iter += 1) {
        const plan = (try ac.acPlan(prove, symbols, rules, assoc_idx, comm_idx, swap_idx, nf)) orelse return null;
        try trace.appendSlice(prove.ctx.arena, plan.trace);
        // BUBBLE-cancel non-adjacent inverse pairs (`x … neg(x)` separated by other summands):
        // reuse Polynomial's cancelInverses, which moves the pair together before applying
        // addNegRight/Left — sort adjacency alone (the re-normalize below) misses separated pairs.
        const cancelled = (try ac.cancelInverses(prove, symbols, rules, comm_idx, swap_idx, plan.sorted, &trace)) orelse plan.sorted;
        // re-normalize the (bubble-cancelled) sorted form (drop any residual ZERO, fold).
        const renorm = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, pre_rules, cancelled, 1000) catch |e| switch (e) {
            error.Limit => return null,
            error.OutOfMemory => return error.OutOfMemory,
        };
        try trace.appendSlice(prove.ctx.arena, renorm.trace);
        if (prove.pool.alphaEq(renorm.nf, plan.sorted)) {
            // stable: sort + cancel produced no change this round.
            return .{ .nf = renorm.nf, .trace = trace.items };
        }
        nf = renorm.nf;
    }
    return .{ .nf = nf, .trace = trace.items };
}

/// Emit a proof of `less_than(s, t)` via `lessThanIntro`: synthesize the difference witness
/// `d` (from the normalized towers), prove `add(s, succ(d)) = t`, then cite `lessThanIntro`,
/// apply_at at (s, d, t), and modus_ponens the equation. Declines (false) when the towers
/// don't yield a nonneg difference or the equation can't join. (Peano shape; the ℤ nonneg-
/// antecedent variant is not needed by the fixtures.)
fn arithEmitOrder(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), body: TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const succ = symbols.succ orelse return false;
    const add = symbols.add orelse return false;
    const pred = prove.pool.get(body).pred;
    const args = prove.pool.args(pred);
    const s = args[0];
    const t = args[1];

    // find the difference d such that add(s, succ(d)) = t. Try d = ZERO, then peel: since the
    // engine already decided validity, search a small tower / structural difference. Simple
    // structural approach: if t = add(s, succ(x)) syntactically, d = x; else if t = succ^k(s)-
    // shaped, compute via normalized towers. Use the additive normalizer to canonicalize.
    const d = (try arithOrderDiff(prove, s, t, symbols)) orelse
        // no GROUND difference: try an order PREMISE + transitivity (e.g. prove
        // `less_than(a, succ(b))` from the premise `less_than(a, b)` by chaining a ground
        // edge `less_than(b, succ(b))`). Only fires when a premise anchors the difference.
        return arithEmitOrderFromPremise(prove, cert, block, s, t, prems, symbols);
    const succ_d = try prove.pool.addApp(.app, succ, &.{d});
    const eq_lhs = try prove.pool.addApp(.app, add, &.{ s, succ_d });

    // prove add(s, succ(d)) = t via the equation cert.
    if (!try arithEmitEquation(prove, cert, block, eq_lhs, t, &.{}, symbols)) return false;
    const eq_label = try arithLastLabel(prove, block.items);

    // cite lessThanIntro, apply_at at (s, d, t), modus_ponens the equation → less_than(s,t).
    const intro_stmt = (try arithLemmaFormula(prove, "lessThanIntro", symbols)) orelse return false;
    const intro_label = try cert.citeLemma(block, "lessThanIntro", intro_stmt);
    const elim = try cert.elimChain(block, intro_label, intro_stmt, &.{ s, d, t });
    _ = try cert.claim(block, body, "modus_ponens", &.{}, &.{ elim.label, eq_label });
    return true;
}

/// Prove `less_than(s, t)` from an order PREMISE `less_than(s, m)` (matching the goal's lower
/// bound) via `lessThanElim` + `lessThanIntro`: unpack the premise's witness `w` (so
/// `add(s, succ(w)) = m`), then the goal's own difference `d = arithOrderDiff(m, t)` gives
/// `add(m, succ(d)) = t`; substituting `m` yields `add(s, succ(add(succ(w), d))) = t`, i.e. the
/// goal's difference is `add(succ(w), d)`. Emit: the elim instance + mp, an `unpack w` block
/// proving the goal via `lessThanIntro` (the difference equation reduced under the witness
/// equation), and `unpacked` exporting `less_than(s, t)`. Declines when no premise anchors
/// `s`, the goal→premise difference isn't a ground tower, or a lemma is absent.
fn arithEmitOrderFromPremise(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const less_than = symbols.less_than orelse return false;
    const succ = symbols.succ orelse return false;
    const add = symbols.add orelse return false;
    const elim_stmt = (try arithLemmaFormula(prove, "lessThanElim", symbols)) orelse return false;
    const intro_stmt = (try arithLemmaFormula(prove, "lessThanIntro", symbols)) orelse return false;
    for (prems) |p| {
        const pn = prove.pool.get(p.formula);
        if (pn != .pred or !ac.symIs(pn.pred.sym, less_than) or pn.pred.args.len != 2) continue;
        const pargs = prove.pool.args(pn.pred);
        const pl = pargs[0];
        const pr = pargs[1]; // premise: less_than(pl, pr)
        if (!prove.pool.alphaEq(pl, s)) continue; // need the premise's lower bound = goal's

        // the goal's difference over the premise's upper bound `pr`: add(pr, succ(dg)) = t.
        const dg = (try arithOrderDiff(prove, pr, t, symbols)) orelse continue;

        // cite the premise, instantiate lessThanElim at (pl, pr), MP → exists w; add(pl,succ(w))=pr.
        const prem_label = if (p.local) p.hyp else try cert.citeGlobalPremise(block, p);
        const elim_label = try cert.citeLemma(block, "lessThanElim", elim_stmt);
        const elim = try cert.elimChain(block, elim_label, elim_stmt, &.{ pl, pr });
        const exists_f = prove.pool.get(elim.formula).bin.rhs; // exists w; add(pl, succ(w)) = pr
        const exists_label = try cert.claim(block, exists_f, "modus_ponens", &.{}, &.{ elim.label, prem_label });

        // unpack the witness w; inside prove less_than(s, t) via lessThanIntro at difference
        // `add(succ(w), dg)` (add(s, succ(add(succ(w), dg))) = t reduces under add(s,succ(w))=pr).
        const en = prove.pool.get(exists_f);
        const w: term.Node.Fvar = .{ .name = try prove.freshNamed("w"), .sort = en.quant.sort };
        const w_id = try prove.pool.add(.{ .fvar = .{ .name = w.name, .sort = w.sort } });
        const wit_eq = try prove.pool.open(en.quant.body, w_id); // add(pl, succ(w)) = pr
        const unpack_block = try prove.freshNamed("order-witness");
        const wit_hyp = try prove.freshNamed("witness-eq");
        var ub: std.ArrayList(ast.Step) = .empty;
        try ub.append(prove.ctx.arena, try cert.b.claimStep(wit_hyp, try cert.b.termExpr(wit_eq), .by, try prove.internStr("hypothesis"), &.{}, try common.oneRef(prove, cert.b, unpack_block)));
        // FLIP the witness eq to `pr = add(s, succ(w))` (symmetry): the additive normalizer lifts
        // `add(s, succ(w))` to a `succ`-tower, so a forward rule `add(s,succ(w)) -> pr` would never
        // fire; the reverse rule `pr -> add(s, succ(w))` rewrites the opaque `pr` into the tower.
        const wn = prove.pool.get(wit_eq).eq;
        const flipped = try prove.pool.add(.{ .eq = .{ .lhs = wn.rhs, .rhs = wn.lhs } });
        const flip_hyp = try cert.claim(&ub, flipped, "symmetry", &.{}, &.{wit_hyp});
        // difference d = add(succ(w), dg); prove add(s, succ(d)) = t using the flipped witness eq.
        const d = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, succ, &.{w_id}), dg });
        const goal = try prove.pool.addApp(.pred, less_than, &.{ s, t });
        const succ_d = try prove.pool.addApp(.app, succ, &.{d});
        const eq_lhs = try prove.pool.addApp(.app, add, &.{ s, succ_d });
        const wit_prem = try prove.ctx.arena.dupe(ArithPremise, &.{.{ .formula = flipped, .local = true, .hyp = flip_hyp, .head = undefined, .is_axiom = false }});
        if (!try arithEmitEquation(prove, cert, &ub, eq_lhs, t, wit_prem, symbols)) continue;
        const eq_label = try arithLastLabel(prove, ub.items);
        const intro_label = try cert.citeLemma(&ub, "lessThanIntro", intro_stmt);
        const intro_elim = try cert.elimChain(&ub, intro_label, intro_stmt, &.{ s, d, t });
        _ = try cert.claim(&ub, goal, "modus_ponens", &.{}, &.{ intro_elim.label, eq_label });

        const unpack_step: ast.Step = .{ .label = cert.b.tok(unpack_block), .body = .{ .unpack = .{
            .name = cert.b.tok(try common.displayName(prove, w.name)),
            .sort = cert.b.sortTok(w.sort),
            .from = cert.b.tok(exists_label),
            .steps = ub.items,
        } } };
        try block.append(prove.ctx.arena, unpack_step);
        _ = try cert.claim(block, goal, "unpacked", &.{}, &.{unpack_block});
        return true;
    }
    return false;
}

/// Synthesize the difference `d` with `add(s, succ(d)) = t` for a valid `less_than(s, t)`.
/// Uses the additive-tower parse: t-tower minus s-tower (leaves + offset), minus one for the
/// `succ`. Returns null if the difference isn't a nonneg tower over the shared leaves.
fn arithOrderDiff(prove: *Prove, s: TermId, t: TermId, symbols: Symbols) Error!?TermId {
    // canonicalize both sides additively (fold sub/neg, sort) so the tower parse is clean.
    var rules: std.ArrayList(rewrite.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    try pushAdditiveElim(prove, &rules, &cites, symbols, .none, 0);
    const rs = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules.items, s, 1000) catch return null;
    const rt = rewrite.normalize(prove.ctx.arena, prove.pool, prove.ctx.interner, rules.items, t, 1000) catch return null;
    const tower_s = (try parseArithTower(prove, rs.nf, symbols)) orelse return null;
    const tower_t = (try parseArithTower(prove, rt.nf, symbols)) orelse return null;
    if (tower_t.offset < tower_s.offset + 1) return null;
    // multiset difference t - s
    var remaining: std.ArrayList(TermId) = .empty;
    try remaining.appendSlice(prove.ctx.arena, tower_t.leaves);
    for (tower_s.leaves) |sl| {
        const found = for (remaining.items, 0..) |rl, i| {
            if (prove.pool.termOrder(rl, sl) == .eq) break i;
        } else return null;
        _ = remaining.swapRemove(found);
    }
    const comb = (try buildArithComb(prove, remaining.items, symbols)) orelse return null;
    return try ac.buildArithTowerSigned(prove, tower_t.offset - tower_s.offset - 1, comb, symbols);
}

const ArithTower = struct { offset: i128, leaves: []const TermId };

/// Parse `succ^j(prev^k(right-nested add of leaves))`, folding numeral summands into a signed
/// offset. Anything else → null (out of the additive fragment). Port of the old `parseTower`.
fn parseArithTower(prove: *Prove, t: TermId, symbols: Symbols) Error!?ArithTower {
    var offset: i128 = 0;
    var cur = t;
    while (true) {
        const node = prove.pool.get(cur);
        if (node == .app and ac.symIs(node.app.sym, symbols.succ) and node.app.args.len == 1) {
            offset += 1;
            cur = prove.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and ac.symIs(node.app.sym, symbols.prev) and node.app.args.len == 1) {
            offset -= 1;
            cur = prove.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    var leaves: std.ArrayList(TermId) = .empty;
    while (true) {
        if (arithNumeral(prove, cur, symbols)) |v| {
            offset += v;
            break;
        }
        if (isArithLeaf(prove, cur, symbols)) {
            try leaves.append(prove.ctx.arena, cur);
            break;
        }
        const node = prove.pool.get(cur);
        if (node != .app) return null;
        if (ac.symIs(node.app.sym, symbols.add) and node.app.args.len == 2) {
            const a = try prove.ctx.arena.dupe(TermId, prove.pool.args(node.app));
            if (arithNumeral(prove, a[0], symbols)) |v| {
                offset += v;
                cur = a[1];
                continue;
            }
            if (!isArithLeaf(prove, a[0], symbols)) return null;
            try leaves.append(prove.ctx.arena, a[0]);
            cur = a[1];
            continue;
        }
        return null;
    }
    return .{ .offset = offset, .leaves = leaves.items };
}

/// Signed numeral value of `t` (`succ^n(ZERO)`→+n, `prev^n(ZERO)`→−n, `neg` flips), else null.
fn arithNumeral(prove: *Prove, t: TermId, symbols: Symbols) ?i128 {
    var cur = t;
    var sign: i128 = 1;
    while (true) {
        const node = prove.pool.get(cur);
        if (node == .app and ac.symIs(node.app.sym, symbols.neg) and node.app.args.len == 1) {
            sign = -sign;
            cur = prove.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    var mag: i128 = 0;
    while (true) {
        const node = prove.pool.get(cur);
        if (node == .app and ac.symIs(node.app.sym, symbols.succ) and node.app.args.len == 1) {
            mag += 1;
            cur = prove.pool.args(node.app)[0];
            continue;
        }
        if (node == .app and ac.symIs(node.app.sym, symbols.prev) and node.app.args.len == 1) {
            mag -= 1;
            cur = prove.pool.args(node.app)[0];
            continue;
        }
        break;
    }
    const node = prove.pool.get(cur);
    if (node == .app and ac.symIs(node.app.sym, symbols.zero) and node.app.args.len == 0) return sign * mag;
    return null;
}

/// A tower leaf: an fvar, an opaque atom, or `neg` of a leaf (so inverse pairs can cancel).
fn isArithLeaf(prove: *Prove, t0: TermId, symbols: Symbols) bool {
    // linear neg-peel recursion → loop.
    var t = t0;
    const node = while (true) {
        const n = prove.pool.get(t);
        if (n == .app and ac.symIs(n.app.sym, symbols.neg) and n.app.args.len == 1) {
            t = prove.pool.args(n.app)[0];
            continue;
        }
        break n;
    };
    if (node == .fvar) return true;
    if (node != .app) return false;
    const sym = node.app.sym;
    return !(ac.symIs(sym, symbols.add) or ac.symIs(sym, symbols.succ) or
        ac.symIs(sym, symbols.prev) or ac.symIs(sym, symbols.neg) or
        ac.symIs(sym, symbols.sub) or ac.symIs(sym, symbols.zero) or ac.symIs(sym, symbols.one));
}

/// Right-nested `add`-comb of `leaves` (ZERO for empty).
fn buildArithComb(prove: *Prove, leaves: []const TermId, symbols: Symbols) Error!?TermId {
    if (leaves.len == 0) {
        const zero = symbols.zero orelse return null;
        return try prove.pool.addApp(.app, zero, &.{});
    }
    var cur = leaves[leaves.len - 1];
    var i = leaves.len - 1;
    while (i > 0) {
        i -= 1;
        const add = symbols.add orelse return null;
        cur = try prove.pool.addApp(.app, add, &.{ leaves[i], cur });
    }
    return cur;
}

/// Append the well-known ℤ elimination rules (sub/neg/prev folding toward an add-of-atoms
/// form) as hardcoded shapes cited by name, gated on the theory providing each symbol. These
/// let an additive goal over sub/neg normalize before the AC sort (e.g. `add(a, sub(b,a))`).
pub fn pushAdditiveElim(prove: *Prove, rules: *std.ArrayList(rewrite.Rule), cites: *std.ArrayList(EqCert.RuleCite), symbols: Symbols, qualifier: StrId, loc: u32) Error!void {
    const add = symbols.add orelse return;
    const sort: term.SortId = @enumFromInt(@intFromEnum(prove.ctx.interner.symResult(@enumFromInt(@intFromEnum(add)))));
    // succ FLOAT: addSuccLeft add(succ(a),b)=succ(add(a,b)); addSuccRight add(a,succ(b))=
    // succ(add(a,b)) — lift succ to the tower prefix so the tower parse is clean.
    if (symbols.succ) |succ| {
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, succ, &.{a.t}), bb.t });
            const rhs = try prove.pool.addApp(.app, succ, &.{try prove.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addSuccLeft", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, add, &.{ a.t, try prove.pool.addApp(.app, succ, &.{bb.t}) });
            const rhs = try prove.pool.addApp(.app, succ, &.{try prove.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addSuccRight", qualifier, loc);
        }
    }
    // ZERO drop: addZeroLeft add(ZERO,b)=b; addZeroRight add(n,ZERO)=n.
    if (symbols.zero) |zero| {
        const z = try prove.pool.addApp(.app, zero, &.{});
        {
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, add, &.{ z, bb.t });
            try pushQualified(prove, rules, cites, &.{.{ .fvar = bb.name, .sort = sort }}, lhs, bb.t, "addZeroLeft", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, add, &.{ a.t, z });
            try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "addZeroRight", qualifier, loc);
        }
        // ONE unfold: oneIsSuccZero ONE = succ(ZERO) — dissolve a bare `ONE` constant into the
        // succ-tower so numeral goals (`add(ONE, ONE) = succ(succ(ZERO))`) reduce to a common
        // form. Nullary rule; gated on the theory declaring `oneIsSuccZero` (+ ONE/succ present).
        if (symbols.one) |one| if (symbols.succ) |succ| {
            const one_t = try prove.pool.addApp(.app, one, &.{});
            const succ_z = try prove.pool.addApp(.app, succ, &.{z});
            try pushQualified(prove, rules, cites, &.{}, one_t, succ_z, "oneIsSuccZero", qualifier, loc);
        };
    }
    // mul RECURSION (ground numeric evaluation): mulZeroLeft mul(ZERO,b)=ZERO; mulSuccLeft
    // mul(succ(a),b)=add(mul(a,b),b) — expands `mul(n, x)` to a sum for numeral n.
    if (symbols.mul) |mul| if (symbols.zero) |zero| if (symbols.succ) |succ| {
        const z = try prove.pool.addApp(.app, zero, &.{});
        {
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, mul, &.{ z, bb.t });
            try pushQualified(prove, rules, cites, &.{.{ .fvar = bb.name, .sort = sort }}, lhs, z, "mulZeroLeft", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, mul, &.{ try prove.pool.addApp(.app, succ, &.{a.t}), bb.t });
            const rhs = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, mul, &.{ a.t, bb.t }), bb.t });
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "mulSuccLeft", qualifier, loc);
        }
        // mulZeroRight mul(n,ZERO)=ZERO; mulSuccRight mul(a,succ(b))=add(mul(a,b),a) — the right
        // mirrors, so a numeral on EITHER factor expands.
        {
            const a = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, mul, &.{ a.t, z });
            try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, z, "mulZeroRight", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, mul, &.{ a.t, try prove.pool.addApp(.app, succ, &.{bb.t}) });
            const rhs = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, mul, &.{ a.t, bb.t }), a.t });
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "mulSuccRight", qualifier, loc);
        }
    };
    // definitionOfSubtraction: sub(a,b) = add(a, neg(b))
    if (symbols.sub != null and symbols.neg != null) {
        const a = try ac.freshACFvar(prove, sort);
        const bb = try ac.freshACFvar(prove, sort);
        const lhs = try prove.pool.addApp(.app, symbols.sub.?, &.{ a.t, bb.t });
        const rhs = try prove.pool.addApp(.app, add, &.{ a.t, try prove.pool.addApp(.app, symbols.neg.?, &.{bb.t}) });
        try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "definitionOfSubtraction", qualifier, loc);
    }
    if (symbols.neg) |neg| {
        // negAdd: neg(add(a,b)) = add(neg(a), neg(b))
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, neg, &.{try prove.pool.addApp(.app, add, &.{ a.t, bb.t })});
            const rhs = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, neg, &.{a.t}), try prove.pool.addApp(.app, neg, &.{bb.t}) });
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "negAdd", qualifier, loc);
        }
        // negNeg: neg(neg(a)) = a
        {
            const a = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, neg, &.{try prove.pool.addApp(.app, neg, &.{a.t})});
            try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "negNeg", qualifier, loc);
        }
        // addNegRight: add(a, neg(a)) = ZERO; addNegLeft: add(neg(a), a) = ZERO — cancel an
        // inverse pair the AC sort brings adjacent (the addZero rules then drop the ZERO).
        if (symbols.zero) |zero| {
            const z = try prove.pool.addApp(.app, zero, &.{});
            {
                const a = try ac.freshACFvar(prove, sort);
                const lhs = try prove.pool.addApp(.app, add, &.{ a.t, try prove.pool.addApp(.app, neg, &.{a.t}) });
                try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, z, "addNegRight", qualifier, loc);
            }
            {
                const a = try ac.freshACFvar(prove, sort);
                const lhs = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, neg, &.{a.t}), a.t });
                try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, z, "addNegLeft", qualifier, loc);
            }
            // negZero: neg(ZERO) = ZERO (nullary).
            {
                const lhs = try prove.pool.addApp(.app, neg, &.{z});
                try pushQualified(prove, rules, cites, &.{}, lhs, z, "negZero", qualifier, loc);
            }
        }
        // negSucc: neg(succ(a)) = prev(neg(a)); negPrev: neg(prev(a)) = succ(neg(a)) — push neg
        // through succ/prev toward the leaves so a `neg`-of-numeral becomes a prev/succ tower.
        if (symbols.succ) |succ| if (symbols.prev) |prev| {
            {
                const a = try ac.freshACFvar(prove, sort);
                const lhs = try prove.pool.addApp(.app, neg, &.{try prove.pool.addApp(.app, succ, &.{a.t})});
                const rhs = try prove.pool.addApp(.app, prev, &.{try prove.pool.addApp(.app, neg, &.{a.t})});
                try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, rhs, "negSucc", qualifier, loc);
            }
            {
                const a = try ac.freshACFvar(prove, sort);
                const lhs = try prove.pool.addApp(.app, neg, &.{try prove.pool.addApp(.app, prev, &.{a.t})});
                const rhs = try prove.pool.addApp(.app, succ, &.{try prove.pool.addApp(.app, neg, &.{a.t})});
                try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, rhs, "negPrev", qualifier, loc);
            }
        };
    }
    // succ/prev collapse + prev FLOAT (ℤ): prevSucc prev(succ(a))=a; succPrev succ(prev(a))=a;
    // addPrevLeft add(prev(a),b)=prev(add(a,b)); addPrevRight add(a,prev(b))=prev(add(a,b)) —
    // lift prev to the tower prefix (mirror of the succ float) so the tower parse is clean.
    if (symbols.prev) |prev| if (symbols.succ) |succ| {
        {
            const a = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, prev, &.{try prove.pool.addApp(.app, succ, &.{a.t})});
            try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "prevSucc", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, succ, &.{try prove.pool.addApp(.app, prev, &.{a.t})});
            try pushQualified(prove, rules, cites, &.{.{ .fvar = a.name, .sort = sort }}, lhs, a.t, "succPrev", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, add, &.{ try prove.pool.addApp(.app, prev, &.{a.t}), bb.t });
            const rhs = try prove.pool.addApp(.app, prev, &.{try prove.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addPrevLeft", qualifier, loc);
        }
        {
            const a = try ac.freshACFvar(prove, sort);
            const bb = try ac.freshACFvar(prove, sort);
            const lhs = try prove.pool.addApp(.app, add, &.{ a.t, try prove.pool.addApp(.app, prev, &.{bb.t}) });
            const rhs = try prove.pool.addApp(.app, prev, &.{try prove.pool.addApp(.app, add, &.{ a.t, bb.t })});
            try pushQualified(prove, rules, cites, &.{ .{ .fvar = a.name, .sort = sort }, .{ .fvar = bb.name, .sort = sort } }, lhs, rhs, "addPrevRight", qualifier, loc);
        }
    };
}

/// `pushHardcoded` but with the theory-selector `qualifier` stamped onto the cite (so
/// `arithmetic(theory)` resolves the lemma in the theory's namespace).
fn pushQualified(prove: *Prove, rules: *std.ArrayList(rewrite.Rule), cites: *std.ArrayList(EqCert.RuleCite), binders_in: []const rewrite.Binder, lhs: TermId, rhs: TermId, name_text: []const u8, qualifier: StrId, loc: u32) Error!void {
    // Skip a rule whose lemma this file does NOT declare (unqualified only): pushing it would
    // let `normalize` cite an absent lemma, failing the generated proof. A qualified cite
    // (theory selector) targets another namespace we can't check here, so it's kept.
    const name = prove.ctx.interner.internString(name_text) catch return error.OutOfMemory;
    if (qualifier == InternPool.Index.none) {
        const fid = prove.ctx.fileOf(prove.file).?;
        if (prove.ctx.declOf(fid, name) == null) return;
    }
    // dupe onto the arena — callers pass inline `&.{…}` literals (stack temporaries).
    const binders = try prove.ctx.arena.dupe(rewrite.Binder, binders_in);
    var formula = try prove.pool.add(.{ .eq = .{ .lhs = lhs, .rhs = rhs } });
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        const closed = try prove.pool.close(formula, binders[i].fvar);
        formula = try prove.pool.add(.{ .quant = .{ .q = .forall, .sort = binders[i].sort, .hint = binders[i].fvar, .body = closed } });
    }
    try rules.append(prove.ctx.arena, .{ .binders = binders, .lhs = lhs, .rhs = rhs, .formula = formula });
    try cites.append(prove.ctx.arena, .{ .global = .{ .head = .{ .tag = .identifier, .start = loc, .end = loc, .name = name, .qualifier = qualifier }, .is_axiom = false } });
}

/// Push each equation premise `P_l = P_r` as a ground rewrite rule (`P_l -> P_r`) with its
/// citation (LOCAL restated-hypothesis label / GLOBAL fact cite). A prove-embedding rule
/// (`P_l` a subterm of `P_r`) is skipped — it would loop the normalizer.
fn pushPremiseRules(prove: *Prove, rules: *std.ArrayList(rewrite.Rule), cites: *std.ArrayList(EqCert.RuleCite), prems: []const ArithPremise) Error!void {
    for (prems) |p| {
        const pn = prove.pool.get(p.formula);
        if (pn != .eq) continue;
        if (containsSubterm(prove, pn.eq.rhs, pn.eq.lhs)) continue;
        try rules.append(prove.ctx.arena, .{ .binders = &.{}, .lhs = pn.eq.lhs, .rhs = pn.eq.rhs, .formula = p.formula });
        try cites.append(prove.ctx.arena, if (p.local)
            .{ .local = .{ .hyp = p.hyp } }
        else
            .{ .global = .{ .head = p.head, .is_axiom = p.is_axiom } });
    }
}

/// Does `hay` contain `needle` (alpha-equal) as a subterm?
fn containsSubterm(prove: *Prove, hay: TermId, needle: TermId) bool {
    var fb = std.heap.stackFallback(term.Pool.inline_stack * @sizeOf(TermId), prove.ctx.gpa);
    const a = fb.get();
    var stack: std.ArrayList(TermId) = .empty;
    defer stack.deinit(a);
    stack.append(a, hay) catch return true; // OOM conservative
    while (stack.pop()) |cur| {
        if (prove.pool.alphaEq(cur, needle)) return true;
        prove.pool.pushChildren(&stack, a, prove.pool.get(cur)) catch return true;
    }
    return false;
}

/// Certify `s = t` as a linear combination of an equality PREMISE `P_l = P_r`: it holds iff
/// `add(P_l, s) = add(P_r, t)` is a pure additive identity. Emit that identity, rewrite the
/// premise (P_l→P_r), then cancel with addCancelLeft. Every step kernel-checked. Only fires
/// for a LOCAL/GLOBAL premise cited at this scope.
fn arithPremiseCombination(prove: *Prove, cert: *ArithCert, block: *std.ArrayList(ast.Step), s: TermId, t: TermId, prems: []const ArithPremise, symbols: Symbols) Error!bool {
    const add = symbols.add orelse return false;
    for (prems) |p| {
        const pn = prove.pool.get(p.formula);
        if (pn != .eq) continue;
        const pl = pn.eq.lhs;
        const pr = pn.eq.rhs;
        const comb_lhs = try prove.pool.addApp(.app, add, &.{ pl, s });
        const comb_rhs = try prove.pool.addApp(.app, add, &.{ pr, t });
        // certify the combined identity as an additive identity (no premise rules).
        var probe_steps: std.ArrayList(ast.Step) = .empty;
        var probe_cert: ArithCert = .{ .p = prove, .b = cert.b, .c = cert.c };
        if (!try arithEmitEquation(prove, &probe_cert, &probe_steps, comb_lhs, comb_rhs, &.{}, symbols)) continue;

        // PLAN OK — emit for real. combined identity add(P_l,s) = add(P_r,t).
        var join_steps: std.ArrayList(ast.Step) = .empty;
        _ = try arithEmitEquation(prove, cert, &join_steps, comb_lhs, comb_rhs, &.{}, symbols);
        try block.appendSlice(prove.ctx.arena, join_steps.items);
        const comb_label = try arithLastLabel(prove, join_steps.items);

        // the premise, cited at this scope (LOCAL restated hyp / GLOBAL cite).
        const prem_label = if (p.local) p.hyp else try cert.citeGlobalPremise(block, p);
        // rewrite P_l→P_r in the combined identity's LHS: add(P_r, s) = add(P_r, t).
        const rewritten = try prove.pool.add(.{ .eq = .{ .lhs = try prove.pool.addApp(.app, add, &.{ pr, s }), .rhs = comb_rhs } });
        const rewritten_label = try cert.claim(block, rewritten, "rewrite", &.{}, &.{ prem_label, comb_label });
        // addCancelLeft(P_r, s, t): add(P_r,s)=add(P_r,t) -> s=t. cite + elim + mp.
        const cancel_stmt = (try arithLemmaFormula(prove, "addCancelLeft", symbols)) orelse return false;
        const cancel_label = try cert.citeLemma(block, "addCancelLeft", cancel_stmt);
        const elim = try cert.elimChain(block, cancel_label, cancel_stmt, &.{ pr, s, t });
        const goal_eq = try prove.pool.add(.{ .eq = .{ .lhs = s, .rhs = t } });
        _ = try cert.claim(block, goal_eq, "modus_ponens", &.{}, &.{ elim.label, rewritten_label });
        return true;
    }
    return false;
}

/// The last step's label in an emitted slice (its concluding equation).
fn arithLastLabel(prove: *Prove, steps: []const ast.Step) Error!StrId {
    _ = prove;
    return Prove.tokName(steps[steps.len - 1].label);
}

/// Build a well-known lemma's exact `forall …` statement from the arithmetic `symbols`. The
/// cert cites the lemma by name and states THIS formula on the cite step (the kernel re-checks
/// it against the resolved fact, and apply_at opens it at the arguments). The shapes match
/// the std peano/integer statements: a mis-shape simply fails the generated ProveTask's
/// kernel check. `null` when a needed symbol is absent.
fn arithLemmaFormula(prove: *Prove, name: []const u8, symbols: Symbols) Error!?TermId {
    const sort = symbols.nat orelse return null;
    const mkfv = struct {
        fn f(p: *Prove, s: term.SortId, hint: []const u8) Error!ArithVar {
            const nm = try p.freshNamed(hint);
            return .{ .name = nm, .t = try p.pool.add(.{ .fvar = .{ .name = nm, .sort = s } }) };
        }
    }.f;
    if (std.mem.eql(u8, name, "addCancelLeft")) {
        // forall c, a, b; add(c, a) = add(c, b) -> a = b
        const add = symbols.add orelse return null;
        const cc = try mkfv(prove, sort, "c");
        const a = try mkfv(prove, sort, "a");
        const bb = try mkfv(prove, sort, "b");
        const lhs = try prove.pool.add(.{ .eq = .{ .lhs = try prove.pool.addApp(.app, add, &.{ cc.t, a.t }), .rhs = try prove.pool.addApp(.app, add, &.{ cc.t, bb.t }) } });
        const rhs = try prove.pool.add(.{ .eq = .{ .lhs = a.t, .rhs = bb.t } });
        const body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = lhs, .rhs = rhs } });
        return try closeForallChain(prove, body, &.{ cc, a, bb }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanIntro")) {
        // forall a, d, b; add(a, succ(d)) = b -> less_than(a, b)
        const add = symbols.add orelse return null;
        const less_than = symbols.less_than orelse return null;
        const succ = symbols.succ orelse return null;
        const a = try mkfv(prove, sort, "a");
        const d = try mkfv(prove, sort, "d");
        const bb = try mkfv(prove, sort, "b");
        const eq = try prove.pool.add(.{ .eq = .{ .lhs = try prove.pool.addApp(.app, add, &.{ a.t, try prove.pool.addApp(.app, succ, &.{d.t}) }), .rhs = bb.t } });
        const lt = try prove.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = eq, .rhs = lt } });
        return try closeForallChain(prove, body, &.{ a, d, bb }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanElim")) {
        // forall a, b; less_than(a, b) -> exists d; add(a, succ(d)) = b
        const add = symbols.add orelse return null;
        const less_than = symbols.less_than orelse return null;
        const succ = symbols.succ orelse return null;
        const a = try mkfv(prove, sort, "a");
        const bb = try mkfv(prove, sort, "b");
        const d = try mkfv(prove, sort, "d");
        const lt = try prove.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const eq = try prove.pool.add(.{ .eq = .{ .lhs = try prove.pool.addApp(.app, add, &.{ a.t, try prove.pool.addApp(.app, succ, &.{d.t}) }), .rhs = bb.t } });
        const closed_d = try prove.pool.close(eq, d.name);
        const exists_d = try prove.pool.add(.{ .quant = .{ .q = .exists, .sort = sort, .hint = d.name, .body = closed_d } });
        const body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = lt, .rhs = exists_d } });
        return try closeForallChain(prove, body, &.{ a, bb }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanTransitive")) {
        // forall a, b, c; less_than(a, b) -> less_than(b, c) -> less_than(a, c)
        const less_than = symbols.less_than orelse return null;
        const a = try mkfv(prove, sort, "a");
        const bb = try mkfv(prove, sort, "b");
        const cc = try mkfv(prove, sort, "c");
        const ab = try prove.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const bc = try prove.pool.addApp(.pred, less_than, &.{ bb.t, cc.t });
        const a_lt_c = try prove.pool.addApp(.pred, less_than, &.{ a.t, cc.t });
        const body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = ab, .rhs = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = bc, .rhs = a_lt_c } }) } });
        return try closeForallChain(prove, body, &.{ a, bb, cc }, sort);
    }
    if (std.mem.eql(u8, name, "lessThanIrreflexive")) {
        // forall n; not less_than(n, n)
        const less_than = symbols.less_than orelse return null;
        const n = try mkfv(prove, sort, "n");
        const nn = try prove.pool.addApp(.pred, less_than, &.{ n.t, n.t });
        const body = try prove.pool.add(.{ .not = nn });
        return try closeForallChain(prove, body, &.{n}, sort);
    }
    if (std.mem.eql(u8, name, "additionPreservesOrder")) {
        // forall a, b, c; less_than(a, b) -> less_than(add(c, a), add(c, b))
        const add = symbols.add orelse return null;
        const less_than = symbols.less_than orelse return null;
        const a = try mkfv(prove, sort, "a");
        const bb = try mkfv(prove, sort, "b");
        const cc = try mkfv(prove, sort, "c");
        const ab = try prove.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const ca = try prove.pool.addApp(.app, add, &.{ cc.t, a.t });
        const cb = try prove.pool.addApp(.app, add, &.{ cc.t, bb.t });
        const lifted = try prove.pool.addApp(.pred, less_than, &.{ ca, cb });
        const body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = ab, .rhs = lifted } });
        return try closeForallChain(prove, body, &.{ a, bb, cc }, sort);
    }
    if (std.mem.eql(u8, name, "multiplicationPreservesOrder")) {
        // forall a, b, c; less_than(a, b) -> less_than(mul(succ(c), a), mul(succ(c), b))
        const less_than = symbols.less_than orelse return null;
        const succ = symbols.succ orelse return null;
        const mul = symbols.mul orelse return null;
        const a = try mkfv(prove, sort, "a");
        const bb = try mkfv(prove, sort, "b");
        const cc = try mkfv(prove, sort, "c");
        const ab = try prove.pool.addApp(.pred, less_than, &.{ a.t, bb.t });
        const succ_c = try prove.pool.addApp(.app, succ, &.{cc.t});
        const ma = try prove.pool.addApp(.app, mul, &.{ succ_c, a.t });
        const mb = try prove.pool.addApp(.app, mul, &.{ succ_c, bb.t });
        const lifted = try prove.pool.addApp(.pred, less_than, &.{ ma, mb });
        const body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = ab, .rhs = lifted } });
        return try closeForallChain(prove, body, &.{ a, bb, cc }, sort);
    }
    if (std.mem.eql(u8, name, "addIsCommutative")) {
        // forall a, b; add(a, b) = add(b, a)
        const add = symbols.add orelse return null;
        const a = try mkfv(prove, sort, "a");
        const bb = try mkfv(prove, sort, "b");
        const ab = try prove.pool.addApp(.app, add, &.{ a.t, bb.t });
        const ba = try prove.pool.addApp(.app, add, &.{ bb.t, a.t });
        const body = try prove.pool.add(.{ .eq = .{ .lhs = ab, .rhs = ba } });
        return try closeForallChain(prove, body, &.{ a, bb }, sort);
    }
    return null;
}

/// A fresh var pair: its interned name + its fvar term (for lemma-shape construction).
const ArithVar = struct { name: StrId, t: TermId };

/// Close `body` in `forall v0, v1, …;` over the fresh vars (outermost = vars[0]).
fn closeForallChain(prove: *Prove, body: TermId, vars: []const ArithVar, sort: term.SortId) Error!TermId {
    var f = body;
    var i = vars.len;
    while (i > 0) {
        i -= 1;
        const closed = try prove.pool.close(f, vars[i].name);
        f = try prove.pool.add(.{ .quant = .{ .q = .forall, .sort = sort, .hint = vars[i].name, .body = closed } });
    }
    return f;
}

test "mixedCertShape: a bare equation/order atom is in scope for the mixed skeleton" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;
    const a = try rig.v("a");
    const b = try rig.v("b");
    // `a = b` — the std/integer/divides.b4m:1073 shape (a bare equation the equation cert
    // cannot reach by rewriting, decided semantically by the skeleton instead).
    try testing.expect(mixedCertShape(p, try rig.eq(a, b)));
    // a boolean combination is in scope too (the original motivating shape).
    const conj = try p.pool.add(.{ .bin = .{ .op = .and_op, .lhs = try rig.eq(a, b), .rhs = try rig.eq(b, a) } });
    try testing.expect(mixedCertShape(p, conj));
    const neg = try p.pool.add(.{ .not = try rig.eq(a, b) });
    try testing.expect(mixedCertShape(p, neg));
}

test "mixedCertShape: a QUANTIFIED body is not a skeleton (its binders are peeled first)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const p = rig.prove;
    const a = try rig.v("a");
    const body = try rig.eq(a, a);
    const closed = try p.pool.close(body, try rig.ctx.interner.internString("a"));
    const q = try p.pool.add(.{ .quant = .{ .q = .forall, .sort = rig.int, .hint = try rig.ctx.interner.internString("a"), .body = closed } });
    try testing.expect(!mixedCertShape(p, q));
}

test "arithCanon: sort + inverse-cancel both act UNDER the succ tower — succ(add(add(x, d), add(y, neg(x)))) ≡ succ(add(y, d))" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const tr = try towerRules(rig);
    const x = try rig.v("x");
    const y = try rig.v("y");
    const d = try rig.v("d");
    const lhs = try rig.a1(rig.succ, try rig.a2(rig.add, try rig.a2(rig.add, x, d), try rig.a2(rig.add, y, try rig.a1(rig.neg, x))));
    const rhs = try rig.a1(rig.succ, try rig.a2(rig.add, y, d));
    const pre_rules = tr.rules[0..tr.assoc];
    const rs = (try arithCanon(rig.prove, tr.symbols, tr.rules, pre_rules, tr.assoc, tr.comm, tr.swap, .{ .nf = lhs, .trace = &.{} })).?;
    const rt = (try arithCanon(rig.prove, tr.symbols, tr.rules, pre_rules, tr.assoc, tr.comm, tr.swap, .{ .nf = rhs, .trace = &.{} })).?;
    try testing.expect(rig.prove.pool.alphaEq(rs.nf, rt.nf));
}

/// The additive normalizer's rule set over the rig's ring + succ, exactly as arithEmitEquation
/// builds it: the ℤ elimination pre-rules (qualified, so the rig file needn't declare the
/// lemmas) followed by the add AC triple at assoc/comm/swap.
const TowerRules = struct { rules: []const rewrite.Rule, assoc: usize, comm: usize, swap: usize, symbols: Symbols };

fn towerRules(rig: testrig.Rig) !TowerRules {
    const symbols: Symbols = .{ .nat = rig.int, .zero = rig.zero, .succ = rig.succ, .add = rig.add, .neg = rig.neg };
    var rules: std.ArrayList(rewrite.Rule) = .empty;
    var cites: std.ArrayList(EqCert.RuleCite) = .empty;
    try pushAdditiveElim(rig.prove, &rules, &cites, symbols, try rig.ctx.interner.internString("T"), 0);
    const pre = rules.items.len;
    try ac.pushACTriple(rig.prove, &rules, &cites, rig.add, rig.int, "addIsAssociative", "addIsCommutative", "addLeftSwap", 0);
    return .{ .rules = rules.items, .assoc = pre, .comm = pre + 1, .swap = pre + 2, .symbols = symbols };
}

test "acPlan: a succ-tower root sorts the sum UNDER the tower — succ(add(y, x)) ≡ succ(add(x, y))" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const tr = try towerRules(rig);
    const x = try rig.v("x");
    const y = try rig.v("y");
    const yx = try rig.a1(rig.succ, try rig.a2(rig.add, y, x));
    const xy = try rig.a1(rig.succ, try rig.a2(rig.add, x, y));
    const ps = (try ac.acPlan(rig.prove, tr.symbols, tr.rules, tr.assoc, tr.comm, tr.swap, yx)).?;
    const pt = (try ac.acPlan(rig.prove, tr.symbols, tr.rules, tr.assoc, tr.comm, tr.swap, xy)).?;
    try testing.expect(rig.prove.pool.alphaEq(ps.sorted, pt.sorted));
    // exactly one side moved, by ONE commutativity rewrite whose before/after are the whole towers.
    const moved = if (ps.trace.len > 0) ps else pt;
    const moved_start = if (ps.trace.len > 0) yx else xy;
    try testing.expectEqual(@as(usize, 1), moved.trace.len);
    try testing.expect(rig.prove.pool.alphaEq(moved.trace[0].before, moved_start));
    try testing.expect(rig.prove.pool.alphaEq(moved.trace[0].after, moved.sorted));
}

test "cancelInverses: an inverse pair UNDER a succ tower cancels and the tower survives — succ(add(x, add(d, neg(x)))) ≡ succ(d)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const tr = try towerRules(rig);
    const x = try rig.v("x");
    const d = try rig.v("d");
    const whole = try rig.a1(rig.succ, try rig.a2(rig.add, x, try rig.a2(rig.add, d, try rig.a1(rig.neg, x))));
    var trace: std.ArrayList(rewrite.Rewrite) = .empty;
    const out = (try ac.cancelInverses(rig.prove, tr.symbols, tr.rules, tr.comm, tr.swap, whole, &trace)).?;
    try testing.expect(rig.prove.pool.alphaEq(out, try rig.a1(rig.succ, d)));
    // the rewrites chain: the first starts at the whole tower, each next at the previous after,
    // the last lands on the result — every step names the WHOLE term (kernel `rewrite` shape).
    try testing.expect(trace.items.len > 0);
    try testing.expect(rig.prove.pool.alphaEq(trace.items[0].before, whole));
    for (trace.items[1..], 0..) |rw, i| try testing.expect(rig.prove.pool.alphaEq(rw.before, trace.items[i].after));
    try testing.expect(rig.prove.pool.alphaEq(trace.items[trace.items.len - 1].after, out));
}
