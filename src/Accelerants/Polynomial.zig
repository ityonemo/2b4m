//! The `polynomial` accelerated tactic — a struct that is one variant of `Accelerants.Tactic`. See
//! `Accelerants.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const TermId = term.TermId;
const Engine = @import("../Engine.zig");
const Walk = @import("../Engine/ProveTask/Walk.zig");
const RefScan = @import("../Engine/ProveTask/RefScan.zig");
const Elab = @import("../Engine/ProveTask/Elab.zig");
const Accelerants = @import("../Accelerants.zig");
const polycanon = @import("polycanon.zig");
const FetchTask = @import("../Engine/FetchTask.zig");
const Site = @import("Site.zig");
const Demand = @import("../Engine/ProveTask/Demand.zig");
const Error = Site.Error;
const tokName = Site.tokName;
const testing = std.testing;
const common = @import("common.zig");
const testrig = @import("testrig.zig");

/// the `_quantified` variant: a `forall …; s = t` goal, peeled first
quantified: bool,

pub const schema_slot: Accelerants.SchemaSlot = .theory_selector;
pub const premise_shape: Accelerants.PremiseShape = .local_refs_kept;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

/// Phase 1: the vocabulary completion (`completePolyOps`) racks ident FetchTasks for operators
/// the goal implies the theory has — `ZERO` for a `neg`, `add` for a `mul`+`succ`. Those must be
/// resolved BEFORE the producer runs, since a park during decide has no channel to propagate.
/// Demand the well-known ring names in the theory namespace: the selector's import when given,
/// else this proof's file.
pub fn read(self: @This(), site: *Site, w: *const Walk, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    _ = self;
    _ = w;
    const names = [_][]const u8{ "add", "mul", "succ", "prev", "ZERO", "ONE", "neg", "sub" };
    var tfile = site.file;
    if (c.schema) |sel| {
        const st = site.ctx.idents.lookup(site.ctx.io, .{ .namespace = site.ns, .name = tokName(sel) });
        if (st == null) {
            return try site.h.rackIndexed(try FetchTask.new(site.ctx.arena, .{
                .file = site.file,
                .name = tokName(sel),
                .loc = sel.start,
                .loc_file = site.file,
            }));
        }
        switch (st.?) {
            .in_flight => |owner| return owner,
            .done => |ix| if (site.ctx.interner.keyOf(ix) == .import) {
                tfile = site.ctx.interner.keyOf(site.ctx.interner.keyOf(ix).import.namespace).namespace.file;
            },
        }
    }
    const fid = site.ctx.fileOf(tfile) orelse return null;
    const tns = try site.ctx.interner.namespace(.universe, tfile);
    var refs: std.ArrayList(RefScan.Ref) = .empty;
    for (names) |nm| {
        const nid = try site.ctx.interner.internString(nm);
        const d = site.ctx.declOf(fid, nid) orelse continue;
        if (d.* == .define) continue;
        try refs.append(site.ctx.arena, .{ .ns = null, .name = nid, .domain = .ident, .loc = c.rule.start });
    }
    return Demand.resolveRefs(site.ctx, site.h, tfile, tns, site.model, site.self_key, refs.items);
}

pub fn decide(self: @This(), site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    return common.decideFused(self, site, w, e, goal, c);
}

pub fn certify(self: @This(), site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    return if (self.quantified) producePolynomialQuantified(site, w, e, goal, c) else producePolynomial(site, w, e, goal, c);
}

/// `[using polynomial(M) ]` — prove an equation goal `s = t` as a ring identity.
pub fn producePolynomial(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    if (c.args.len != 0) return site.fail(c.rule.start, "polynomial takes no arguments (the theory is the parenthesized selector)", .{});
    const gn = site.pool.get(goal);
    if (gn != .eq) {
        if (gn == .quant and gn.quant.q == .forall) {
            return site.fail(c.rule.start, "polynomial proves equations; did you mean polynomial_quantified?", .{});
        }
        return site.fail(c.rule.start, "polynomial: goal is not an equation", .{});
    }
    return buildPolynomial(site, w, e, c, goal, &.{});
}

/// `[using polynomial_quantified(M) ]` — like polynomial but the goal is `forall …; s = t`.
pub fn producePolynomialQuantified(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    if (c.args.len != 0) return site.fail(c.rule.start, "polynomial_quantified takes no arguments (the theory is the parenthesized selector)", .{});
    const peeled = try common.peelForallEq(site, goal, c, "polynomial_quantified") orelse return null;
    return buildPolynomial(site, w, e, c, peeled.body, peeled.eigen);
}

/// Shared polynomial core over the (possibly ∀-peeled) equation body `eq_goal_raw`. Reads the
/// ring operator syms off the goal, builds the hardcoded rule set + selector-qualified cites,
/// abstracts free caller-locals into params, canonicalizes both sides IN PARAM SPACE, and hands
/// the traces to `finishReorder`. `polynomial` has no LOCAL premises (all its rules are global
/// well-known lemmas cited inside the cert), so `local_prems` is empty.
fn buildPolynomial(site: *Site, w: *const Walk, e: *Elab, c: ast.Step.Claim, eq_goal_raw: TermId, eigen: []const term.Node.Fvar) Error!?Accelerants.Synthetic {
    var b: Accelerants.Builder = .{ .arena = site.ctx.arena, .interner = site.ctx.interner, .pool = site.pool, .loc = c.rule.start };

    // read the ring operators off the goal (by well-known head NAME — inspecting the goal, not
    // a scope lookup). `add`/`mul` are required; the rest are optional (present iff the goal
    // has them). The theory selector's qualifier is stamped into every emitted cite.
    const goal_ops = (try polycanon.readPolyOps(site, eq_goal_raw)) orelse
        return site.fail(c.rule.start, "polynomial: the goal has no add/mul structure", .{});
    // `--fast` declines to EMIT the certificate; the CANONICALIZATION DECISION still runs.
    // Admitting here accepted any add/mul-shaped equation, true or not. `completePolyOps`
    // already parks on an outstanding ident demand (null → blocked), which is exactly what the
    // decision needs — so admit lands after the normal-form comparison below, before
    // `finishReorder` emits the cert. See design/acceleration.md.
    // COMPLETE the vocabulary from the theory (a demand may be outstanding → null, blocked).
    // In ADMIT mode a null is a PARK the dispatch has no channel for, so the read pass must
    // have demanded these already; reaching here parked means it did not.
    const ops = (try completePolyOps(site, c.schema, goal_ops)) orelse return null;
    const qualifier: StrId = if (c.schema) |s| s.name else .none;
    const pr = try polycanon.polyRules(site, ops, qualifier, c.rule.start);

    // abstract free caller-local fvars (an enclosing `fix`) into value params, then canonicalize
    // in PARAM space so the trace + schema body speak `p1, p2, …`. Eigenvariables (the peeled ∀
    // vars) stay free and are re-bound by the `fix` wrapper in finishReorder.
    const ag = try common.abstractGoal(site, &b, eq_goal_raw, &.{}, eigen);
    const abs = ag.abs;
    const eq_goal = ag.goal_p;
    const gn = site.pool.get(eq_goal).eq;
    const s0 = gn.lhs;
    const t0 = gn.rhs;

    const rs = (try polycanon.polyCanon(site, pr, s0)) orelse
        return site.fail(c.rule.start, "polynomial: could not canonicalize the left side", .{});
    const rt = (try polycanon.polyCanon(site, pr, t0)) orelse
        return site.fail(c.rule.start, "polynomial: could not canonicalize the right side", .{});
    if (!site.pool.alphaEq(rs.nf, rt.nf)) {
        return site.fail(c.rule.start, "polynomial: sides expand differently: '{s}' vs '{s}'", .{
            try site.renderTerm(try common.unabstract(site, rs.nf, abs)),
            try site.renderTerm(try common.unabstract(site, rt.nf, abs)),
        });
    }
    // ADMIT: both sides expanded to the SAME canonical form, so a certificate demonstrably
    // exists — only emitting it is pruned.
    if (site.admit_mode) {
        site.producer_premise_refs = null;
        site.admit_ok = true;
        return null;
    }
    return common.finishReorder(site, w, e, &b, c, "polynomial", s0, t0, pr.rules, pr.cites, rs, rt, abs, eigen, &.{});
}

/// COMPLETE a goal's ring vocabulary from the THEORY: the canonicalization can need a symbol
/// the goal never mentions — `ZERO` to cancel an inverse pair (`t + neg(t) → ZERO`), `neg`
/// to expand `sub`, `add` to expand a numeral coefficient (`mul(succ(a), b) → add(…)`) or a
/// `sub`. Deterministic in (goal, selector): only the vocabulary the goal's own operators
/// IMPLY the theory has is demanded (a `neg` implies a ring with `ZERO`; never a probe for
/// optional vocabulary such as `succ` in a field). Resolved by name in the theory namespace
/// (the selector's import, else this proof's); an unfetched symbol racks its FetchTask and
/// returns null with `producer_blocker` set (the step suspends; the producer re-runs). A
/// missing symbol surfaces as that FetchTask's "reference not found" at the step.
fn completePolyOps(site: *Site, selector: ?lexer.Token, goal: polycanon.Ops) Error!?polycanon.Ops {
    var ops = goal;
    const need_zero = ops.zero == null and (ops.neg != null or ops.sub != null);
    const need_neg = ops.neg == null and ops.sub != null;
    const need_add = ops.add == null and (ops.sub != null or (ops.mul != null and (ops.succ != null or ops.prev != null)));
    if (!need_zero and !need_neg and !need_add) return ops;
    // the theory namespace + file: the selector's import (demanded if unfetched), else ours.
    var ns = site.ns;
    var file = site.file;
    if (selector) |sel| {
        const st = site.ctx.idents.lookup(site.ctx.io, .{ .namespace = site.ns, .name = Site.tokName(sel) }) orelse {
            site.producer_blocker = try site.h.rackIndexed(try FetchTask.new(site.ctx.arena, .{ .file = site.file, .name = Site.tokName(sel), .loc = sel.start, .loc_file = site.file }));
            return null;
        };
        switch (st) {
            .in_flight => |owner| {
                site.producer_blocker = owner;
                return null;
            },
            .done => |ix| switch (site.ctx.interner.keyOf(ix)) {
                .import => |m| {
                    ns = m.namespace;
                    file = site.ctx.interner.keyOf(m.namespace).namespace.file;
                },
                else => return site.fail(sel.start, "'{s}' is not a theory (an import)", .{site.text(sel)}),
            },
        }
    }
    if (need_zero) ops.zero = (try demandWellKnown(site, ns, file, "ZERO", .constant, selector)) orelse return null;
    if (need_neg) ops.neg = (try demandWellKnown(site, ns, file, "neg", .func, selector)) orelse return null;
    if (need_add) ops.add = (try demandWellKnown(site, ns, file, "add", .func, selector)) orelse return null;
    return ops;
}

/// A well-known symbol by NAME in the theory namespace `ns` (file `file`): its SymId when
/// fetched (kind-checked; the ambient model applied), else null with `producer_blocker` set
/// (racked or already in flight). Diagnoses a fetched symbol of the wrong kind.
fn demandWellKnown(site: *Site, ns: InternPool.Index, file: InternPool.Index, name: []const u8, comptime kind: enum { func, constant }, at: ?lexer.Token) Error!?term.SymId {
    const nid = try common.internStrRt(site, name);
    const loc: u32 = if (at) |t| t.start else 0;
    const st = site.ctx.idents.lookup(site.ctx.io, .{ .namespace = ns, .name = nid }) orelse {
        site.producer_blocker = try site.h.rackIndexed(try FetchTask.new(site.ctx.arena, .{ .file = file, .name = nid, .loc = loc, .loc_file = site.file }));
        return null;
    };
    const ix = switch (st) {
        .done => |x| site.ctx.interner.applyModel(site.model, x),
        .in_flight => |owner| {
            site.producer_blocker = owner;
            return null;
        },
    };
    const ok = switch (site.ctx.interner.keyOf(ix)) {
        .func => kind == .func,
        .constant => kind == .constant,
        else => false,
    };
    if (!ok) return site.fail(loc, "polynomial: the theory's '{s}' is not a {s}", .{ name, if (kind == .func) "function" else "constant" });
    return @enumFromInt(@intFromEnum(ix));
}

test "completePolyOps: a goal with neg but no ZERO demands ZERO from the theory — blocked until fetched, then filled" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var threaded: std.Io.Threaded = .init(arena, .{});
    const rig = try testrig.Rig.init(arena, threaded.io());
    const e = try rig.v("e");
    const goal = try rig.eq(try rig.a2(rig.add, e, try rig.a1(rig.neg, e)), e);
    var ops = (try polycanon.readPolyOps(rig.site, goal)).?;
    try testing.expect(ops.zero == null);
    // ZERO is already fetched in the rig's namespace → completes immediately, no blocker.
    const done = (try completePolyOps(rig.site, null, ops)).?;
    try testing.expectEqual(rig.zero, done.zero.?);
    try testing.expect(rig.site.producer_blocker == null);
    // a goal with NO neg never asks for ZERO (the vocabulary the goal implies is all we demand).
    const plain = try rig.eq(try rig.a2(rig.add, e, e), try rig.a2(rig.add, e, e));
    ops = (try polycanon.readPolyOps(rig.site, plain)).?;
    const done2 = (try completePolyOps(rig.site, null, ops)).?;
    try testing.expect(done2.zero == null);
}
