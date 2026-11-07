//! The `specialize` accelerated tactic — a struct that is one variant of `Accelerants.Tactic`. See
//! `Accelerants.zig` for the three-phase contract it implements.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../ast.zig");
const InternPool = @import("../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../term.zig");
const TermId = term.TermId;
const SortId = term.SortId;
const kernel = @import("../kernel.zig");
const Engine = @import("../Engine.zig");
const Walk = @import("../Engine/ProveTask/Walk.zig");
const Elab = @import("../Engine/ProveTask/Elab.zig");
const Schema = @import("../Engine/ProveTask/Schema.zig");
const Accelerants = @import("../Accelerants.zig");
const Site = @import("Site.zig");
const Error = Site.Error;
const tokName = Site.tokName;
const common = @import("common.zig");

pub const schema_slot: Accelerants.SchemaSlot = .head;
pub const premise_shape: Accelerants.PremiseShape = .head_then_refs;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

/// Phase 1: nothing beyond the cited facts, which the scaffolding demands from the consts above.
pub fn read(self: @This(), site: *Site, w: *const Walk, c: ast.Step.Claim) Allocator.Error!?Engine.TaskIndex {
    _ = self;
    _ = site;
    _ = w;
    _ = c;
    return null;
}

/// Phase 2: does this head, at these args, YIELD the claim? Strict answers that only after the
/// instance is PROVEN (`withGuardPremises`, or the kernel's instantiation check), which admit
/// mode skips — so the check runs here, on the head's STATEMENT: open one ∀ per arg at the
/// ELABORATED argument, strip the antecedents the refs discharge, and α-match the remainder
/// against the goal. The head is trusted on its statement — a trusted fact that turns out false
/// is a sanctioned way `--fast` outruns strict; admitting a claim the head cannot yield is not.
///
/// The consequent cannot be matched in PARAM space (`forall a, b; a = b` is literally
/// `p1 = p2`, which matches ANY equation goal), hence the elaborated args. They elaborate in the
/// caller's scope with the head's free eigenvars bound — exactly what the instance does.
pub fn decide(self: @This(), site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    _ = self;
    const head = c.schema orelse return site.fail(c.rule.start, "specialize requires a head theorem/axiom or local step", .{});
    const head_local = w.findStep(tokName(head)) != null;
    // A head that names nothing is a TYPO, not a mismatch: the scaffolding's root check
    // diagnoses it with position after decide returns, and `--fast` must report exactly what
    // strict does — reading it here would diagnose it first, badly located.
    if (!head_local and !site.citationDeclared(head)) return;
    const head_formula = if (head_local)
        site.producerPremiseFormula(try site.resolveStepRef(w, head))
    else
        try common.factStatement(site, head);

    // a LOCAL head carries the enclosing `fix` eigenvars free; bind them so an arg naming one
    // elaborates back to the very fvar (sort is part of its identity — bind at the carrier).
    var free_fvars: std.ArrayList(term.Node.Fvar) = .empty;
    try site.collectFreeFvars(head_formula, &free_fvars);
    const mark = e.scopeMark();
    defer e.scopeTruncate(mark);
    for (free_fvars.items) |fv| {
        const sort_ix: InternPool.Index = @enumFromInt(@intFromEnum(fv.sort));
        const carrier: SortId = @enumFromInt(@intFromEnum(site.ctx.interner.carrierOf(sort_ix)));
        try e.pushBinder(fv.name, carrier, fv.name);
    }

    var instance = head_formula;
    for (c.args) |arg| {
        const typed = try e.elaborateExpr(arg);
        instance = try openForallAt(site, instance, typed.id) orelse
            return site.fail(c.rule.start, "specialize: head is not universally quantified enough for {d} argument(s)", .{c.args.len});
    }
    // The claim is the instance's CONCLUSION: some suffix of its `->` chain. The antecedents
    // before it are what the refs discharge plus the refined-binder GUARDS the opening injected
    // (`invertible(g) ->` for a `forall g: Perm`), which strict discharges from the caller's
    // context at certify time — the same walk `withGuardPremises` does to count them.
    var rest = instance;
    while (true) {
        if (site.pool.alphaEq(rest, goal)) return;
        const n = site.pool.get(rest);
        if (n != .bin or n.bin.op != .implies) break;
        rest = n.bin.rhs;
    }
    return site.fail(c.rule.start, "the claim does not match the instance's conclusion:\n  claim:      {s}\n  instance:   {s}", .{ try site.renderTerm(goal), try site.renderTerm(instance) });
}

/// Open the next `forall` AT a term: walk any leading `->` chain to the binder, open its body at
/// `at`, and rebuild the `->` prefix around the result. Null when no `forall` is left.
fn openForallAt(site: *Site, formula: TermId, at: TermId) Error!?TermId {
    var ants: std.ArrayList(TermId) = .empty;
    var t = formula;
    while (true) {
        const node = site.pool.get(t);
        if (node == .quant and node.quant.q == .forall) {
            var opened = try site.pool.open(node.quant.body, at);
            var i = ants.items.len;
            while (i > 0) : (i -= 1) {
                opened = try site.pool.add(.{ .bin = .{ .op = .implies, .lhs = ants.items[i - 1], .rhs = opened } });
            }
            return opened;
        }
        if (node == .bin and node.bin.op == .implies) {
            try ants.append(site.ctx.arena, node.bin.lhs);
            t = node.bin.rhs;
            continue;
        }
        return null;
    }
}

pub fn certify(self: @This(), site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    _ = self;
    return produceSpecialize(site, w, e, goal, c);
}

/// Build the synthetic schema for `using specialize HEAD(args) hyps`. HEAD is a forall-
/// quantified fact (global theorem/axiom) or a LOCAL forall-shaped step. The schema:
///   params  = one value param per arg (sorts = the peeled ∀-binder sorts)
///   body    = [HEAD-formula ->]  <arg-instantiated HEAD tail>   (the `->`-tail after the
///             ∀ prefix is peeled at the params; a LOCAL head prepends its formula as the
///             first antecedent so the schema proof needn't cite it externally)
///   proof   = (global) cite HEAD; apply_at(params)
///             (local)  assume HEAD-formula; apply_at(params) on the assumption
/// The call site then instantiates at the args and discharges: (local head-step +) the hyps.
pub fn produceSpecialize(site: *Site, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!?Accelerants.Synthetic {
    _ = e;
    _ = goal;
    const head = c.schema orelse return site.fail(c.rule.start, "specialize requires a head theorem/axiom or local step", .{});
    // STRICT ONLY. `--fast` never reaches the producer: `decide` above settles the claim on the
    // head's statement, and the claim-vs-instance match strict relies on (`withGuardPremises`,
    // after the instance is proven) is what decide mirrors. Nothing here is admit-aware.
    var b: Accelerants.Builder = .{ .arena = site.ctx.arena, .interner = site.ctx.interner, .pool = site.pool, .loc = c.rule.start };

    // resolve HEAD → its formula term + how the schema proof cites it.
    const head_local = w.findStep(Site.tokName(head)) != null;
    var head_formula: TermId = undefined;
    if (head_local) {
        const sref = try site.resolveStepRef(w, head);
        head_formula = site.producerPremiseFormula(sref);
    } else {
        // resolveFactRef rejects a schema head (no ground formula) — a clean diagnostic, not a
        // crash — so `.fact` is safe here. (The generated cert cites it kind-agnostically with
        // `cite`, so the head's axiom-vs-theorem kind is never needed.) `citedFactFormula`
        // routes by mode: strict resolves the proven fact, admit mode reads the STATEMENT so
        // the ∀-peel below can run under `--fast` without racking a ProveTask.
        head_formula = (try common.citedFactFormula(site, head)).formula;
    }

    // Instantiate one ∀ per arg at a fresh param fvar, INTERLEAVED with `->` antecedents:
    // a head `∀k; guard(k) -> ∀s; …` opens `k`, then must descend past `guard(k) ->` to
    // reach `∀s`. `openNextForall` walks the leading `->` chain (preserving it) to the next
    // forall, opens it at the param, and rebuilds the `->` prefix around the opened body.
    // ABSTRACT the head formula's FREE caller-local eigenvars (an enclosing `fix k`) into value
    // params UP FRONT — a LOCAL head like `forall a,b; add(k,a)=add(k,b) -> a=b` carries the free
    // `k`, which must become a schema param (else the generated schema references `k`, absent from
    // its scope: "reference not found: 'k'"). Named `f1,f2,…` (distinct from the ∀-arg params
    // `p1..pN` below); substituted through head_formula before the ∀ peel. A GLOBAL head is closed
    // (no free eigenvars) so this is a no-op there.
    var free_fvars: std.ArrayList(term.Node.Fvar) = .empty;
    try site.collectFreeFvars(head_formula, &free_fvars);
    const fparams = try site.ctx.arena.alloc(ast.SchemaParam, free_fvars.items.len);
    const fargs = try site.ctx.arena.alloc(*const ast.Expr, free_fvars.items.len);
    // Bindings so each call-site arg (a display-trimmed fvar name) re-resolves to its very
    // fvar. A caller `fix`-bound eigenvar already resolves through the proof-local scope, but a
    // free fvar INHERITED from a schema-instance monomorphization (see `Synthetic.fvar_binds`)
    // has no source binder — the plumbing installs these into the caller Elab scope.
    const fbinds = try site.ctx.arena.alloc(Accelerants.Synthetic.FvarBind, free_fvars.items.len);
    for (free_fvars.items, 0..) |fv, i| {
        const fname = try b.intern(try std.fmt.allocPrint(site.ctx.arena, "f{d}", .{i + 1}));
        const pf = try site.pool.add(.{ .fvar = .{ .name = fname, .sort = fv.sort } });
        head_formula = try site.pool.substFvar(head_formula, fv.name, pf);
        fparams[i] = .{ .name = b.tok(fname), .kind = .{ .value = b.sortTok(fv.sort) } };
        // the call-site arg names the fvar by its EXACT hygienic name (`n#6`, never lexable), and
        // the bind is keyed the same way: two eigenvariables that DISPLAY alike (the schema's
        // own `fix n` and a caller `n` captured through a lambda) stay distinct.
        fargs[i] = try b.nameExpr(fv.name);
        fbinds[i] = .{ .name = fv.name, .fvar = fv.name, .sort = fv.sort };
    }

    const nargs = c.args.len;
    const pnames = try site.ctx.arena.alloc(StrId, nargs);
    const arg_params = try site.ctx.arena.alloc(ast.SchemaParam, nargs);
    var tail = head_formula;
    for (0..nargs) |i| {
        pnames[i] = try b.intern(try std.fmt.allocPrint(site.ctx.arena, "p{d}", .{i + 1}));
        const opened = try openNextForall(site, tail, pnames[i]) orelse {
            return site.fail(c.rule.start, "specialize: head is not universally quantified enough for {d} argument(s)", .{nargs});
        };
        tail = opened.body;
        arg_params[i] = .{ .name = b.tok(pnames[i]), .kind = .{ .value = b.sortTok(opened.sort) } };
    }
    // schema params = the free-eigenvar params FIRST, then the ∀-arg params.
    const params = try std.mem.concat(site.ctx.arena, ast.SchemaParam, &.{ fparams, arg_params });

    // WALK the head formula (as `tail` was built) collecting, IN ORDER, the ∀-binders'
    // params and the kept `->` ANTECEDENTS — the schema body is `ant0 -> ant1 -> … -> C`
    // and its proof assumes each antecedent, threads apply_at(param)/modus_ponens(ant)
    // to C, then discharge back. For a LOCAL head the head formula is antecedent #0.
    var ants: std.ArrayList(TermId) = .empty; // kept antecedents, in body order
    if (head_local) try ants.append(site.ctx.arena, head_formula);
    // re-walk head_formula interleaving to enumerate the `->` LHSs at the params.
    {
        var t2 = head_formula;
        var ai: usize = 0;
        while (true) {
            const node = site.pool.get(t2);
            if (node == .quant and node.quant.q == .forall and ai < nargs) {
                const pf = try site.pool.add(.{ .fvar = .{ .name = pnames[ai], .sort = node.quant.sort } });
                t2 = try site.pool.open(node.quant.body, pf);
                ai += 1;
            } else if (node == .bin and node.bin.op == .implies) {
                try ants.append(site.ctx.arena, node.bin.lhs);
                t2 = node.bin.rhs;
            } else break;
        }
    }
    const consequent = tail_consequent: {
        // C = tail with all leading `->` antecedents stripped (they're the kept ants after
        // the local-head one). Strip (ants.len - localOffset) implications off `tail`.
        var t3 = tail;
        var strip = ants.items.len - @intFromBool(head_local);
        while (strip > 0) : (strip -= 1) {
            t3 = site.pool.get(t3).bin.rhs;
        }
        break :tail_consequent t3;
    };

    var body_expr = try b.termExpr(tail);
    if (head_local) body_expr = try b.implies(try b.termExpr(head_formula), body_expr);

    const steps = try common.buildSpecializeProof(site, &b, head, head_local, head_formula, pnames, ants.items, consequent);

    // deterministic hash-name from the head formula + arg count + HEAD FLAVOUR (re-entry
    // stable). The flavour must be in the name: a LOCAL head's body carries the head formula as
    // antecedent #0 and a DECLARED head's does not, yet a local step that `[by cite]`s a fact
    // has exactly the fact's formula — so without this bit the two flavours hash alike and
    // `registerDecl`'s keep-first lets whichever theorem runs second instantiate the OTHER
    // flavour's body against its own premise list (tests/cases/schema/instance_crosstalk/).
    const flavour: u64 = if (head_local) 0xA5A5A5A5A5A5A5A5 else 0;
    const hash = Schema.termHash(site.ctx.interner, site.pool, head_formula) ^ (@as(u64, @intCast(nargs)) *% 0x9E3779B97F4A7C15) ^ flavour;
    const name = try b.intern(try std.fmt.allocPrint(site.ctx.arena, "specialize{{{x}}}", .{hash}));

    // call-site args mirror the params: the free-eigenvar args FIRST, then the user's ∀-args.
    const args = try std.mem.concat(site.ctx.arena, *const ast.Expr, &.{ fargs, c.args });
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = args,
        .premises = c.refs,
        .seen = b.seen.items,
        .assumed = b.assumed.items,
        .fvar_binds = fbinds,
    };
}

/// Instantiate the NEXT `forall` reachable through a leading `->` chain, at a fresh fvar
/// named `pname`. Descends the RHS of `->` nodes (preserving them), opens the forall's body
/// at the fvar, and rebuilds the `->` prefix around it. Returns the rebuilt term + the
/// binder's sort, or null if no forall is reachable (only `->`s / a non-quant leaf).
const OpenedForall = struct { body: TermId, sort: SortId };

fn openNextForall(site: *Site, id: TermId, pname: StrId) Error!?OpenedForall {
    // Descend the leading `->` chain to the first `forall`, opening it, then rewrap the `->`
    // prefix around the opened body. Iterative (was linear recursion + rebuild-unwind): collect
    // the implication LHSs on the way down, then fold them back over the opened body innermost-out.
    var prefix: std.ArrayList(TermId) = .empty; // implication LHSs, outer→inner
    defer prefix.deinit(site.ctx.gpa);
    var cur = id;
    const opened: OpenedForall = while (true) {
        const node = site.pool.get(cur);
        switch (node) {
            .quant => |q| {
                if (q.q != .forall) return null;
                const pf = try site.pool.add(.{ .fvar = .{ .name = pname, .sort = q.sort } });
                break .{ .body = try site.pool.open(q.body, pf), .sort = q.sort };
            },
            .bin => |bn| {
                if (bn.op != .implies) return null;
                try prefix.append(site.ctx.gpa, bn.lhs);
                cur = bn.rhs;
            },
            else => return null,
        }
    };
    // rewrap: `lhs_outer -> ( … -> ( lhs_inner -> opened.body ) )` — fold prefix inner-to-outer.
    var body = opened.body;
    var i = prefix.items.len;
    while (i > 0) {
        i -= 1;
        body = try site.pool.add(.{ .bin = .{ .op = .implies, .lhs = prefix.items[i], .rhs = body } });
    }
    return .{ .body = body, .sort = opened.sort };
}
