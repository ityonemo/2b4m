//! The `specialize` accelerated tactic — a struct that is one variant of `Prove.Tactic`. See
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
const Context = @import("../../../Context.zig");
const Walk = @import("../Walk.zig");
const RefScan = @import("../RefScan.zig");
const Elab = @import("../Elab.zig");
const Schema = @import("../Schema.zig");
const Accelerant = @import("../Accelerant.zig");
const Verify = @import("../../../Verify.zig");
const EqCert = @import("../EqCert.zig");
const Polynomial = @import("../Polynomial.zig");
const simplify_mod = @import("../simplify.zig");
const presburger_mod = @import("../presburger.zig");
const smt = @import("../smt.zig");
const farkas = @import("../farkas.zig");
const FactKV = @import("../../../FactKV.zig");
const FetchTask = @import("../../../Engine/FetchTask.zig");
const Prove = @import("../Prove.zig");
const Error = Prove.Error;
const tokName = Prove.tokName;
const testing = std.testing;
const common = @import("common.zig");

pub const schema_slot: Accelerant.SchemaSlot = .head;
pub const premise_shape: Accelerant.PremiseShape = .head_then_refs;
/// `Claim.args` name LEMMAS (not value terms): demanded as facts, never elaborated as terms
pub const lemma_args = false;

pub fn decide(self: @This(), prove: *Prove, w: *const Walk, e: *Elab, goal: TermId, c: ast.Step.Claim) Error!void {
    return common.decideFused(self, prove, w, e, goal, c);
}

pub fn certify(self: @This(), prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    _ = self;
    return produceSpecialize(prove, w, goal, c);
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
pub fn produceSpecialize(prove: *Prove, w: *const Walk, goal: TermId, c: ast.Step.Claim) Error!?Accelerant.Synthetic {
    _ = goal;
    const head = c.schema orelse return prove.fail(c.rule.start, "specialize requires a head theorem/axiom or local step", .{});
    // ADMIT UP FRONT — the one trustable word whose decision genuinely cannot move here.
    //
    // What `--fast` must never do is admit a claim the specialization cannot produce, and that
    // match is done by `withGuardPremises` only AFTER the instance is PROVEN — which `--fast`
    // skips. Doing it in the producer does not work: the consequent is in PARAM space (for
    // `forall a, b; a = b` it is literally `p1 = p2`), and the actual arguments are AST exprs
    // that only the instance pass elaborates, so matching the consequent against the goal with
    // the params as pattern variables succeeds for ANY equation goal — measured 2026-10-26,
    // `succ(ZERO) = ZERO` matched `p1 = p2`. A real check needs the elaborated args, i.e. the
    // instance. (Moving admit past the peel is independently wrong: the caller installs
    // `fvar_binds` only after the producer returns, so a local head's abstracted params become
    // unresolvable — "reference not found: 'k'" across std/subgroup/products.b4m.)
    //
    // UNSOUND, TO FIX: `--fast` accepts a `specialize` whose instance conclusion differs from
    // the claim — so a FALSE goal is admitted (`succ(ZERO) = ZERO`). Every other trustable word
    // runs its decision or α-matches; this one checks only that a head is present. Gated by
    // `tests/cases/tactics/specialize/specialize_claim_mismatch_fast.b4m`, which pins today's
    // behaviour so the fix is noticed. See SPECIALIZE-FAST-UNSOUND.md for why the two obvious
    // fixes do not work.
    if (prove.admit_mode) {
        prove.admit_ok = true;
        return null;
    }
    var b: Accelerant.Builder = .{ .arena = prove.ctx.arena, .interner = prove.ctx.interner, .pool = prove.pool, .loc = c.rule.start };

    // resolve HEAD → its formula term + how the schema proof cites it.
    const head_local = w.findStep(Prove.tokName(head)) != null;
    var head_formula: TermId = undefined;
    if (head_local) {
        const sref = try prove.resolveStepRef(w, head);
        head_formula = prove.producerPremiseFormula(sref);
    } else {
        // resolveFactRef rejects a schema head (no ground formula) — a clean diagnostic, not a
        // crash — so `.fact` is safe here. (The generated cert cites it kind-agnostically with
        // `cite`, so the head's axiom-vs-theorem kind is never needed.) `citedFactFormula`
        // routes by mode: strict resolves the proven fact, admit mode reads the STATEMENT so
        // the ∀-peel below can run under `--fast` without racking a ProveTask.
        head_formula = (try common.citedFactFormula(prove, head)).formula;
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
    try prove.collectFreeFvars(head_formula, &free_fvars);
    const fparams = try prove.ctx.arena.alloc(ast.SchemaParam, free_fvars.items.len);
    const fargs = try prove.ctx.arena.alloc(*const ast.Expr, free_fvars.items.len);
    // Bindings so each call-site arg (a display-trimmed fvar name) re-resolves to its very
    // fvar. A caller `fix`-bound eigenvar already resolves through the proof-local scope, but a
    // free fvar INHERITED from a schema-instance monomorphization (see `Synthetic.fvar_binds`)
    // has no source binder — the plumbing installs these into the caller Elab scope.
    const fbinds = try prove.ctx.arena.alloc(Accelerant.Synthetic.FvarBind, free_fvars.items.len);
    for (free_fvars.items, 0..) |fv, i| {
        const fname = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "f{d}", .{i + 1}));
        const pf = try prove.pool.add(.{ .fvar = .{ .name = fname, .sort = fv.sort } });
        head_formula = try prove.pool.substFvar(head_formula, fv.name, pf);
        fparams[i] = .{ .name = b.tok(fname), .kind = .{ .value = b.sortTok(fv.sort) } };
        // the call-site arg names the fvar by its EXACT hygienic name (`n#6`, never lexable), and
        // the bind is keyed the same way: two eigenvariables that DISPLAY alike (the schema's
        // own `fix n` and a caller `n` captured through a lambda) stay distinct.
        fargs[i] = try b.nameExpr(fv.name);
        fbinds[i] = .{ .name = fv.name, .fvar = fv.name, .sort = fv.sort };
    }

    const nargs = c.args.len;
    const pnames = try prove.ctx.arena.alloc(StrId, nargs);
    const arg_params = try prove.ctx.arena.alloc(ast.SchemaParam, nargs);
    var tail = head_formula;
    for (0..nargs) |i| {
        pnames[i] = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "p{d}", .{i + 1}));
        const opened = try openNextForall(prove, tail, pnames[i]) orelse {
            return prove.fail(c.rule.start, "specialize: head is not universally quantified enough for {d} argument(s)", .{nargs});
        };
        tail = opened.body;
        arg_params[i] = .{ .name = b.tok(pnames[i]), .kind = .{ .value = b.sortTok(opened.sort) } };
    }
    // schema params = the free-eigenvar params FIRST, then the ∀-arg params.
    const params = try std.mem.concat(prove.ctx.arena, ast.SchemaParam, &.{ fparams, arg_params });

    // WALK the head formula (as `tail` was built) collecting, IN ORDER, the ∀-binders'
    // params and the kept `->` ANTECEDENTS — the schema body is `ant0 -> ant1 -> … -> C`
    // and its proof assumes each antecedent, threads apply_at(param)/modus_ponens(ant)
    // to C, then discharge back. For a LOCAL head the head formula is antecedent #0.
    var ants: std.ArrayList(TermId) = .empty; // kept antecedents, in body order
    if (head_local) try ants.append(prove.ctx.arena, head_formula);
    // re-walk head_formula interleaving to enumerate the `->` LHSs at the params.
    {
        var t2 = head_formula;
        var ai: usize = 0;
        while (true) {
            const node = prove.pool.get(t2);
            if (node == .quant and node.quant.q == .forall and ai < nargs) {
                const pf = try prove.pool.add(.{ .fvar = .{ .name = pnames[ai], .sort = node.quant.sort } });
                t2 = try prove.pool.open(node.quant.body, pf);
                ai += 1;
            } else if (node == .bin and node.bin.op == .implies) {
                try ants.append(prove.ctx.arena, node.bin.lhs);
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
            t3 = prove.pool.get(t3).bin.rhs;
        }
        break :tail_consequent t3;
    };

    var body_expr = try b.termExpr(tail);
    if (head_local) body_expr = try b.implies(try b.termExpr(head_formula), body_expr);

    const steps = try common.buildSpecializeProof(prove, &b, head, head_local, head_formula, pnames, ants.items, consequent);

    // deterministic hash-name from the head formula + arg count + HEAD FLAVOUR (re-entry
    // stable). The flavour must be in the name: a LOCAL head's body carries the head formula as
    // antecedent #0 and a DECLARED head's does not, yet a local step that `[by cite]`s a fact
    // has exactly the fact's formula — so without this bit the two flavours hash alike and
    // `registerDecl`'s keep-first lets whichever theorem runs second instantiate the OTHER
    // flavour's body against its own premise list (drafts/schema-instance-crosstalk/).
    const flavour: u64 = if (head_local) 0xA5A5A5A5A5A5A5A5 else 0;
    const hash = Schema.termHash(prove.ctx.interner, prove.pool, head_formula) ^ (@as(u64, @intCast(nargs)) *% 0x9E3779B97F4A7C15) ^ flavour;
    const name = try b.intern(try std.fmt.allocPrint(prove.ctx.arena, "specialize{{{x}}}", .{hash}));

    // call-site args mirror the params: the free-eigenvar args FIRST, then the user's ∀-args.
    const args = try std.mem.concat(prove.ctx.arena, *const ast.Expr, &.{ fargs, c.args });
    return .{
        .name = name,
        .decl = .{ .theorem = .{ .local = .{ .fact = .{ .name = b.tok(name), .formula = body_expr, .params = params }, .steps = steps } } },
        .args = args,
        .premises = c.refs,
        .seen = b.seen.items,
        .fvar_binds = fbinds,
    };
}

/// Instantiate the NEXT `forall` reachable through a leading `->` chain, at a fresh fvar
/// named `pname`. Descends the RHS of `->` nodes (preserving them), opens the forall's body
/// at the fvar, and rebuilds the `->` prefix around it. Returns the rebuilt term + the
/// binder's sort, or null if no forall is reachable (only `->`s / a non-quant leaf).
const OpenedForall = struct { body: TermId, sort: SortId };

fn openNextForall(prove: *Prove, id: TermId, pname: StrId) Error!?OpenedForall {
    // Descend the leading `->` chain to the first `forall`, opening it, then rewrap the `->`
    // prefix around the opened body. Iterative (was linear recursion + rebuild-unwind): collect
    // the implication LHSs on the way down, then fold them back over the opened body innermost-out.
    var prefix: std.ArrayList(TermId) = .empty; // implication LHSs, outer→inner
    defer prefix.deinit(prove.ctx.gpa);
    var cur = id;
    const opened: OpenedForall = while (true) {
        const node = prove.pool.get(cur);
        switch (node) {
            .quant => |q| {
                if (q.q != .forall) return null;
                const pf = try prove.pool.add(.{ .fvar = .{ .name = pname, .sort = q.sort } });
                break .{ .body = try prove.pool.open(q.body, pf), .sort = q.sort };
            },
            .bin => |bn| {
                if (bn.op != .implies) return null;
                try prefix.append(prove.ctx.gpa, bn.lhs);
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
        body = try prove.pool.add(.{ .bin = .{ .op = .implies, .lhs = prefix.items[i], .rhs = body } });
    }
    return .{ .body = body, .sort = opened.sort };
}
