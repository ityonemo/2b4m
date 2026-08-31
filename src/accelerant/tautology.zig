//! The `tautology` accelerant: closes a goal that is a propositional
//! consequence of its premises. The SMT engine (`smt_mod.tautology`) decides
//! validity; on `valid` the tactic first replays the truth search as ordinary
//! kernel steps (`tautologyCertificate` → `emitTautologyFrom`), staying
//! kernel-checked, and only falls back to the accelerated verdict when the
//! replay's step budget runs out. Split out of the elaborate monolith; the
//! shared propositional substrate (`emitTautologyFrom`, the `TautCert` struct)
//! stays as `pub` members on `Elaborator` — `ext` and the arithmetic mixed
//! certificate reuse them.

const elaborate = @import("../elaborate.zig");
const Elaborator = elaborate.Elaborator;
const Lowering = Elaborator.Lowering;
const ElabError = elaborate.ElabError;

const ast = @import("../ast.zig");
const kernel = @import("../kernel.zig");
const lexer = @import("../lexer.zig");
const term = @import("../term.zig");
const TermId = term.TermId;

const std = @import("std");
const smt_mod = @import("arithmetic/smt.zig");
const common = @import("_common.zig");

const TautCert = Elaborator.TautCert;

pub fn justify(self: *Elaborator, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const loc = c.rule.start;
    // DECIDE: the SMT engine settles validity (a real, cheap oracle — unlike the
    // certificate-total accelerants, which decide by building). This runs in every
    // mode and rejects a non-consequence with a countermodel.
    const premises = try self.resolvePremises(low, block_id, c, "tautology");
    const verdict = smt_mod.tautology(self.arena, self.pool, premises, goal) catch return error.OutOfMemory;
    switch (verdict) {
        .valid => {},
        .too_many_atoms => |n| {
            return self.fail(loc, "tautology: {d} distinct atoms exceeds the limit of {d}", .{ n, smt_mod.atom_limit });
        },
        .countermodel => |lits| {
            var msg: std.Io.Writer.Allocating = .init(self.arena);
            for (lits, 0..) |lit, i| {
                msg.writer.print("{s}{s} := {s}", .{
                    if (i > 0) ", " else "",
                    try self.renderTerm(lit.atom),
                    if (lit.value) "true" else "false",
                }) catch return error.OutOfMemory;
            }
            return self.fail(loc, "tautology: not a propositional consequence; countermodel: {s}", .{msg.written()});
        },
    }

    // valid. --fast: decide-only — taint, no certificate (the SMT verdict is
    // trusted). Skip generate entirely (its oracle already ran, above).
    if (!self.verify.certify_arithmetic) {
        const name = self.interner.internString("tautology") catch return error.OutOfMemory;
        try self.recordAccelerated(name, loc);
        return .{ .accelerated = name };
    }

    // strict: GENERATE the context-free synthetic theorem, closing every cited
    // ref as a premise (tautology routinely cites caller-local hypotheses). The
    // certificate replay is BUDGETED — a valid goal may still fail to certify
    // within budget, in which case generate returns null and we fall back to the
    // accelerated verdict (which, in strict mode, `recordAccelerated` rejects
    // with a "use --fast" error — the correct outcome for an uncertifiable goal).
    var body: TautBody = .{ .refs = c.refs, .loc = loc };
    if (try common.generate(self, low, block_id, loc, "tautology", goal, c.refs, &body)) |just| {
        return just;
    }
    const name = self.interner.internString("tautology") catch return error.OutOfMemory;
    try self.recordAccelerated(name, loc);
    return .{ .accelerated = name };
}

/// The body-emit for tautology's closure: replay the truth search as kernel
/// steps against the (fresh-eigenvar) goal. The closure has surfaced each cited
/// premise as a labeled `hypothesis` step in `low`; this resolves those labels
/// back into the `TautCert.Premise` list the replay consumes. Returns null when
/// the replay exceeds its step budget (the accelerant then falls back).
const TautBody = struct {
    refs: []const lexer.Token,
    loc: u32,
    pub fn emit(b: *TautBody, self: *Elaborator, low: *Lowering, block: kernel.BlockId, body_goal: TermId) ElabError!?kernel.Justification {
        const steps_mark = low.steps.items.len;
        const blocks_mark = low.blocks.items.len;
        // each ref now names a surfaced hypothesis step in this fresh Lowering.
        const premise_steps = try self.arena.alloc(TautCert.Premise, b.refs.len);
        for (b.refs, premise_steps) |ref, *out| {
            const name = try self.internTok(ref);
            const sid = low.labels.get(name).?.step; // surfaced by the closure
            out.* = .{
                .formula = low.steps.items[@intFromEnum(sid)].formula,
                .ref = .{ .id = sid, .loc = ref.start },
            };
        }
        return try self.emitTautologyFrom(low, block, body_goal, premise_steps, b.loc, steps_mark, blocks_mark);
    }
};

// The truth-search replay (`emitTautologyFrom`, a `pub` Elaborator method) emits
// ordinary kernel steps: each split atom gets an inline excluded-middle and an
// or_elim over the two assumption branches; leaves derive the goal structurally
// from the literal assumptions or explode a refuted premise with absurd. Every
// step is kernel-checked. A step budget bounds the exponential replay; past it
// it returns null and `TautBody.emit` propagates the decline.
