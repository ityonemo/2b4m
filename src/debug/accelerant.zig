//! `bpa debug accelerant <file> <line>` (or `<file> <theorem> <step-label>`):
//! reprint, AS VALID BPA SOURCE, the synthetic theorem an accelerant produced.
//!
//! In strict mode every `[by <tactic> …]` step wraps its certificate into a
//! kernel-checked synthetic theorem (`<tactic>$<n>`, suppressed from user counts;
//! see `src/accelerant/_common.zig`). That theorem's proof is a lowered
//! `kernel.Step`/`Block` chain — it has no surface AST. This module elaborates the
//! file (so the synthetics are created), finds the one whose source location is
//! the selected accelerant step, and renders its statement + proof back into the
//! `theorem … proof … qed` form a human would have written — so you can read
//! exactly what was kernel-checked (and, mangled name aside, paste it back).
//!
//! The kernel-proof → bpa-source renderer (`renderTheorem`) is the reusable core:
//! the same named-theorem-chain is the IR a Lean/Isabelle/Rocq export consumes.

const std = @import("std");
const Allocator = std.mem.Allocator;

const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");
const InternPool = @import("../InternPool.zig");
const term = @import("../term.zig");
const env = @import("../env.zig");
const kernel = @import("../kernel.zig");
const elaborate = @import("../elaborate.zig");
const print = @import("../print.zig");

const Env = env.Env;
const Pool = term.Pool;
const Interner = InternPool;
const StatementId = env.StatementId;
const root = @import("../root.zig");

pub const Result = struct {
    text: []const u8,
    ok: bool,
};

/// `selector`: a line number (`"15"`) OR a `<theorem> <step-label>` pair. Load the
/// file THROUGH THE MULTI-FILE LOADER (so imports resolve and synthetics — incl.
/// nested/recursive ones like a `model` materialization — are produced), locate
/// the accelerant step it names, and render the synthetic theorem that step
/// produced. `read_fn`/`std_root` are the same import-resolution hooks `check`
/// uses (the CLI passes its filesystem reader).
pub fn accelerant(
    arena: Allocator,
    path: []const u8,
    source: []const u8,
    selector: Selector,
    read_ctx: ?*anyopaque,
    read_fn: root.ReadFileFn,
    std_root: []const u8,
) Allocator.Error!Result {
    // parse the ROOT file separately for selector resolution (line/label -> the
    // accelerant step's byte offset); its AST is what the user is pointing at.
    const psink = try arena.create(diagnostics.Sink);
    psink.* = .init(arena);
    var p: parser.Parser = .init(arena, source, psink);
    const file = p.parseFile() catch return error.OutOfMemory;
    if (psink.list.items.len > 0) return renderDiagnostics(arena, path, source, psink);

    const target_offset = switch (selector) {
        .line => |ln| lineToStepOffset(source, file, ln) orelse
            return fail(arena, "no proof step on line {d}", .{ln}),
        .step => |s| stepLabelOffset(source, file, s.theorem, s.label) orelse
            return fail(arena, "no step '{s}' in theorem '{s}'", .{ s.label, s.theorem }),
    };

    // load + strict-elaborate the whole project (default Verify → synthetics
    // produced). A proof/resolution error surfaces as a diagnostic.
    const loaded = try root.loadProject(arena, path, source, read_ctx, read_fn, .{}, std_root);
    if (loaded.sink.list.items.len > 0) return renderDiagnostics(arena, path, source, loaded.sink);

    // find the synthetic theorem the accelerant produced at that step. Its `loc`
    // is the citing step's byte offset, and it belongs to the ROOT file.
    var found: ?StatementId = null;
    for (loaded.environment.statements.items, 0..) |stmt, i| {
        if (stmt != .theorem or !stmt.theorem.synthetic) continue;
        if (stmt.theorem.file == loaded.root_file and stmt.theorem.loc == target_offset) {
            found = @enumFromInt(i);
            break;
        }
    }
    const id = found orelse {
        // No synthetic — but if this is an `arithmetic … fallback(<thm>)` step, the
        // step is proved by CITING that manual theorem (the certifier chain
        // declined), not by an accelerant certificate. Say so, and name it, instead
        // of the generic "no accelerant" message.
        if (fallbackAt(file, target_offset)) |fb|
            return fail(arena, "proof by fallback: this `arithmetic` step is discharged by the manual theorem '{s}' (the certifiers declined), so there is no accelerant synthetic to reprint", .{tokenText(source, fb)});
        return fail(arena, "no accelerant produced a theorem there (is it a `[by <tactic> …]` step in strict mode?)", .{});
    };

    const text = try renderTheorem(arena, loaded.pool, loaded.environment, loaded.interner, id);
    return .{ .text = text, .ok = true };
}

pub const Selector = union(enum) {
    line: usize,
    step: struct { theorem: []const u8, label: []const u8 },
};

/// Render a (synthetic) theorem's statement + lowered kernel proof as bpa source:
/// `theorem <name>: <formula>\nproof\n  …\nqed\n`. The reusable IR renderer.
pub fn renderTheorem(arena: Allocator, pool: *Pool, environment: *Env, interner: *Interner, id: StatementId) Allocator.Error![]const u8 {
    const fact = environment.statements.items[@intFromEnum(id)].theorem;
    var out: std.Io.Writer.Allocating = .init(arena);
    const w = &out.writer;

    const name = displayName(arena, interner.stringBytes(fact.name));
    const formula = try print.render(arena, pool, environment, interner, fact.formula);
    w.print("theorem {s}: {s}\n", .{ name, formula }) catch return error.OutOfMemory;

    const proof = fact.proof orelse {
        w.writeAll("  // (proof not retained)\n") catch return error.OutOfMemory;
        return out.toOwnedSlice();
    };
    w.writeAll("proof\n") catch return error.OutOfMemory;

    var r: Renderer = .{ .arena = arena, .pool = pool, .env = environment, .interner = interner, .proof = proof };
    // Fresh, unique, LEGAL labels: the synthetic proof's own labels are
    // freshNamed (`simplify#9`, `assume#4`) that all trim to the same word and
    // collide — invalid as bpa. Reassign `s<n>` / `b<n>` in step/block order so
    // the reprint is paste-able.
    try r.assignLabels(arena);
    // render the root block's top-level steps (depth 1 = two-space indent).
    try r.renderBlockBody(w, @enumFromInt(0), 1);
    w.writeAll("qed\n") catch return error.OutOfMemory;
    return out.toOwnedSlice();
}

const Renderer = struct {
    arena: Allocator,
    pool: *Pool,
    env: *Env,
    interner: *Interner,
    proof: env.Statement.LoweredProof,
    /// StepId/BlockId (as usize) -> fresh legal label (`s1`, `b1`, …).
    step_labels: []const []const u8 = &.{},
    block_labels: []const []const u8 = &.{},

    fn assignLabels(self: *Renderer, arena: Allocator) Allocator.Error!void {
        const sl = try arena.alloc([]const u8, self.proof.steps.len);
        for (sl, 0..) |*out, i| out.* = try std.fmt.allocPrint(arena, "s{d}", .{i + 1});
        self.step_labels = sl;
        const bl = try arena.alloc([]const u8, self.proof.blocks.len);
        for (bl, 0..) |*out, i| out.* = try std.fmt.allocPrint(arena, "b{d}", .{i + 1});
        self.block_labels = bl;
    }

    /// Render the steps directly owned by `block` (those whose `.block` == block),
    /// each at `depth` indent; a step that OPENS a child block (fix/assume/unpack)
    /// renders the block header + recurses. Steps are stored flat and ordered.
    fn renderBlockBody(self: *Renderer, w: *std.Io.Writer, block: kernel.BlockId, depth: u32) Allocator.Error!void {
        const b = self.proof.blocks[@intFromEnum(block)];
        var i: u32 = b.first_step;
        while (i < b.last_step) : (i += 1) {
            const step = self.proof.steps[@intFromEnum(@as(kernel.StepId, @enumFromInt(i)))];
            if (@intFromEnum(step.block) != @intFromEnum(block)) continue; // owned by a nested block; rendered there
            try self.renderStep(w, @enumFromInt(i), depth);
        }
    }

    fn renderStep(self: *Renderer, w: *std.Io.Writer, sid: kernel.StepId, depth: u32) Allocator.Error!void {
        const step = self.proof.steps[@intFromEnum(sid)];
        const pad = try indent(self.arena, depth);
        const label = self.step_labels[@intFromEnum(sid)];
        const formula = try print.render(self.arena, self.pool, self.env, self.interner, step.formula);

        // a justification that references a block (fix/assume/unpack subproof)
        // renders the block INLINE (its header + body) then the closing rule.
        switch (step.just) {
            .forall_intro, .implies_intro, .exists_elim => |bref| {
                try self.renderBlock(w, bref.id, depth);
                w.print("{s}@{s} |\n{s}  {s}\n{s}  [by {s} {s}]\n", .{
                    pad, label, pad, formula, pad, ruleName(step.just), self.blockLabel(bref.id),
                }) catch return error.OutOfMemory;
                return;
            },
            .or_elim => |r| {
                try self.renderBlock(w, r.left.id, depth);
                try self.renderBlock(w, r.right.id, depth);
                w.print("{s}@{s} |\n{s}  {s}\n{s}  [by or_elim {s} {s} {s}]\n", .{
                    pad, label, pad, formula, pad,
                    self.stepLabel(r.disj.id), self.blockLabel(r.left.id), self.blockLabel(r.right.id),
                }) catch return error.OutOfMemory;
                return;
            },
            else => {},
        }

        const by = try self.renderJust(step.just);
        w.print("{s}@{s} |\n{s}  {s}\n{s}  [by {s}]\n", .{ pad, label, pad, formula, pad, by }) catch return error.OutOfMemory;
    }

    /// Render a subproof block: `fix x: S {` / `assume F {` / `unpack … {`,
    /// its body one level deeper, then the closing `}`.
    fn renderBlock(self: *Renderer, w: *std.Io.Writer, bid: kernel.BlockId, depth: u32) Allocator.Error!void {
        const b = self.proof.blocks[@intFromEnum(bid)];
        const pad = try indent(self.arena, depth);
        const header_label = self.block_labels[@intFromEnum(bid)];
        switch (b.kind) {
            .fix => |f| {
                const fv = f.v;
                const nm = displayName(self.arena, self.interner.stringBytes(fv.name));
                const sort = self.env.sortName(self.interner, fv.sort);
                w.print("{s}@{s} |\n{s}  fix {s}: {s} {{\n", .{ pad, header_label, pad, nm, sort }) catch return error.OutOfMemory;
            },
            .assume => |f| {
                const fs = try print.render(self.arena, self.pool, self.env, self.interner, f);
                w.print("{s}@{s} |\n{s}  assume {s} {{\n", .{ pad, header_label, pad, fs }) catch return error.OutOfMemory;
            },
            .unpack => |u| {
                const nm = displayName(self.arena, self.interner.stringBytes(u.v.name));
                const sort = self.env.sortName(self.interner, u.v.sort);
                w.print("{s}@{s} |\n{s}  unpack {s}: {s} from {s} {{\n", .{ pad, header_label, pad, nm, sort, self.stepLabel(u.source.id) }) catch return error.OutOfMemory;
            },
            .root => {},
        }
        try self.renderBlockBody(w, bid, depth + 1);
        w.print("{s}  }}\n", .{pad}) catch return error.OutOfMemory;
    }

    /// The `<rule> <refs>` body of a non-block-closing justification.
    fn renderJust(self: *Renderer, just: kernel.Justification) Allocator.Error![]const u8 {
        var out: std.Io.Writer.Allocating = .init(self.arena);
        const w = &out.writer;
        switch (just) {
            .reflexivity => w.writeAll("reflexivity") catch return error.OutOfMemory,
            .hypothesis => |b| w.print("hypothesis {s}", .{self.blockLabel(b.id)}) catch return error.OutOfMemory,
            .axiom_ref => |r| w.print("axiom {s}", .{self.statementName(r.stmt)}) catch return error.OutOfMemory,
            .theorem_ref => |r| w.print("theorem {s}", .{self.statementName(r.stmt)}) catch return error.OutOfMemory,
            .modus_ponens => |r| w.print("modus_ponens {s} {s}", .{ self.stepLabel(r.implication.id), self.stepLabel(r.antecedent.id) }) catch return error.OutOfMemory,
            .forall_elim => |r| {
                const arg = try print.render(self.arena, self.pool, self.env, self.interner, r.with);
                w.print("forall_elim({s}) {s}", .{ arg, self.stepLabel(r.step.id) }) catch return error.OutOfMemory;
            },
            .exists_intro => |r| {
                const wit = try print.render(self.arena, self.pool, self.env, self.interner, r.witness);
                w.print("exists_intro({s}) {s}", .{ wit, self.stepLabel(r.step.id) }) catch return error.OutOfMemory;
            },
            .and_intro => |r| w.print("and_intro {s} {s}", .{ self.stepLabel(r.left.id), self.stepLabel(r.right.id) }) catch return error.OutOfMemory,
            .and_elim_left => |s| w.print("and_elim_left {s}", .{self.stepLabel(s.id)}) catch return error.OutOfMemory,
            .and_elim_right => |s| w.print("and_elim_right {s}", .{self.stepLabel(s.id)}) catch return error.OutOfMemory,
            .or_intro_left => |s| w.print("or_intro_left {s}", .{self.stepLabel(s.id)}) catch return error.OutOfMemory,
            .or_intro_right => |s| w.print("or_intro_right {s}", .{self.stepLabel(s.id)}) catch return error.OutOfMemory,
            .not_intro => |r| w.print("not_intro {s} {s} {s}", .{ self.blockLabel(r.block.id), self.stepLabel(r.s1.id), self.stepLabel(r.s2.id) }) catch return error.OutOfMemory,
            .absurd => |r| w.print("absurd {s} {s}", .{ self.stepLabel(r.s1.id), self.stepLabel(r.s2.id) }) catch return error.OutOfMemory,
            .double_negation => |s| w.print("double_negation {s}", .{self.stepLabel(s.id)}) catch return error.OutOfMemory,
            .symmetry => |s| w.print("symmetry {s}", .{self.stepLabel(s.id)}) catch return error.OutOfMemory,
            .rewrite => |r| w.print("rewrite {s} {s}", .{ self.stepLabel(r.equation.id), self.stepLabel(r.target.id) }) catch return error.OutOfMemory,
            .iff_rewrite => |r| w.print("iff_rewrite {s} {s}", .{ self.stepLabel(r.biconditional.id), self.stepLabel(r.target.id) }) catch return error.OutOfMemory,
            .accelerated => |name| w.print("{s} /* accelerated */", .{self.interner.stringBytes(name)}) catch return error.OutOfMemory,
            .schema_instance => w.writeAll("instantiate /* schema */") catch return error.OutOfMemory,
            // block-closing rules are handled by renderStep, never reach here.
            .forall_intro, .implies_intro, .exists_elim, .or_elim => unreachable,
        }
        return out.toOwnedSlice();
    }

    fn stepLabel(self: *Renderer, sid: kernel.StepId) []const u8 {
        return self.step_labels[@intFromEnum(sid)];
    }
    fn blockLabel(self: *Renderer, bid: kernel.BlockId) []const u8 {
        return self.block_labels[@intFromEnum(bid)];
    }
    fn statementName(self: *Renderer, id: StatementId) []const u8 {
        return switch (self.env.statements.items[@intFromEnum(id)]) {
            .axiom => |f| self.interner.stringBytes(f.name),
            .theorem => |f| displayName(self.arena, self.interner.stringBytes(f.name)),
            .schema => |s| self.interner.stringBytes(s.name),
        };
    }
};

fn ruleName(just: kernel.Justification) []const u8 {
    return switch (just) {
        .forall_intro => "forall_intro",
        .implies_intro => "implies_intro",
        .exists_elim => "exists_elim",
        else => unreachable,
    };
}

/// Two spaces per depth level.
fn indent(arena: Allocator, depth: u32) Allocator.Error![]const u8 {
    const buf = try arena.alloc(u8, depth * 2);
    @memset(buf, ' ');
    return buf;
}

/// A synthetic/eigenvariable name carries a disambiguating suffix (`$`/`#`) that
/// is not a legal identifier char; trim it so the reprint reads as bpa. (`#` from
/// eigenvariable disambiguation, `$` from accelerant mangling.)
fn displayName(arena: Allocator, name: []const u8) []const u8 {
    _ = arena;
    var end = name.len;
    if (std.mem.indexOfScalar(u8, name, '#')) |i| end = @min(end, i);
    if (std.mem.indexOfScalar(u8, name, '$')) |i| end = @min(end, i);
    return name[0..end];
}

// --- selector resolution -------------------------------------------------

/// The byte offset of the first `[by <tactic> …]`-carrying step whose CLAIM sits
/// on `line` (1-based). Walks the AST proofs; returns the step's rule token start
/// (matching the accelerant's `loc = c.rule.start`).
fn lineToStepOffset(source: []const u8, file: ast.File, line: usize) ?u32 {
    var best: ?u32 = null;
    for (file.decls) |*d| {
        const steps = declSteps(d) orelse continue;
        walkStepsForLine(source, steps, line, &best);
    }
    return best;
}

fn walkStepsForLine(source: []const u8, steps: []const ast.Step, line: usize, best: *?u32) void {
    for (steps) |*s| switch (s.body) {
        .claim => |c| {
            // a step spans its label line through its `[by …]` rule line; match
            // if the target line falls anywhere in that span (the user may point
            // at the label, the formula, or the justification).
            const first = offsetLine(source, s.label.start);
            const last = offsetLine(source, c.rule.start);
            if (line >= first and line <= last) {
                if (best.* == null or c.rule.start < best.*.?) best.* = c.rule.start;
            }
        },
        .assume => |blk| walkStepsForLine(source, blk.steps, line, best),
        .fix => |blk| walkStepsForLine(source, blk.steps, line, best),
        .unpack => |blk| walkStepsForLine(source, blk.steps, line, best),
        .case => |blk| for (blk.arms) |arm| walkStepsForLine(source, arm.steps, line, best),
    };
}

fn stepLabelOffset(source: []const u8, file: ast.File, theorem: []const u8, label: []const u8) ?u32 {
    for (file.decls) |*d| {
        const nm = declName(source, d) orelse continue;
        if (!std.mem.eql(u8, nm, theorem)) continue;
        const steps = declSteps(d) orelse return null;
        return findLabel(source, steps, label);
    }
    return null;
}

/// The `fallback(<thm>)` token of the claim step at `offset` (its `[by …]` rule
/// start), if that step carries one — else null. Walks nested blocks.
fn fallbackAt(file: ast.File, offset: u32) ?lexer.Token {
    for (file.decls) |*d| {
        const steps = declSteps(d) orelse continue;
        if (fallbackInSteps(steps, offset)) |fb| return fb;
    }
    return null;
}

fn fallbackInSteps(steps: []const ast.Step, offset: u32) ?lexer.Token {
    for (steps) |*s| {
        switch (s.body) {
            .claim => |c| if (c.rule.start == offset) return c.fallback,
            .assume => |blk| if (fallbackInSteps(blk.steps, offset)) |fb| return fb,
            .fix => |blk| if (fallbackInSteps(blk.steps, offset)) |fb| return fb,
            .unpack => |blk| if (fallbackInSteps(blk.steps, offset)) |fb| return fb,
            .case => |blk| for (blk.arms) |arm| {
                if (fallbackInSteps(arm.steps, offset)) |fb| return fb;
            },
        }
    }
    return null;
}

fn findLabel(source: []const u8, steps: []const ast.Step, label: []const u8) ?u32 {
    for (steps) |*s| {
        if (std.mem.eql(u8, tokenText(source, s.label), label)) {
            switch (s.body) {
                .claim => |c| return c.rule.start,
                else => return null, // a block-opening label has no single tactic
            }
        }
        const inner: ?u32 = switch (s.body) {
            .claim => null,
            .assume => |blk| findLabel(source, blk.steps, label),
            .fix => |blk| findLabel(source, blk.steps, label),
            .unpack => |blk| findLabel(source, blk.steps, label),
            .case => |blk| blk: {
                for (blk.arms) |arm| if (findLabel(source, arm.steps, label)) |o| break :blk o;
                break :blk null;
            },
        };
        if (inner) |o| return o;
    }
    return null;
}

fn declSteps(d: *const ast.Decl) ?[]const ast.Step {
    return switch (d.*) {
        .theorem => |t| t.steps,
        .schema => |s| s.steps, // proof-carrying schema (null if axiom-schema)
        else => null,
    };
}

fn declName(source: []const u8, d: *const ast.Decl) ?[]const u8 {
    return switch (d.*) {
        .theorem => |t| tokenText(source, t.name),
        .schema => |s| tokenText(source, s.name),
        else => null,
    };
}

fn offsetLine(source: []const u8, offset: u32) usize {
    var line: usize = 1;
    for (source[0..@min(offset, source.len)]) |ch| {
        if (ch == '\n') line += 1;
    }
    return line;
}

fn tokenText(source: []const u8, t: anytype) []const u8 {
    return source[t.start..t.end];
}

fn renderDiagnostics(arena: Allocator, path: []const u8, source: []const u8, sink: *diagnostics.Sink) Allocator.Error!Result {
    var out: std.Io.Writer.Allocating = .init(arena);
    const files = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
    sink.render(&out.writer, &files) catch return error.OutOfMemory;
    return .{ .text = try out.toOwnedSlice(), .ok = false };
}

fn fail(arena: Allocator, comptime fmt: []const u8, args: anytype) Allocator.Error!Result {
    const msg = std.fmt.allocPrint(arena, "error: " ++ fmt ++ "\n", args) catch return error.OutOfMemory;
    return .{ .text = msg, .ok = false };
}
