//! The demand PROVER — a fresh, smaller sibling of `elaborate.zig`'s `Elaborator`
//! that checks ONE theorem's proof and nothing else. It is a HAND-PORT of the
//! Elaborator's PURE-KERNEL subset: proof lowering (surface AST steps -> kernel
//! steps/blocks), kernel check, and use-all-facts reachability. Every accelerant /
//! schema `instantiate` / `model` code path is deliberately DROPPED — a proof that
//! reaches for one hard-errors ("unsupported by the demand prover"). This is the
//! risky slice the ProveTask will eventually drive; it lives apart so the eager
//! Elaborator (which 15 accelerant files depend on) stays untouched.
//!
//! HARD INVARIANT: a `Prover` carries ZERO per-file mutable state. It holds the
//! shared world (interner/pool/env/sink), immutable per-proof config (source/file/
//! trusted/verify/theory_file), and per-proof MUTABLE state that is reset per proof.
//! There is no `models`/`forwards`/`schema_args`/`instantiating` — those belong to
//! whole-file elaboration and schema/model machinery, which this prover does not do.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const term = @import("../../term.zig");
const SortId = term.SortId;
const TermId = term.TermId;
const env_mod = @import("../../env.zig");
const Env = env_mod.Env;
const FileId = env_mod.FileId;
const Symbol = env_mod.Symbol;
const Statement = env_mod.Statement;
const Diagnostics = @import("../../diagnostics.zig");
const kernel = @import("../../kernel.zig");
const print = @import("../../print.zig");
const elaborate = @import("../../elaborate.zig");

/// reuse the Elaborator's public types (identity, not a copy)
pub const Verify = elaborate.Verify;
pub const StatementId = elaborate.StatementId;
pub const ElabError = elaborate.ElabError;

const Prover = @This();

// -- shared world --------------------------------------------------------------
arena: Allocator,
interner: *InternPool,
pool: *term.Pool,
env: *Env,
sink: *Diagnostics.Sink,

// -- immutable per-proof config ------------------------------------------------
/// the file's source: the proof's AST tokens index into it (needed by `text`).
/// Per-proof immutable, not per-file mutable state — set once at construction.
source: []const u8,
/// the file being proved in: all unqualified names resolve in its scope
file: FileId,
/// trusted mode: obligations are not owed (imported, unchecked bodies).
trusted: bool = false,
/// which layers to verify (see `Verify`).
verify: Verify = .{},
/// the scope well-known names resolve in; null means local (`self.file`).
theory_file: ?FileId = null,

// -- per-proof MUTABLE state (reset per `prove`) -------------------------------
/// innermost binding last: quantifier binders, proof vars.
scope: std.ArrayList(ScopeEntry) = .empty,
/// proof obligations (TCCs) from guarded-function applications.
pending_tccs: std.ArrayList(Tcc) = .empty,
/// RESULT POSTCONDITIONS surfaced by predicated-result funcs.
result_facts: std.ArrayList(TermId) = .empty,
/// generator for hygienic binder fvar names ('#' cannot lex).
fresh_counter: u32 = 0,
/// USE-ALL-FACTS extra reachability roots (TCC dischargers).
extra_reachable_steps: std.ArrayList(u32) = .empty,
/// accelerated-tactic names the proof leaned on (only via cited facts; a
/// direct accelerant is unsupported here).
accelerated_used: std.ArrayList(StrId) = .empty,
/// hole names the proof rests on (cited facts).
holes_used: std.ArrayList(StrId) = .empty,
/// PREDICATED fix/unpack blocks -> injected guard-assume block.
fix_guard_block: std.AutoHashMapUnmanaged(kernel.BlockId, kernel.BlockId) = .empty,

const Tcc = struct { formula: TermId, loc: u32 };

const ScopeEntry = struct {
    name: StrId,
    sort: SortId,
    fvar: StrId,
};

const Typed = struct { id: TermId, sort: SortId };

pub const Lowering = struct {
    steps: std.ArrayList(kernel.Step) = .empty,
    blocks: std.ArrayList(kernel.Block) = .empty,
    labels: std.AutoHashMapUnmanaged(StrId, LabelTarget) = .empty,

    const LabelTarget = union(enum) { step: kernel.StepId, block: kernel.BlockId };
};

pub fn init(
    arena: Allocator,
    source: []const u8,
    interner: *InternPool,
    pool: *term.Pool,
    environment: *Env,
    sink: *Diagnostics.Sink,
    file: FileId,
) Prover {
    return .{
        .arena = arena,
        .source = source,
        .interner = interner,
        .pool = pool,
        .env = environment,
        .sink = sink,
        .file = file,
    };
}

// -- small utilities -----------------------------------------------------------

pub fn text(self: *const Prover, tok: lexer.Token) []const u8 {
    return self.source[tok.start..tok.end];
}

pub fn internTok(self: *Prover, tok: lexer.Token) !StrId {
    return self.interner.internString(self.text(tok));
}

pub fn fail(self: *Prover, offset: u32, comptime fmt: []const u8, args: anytype) ElabError {
    self.sink.add(offset, fmt, args) catch return error.OutOfMemory;
    return error.Recover;
}

fn sortName(self: *const Prover, id: SortId) []const u8 {
    return self.env.sortName(self.interner, id);
}

pub fn theoryScope(self: *const Prover) FileId {
    return self.theory_file orelse self.file;
}

pub fn renderTerm(self: *Prover, id: TermId) ElabError![]const u8 {
    return print.render(self.arena, self.pool, self.env, self.interner, id) catch return error.OutOfMemory;
}

fn freshName(self: *Prover) ElabError!StrId {
    return self.freshNamed("b");
}

pub fn freshNamed(self: *Prover, prefix: []const u8) ElabError!StrId {
    self.fresh_counter += 1;
    const s = std.fmt.allocPrint(self.arena, "{s}#{d}", .{ prefix, self.fresh_counter }) catch return error.OutOfMemory;
    return self.interner.internString(s) catch error.OutOfMemory;
}

pub fn exprLoc(e: *const ast.Expr) u32 {
    return switch (e.*) {
        .name => |t| t.start,
        .call => |c| c.callee.start,
        .binary => |b| exprLoc(b.lhs),
        .not => |n| n.tok.start,
        .quant => |q| q.tok.start,
        .lambda => |l| l.tok.start,
    };
}

pub fn inheritAccelerated(self: *Prover, names: []const StrId) Allocator.Error!void {
    outer: for (names) |name| {
        for (self.accelerated_used.items) |o| {
            if (o == name) continue :outer;
        }
        try self.accelerated_used.append(self.arena, name);
    }
}

pub fn inheritHoles(self: *Prover, names: []const StrId) Allocator.Error!void {
    outer: for (names) |name| {
        for (self.holes_used.items) |o| {
            if (o == name) continue :outer;
        }
        try self.holes_used.append(self.arena, name);
    }
}

// -- entry point ---------------------------------------------------------------

/// Lower and kernel-check `steps` proving `goal`. Returns true iff proven (and
/// no dead steps unless --draft). Resets all per-proof mutable state up front so
/// one Prover can prove several theorems in sequence. A lowering error records a
/// diagnostic and yields false.
pub fn prove(self: *Prover, steps: []const ast.Step, goal: TermId, goal_loc: u32) Allocator.Error!bool {
    // per-proof state reset (a Prover holds no per-file state, so this is the
    // whole reset — no models/forwards/schema tables to clear).
    self.scope.clearRetainingCapacity();
    self.pending_tccs.clearRetainingCapacity();
    self.result_facts.clearRetainingCapacity();
    self.extra_reachable_steps.clearRetainingCapacity();
    self.accelerated_used.clearRetainingCapacity();
    self.holes_used.clearRetainingCapacity();
    self.fix_guard_block.clearRetainingCapacity();
    self.fresh_counter = 0;

    var low: Lowering = .{};
    const root_label = try self.interner.internString("proof");
    try low.blocks.append(self.arena, .{
        .parent = null,
        .label = root_label,
        .kind = .root,
        .first_step = 0,
        .last_step = 0,
    });
    self.lowerSteps(&low, steps, @enumFromInt(0)) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Recover => return false,
    };
    low.blocks.items[0].last_step = @intCast(low.steps.items.len);

    var k: kernel.Kernel = .{
        .arena = self.arena,
        .pool = self.pool,
        .env = self.env,
        .interner = self.interner,
        .sink = self.sink,
    };
    const proven = try k.check(
        .{ .steps = low.steps.items, .blocks = low.blocks.items },
        goal,
        goal_loc,
    );
    if (!proven) return false;
    if (!self.verify.draft) {
        if (try self.checkAllStepsUsed(low.steps.items, low.blocks.items) == false) return false;
    }
    return true;
}

// -- use-all-facts reachability ------------------------------------------------

fn checkAllStepsUsed(self: *Prover, steps: []const kernel.Step, blocks: []const kernel.Block) Allocator.Error!bool {
    if (steps.len == 0) return true;
    const reached = try self.arena.alloc(bool, steps.len);
    @memset(reached, false);
    const lastStepOf = struct {
        fn f(bs: []const kernel.Block, b: kernel.BlockId) ?u32 {
            const blk = bs[@intFromEnum(b)];
            if (blk.last_step > blk.first_step) return blk.last_step - 1;
            return null;
        }
    }.f;
    var seed: ?u32 = null;
    {
        var it: usize = steps.len;
        while (it > 0) {
            it -= 1;
            if (@intFromEnum(steps[it].block) == 0) {
                seed = @intCast(it);
                break;
            }
        }
    }
    const start = seed orelse return true;
    var work: std.ArrayList(u32) = .empty;
    try work.append(self.arena, start);
    reached[start] = true;
    for (self.extra_reachable_steps.items) |di| try mark(reached, &work, self.arena, di);
    while (work.pop()) |si| {
        {
            var b: ?kernel.BlockId = steps[si].block;
            while (b) |bid| {
                const blk = blocks[@intFromEnum(bid)];
                if (blk.kind == .unpack) try mark(reached, &work, self.arena, @intFromEnum(blk.kind.unpack.source.id));
                b = blk.parent;
            }
        }
        const j = steps[si].just;
        switch (j) {
            .modus_ponens => |r| {
                try mark(reached, &work, self.arena, @intFromEnum(r.implication.id));
                try mark(reached, &work, self.arena, @intFromEnum(r.antecedent.id));
            },
            .forall_elim => |r| try mark(reached, &work, self.arena, @intFromEnum(r.step.id)),
            .exists_intro => |r| try mark(reached, &work, self.arena, @intFromEnum(r.step.id)),
            .and_intro => |r| {
                try mark(reached, &work, self.arena, @intFromEnum(r.left.id));
                try mark(reached, &work, self.arena, @intFromEnum(r.right.id));
            },
            .and_elim_left, .and_elim_right, .or_intro_left, .or_intro_right, .double_negation, .symmetry => |sr| try mark(reached, &work, self.arena, @intFromEnum(sr.id)),
            .rewrite => |r| {
                try mark(reached, &work, self.arena, @intFromEnum(r.equation.id));
                try mark(reached, &work, self.arena, @intFromEnum(r.target.id));
            },
            .iff_rewrite => |r| {
                try mark(reached, &work, self.arena, @intFromEnum(r.biconditional.id));
                try mark(reached, &work, self.arena, @intFromEnum(r.target.id));
            },
            .absurd => |r| {
                try mark(reached, &work, self.arena, @intFromEnum(r.s1.id));
                try mark(reached, &work, self.arena, @intFromEnum(r.s2.id));
            },
            .not_intro => |r| {
                if (lastStepOf(blocks, r.block.id)) |ls| try mark(reached, &work, self.arena, ls);
                try mark(reached, &work, self.arena, @intFromEnum(r.s1.id));
                try mark(reached, &work, self.arena, @intFromEnum(r.s2.id));
            },
            .or_elim => |r| {
                try mark(reached, &work, self.arena, @intFromEnum(r.disj.id));
                if (lastStepOf(blocks, r.left.id)) |ls| try mark(reached, &work, self.arena, ls);
                if (lastStepOf(blocks, r.right.id)) |ls| try mark(reached, &work, self.arena, ls);
            },
            .implies_intro, .forall_intro, .exists_elim => |b| {
                if (lastStepOf(blocks, b.id)) |ls| try mark(reached, &work, self.arena, ls);
            },
            .hypothesis => {},
            .schema_instance => |r| for (r.premises) |p| try mark(reached, &work, self.arena, @intFromEnum(p.id)),
            .axiom_ref, .theorem_ref, .reflexivity, .accelerated => {},
        }
    }
    var any_dead = false;
    for (steps, 0..) |s, i| {
        if (reached[i]) continue;
        const label = self.interner.stringBytes(s.label);
        if (std.mem.indexOfScalar(u8, label, '#') != null) continue; // synthetic
        self.sink.add(s.loc, "unused fact: step '{s}' is never used — no later step or the conclusion cites it (a proof must use every fact it introduces; use --draft while filling in a proof)", .{label}) catch return error.OutOfMemory;
        any_dead = true;
    }
    return !any_dead;
}

fn mark(reached: []bool, work: *std.ArrayList(u32), arena: Allocator, id: u32) Allocator.Error!void {
    if (id >= reached.len or reached[id]) return;
    reached[id] = true;
    try work.append(arena, id);
}

// -- lowering driver -----------------------------------------------------------

const WorkItem = union(enum) {
    lower_step: struct { step: *const ast.Step, block_id: kernel.BlockId },
    exit_block: struct { block_id: kernel.BlockId, pop_scope: bool },
};

fn lowerSteps(self: *Prover, low: *Lowering, steps: []const ast.Step, block_id: kernel.BlockId) ElabError!void {
    var stack: std.ArrayList(WorkItem) = .empty;
    try self.pushBlockBody(low, &stack, steps, block_id);
    while (stack.pop()) |item| {
        switch (item) {
            .exit_block => |e| {
                self.closeBlock(low, e.block_id);
                if (e.pop_scope) _ = self.scope.pop();
            },
            .lower_step => |ls| try self.driveOneStep(low, &stack, ls.step, ls.block_id),
        }
    }
}

fn pushBlockBody(self: *Prover, low: *Lowering, stack: *std.ArrayList(WorkItem), steps: []const ast.Step, block_id: kernel.BlockId) ElabError!void {
    var index_of: std.AutoHashMapUnmanaged(StrId, usize) = .empty;
    for (steps, 0..) |*s, i| {
        const label = try self.internTok(s.label);
        if (self.labelInScope(low, label, block_id)) {
            return self.fail(s.label.start, "label '{s}' shadows an enclosing label; choose a fresh name", .{self.text(s.label)});
        }
        const gop = index_of.getOrPut(self.arena, label) catch return error.OutOfMemory;
        if (gop.found_existing) {
            return self.fail(s.label.start, "duplicate label '{s}'", .{self.text(s.label)});
        }
        gop.value_ptr.* = i;
    }
    const order = try self.topoSortSteps(steps, index_of);
    var i = order.len;
    while (i > 0) {
        i -= 1;
        try stack.append(self.arena, .{ .lower_step = .{ .step = &steps[order[i]], .block_id = block_id } });
    }
}

fn labelInScope(self: *Prover, low: *const Lowering, label: StrId, block_id: kernel.BlockId) bool {
    _ = self;
    const target = low.labels.get(label) orelse return false;
    const home: ?kernel.BlockId = switch (target) {
        .step => |id| low.steps.items[@intFromEnum(id)].block,
        .block => |id| low.blocks.items[@intFromEnum(id)].parent,
    };
    var cur: ?kernel.BlockId = block_id;
    while (cur) |c| {
        if (home == c) return true;
        cur = low.blocks.items[@intFromEnum(c)].parent;
    }
    return false;
}

fn stepSiblingDeps(step: *const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize), interner: *InternPool, source: []const u8, out: *std.ArrayList(usize), arena: Allocator) !void {
    const tok = struct {
        fn ref(t: lexer.Token, idx: std.AutoHashMapUnmanaged(StrId, usize), in: *InternPool, src: []const u8, o: *std.ArrayList(usize), a: Allocator) !void {
            const name = in.internString(src[t.start..t.end]) catch return error.OutOfMemory;
            if (idx.get(name)) |dep| try o.append(a, dep);
        }
    };
    switch (step.body) {
        .claim => |c| for (c.refs) |r| try tok.ref(r, index_of, interner, source, out, arena),
        .unpack => |blk| try tok.ref(blk.from, index_of, interner, source, out, arena),
        .case => |c| try tok.ref(c.disj, index_of, interner, source, out, arena),
        .assume, .fix => {},
    }
}

fn topoSortSteps(self: *Prover, steps: []const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize)) ElabError![]const usize {
    const n = steps.len;
    const deps = try self.arena.alloc([]const usize, n);
    const remaining = try self.arena.alloc(usize, n);
    for (steps, 0..) |*s, i| {
        var d: std.ArrayList(usize) = .empty;
        try stepSiblingDeps(s, index_of, self.interner, self.source, &d, self.arena);
        deps[i] = d.items;
        remaining[i] = d.items.len;
    }
    var order: std.ArrayList(usize) = .empty;
    var emitted = try self.arena.alloc(bool, n);
    @memset(emitted, false);
    while (order.items.len < n) {
        var progressed = false;
        for (0..n) |i| {
            if (emitted[i] or remaining[i] != 0) continue;
            emitted[i] = true;
            try order.append(self.arena, i);
            for (0..n) |jj| {
                if (emitted[jj]) continue;
                for (deps[jj]) |dj| {
                    if (dj == i) remaining[jj] -= 1;
                }
            }
            progressed = true;
            break;
        }
        if (!progressed) return self.reportCycle(steps, deps, emitted);
    }
    return order.items;
}

fn reportCycle(self: *Prover, steps: []const ast.Step, deps: []const []const usize, emitted: []const bool) ElabError {
    var start: usize = 0;
    while (start < steps.len and emitted[start]) start += 1;
    var path: std.ArrayList(usize) = .empty;
    var on_path = self.arena.alloc(bool, steps.len) catch return error.OutOfMemory;
    @memset(on_path, false);
    var cur = start;
    while (!on_path[cur]) {
        on_path[cur] = true;
        path.append(self.arena, cur) catch return error.OutOfMemory;
        var next: ?usize = null;
        for (deps[cur]) |d| {
            if (!emitted[d]) {
                next = d;
                break;
            }
        }
        cur = next orelse break;
    }
    var msg: std.Io.Writer.Allocating = .init(self.arena);
    var started = false;
    for (path.items) |i| {
        if (!started and i != cur) continue;
        started = true;
        msg.writer.print("{s} -> ", .{self.text(steps[i].label)}) catch return error.OutOfMemory;
    }
    msg.writer.print("{s}", .{self.text(steps[cur].label)}) catch return error.OutOfMemory;
    return self.fail(steps[cur].label.start, "cyclic justification: {s}", .{msg.written()});
}

fn driveOneStep(self: *Prover, low: *Lowering, stack: *std.ArrayList(WorkItem), s: *const ast.Step, block_id: kernel.BlockId) ElabError!void {
    const label = try self.internTok(s.label);
    switch (s.body) {
        .assume => |blk| {
            const tcc_start = self.pending_tccs.items.len;
            const f = try self.requireProp(try self.elaborateExpr(blk.formula), blk.formula);
            try self.dischargeTccs(low, block_id, tcc_start);
            const b = try self.newBlock(low, label, block_id, .{ .assume = f.id });
            low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
            try stack.append(self.arena, .{ .exit_block = .{ .block_id = b, .pop_scope = false } });
            try self.pushBlockBody(low, stack, blk.steps, b);
        },
        .fix => |blk| {
            const v = try self.bindProofVar(blk.name, blk.sort);
            const guard = try self.fixGuard(blk.sort, v);
            const b = try self.newBlock(low, label, block_id, .{ .fix = .{ .v = v, .guard = guard } });
            low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
            try stack.append(self.arena, .{ .exit_block = .{ .block_id = b, .pop_scope = true } });
            try self.pushBlockBody(low, stack, blk.steps, b);
        },
        .unpack => |blk| {
            const source = try self.resolveStepRef(low, blk.from);
            const v = try self.bindProofVar(blk.name, blk.sort);
            const b = try self.newBlock(low, label, block_id, .{ .unpack = .{ .v = v, .source = source } });
            low.labels.put(self.arena, label, .{ .block = b }) catch return error.OutOfMemory;
            try stack.append(self.arena, .{ .exit_block = .{ .block_id = b, .pop_scope = true } });
            try self.pushBlockBody(low, stack, blk.steps, b);
        },
        .claim => |c| {
            const tcc_start = self.pending_tccs.items.len;
            const f = try self.requireProp(try self.elaborateExpr(c.formula), c.formula);
            const just = try self.lowerJustification(low, block_id, f.id, c);
            try self.dischargeTccs(low, block_id, tcc_start);
            low.labels.put(self.arena, label, .{ .step = @enumFromInt(low.steps.items.len) }) catch return error.OutOfMemory;
            try low.steps.append(self.arena, .{
                .formula = f.id,
                .just = just,
                .block = block_id,
                .label = label,
                .loc = s.label.start,
            });
        },
        .case => |c| try self.lowerCase(low, s, block_id, label, c),
    }
}

fn lowerCase(self: *Prover, low: *Lowering, s: *const ast.Step, block_id: kernel.BlockId, label: StrId, c: ast.Step.CaseBlock) ElabError!void {
    const loc = s.label.start;
    const goal_tcc = self.pending_tccs.items.len;
    const goal = try self.requireProp(try self.elaborateExpr(c.goal), c.goal);
    try self.dischargeTccs(low, block_id, goal_tcc);
    const disj = try self.resolveStepRef(low, c.disj);
    const just = try self.emitCaseTree(low, block_id, loc, disj, c.arms, goal.id);
    low.labels.put(self.arena, label, .{ .step = @enumFromInt(low.steps.items.len) }) catch return error.OutOfMemory;
    try low.steps.append(self.arena, .{ .formula = goal.id, .just = just, .block = block_id, .label = label, .loc = loc });
}

fn emitArmBlock(self: *Prover, low: *Lowering, parent: kernel.BlockId, arm: ast.Step.CaseBlock.Arm, expected: TermId) ElabError!kernel.BlockId {
    const f = try self.requireProp(try self.elaborateExpr(arm.assumption), arm.assumption);
    if (!self.pool.alphaEq(f.id, expected)) {
        return self.fail(exprLoc(arm.assumption), "case arm assumes '{s}', but the disjunct here is '{s}'", .{
            try self.renderTerm(f.id), try self.renderTerm(expected),
        });
    }
    const b = try self.newBlock(low, try self.internTok(arm.label), parent, .{ .assume = f.id });
    low.labels.put(self.arena, try self.internTok(arm.label), .{ .block = b }) catch return error.OutOfMemory;
    try self.lowerSteps(low, arm.steps, b);
    self.closeBlock(low, b);
    return b;
}

fn emitCaseTree(self: *Prover, low: *Lowering, parent: kernel.BlockId, loc: u32, disj: kernel.SRef, arms: []const ast.Step.CaseBlock.Arm, goal: TermId) ElabError!kernel.Justification {
    const disj_formula = low.steps.items[@intFromEnum(disj.id)].formula;
    const node = self.pool.get(disj_formula);
    if (node != .bin or node.bin.op != .or_op) {
        return self.fail(loc, "case: 'on' step is '{s}', not a disjunction", .{try self.renderTerm(disj_formula)});
    }
    if (arms.len < 2) {
        return self.fail(loc, "case over a disjunction needs at least two arms", .{});
    }
    const right_block = try self.emitArmBlock(low, parent, arms[arms.len - 1], node.bin.rhs);
    const left_block = if (arms.len == 2)
        try self.emitArmBlock(low, parent, arms[0], node.bin.lhs)
    else blk: {
        const lb = try self.newBlock(low, try self.freshNamed("case"), parent, .{ .assume = node.bin.lhs });
        const hyp = try self.emitStep(low, lb, loc, node.bin.lhs, .{ .hypothesis = .{ .id = lb, .loc = loc } });
        const inner = try self.emitCaseTree(low, lb, loc, hyp, arms[0 .. arms.len - 1], goal);
        _ = try self.emitStep(low, lb, loc, goal, inner);
        self.closeBlock(low, lb);
        break :blk lb;
    };
    return .{ .or_elim = .{
        .disj = disj,
        .left = .{ .id = left_block, .loc = loc },
        .right = .{ .id = right_block, .loc = loc },
    } };
}

pub fn newBlock(self: *Prover, low: *Lowering, label: StrId, parent: kernel.BlockId, kind: kernel.Block.Kind) ElabError!kernel.BlockId {
    const id: kernel.BlockId = @enumFromInt(low.blocks.items.len);
    try low.blocks.append(self.arena, .{
        .parent = parent,
        .label = label,
        .kind = kind,
        .first_step = @intCast(low.steps.items.len),
        .last_step = 0,
    });
    return id;
}

pub fn closeBlock(self: *Prover, low: *Lowering, id: kernel.BlockId) void {
    _ = self;
    const blk = &low.blocks.items[@intFromEnum(id)];
    blk.last_step = @intCast(low.steps.items.len);
    if (std.debug.runtime_safety) {
        const self_idx = @intFromEnum(id);
        var i: usize = blk.first_step;
        while (i < blk.last_step) : (i += 1) {
            var bi = @intFromEnum(low.steps.items[i].block);
            while (bi > self_idx) {
                bi = @intFromEnum(low.blocks.items[bi].parent.?);
            }
            std.debug.assert(bi == self_idx);
        }
    }
}

fn bindProofVar(self: *Prover, name_tok: lexer.Token, sort_tok: lexer.Token) ElabError!term.Node.Fvar {
    const name = try self.internTok(name_tok);
    for (self.scope.items) |entry| {
        if (entry.name == name) {
            return self.fail(name_tok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(name_tok)});
        }
    }
    if (self.env.findSym(self.file, name) != null) {
        return self.fail(name_tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(name_tok)});
    }
    const sort = self.env.carrierOf(try self.resolveSort(sort_tok));
    const fvar = try self.freshNamed(self.text(name_tok));
    try self.scope.append(self.arena, .{ .name = name, .sort = sort, .fvar = fvar });
    return .{ .name = fvar, .sort = sort };
}

// -- reference resolution ------------------------------------------------------

pub fn resolveStepRef(self: *Prover, low: *Lowering, tok: lexer.Token) ElabError!kernel.SRef {
    const name = try self.internTok(tok);
    const target = low.labels.get(name) orelse {
        const name_text = self.text(tok);
        if (self.statementByName(name)) |stmt| {
            const desc: []const u8, const intro: []const u8 = switch (stmt) {
                .axiom => .{ "an axiom", "axiom" },
                .theorem => .{ "a theorem", "theorem" },
                .schema => .{ "a schema", "instantiate" },
            };
            return self.fail(tok.start, "'{s}' is {s}, not a proof step; introduce it as a step first with `[by {s} {s}]`, then reference that step", .{
                name_text, desc, intro, name_text,
            });
        }
        return self.fail(tok.start, "unknown reference '{s}'", .{name_text});
    };
    return switch (target) {
        .step => |id| .{ .id = id, .loc = tok.start },
        .block => self.fail(tok.start, "'{s}' names a subproof; a step reference is required", .{self.text(tok)}),
    };
}

fn statementByName(self: *Prover, name: StrId) ?Statement {
    const id = self.env.findStatementId(self.theoryScope(), name) orelse
        self.env.findStatementId(self.file, name) orelse return null;
    return self.env.statements.items[@intFromEnum(id)];
}

fn resolveBlockRef(self: *Prover, low: *Lowering, tok: lexer.Token) ElabError!kernel.BRef {
    const name = try self.internTok(tok);
    const target = low.labels.get(name) orelse {
        return self.fail(tok.start, "unknown reference '{s}'", .{self.text(tok)});
    };
    return switch (target) {
        .block => |id| .{ .id = id, .loc = tok.start },
        .step => self.fail(tok.start, "'{s}' names a step; a subproof reference is required", .{self.text(tok)}),
    };
}

pub fn resolveStatementRef(self: *Prover, tok: lexer.Token) ElabError!StatementId {
    const target = try self.resolveTarget(tok);
    return self.env.findStatementId(target.file, target.base) orelse
        self.fail(tok.start, "unknown statement '{s}'", .{self.text(tok)});
}

// -- justification lowering ----------------------------------------------------

const RuleKind = enum {
    axiom,
    theorem,
    hypothesis,
    predicate,
    modus_ponens,
    implies_intro,
    forall_intro,
    forall_elim,
    exists_intro,
    exists_elim,
    and_intro,
    and_elim_left,
    and_elim_right,
    iff_intro,
    iff_elim_forward,
    iff_elim_backward,
    or_intro_left,
    or_intro_right,
    or_elim,
    not_intro,
    absurd,
    double_negation,
    reflexivity,
    symmetry,
    rewrite,
    iff_rewrite,
};

const rule_names = std.StaticStringMap(RuleKind).initComptime(.{
    .{ "axiom", .axiom },
    .{ "theorem", .theorem },
    .{ "hypothesis", .hypothesis },
    .{ "predicate", .predicate },
    .{ "modus_ponens", .modus_ponens },
    .{ "implies_intro", .implies_intro },
    .{ "forall_intro", .forall_intro },
    .{ "forall_elim", .forall_elim },
    .{ "exists_intro", .exists_intro },
    .{ "exists_elim", .exists_elim },
    .{ "and_intro", .and_intro },
    .{ "and_elim_left", .and_elim_left },
    .{ "and_elim_right", .and_elim_right },
    .{ "iff_intro", .iff_intro },
    .{ "iff_elim_forward", .iff_elim_forward },
    .{ "iff_elim_backward", .iff_elim_backward },
    .{ "or_intro_left", .or_intro_left },
    .{ "or_intro_right", .or_intro_right },
    .{ "or_elim", .or_elim },
    .{ "not_intro", .not_intro },
    .{ "absurd", .absurd },
    .{ "double_negation", .double_negation },
    .{ "symmetry", .symmetry },
    .{ "reflexivity", .reflexivity },
    .{ "rewrite", .rewrite },
    .{ "iff_rewrite", .iff_rewrite },
});

fn isBiconditionalShape(self: *const Prover, id: TermId) bool {
    const n = self.pool.get(id);
    if (n != .bin or n.bin.op != .and_op) return false;
    const l = self.pool.get(n.bin.lhs);
    const r = self.pool.get(n.bin.rhs);
    if (l != .bin or l.bin.op != .implies) return false;
    if (r != .bin or r.bin.op != .implies) return false;
    return self.pool.alphaEq(l.bin.lhs, r.bin.rhs) and
        self.pool.alphaEq(l.bin.rhs, r.bin.lhs);
}

fn wantRefs(self: *Prover, c: ast.Step.Claim, n: usize) ElabError!void {
    if (c.refs.len != n) {
        return self.fail(c.rule.start, "'{s}' expects {d} reference(s), got {d}", .{
            self.text(c.rule), n, c.refs.len,
        });
    }
}

fn lowerJustification(self: *Prover, low: *Lowering, block_id: kernel.BlockId, goal: TermId, c: ast.Step.Claim) ElabError!kernel.Justification {
    const rule_text = self.text(c.rule);
    const kind = rule_names.get(rule_text) orelse {
        // an unrecognized rule name here is either a genuine typo or an
        // accelerant / `instantiate` / `model` — none of which this pure-kernel
        // prover supports. Hard-error rather than silently misbehave.
        return self.fail(c.rule.start, "unsupported by the demand prover: '{s}'", .{rule_text});
    };
    const wants_args: usize = switch (kind) {
        .forall_elim => if (c.args.len == 0) 1 else c.args.len,
        .exists_intro => 1,
        else => 0,
    };
    if (c.args.len != wants_args) {
        return self.fail(c.rule.start, "'{s}' expects {d} argument(s), got {d}", .{
            rule_text, wants_args, c.args.len,
        });
    }
    switch (kind) {
        .axiom => {
            try self.wantRefs(c, 1);
            const stmt_id = try self.resolveStatementRef(c.refs[0]);
            const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
            if (stmt == .axiom and stmt.axiom.is_hole) try self.inheritHoles(stmt.axiom.holes);
            return .{ .axiom_ref = .{ .stmt = stmt_id, .loc = c.refs[0].start } };
        },
        .theorem => {
            try self.wantRefs(c, 1);
            const stmt_id = try self.resolveStatementRef(c.refs[0]);
            const stmt = self.env.statements.items[@intFromEnum(stmt_id)];
            if (stmt == .theorem) {
                try self.inheritAccelerated(stmt.theorem.accelerated);
                try self.inheritHoles(stmt.theorem.holes);
            }
            return .{ .theorem_ref = .{ .stmt = stmt_id, .loc = c.refs[0].start } };
        },
        .hypothesis => {
            try self.wantRefs(c, 1);
            return .{ .hypothesis = try self.resolveBlockRef(low, c.refs[0]) };
        },
        .predicate => {
            try self.wantRefs(c, 1);
            return .{ .hypothesis = try self.resolveBlockRef(low, c.refs[0]) };
        },
        .modus_ponens => {
            try self.wantRefs(c, 2);
            return .{ .modus_ponens = .{
                .implication = try self.resolveStepRef(low, c.refs[0]),
                .antecedent = try self.resolveStepRef(low, c.refs[1]),
            } };
        },
        .implies_intro => {
            try self.wantRefs(c, 1);
            return .{ .implies_intro = try self.resolveBlockRef(low, c.refs[0]) };
        },
        .forall_intro => {
            try self.wantRefs(c, 1);
            return .{ .forall_intro = try self.resolveBlockRef(low, c.refs[0]) };
        },
        .forall_elim => {
            try self.wantRefs(c, 1);
            var cur = try self.resolveStepRef(low, c.refs[0]);
            var cur_formula = low.steps.items[@intFromEnum(cur.id)].formula;
            for (c.args[0 .. c.args.len - 1]) |arg_expr| {
                const node = self.pool.get(cur_formula);
                if (node != .quant or node.quant.q != .forall) {
                    return self.fail(exprLoc(arg_expr), "forall_elim: '{s}' is not universally quantified here", .{try self.renderTerm(cur_formula)});
                }
                const arg = try self.elaborateExpr(arg_expr);
                const opened = try self.pool.open(node.quant.body, arg.id);
                cur = try self.emitStep(low, block_id, exprLoc(arg_expr), opened, .{
                    .forall_elim = .{ .step = cur, .with = arg.id, .with_loc = exprLoc(arg_expr) },
                });
                cur_formula = opened;
            }
            const last = c.args[c.args.len - 1];
            const arg = try self.elaborateExpr(last);
            return .{ .forall_elim = .{
                .step = cur,
                .with = arg.id,
                .with_loc = exprLoc(last),
            } };
        },
        .exists_intro => {
            try self.wantRefs(c, 1);
            const arg = try self.elaborateExpr(c.args[0]);
            return .{ .exists_intro = .{
                .step = try self.resolveStepRef(low, c.refs[0]),
                .witness = arg.id,
                .witness_loc = exprLoc(c.args[0]),
            } };
        },
        .exists_elim => {
            try self.wantRefs(c, 1);
            return .{ .exists_elim = try self.resolveBlockRef(low, c.refs[0]) };
        },
        .and_intro => {
            try self.wantRefs(c, 2);
            if (self.isBiconditionalShape(goal)) {
                return self.fail(c.rule.start, "this goal is a biconditional '(X -> Y) and (Y -> X)' — use `iff_intro` (which is the same rule, named for what it proves)", .{});
            }
            return .{ .and_intro = .{
                .left = try self.resolveStepRef(low, c.refs[0]),
                .right = try self.resolveStepRef(low, c.refs[1]),
            } };
        },
        .and_elim_left => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_left = try self.resolveStepRef(low, c.refs[0]) };
        },
        .and_elim_right => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_right = try self.resolveStepRef(low, c.refs[0]) };
        },
        .iff_intro => {
            try self.wantRefs(c, 2);
            if (!self.isBiconditionalShape(goal)) {
                return self.fail(c.rule.start, "iff_intro's goal must be a biconditional (from `P iff Q`); this goal is not of the form '(X -> Y) and (Y -> X)' — did you mean `and_intro`?", .{});
            }
            return .{ .and_intro = .{
                .left = try self.resolveStepRef(low, c.refs[0]),
                .right = try self.resolveStepRef(low, c.refs[1]),
            } };
        },
        .iff_elim_forward => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_left = try self.resolveStepRef(low, c.refs[0]) };
        },
        .iff_elim_backward => {
            try self.wantRefs(c, 1);
            return .{ .and_elim_right = try self.resolveStepRef(low, c.refs[0]) };
        },
        .or_intro_left => {
            try self.wantRefs(c, 1);
            return .{ .or_intro_left = try self.resolveStepRef(low, c.refs[0]) };
        },
        .or_intro_right => {
            try self.wantRefs(c, 1);
            return .{ .or_intro_right = try self.resolveStepRef(low, c.refs[0]) };
        },
        .or_elim => {
            try self.wantRefs(c, 3);
            return .{ .or_elim = .{
                .disj = try self.resolveStepRef(low, c.refs[0]),
                .left = try self.resolveBlockRef(low, c.refs[1]),
                .right = try self.resolveBlockRef(low, c.refs[2]),
            } };
        },
        .not_intro => {
            try self.wantRefs(c, 3);
            return .{ .not_intro = .{
                .block = try self.resolveBlockRef(low, c.refs[0]),
                .s1 = try self.resolveStepRef(low, c.refs[1]),
                .s2 = try self.resolveStepRef(low, c.refs[2]),
            } };
        },
        .absurd => {
            try self.wantRefs(c, 2);
            return .{ .absurd = .{
                .s1 = try self.resolveStepRef(low, c.refs[0]),
                .s2 = try self.resolveStepRef(low, c.refs[1]),
            } };
        },
        .double_negation => {
            try self.wantRefs(c, 1);
            return .{ .double_negation = try self.resolveStepRef(low, c.refs[0]) };
        },
        .reflexivity => {
            try self.wantRefs(c, 0);
            return .reflexivity;
        },
        .symmetry => {
            try self.wantRefs(c, 1);
            return .{ .symmetry = try self.resolveStepRef(low, c.refs[0]) };
        },
        .rewrite => {
            try self.wantRefs(c, 2);
            return .{ .rewrite = .{
                .equation = try self.resolveStepRef(low, c.refs[0]),
                .target = try self.resolveStepRef(low, c.refs[1]),
            } };
        },
        .iff_rewrite => {
            try self.wantRefs(c, 2);
            return .{ .iff_rewrite = .{
                .biconditional = try self.resolveStepRef(low, c.refs[0]),
                .target = try self.resolveStepRef(low, c.refs[1]),
            } };
        },
    }
}

/// Append a synthesized step to the proof; returns a reference to it.
pub fn emitStep(self: *Prover, low: *Lowering, block_id: kernel.BlockId, loc: u32, formula: TermId, just: kernel.Justification) ElabError!kernel.SRef {
    const id: kernel.StepId = @enumFromInt(low.steps.items.len);
    try low.steps.append(self.arena, .{
        .formula = formula,
        .just = just,
        .block = block_id,
        .label = try self.freshNamed("simplify"),
        .loc = loc,
    });
    return .{ .id = id, .loc = loc };
}

// -- TCC discharge -------------------------------------------------------------

fn dischargeTccs(self: *Prover, low: ?*const Lowering, block_id: kernel.BlockId, start: usize) ElabError!void {
    if (self.trusted) {
        self.pending_tccs.shrinkRetainingCapacity(start);
        return;
    }
    var any_failed = false;
    for (self.pending_tccs.items[start..]) |t| {
        if (!try self.tccDischarged(low, block_id, t.formula)) {
            const rendered = print.render(self.arena, self.pool, self.env, self.interner, t.formula) catch return error.OutOfMemory;
            self.sink.add(t.loc, "unproved obligation: '{s}'", .{rendered}) catch return error.OutOfMemory;
            any_failed = true;
        }
    }
    self.pending_tccs.shrinkRetainingCapacity(start);
    if (start == 0) self.result_facts.clearRetainingCapacity();
    if (any_failed) return error.Recover;
}

fn tccDischarged(self: *Prover, low: ?*const Lowering, block_id: kernel.BlockId, formula: TermId) ElabError!bool {
    var hyps: std.ArrayList(TermId) = .empty;
    return self.tccDischargedHyps(low, block_id, formula, &hyps);
}

fn tccDischargedHyps(self: *Prover, low: ?*const Lowering, block_id: kernel.BlockId, formula: TermId, hyps: *std.ArrayList(TermId)) ElabError!bool {
    var f = formula;
    while (true) {
        for (hyps.items) |h| {
            if (self.pool.alphaEq(h, f)) return true;
        }
        if (self.tccMatches(low, block_id, f)) return true;
        const node = self.pool.get(f);
        if (node == .bin and node.bin.op == .implies) {
            try hyps.append(self.arena, node.bin.lhs);
            f = node.bin.rhs;
            continue;
        }
        if (node == .bin and node.bin.op == .and_op) {
            return (try self.tccDischargedHyps(low, block_id, node.bin.lhs, hyps)) and
                (try self.tccDischargedHyps(low, block_id, node.bin.rhs, hyps));
        }
        if (node == .quant and node.quant.q == .forall) {
            const fresh = try self.freshName();
            const fv = try self.pool.add(.{ .fvar = .{ .name = fresh, .sort = node.quant.sort } });
            f = try self.pool.open(node.quant.body, fv);
            continue;
        }
        return false;
    }
}

fn tccMatches(self: *Prover, low: ?*const Lowering, block_id: kernel.BlockId, f: TermId) bool {
    for (self.result_facts.items) |fact| {
        if (self.pool.alphaEq(fact, f)) return true;
    }
    for (self.env.statements.items) |stmt| {
        const known: TermId = switch (stmt) {
            .axiom => |a| a.formula,
            .theorem => |t| if (t.proven) t.formula else continue,
            .schema => continue,
        };
        if (self.pool.alphaEq(known, f)) return true;
    }
    const l = low orelse return false;
    var cur: ?kernel.BlockId = block_id;
    while (cur) |c| {
        const b = l.blocks.items[@intFromEnum(c)];
        switch (b.kind) {
            .assume => |a| if (self.pool.alphaEq(a, f)) return true,
            .fix => |fx| if (fx.guard) |g| {
                if (self.pool.alphaEq(g, f)) return true;
            },
            else => {},
        }
        cur = b.parent;
    }
    for (l.steps.items, 0..) |s, i| {
        if (!lowAncestorOrSelf(l, s.block, block_id)) continue;
        if (self.pool.alphaEq(s.formula, f)) {
            self.extra_reachable_steps.append(self.arena, @intCast(i)) catch {};
            return true;
        }
    }
    return false;
}

pub fn lowAncestorOrSelf(low: *const Lowering, a: kernel.BlockId, b: kernel.BlockId) bool {
    var cur: ?kernel.BlockId = b;
    while (cur) |c| {
        if (c == a) return true;
        cur = low.blocks.items[@intFromEnum(c)].parent;
    }
    return false;
}

// -- sort/guard resolution -----------------------------------------------------

const Target = struct { file: FileId, base: StrId };

fn resolveTarget(self: *Prover, tok: lexer.Token) ElabError!Target {
    const text_ = self.text(tok);
    const i = std.mem.indexOfScalar(u8, text_, '.') orelse
        return .{ .file = self.file, .base = try self.internTok(tok) };
    const rest = text_[i + 1 ..];
    if (std.mem.indexOfScalar(u8, rest, '.') != null) {
        return self.fail(tok.start, "only one level of namespace qualification is allowed", .{});
    }
    const ns = self.interner.internString(text_[0..i]) catch return error.OutOfMemory;
    const file = self.env.findNamespace(self.file, ns) orelse
        return self.fail(tok.start, "unknown namespace '{s}'", .{text_[0..i]});
    const base = self.interner.internString(rest) catch return error.OutOfMemory;
    return .{ .file = file, .base = base };
}

pub fn resolveSort(self: *Prover, tok: lexer.Token) ElabError!SortId {
    const target = try self.resolveTarget(tok);
    return self.env.findSort(target.file, target.base) orelse
        self.fail(tok.start, "unknown sort '{s}'", .{self.text(tok)});
}

fn sortQualifiers(self: *Prover, id: SortId) ElabError![]const term.SymId {
    return self.env.qualifiersOf(self.arena, id) catch return error.OutOfMemory;
}

fn resolveBinderSort(self: *Prover, b: ast.Binder) ElabError!SortId {
    const base = try self.resolveSort(b.sort);
    const g = b.guard orelse return base;
    const gname = try self.internTok(g);
    const gsym = self.env.findSym(self.file, gname) orelse
        return self.fail(g.start, "sort refinement '{s}' is not a predicate in scope", .{self.text(g)});
    const sym = self.env.sym(gsym);
    const arg_ok = sym.arg_sorts.len == 1 and
        self.env.carrierOf(sym.arg_sorts[0]) == self.env.carrierOf(base);
    if (sym.kind != .pred or !arg_ok) {
        return self.fail(g.start, "sort refinement '{s}' must be a unary predicate over '{s}'", .{ self.text(g), self.text(b.sort) });
    }
    const quals = try self.arena.dupe(term.SymId, &.{gsym});
    const label = std.fmt.allocPrint(self.arena, "{s} where {s}", .{ self.text(b.sort), self.text(g) }) catch return error.OutOfMemory;
    const nm = self.interner.internString(label) catch return error.OutOfMemory;
    return self.env.addAnonymousRefinedSort(nm, b.sort.start, base, quals) catch return error.OutOfMemory;
}

fn qualifierApp(self: *Prover, qpred: term.SymId, arg: TermId) ElabError!TermId {
    const sym = self.env.sym(qpred);
    if (sym.definition) |body| {
        return self.pool.substFvar(body, sym.param_names[0], arg);
    }
    return self.pool.addApp(.pred, qpred, &.{arg});
}

fn fixGuard(self: *Prover, sort_tok: lexer.Token, v: term.Node.Fvar) ElabError!?TermId {
    const quals = try self.sortQualifiers(try self.resolveSort(sort_tok));
    if (quals.len == 0) return null;
    const fv = try self.pool.add(.{ .fvar = v });
    var g: ?TermId = null;
    for (quals) |qpred| {
        const app = try self.qualifierApp(qpred, fv);
        g = if (g) |prev| try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = prev, .rhs = app } }) else app;
    }
    return g;
}

fn checkNoShadow(self: *Prover, name: StrId, tok: lexer.Token) ElabError!void {
    for (self.scope.items) |entry| {
        if (entry.name == name) {
            return self.fail(tok.start, "'{s}' shadows a variable in scope; choose a fresh name", .{self.text(tok)});
        }
    }
    if (self.env.findSym(self.file, name) != null) {
        return self.fail(tok.start, "'{s}' shadows a declaration; choose a fresh name", .{self.text(tok)});
    }
}

// -- expression elaboration ----------------------------------------------------

fn requireProp(self: *Prover, typed: Typed, e: *const ast.Expr) ElabError!Typed {
    if (typed.sort != .prop) {
        return self.fail(exprLoc(e), "expected a proposition, got sort '{s}'", .{self.sortName(typed.sort)});
    }
    return typed;
}

fn surfaceResultFact(self: *Prover, sym: Symbol, term_id: TermId) ElabError!void {
    if (sym.result_refined == sym.result) return;
    for (try self.sortQualifiers(sym.result_refined)) |qpred| {
        const fact = try self.qualifierApp(qpred, term_id);
        try self.result_facts.append(self.arena, fact);
    }
}

pub fn elaborateExpr(self: *Prover, e: *const ast.Expr) ElabError!Typed {
    switch (e.*) {
        .name => |tok| return self.elaborateName(tok),
        .call => |c| return self.elaborateCall(c),
        .binary => |b| switch (b.op) {
            .implies, .and_op, .or_op => {
                const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                const tcc_start = self.pending_tccs.items.len;
                const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                if (b.op == .implies or b.op == .and_op) {
                    for (self.pending_tccs.items[tcc_start..]) |*t| {
                        t.formula = try self.pool.add(.{ .bin = .{
                            .op = .implies,
                            .lhs = lhs.id,
                            .rhs = t.formula,
                        } });
                    }
                }
                const op: term.BinOp = switch (b.op) {
                    .implies => .implies,
                    .and_op => .and_op,
                    .or_op => .or_op,
                    else => unreachable,
                };
                const id = try self.pool.add(.{ .bin = .{ .op = op, .lhs = lhs.id, .rhs = rhs.id } });
                return .{ .id = id, .sort = .prop };
            },
            .iff => {
                const lhs = try self.requireProp(try self.elaborateExpr(b.lhs), b.lhs);
                const rhs = try self.requireProp(try self.elaborateExpr(b.rhs), b.rhs);
                const fwd = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = lhs.id, .rhs = rhs.id } });
                const bwd = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = rhs.id, .rhs = lhs.id } });
                const id = try self.pool.add(.{ .bin = .{ .op = .and_op, .lhs = fwd, .rhs = bwd } });
                return .{ .id = id, .sort = .prop };
            },
            .equal, .not_equal => {
                const lhs = try self.elaborateExpr(b.lhs);
                const rhs = try self.elaborateExpr(b.rhs);
                if (lhs.sort == .prop) {
                    return self.fail(exprLoc(b.lhs), "'=' compares terms, not propositions", .{});
                }
                if (rhs.sort != lhs.sort) {
                    return self.fail(exprLoc(b.rhs), "expected sort '{s}', got '{s}'", .{
                        self.sortName(lhs.sort), self.sortName(rhs.sort),
                    });
                }
                const eq = try self.pool.add(.{ .eq = .{ .lhs = lhs.id, .rhs = rhs.id } });
                const id = if (b.op == .not_equal) try self.pool.add(.{ .not = eq }) else eq;
                return .{ .id = id, .sort = .prop };
            },
        },
        .not => |n| {
            const inner = try self.requireProp(try self.elaborateExpr(n.operand), n.operand);
            const id = try self.pool.add(.{ .not = inner.id });
            return .{ .id = id, .sort = .prop };
        },
        .quant => |q| {
            const refined = try self.resolveBinderSort(q.binders[0]);
            const sort = self.env.carrierOf(refined);
            const quals = try self.sortQualifiers(refined);
            const fresh = try self.arena.alloc(StrId, q.binders.len);
            for (q.binders, fresh) |b, *fr| {
                const bname = try self.internTok(b.name);
                try self.checkNoShadow(bname, b.name);
                fr.* = try self.freshName();
                try self.scope.append(self.arena, .{
                    .name = bname,
                    .sort = sort,
                    .fvar = fr.*,
                });
            }
            const tcc_start = self.pending_tccs.items.len;
            const rf_start = self.result_facts.items.len;
            const body = try self.requireProp(try self.elaborateExpr(q.body), q.body);
            var id = body.id;
            var i = q.binders.len;
            while (i > 0) {
                i -= 1;
                for (quals) |qpred| {
                    const bfv = try self.pool.add(.{ .fvar = .{ .name = fresh[i], .sort = sort } });
                    const guard_app = try self.qualifierApp(qpred, bfv);
                    const connective: term.BinOp = if (q.q == .forall) .implies else .and_op;
                    id = try self.pool.add(.{ .bin = .{ .op = connective, .lhs = guard_app, .rhs = id } });
                }
                id = try self.pool.close(id, fresh[i]);
                id = try self.pool.add(.{ .quant = .{
                    .q = if (q.q == .forall) .forall else .exists,
                    .sort = sort,
                    .hint = try self.internTok(q.binders[i].name),
                    .body = id,
                } });
                for (self.pending_tccs.items[tcc_start..]) |*t| {
                    var f = t.formula;
                    for (quals) |qpred| {
                        const bound = try self.pool.add(.{ .fvar = .{ .name = fresh[i], .sort = sort } });
                        const guard_app = try self.qualifierApp(qpred, bound);
                        f = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = guard_app, .rhs = f } });
                    }
                    const closed = try self.pool.close(f, fresh[i]);
                    t.formula = try self.pool.add(.{ .quant = .{
                        .q = .forall,
                        .sort = sort,
                        .hint = try self.internTok(q.binders[i].name),
                        .body = closed,
                    } });
                }
                for (self.result_facts.items[rf_start..]) |*rf| {
                    var f = rf.*;
                    for (quals) |qpred| {
                        const bound = try self.pool.add(.{ .fvar = .{ .name = fresh[i], .sort = sort } });
                        const guard_app = try self.qualifierApp(qpred, bound);
                        f = try self.pool.add(.{ .bin = .{ .op = .implies, .lhs = guard_app, .rhs = f } });
                    }
                    const closed = try self.pool.close(f, fresh[i]);
                    rf.* = try self.pool.add(.{ .quant = .{
                        .q = .forall,
                        .sort = sort,
                        .hint = try self.internTok(q.binders[i].name),
                        .body = closed,
                    } });
                }
                _ = self.scope.pop();
            }
            return .{ .id = id, .sort = .prop };
        },
        .lambda => |l| {
            return self.fail(l.tok.start, "lambda literals are only valid as schema arguments", .{});
        },
    }
}

fn elaborateName(self: *Prover, tok: lexer.Token) ElabError!Typed {
    if (std.mem.indexOfScalar(u8, self.text(tok), '.') != null) {
        const target = try self.resolveTarget(tok);
        return self.elaborateSymRef(tok, target);
    }
    const name = try self.internTok(tok);
    var i = self.scope.items.len;
    while (i > 0) {
        i -= 1;
        const entry = self.scope.items[i];
        if (entry.name == name) {
            const id = try self.pool.add(.{ .fvar = .{ .name = entry.fvar, .sort = entry.sort } });
            return .{ .id = id, .sort = entry.sort };
        }
    }
    // NO schema-parameter branch: the Prover has no schema_args (schema proofs
    // are unsupported), so a schema-param name simply won't resolve here — it
    // falls through to a symbol lookup and, failing that, "unknown identifier".
    return self.elaborateSymRef(tok, .{ .file = self.file, .base = name });
}

fn elaborateSymRef(self: *Prover, tok: lexer.Token, target: Target) ElabError!Typed {
    if (self.env.findSym(target.file, target.base)) |sym_id| {
        const sym = self.env.sym(sym_id);
        if (sym.arg_sorts.len != 0) {
            return self.fail(tok.start, "'{s}' expects {d} argument(s), got 0", .{ self.text(tok), sym.arg_sorts.len });
        }
        if (sym.definition) |def| {
            return .{ .id = def, .sort = sym.result };
        }
        const id = try self.pool.addApp(if (sym.kind == .pred) .pred else .app, sym_id, &.{});
        try self.surfaceResultFact(sym, id);
        return .{ .id = id, .sort = sym.result };
    }
    return self.fail(tok.start, "unknown identifier '{s}'", .{self.text(tok)});
}

fn elaborateCall(self: *Prover, c: ast.Expr.Call) ElabError!Typed {
    const target = try self.resolveTarget(c.callee);
    const name = target.base;
    // NO schema-parameter branch (Prover has no schema_args).
    const sym_id = self.env.findSym(target.file, name) orelse {
        return self.fail(c.callee.start, "unknown identifier '{s}'", .{self.text(c.callee)});
    };
    const sym = self.env.sym(sym_id);
    if (sym.arg_sorts.len != c.args.len) {
        return self.fail(c.callee.start, "'{s}' expects {d} argument(s), got {d}", .{
            self.text(c.callee), sym.arg_sorts.len, c.args.len,
        });
    }
    const arg_ids = try self.arena.alloc(TermId, c.args.len);
    for (c.args, sym.arg_sorts, arg_ids) |arg, expected, *out| {
        const typed = try self.elaborateExpr(arg);
        if (typed.sort != expected) {
            return self.fail(exprLoc(arg), "expected sort '{s}', got '{s}'", .{
                self.sortName(expected), self.sortName(typed.sort),
            });
        }
        out.* = typed.id;
    }
    if (sym.guard) |guard| {
        var g = guard;
        const fresh = try self.arena.alloc(StrId, sym.param_names.len);
        for (sym.param_names, fresh) |pn, *fr| {
            fr.* = try self.freshName();
            const fv = try self.pool.add(.{ .fvar = .{ .name = fr.*, .sort = .prop } });
            g = try self.pool.substFvar(g, pn, fv);
        }
        for (fresh, arg_ids) |fr, actual| {
            g = try self.pool.substFvar(g, fr, actual);
        }
        try self.pending_tccs.append(self.arena, .{ .formula = g, .loc = c.callee.start });
    }
    if (sym.definition) |body| {
        var expanded = body;
        const temps = try self.arena.alloc(StrId, sym.param_names.len);
        for (sym.param_names, temps) |pn, *t| {
            t.* = try self.freshName();
            const tv = try self.pool.add(.{ .fvar = .{ .name = t.*, .sort = .prop } });
            expanded = try self.pool.substFvar(expanded, pn, tv);
        }
        for (temps, arg_ids) |t, actual| {
            expanded = try self.pool.substFvar(expanded, t, actual);
        }
        return .{ .id = expanded, .sort = sym.result };
    }
    const id = try self.pool.addApp(if (sym.kind == .pred) .pred else .app, sym_id, arg_ids);
    try self.surfaceResultFact(sym, id);
    return .{ .id = id, .sort = sym.result };
}

// -- tests ---------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../../parser.zig");

test "prove a trivial axiom-citation proof end-to-end" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const interner = try arena.create(InternPool);
    interner.* = try .init(arena);
    const pool = try arena.create(term.Pool);
    pool.* = .init(arena);
    const sink = try arena.create(Diagnostics.Sink);
    sink.* = .init(arena);
    const environment = try arena.create(Env);
    environment.* = try .init(arena, interner);
    const file = try environment.newFile();

    // a 0-ary predicate P and an axiom `axP: P`.
    const p_name = try interner.internString("P");
    _ = try environment.addSym(file, .{
        .name = p_name,
        .kind = .pred,
        .arg_sorts = &.{},
        .result = .prop,
        .guard = null,
        .param_names = &.{},
        .loc = 0,
    });
    const p_pred = try pool.addApp(.pred, environment.findSym(file, p_name).?, &.{});
    const ax_name = try interner.internString("axP");
    _ = try environment.addStatement(file, ax_name, .{ .axiom = .{
        .name = ax_name,
        .formula = p_pred,
        .loc = 0,
    } });

    // a one-step proof: conclude P by citing the axiom.
    const thm_source =
        \\theorem t: P
        \\proof
        \\  @concl |
        \\    P
        \\    [by axiom axP]
        \\qed
    ;
    var tp: parser.Parser = .init(arena, thm_source, sink);
    const parsed = try tp.parseFile();
    try testing.expectEqual(@as(usize, 1), parsed.decls.len);
    const thm = parsed.decls[0].theorem;

    var prover = Prover.init(arena, thm_source, interner, pool, environment, sink, file);
    const ok = try prover.prove(thm.steps, p_pred, thm.name.start);
    try testing.expect(sink.list.items.len == 0);
    try testing.expect(ok);
}

test {
    testing.refAllDecls(@This());
}
