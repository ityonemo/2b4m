//! Walk — the RESUMABLE STEP-WALK state machine of the demand prover (Step 8, W1).
//!
//! A ProveTask proves a theorem by WALKING ITS PROOF'S STEPS in (topological sibling)
//! order. Per step: a READ PASS resolves every referenced name (local scope first, then
//! the global demand tables); if anything is missing the walk SUSPENDS AT THE STEP; once
//! clean, the step is CHECKED and the local declarations it introduces (step labels,
//! fix/unpack binders) are stored. See memory `provetask-step-walk-design`.
//!
//! RESUMABILITY: the explicit `stack` of frames IS the cursor — it lives on the task's
//! arena, so suspending is just RETURNING (stack intact) and resuming is CONTINUING to
//! pop. The pending step uses PEEK-THEN-POP: while its read pass is incomplete it stays
//! on top of the stack; each resume re-runs the (idempotent) read pass until clean, and
//! only then is the frame popped and the step processed. Traversal position is DATA on
//! the task, never the native call stack — the roadmap's "explicit state-machine tasks,
//! no coroutines" (and the same reason the eager `lowerSteps` became an explicit
//! work-stack; see memory `iterative-proof-lowering`).
//!
//! WHAT THE WALK OWNS (structure): sibling topo-sort + duplicate/shadow label checks at
//! block entry (ported from the iterative lowering driver — a step may cite a
//! later-WRITTEN sibling; topo order makes the cited one walk first), the local scope
//! maps (LocalStepKV: label -> step/block ordinal; LocalIdentKV: binder name -> block),
//! and block DESCOPING (exit frames carry marks; internals truncate at exit, while a
//! block's own label lives in the PARENT scope — a closed subproof stays citable for
//! implies_intro/forall_intro, its internals do not; the kernel's accessibility rules,
//! enforced at resolution time).
//!
//! WHAT THE DRIVER OWNS (semantics), via a comptime duck-typed `driver`:
//!   - `readPass(w, step, block) !?Engine.TaskIndex` — resolve the step's referenced
//!     names; rack fetches for the absent; return a blocker to suspend on, or null when
//!     the step's reference closure is complete. MUST be idempotent (it re-runs on every
//!     resume until clean).
//!   - `process(w, step, block) !bool` — the semantic work once refs are clean: elaborate
//!     the claim/hypothesis/binder sort, truth-check. false = failed (diagnostic already
//!     recorded by the driver).
//!   - `caseConclude(w, step, block) !bool` — a `case` step's or_elim conclusion check,
//!     which runs only after ALL its arms have walked.
//! W1 tests fake the driver; later W-steps plug real resolution/checking into this seam.
//!
//! CASE ARMS are assume-shaped (`{label, assumption, steps}` ≅ an `assume` step), so the
//! walk SYNTHESIZES an `ast.Step{.assume}` per arm and reuses the ordinary machinery;
//! a `case_conclude` frame (pushed beneath the arms) fires after they finish.

const std = @import("std");
const Allocator = std.mem.Allocator;
const ast = @import("../../ast.zig");
const lexer = @import("../../lexer.zig");
const InternPool = @import("../../InternPool.zig");
const StrId = InternPool.StrId;
const Diagnostics = @import("../../diagnostics.zig");
const Engine = @import("../../Engine.zig");

const Walk = @This();

/// Proof-local ordinal of a processed (leaf) step, assigned in walk order. W5 aligns
/// these with kernel StepIds (the walk processes in the same order lowering emits).
pub const StepOrdinal = enum(u32) { _ };
/// Proof-local ordinal of an entered block. 0 is the root (the proof body itself).
pub const BlockOrdinal = enum(u32) { root = 0, _ };

/// What a local step-label resolves to: a leaf step or a (possibly closed) block.
pub const LocalTarget = union(enum) { step: StepOrdinal, block: BlockOrdinal };

/// LocalStepKV entry: a step/block label live in the current scope. Flat list,
/// innermost-last; lookup is a reverse scan; block exit truncates to its mark.
const LocalStep = struct { name: StrId, target: LocalTarget };

/// The SEMANTIC half of a binder, computed by the driver while processing a fix/unpack
/// step (it resolves the sort token and mints the hygienic fvar identity) and handed to
/// the walk via `pending_binder`. Defaults are placeholders for structure-only drivers
/// (the W1 fakes) that never read them.
pub const BinderInfo = struct {
    /// the binder's KERNEL sort (numerically a pool Index in the demand world)
    sort: @import("../../term.zig").SortId = @enumFromInt(0),
    /// the hygienic disambiguated fvar identity (`x#N`) terms bind through
    fvar: StrId = .none,
};

/// LocalIdentKV entry: a binder (fix eigenvariable / unpack witness) live in scope.
pub const LocalIdent = struct { name: StrId, block: BlockOrdinal, info: BinderInfo = .{} };

/// One unit of reified traversal state. The stack of these IS the walk's cursor.
pub const Frame = union(enum) {
    /// a step awaiting read-pass + processing (peek-then-pop)
    step: StepFrame,
    /// leave a block: truncate the local maps to the marks (descope its internals)
    exit_block: ExitFrame,
    /// a `case` step's conclusion — fires after all its arm frames have drained
    case_conclude: StepFrame,

    pub const StepFrame = struct { step: *const ast.Step, block: BlockOrdinal };
    pub const ExitFrame = struct { block: BlockOrdinal, steps_mark: u32, idents_mark: u32 };
};

/// What one `drive` call ended as. `blocked` carries the task to suspend on; the walk's
/// state is untouched — call `drive` again after it completes. `failed` means a
/// diagnostic was recorded (by the walk or the driver); the proof is rejected.
pub const Result = union(enum) { done, blocked: Engine.TaskIndex, failed };

arena: Allocator,
interner: *InternPool,
/// the proof's source text — step tokens index into it
source: []const u8,
sink: *Diagnostics.Sink,

/// the reified traversal cursor (see Frame). Arena-resident: survives suspends.
stack: std.ArrayList(Frame) = .empty,
/// LocalStepKV — live step/block labels, innermost-last (reverse-scan lookup).
local_steps: std.ArrayList(LocalStep) = .empty,
/// LocalIdentKV — live binders, innermost-last (reverse-scan lookup).
local_idents: std.ArrayList(LocalIdent) = .empty,
next_step: u32 = 0,
next_block: u32 = 1, // 0 = root
started: bool = false,
/// Set by the driver during `process` of a fix/unpack step (the semantic binder info —
/// resolved sort + hygienic fvar); consumed by the subsequent enterBlock. The handoff is
/// explicit task state, not a return value, because process and enterBlock are separate
/// moments of the state machine.
pending_binder: ?BinderInfo = null,

pub fn init(arena: Allocator, interner: *InternPool, source: []const u8, sink: *Diagnostics.Sink) Walk {
    return .{ .arena = arena, .interner = interner, .source = source, .sink = sink };
}

// -- local scope lookups (pub: drivers resolve local-first through these) --------------

/// Resolve a label against LocalStepKV (innermost wins). Null = not a live local label.
pub fn findStep(self: *const Walk, name: StrId) ?LocalTarget {
    var i = self.local_steps.items.len;
    while (i > 0) {
        i -= 1;
        if (self.local_steps.items[i].name == name) return self.local_steps.items[i].target;
    }
    return null;
}

/// Resolve a binder name against LocalIdentKV (innermost wins). Null = not local.
pub fn findIdent(self: *const Walk, name: StrId) ?LocalIdent {
    var i = self.local_idents.items.len;
    while (i > 0) {
        i -= 1;
        if (self.local_idents.items[i].name == name) return self.local_idents.items[i];
    }
    return null;
}

// -- the drive loop --------------------------------------------------------------------

/// Advance the walk as far as possible. First call seeds the root body (duplicate/shadow
/// label checks + sibling topo-sort); subsequent calls RESUME from the reified cursor.
/// Pass the SAME `steps` slice on every call (the ProveTask holds it).
pub fn drive(self: *Walk, steps: []const ast.Step, driver: anytype) Allocator.Error!Result {
    if (!self.started) {
        self.started = true;
        if (!try self.enterBody(steps, .root)) return .failed;
    }
    while (self.stack.items.len > 0) {
        switch (self.stack.items[self.stack.items.len - 1]) { // PEEK — pop only on success
            .exit_block => |e| {
                _ = self.stack.pop();
                self.local_steps.shrinkRetainingCapacity(e.steps_mark);
                self.local_idents.shrinkRetainingCapacity(e.idents_mark);
            },
            .case_conclude => |fr| {
                _ = self.stack.pop();
                if (!try driver.caseConclude(self, fr.step, fr.block)) return .failed;
                try self.bindStepLabel(fr.step.label);
            },
            .step => |fr| {
                // READ PASS while peeked: if anything's missing, the frame stays on top
                // and we suspend; the resume re-runs this (idempotent) pass until clean.
                if (try driver.readPass(self, fr.step, fr.block)) |blocker| {
                    return .{ .blocked = blocker };
                }
                _ = self.stack.pop();
                if (!try driver.process(self, fr.step, fr.block)) return .failed;
                switch (fr.step.body) {
                    .claim => try self.bindStepLabel(fr.step.label),
                    .assume => |blk| {
                        if (!try self.enterBlock(fr.step.label, null, blk.steps)) return .failed;
                    },
                    .fix => |blk| {
                        if (!try self.enterBlock(fr.step.label, blk.name, blk.steps)) return .failed;
                    },
                    .unpack => |blk| {
                        if (!try self.enterBlock(fr.step.label, blk.name, blk.steps)) return .failed;
                    },
                    .case => |c| {
                        // conclude AFTER the arms: push the conclude frame first (pops
                        // last), then the arms REVERSED (pop left-to-right). Arms are
                        // assume-shaped — synthesize assume steps so they reuse the
                        // ordinary read-pass/process/enterBlock machinery.
                        try self.stack.append(self.arena, .{ .case_conclude = .{ .step = fr.step, .block = fr.block } });
                        var i = c.arms.len;
                        while (i > 0) {
                            i -= 1;
                            const arm = &c.arms[i];
                            const synth = try self.arena.create(ast.Step);
                            synth.* = .{ .label = arm.label, .body = .{ .assume = .{ .formula = arm.assumption, .steps = arm.steps } } };
                            try self.stack.append(self.arena, .{ .step = .{ .step = synth, .block = fr.block } });
                        }
                    },
                }
            },
        }
    }
    return .done;
}

// -- structure: labels, blocks, scoping ------------------------------------------------

/// Record a processed leaf step's label into LocalStepKV, assigning its ordinal.
fn bindStepLabel(self: *Walk, label_tok: lexer.Token) Allocator.Error!void {
    const label = try self.internTok(label_tok);
    const ord: StepOrdinal = @enumFromInt(self.next_step);
    self.next_step += 1;
    try self.local_steps.append(self.arena, .{ .name = label, .target = .{ .step = ord } });
}

/// Enter a block step: bind its label in the PARENT scope (outlives the block — a closed
/// subproof is citable), take the descope marks, bind the binder (if any) INSIDE the
/// block region, push the exit frame, then seed the body (checks + topo + push).
fn enterBlock(self: *Walk, label_tok: lexer.Token, binder: ?lexer.Token, body: []const ast.Step) Allocator.Error!bool {
    const label = try self.internTok(label_tok);
    const ord: BlockOrdinal = @enumFromInt(self.next_block);
    self.next_block += 1;
    try self.local_steps.append(self.arena, .{ .name = label, .target = .{ .block = ord } });
    const steps_mark: u32 = @intCast(self.local_steps.items.len);
    const idents_mark: u32 = @intCast(self.local_idents.items.len);
    try self.stack.append(self.arena, .{ .exit_block = .{ .block = ord, .steps_mark = steps_mark, .idents_mark = idents_mark } });
    if (binder) |btok| {
        const bname = try self.internTok(btok);
        if (self.findIdent(bname) != null) {
            return self.reject(btok.start, "'{s}' shadows an enclosing variable; choose a fresh name", .{self.text(btok)});
        }
        // consume the driver's semantic binder info (set during process; see field doc)
        const info = self.pending_binder orelse BinderInfo{};
        self.pending_binder = null;
        try self.local_idents.append(self.arena, .{ .name = bname, .block = ord, .info = info });
    }
    return self.enterBody(body, ord);
}

/// Seed a block body onto the stack: per-sibling duplicate-label + shadow checks, then
/// TOPO-SORT the siblings by their intra-block citations (a step may cite a later-written
/// label — the cited one must walk first), pushed in reverse so they pop in topo order.
fn enterBody(self: *Walk, steps: []const ast.Step, block: BlockOrdinal) Allocator.Error!bool {
    var index_of: std.AutoHashMapUnmanaged(StrId, usize) = .empty;
    for (steps, 0..) |*s, i| {
        const label = try self.internTok(s.label);
        // a label LIVE in local_steps = it belongs to an ancestor block or an
        // already-walked sibling on the open path — the same set the eager
        // labelInScope rejected (closed subtrees' labels are descoped ⇒ reusable).
        if (self.findStep(label) != null) {
            return self.reject(s.label.start, "label '{s}' shadows an enclosing label; choose a fresh name", .{self.text(s.label)});
        }
        const gop = index_of.getOrPut(self.arena, label) catch return error.OutOfMemory;
        if (gop.found_existing) {
            return self.reject(s.label.start, "duplicate label '{s}'", .{self.text(s.label)});
        }
        gop.value_ptr.* = i;
    }
    const order = (try self.topoSortSteps(steps, index_of)) orelse return false;
    var i = order.len;
    while (i > 0) {
        i -= 1;
        try self.stack.append(self.arena, .{ .step = .{ .step = &steps[order[i]], .block = block } });
    }
    return true;
}

// -- sibling topo-sort (ported from the iterative lowering driver) ---------------------

/// A step's SIBLING dependencies, by label: claim refs, an unpack's `from`, a case's
/// `disj`. Purely AST-structural (token text -> sibling index); no name resolution.
fn stepSiblingDeps(self: *Walk, step: *const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize), out: *std.ArrayList(usize)) Allocator.Error!void {
    switch (step.body) {
        .claim => |c| for (c.refs) |r| try self.depRef(r, index_of, out),
        .unpack => |blk| try self.depRef(blk.from, index_of, out),
        .case => |c| try self.depRef(c.disj, index_of, out),
        .assume, .fix => {},
    }
}

fn depRef(self: *Walk, t: lexer.Token, index_of: std.AutoHashMapUnmanaged(StrId, usize), out: *std.ArrayList(usize)) Allocator.Error!void {
    const name = self.interner.internString(self.source[t.start..t.end]) catch return error.OutOfMemory;
    if (index_of.get(name)) |dep| try out.append(self.arena, dep);
}

/// Topological order of sibling steps by their citation dependencies. Ties break by
/// textual order (already-ordered proofs walk identically). Null = cycle (diagnosed).
fn topoSortSteps(self: *Walk, steps: []const ast.Step, index_of: std.AutoHashMapUnmanaged(StrId, usize)) Allocator.Error!?[]const usize {
    const n = steps.len;
    const deps = try self.arena.alloc([]const usize, n);
    const remaining = try self.arena.alloc(usize, n);
    for (steps, 0..) |*s, i| {
        var d: std.ArrayList(usize) = .empty;
        try self.stepSiblingDeps(s, index_of, &d);
        deps[i] = d.items;
        remaining[i] = d.items.len;
    }
    var order: std.ArrayList(usize) = .empty;
    const emitted = try self.arena.alloc(bool, n);
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
        if (!progressed) {
            _ = try self.reportCycle(steps, deps, emitted);
            return null;
        }
    }
    return order.items;
}

/// Diagnose a citation cycle among siblings: walk unemitted deps until a repeat, print
/// the cycle path. Always "fails" (records the diagnostic; the caller returns .failed).
fn reportCycle(self: *Walk, steps: []const ast.Step, deps: []const []const usize, emitted: []const bool) Allocator.Error!bool {
    var start: usize = 0;
    while (start < steps.len and emitted[start]) start += 1;
    var path: std.ArrayList(usize) = .empty;
    const on_path = self.arena.alloc(bool, steps.len) catch return error.OutOfMemory;
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
    var started_path = false;
    for (path.items) |i| {
        if (!started_path and i != cur) continue;
        started_path = true;
        msg.writer.print("{s} -> ", .{self.text(steps[i].label)}) catch return error.OutOfMemory;
    }
    msg.writer.print("{s}", .{self.text(steps[cur].label)}) catch return error.OutOfMemory;
    return self.reject(steps[cur].label.start, "cyclic justification: {s}", .{msg.written()});
}

// -- small utilities -------------------------------------------------------------------

fn internTok(self: *Walk, t: lexer.Token) Allocator.Error!StrId {
    return self.interner.internString(self.source[t.start..t.end]) catch error.OutOfMemory;
}

fn text(self: *const Walk, t: lexer.Token) []const u8 {
    return self.source[t.start..t.end];
}

/// Record a diagnostic and signal failure (the false propagates up to Result.failed).
fn reject(self: *Walk, offset: u32, comptime fmt: []const u8, args: anytype) Allocator.Error!bool {
    self.sink.add(offset, fmt, args) catch return error.OutOfMemory;
    return false;
}

// --- tests ----------------------------------------------------------------------------

const testing = std.testing;
const parser = @import("../../parser.zig");

/// Test harness: parse a theorem source, hand back its proof steps + the plumbing.
const Rig = struct {
    arena: Allocator,
    interner: *InternPool,
    sink: *Diagnostics.Sink,
    steps: []const ast.Step,
    source: []const u8,

    fn init(arena: Allocator, source: []const u8) !Rig {
        const interner = try arena.create(InternPool);
        interner.* = try .init(arena);
        const sink = try arena.create(Diagnostics.Sink);
        sink.* = .init(arena);
        var p: parser.Parser = .init(arena, source, sink);
        const parsed = try p.parseFile();
        try testing.expectEqual(@as(usize, 0), sink.list.items.len); // source must parse
        return .{
            .arena = arena,
            .interner = interner,
            .sink = sink,
            .steps = parsed.decls[parsed.decls.len - 1].theorem.steps,
            .source = source,
        };
    }

    fn walk(self: *const Rig) Walk {
        return Walk.init(self.arena, self.interner, self.source, self.sink);
    }
};

/// A scripted fake driver: records the order steps are processed (by label text), and
/// can block a named step's read pass a given number of times (simulating racked
/// fetches that complete one wake at a time).
const FakeDriver = struct {
    arena: Allocator,
    source: []const u8,
    processed: std.ArrayList([]const u8) = .empty,
    read_passes: usize = 0,
    /// block the read pass of the step with this label text N times before allowing it
    block_label: []const u8 = "",
    block_times: usize = 0,
    /// scripted assertion hook: label -> expect findIdent(name) present during process
    expect_ident_at: []const u8 = "",
    expect_ident_name: []const u8 = "",
    ident_seen: bool = false,

    fn label(self: *FakeDriver, step: *const ast.Step) []const u8 {
        return self.source[step.label.start..step.label.end];
    }

    pub fn readPass(self: *FakeDriver, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!?Engine.TaskIndex {
        _ = w;
        _ = block;
        self.read_passes += 1;
        if (self.block_times > 0 and std.mem.eql(u8, self.label(step), self.block_label)) {
            self.block_times -= 1;
            return @enumFromInt(7); // a pretend racked-fetch TaskIndex
        }
        return null;
    }

    pub fn process(self: *FakeDriver, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!bool {
        _ = block;
        try self.processed.append(self.arena, self.label(step));
        if (self.expect_ident_at.len > 0 and std.mem.eql(u8, self.label(step), self.expect_ident_at)) {
            const name = try w.interner.internString(self.expect_ident_name);
            self.ident_seen = w.findIdent(name) != null;
        }
        return true;
    }

    pub fn caseConclude(self: *FakeDriver, w: *Walk, step: *const ast.Step, block: Walk.BlockOrdinal) Allocator.Error!bool {
        _ = w;
        _ = block;
        try self.processed.append(self.arena, self.label(step));
        return true;
    }
};

test "walk: linear steps process in topo order (a forward citation walks first)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    // @first cites @second (written later) — topo order must walk second first.
    const rig = try Rig.init(arena,
        \\theorem t: P
        \\proof
        \\  @first |
        \\    P
        \\    [by theorem second]
        \\  @second |
        \\    P
        \\    [by axiom axP]
        \\qed
    );
    var w = rig.walk();
    var d: FakeDriver = .{ .arena = arena, .source = rig.source };
    const result = try w.drive(rig.steps, &d);
    try testing.expect(result == .done);
    try testing.expectEqual(@as(usize, 2), d.processed.items.len);
    try testing.expectEqualStrings("second", d.processed.items[0]);
    try testing.expectEqualStrings("first", d.processed.items[1]);
    // root labels persist after the walk (the conclusion is read from local scope)
    try testing.expect(w.findStep(try rig.interner.internString("first")) != null);
}

test "walk: nested fix block — binder in scope inside, descoped after; block label persists" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rig = try Rig.init(arena,
        \\theorem t: Q
        \\proof
        \\  @outer |
        \\    fix n: Nat {
        \\      @inner |
        \\        P(n)
        \\        [by axiom axP]
        \\    }
        \\  @concl |
        \\    Q
        \\    [by theorem outer]
        \\qed
    );
    var w = rig.walk();
    var d: FakeDriver = .{
        .arena = arena,
        .source = rig.source,
        .expect_ident_at = "inner",
        .expect_ident_name = "n",
    };
    const result = try w.drive(rig.steps, &d);
    try testing.expect(result == .done);
    try testing.expect(d.ident_seen); // the fix binder WAS in LocalIdentKV at @inner
    // after the walk: binder descoped, inner label descoped, block label persists
    try testing.expect(w.findIdent(try rig.interner.internString("n")) == null);
    try testing.expect(w.findStep(try rig.interner.internString("inner")) == null);
    const outer = w.findStep(try rig.interner.internString("outer"));
    try testing.expect(outer != null and outer.? == .block);
    // topo put @outer before @concl (concl cites outer)
    try testing.expectEqualStrings("outer", d.processed.items[0]);
    try testing.expectEqualStrings("inner", d.processed.items[1]);
    try testing.expectEqualStrings("concl", d.processed.items[2]);
}

test "walk: suspends AT the step and resumes there (peek-then-pop)" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rig = try Rig.init(arena,
        \\theorem t: P
        \\proof
        \\  @a |
        \\    P
        \\    [by axiom axP]
        \\  @b |
        \\    P
        \\    [by theorem a]
        \\qed
    );
    var w = rig.walk();
    // @b's read pass blocks TWICE (two waves of pending fetches), then resolves.
    var d: FakeDriver = .{ .arena = arena, .source = rig.source, .block_label = "b", .block_times = 2 };

    const r1 = try w.drive(rig.steps, &d);
    try testing.expect(r1 == .blocked);
    try testing.expectEqual(@as(Engine.TaskIndex, @enumFromInt(7)), r1.blocked);
    // @a processed; @b still pending on top of the stack
    try testing.expectEqual(@as(usize, 1), d.processed.items.len);
    try testing.expectEqualStrings("a", d.processed.items[0]);

    const r2 = try w.drive(rig.steps, &d); // wake #1: still blocked
    try testing.expect(r2 == .blocked);

    const r3 = try w.drive(rig.steps, &d); // wake #2: read pass clean now
    try testing.expect(r3 == .done);
    try testing.expectEqual(@as(usize, 2), d.processed.items.len);
    try testing.expectEqualStrings("b", d.processed.items[1]);
    // @b was read-passed 3 times (blocked, blocked, clean); @a once.
    try testing.expectEqual(@as(usize, 4), d.read_passes);
}

test "walk: duplicate sibling label rejected" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rig = try Rig.init(arena,
        \\theorem t: P
        \\proof
        \\  @a |
        \\    P
        \\    [by axiom axP]
        \\  @a |
        \\    P
        \\    [by axiom axP]
        \\qed
    );
    var w = rig.walk();
    var d: FakeDriver = .{ .arena = arena, .source = rig.source };
    const result = try w.drive(rig.steps, &d);
    try testing.expect(result == .failed);
    try testing.expectEqual(@as(usize, 1), rig.sink.list.items.len);
}

test "walk: cyclic sibling citations rejected with the cycle path" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const rig = try Rig.init(arena,
        \\theorem t: P
        \\proof
        \\  @a |
        \\    P
        \\    [by theorem b]
        \\  @b |
        \\    P
        \\    [by theorem a]
        \\qed
    );
    var w = rig.walk();
    var d: FakeDriver = .{ .arena = arena, .source = rig.source };
    const result = try w.drive(rig.steps, &d);
    try testing.expect(result == .failed);
    try testing.expectEqual(@as(usize, 1), rig.sink.list.items.len);
    try testing.expect(std.mem.indexOf(u8, rig.sink.list.items[0].message, "cyclic") != null);
}
