//! `bpa debug accelerant <file> <line>` (or `<file> <theorem> <step-label>`): reprint, as
//! RE-PARSEABLE BPA SOURCE, the synthetic theorem an accelerant produced for a step.
//!
//! Every `[using <tactic> …]` step is sugar for a GENERATED synthetic schema that the ordinary
//! demand pipeline proves and the kernel re-checks (`Prove.demandUsing`). That decl is plain
//! `ast` — built by the producer, registered on the process arena, and recorded BY STEP in
//! `Context.synthetic_at`. This module runs the ordinary check (EXACTLY the code that generates
//! the decl — no second producer entry point), finds the decl the selected step produced, and
//! renders it back into the `theorem … proof … qed` form a human would have written, so you can
//! read exactly what was kernel-checked.
//!
//! The rendering is separate code from the generation, and it is a READABLE reprint, not a
//! byte-for-byte round-trip: the `{hash}`/`{mN}` name mangle is trimmed, `.symbol` identity
//! tokens print their entity's name, and a hygienic `x#N` binder prints as `x` — so two distinct
//! binders CAN print alike in one scope (paste-and-fix, by design).

const std = @import("std");
const Allocator = std.mem.Allocator;

const ast = @import("../ast.zig");
const lexer = @import("../lexer.zig");
const Token = lexer.Token;
const parser = @import("../parser.zig");
const diagnostics = @import("../diagnostics.zig");
const InternPool = @import("../InternPool.zig");
const root = @import("../root.zig");

pub const Result = struct {
    text: []const u8,
    ok: bool,
};

/// `selector`: a line number (`"15"`) OR a `<theorem> <step-label>` pair.
pub const Selector = union(enum) {
    line: usize,
    step: struct { theorem: []const u8, label: []const u8 },
};

/// Locate the accelerant step `selector` names in the ROOT file, run the ordinary strict check
/// of the whole project (which produces every synthetic), and render the synthetic that step
/// produced. `read_fn`/`std_root` are the same import-resolution hooks `check` uses.
pub fn accelerant(
    io: std.Io,
    arena: Allocator,
    path: []const u8,
    source: []const u8,
    selector: Selector,
    read_ctx: ?*anyopaque,
    read_fn: root.ReadFileFn,
    std_root: []const u8,
) Allocator.Error!Result {
    // parse the ROOT file separately for selector resolution (line/label -> the accelerant
    // step's rule-token offset); its AST is what the user is pointing at.
    const psink = try arena.create(diagnostics.Sink);
    psink.* = .init(arena);
    var p: parser.Parser = .init(arena, source, psink);
    const file = try p.parseFile();
    const root_only = [_]diagnostics.FileSrc{.{ .path = path, .source = source }};
    if (psink.list.items.len > 0) return renderDiagnostics(arena, &root_only, psink);

    const target_offset = switch (selector) {
        .line => |ln| lineToStepOffset(source, file, ln) orelse
            return fail(arena, "no proof step on line {d}", .{ln}),
        .step => |s| stepLabelOffset(source, file, s.theorem, s.label) orelse
            return fail(arena, "no step '{s}' in theorem '{s}'", .{ s.label, s.theorem }),
    };

    // the ordinary STRICT check of the project (default Verify → every synthetic is produced
    // by the very code that always produces it). A proof/resolution error surfaces as a
    // diagnostic, rendered against the root path AS GIVEN (the loader canonicalizes it).
    // `.custom`: this command reads through whatever `read_fn` its caller supplied, so the
    // pool loader (which honours it) rather than the ring (which opens paths itself).
    const loaded = try root.loadProject(io, arena, &.{.{ .path = path }}, read_ctx, read_fn, .custom, .{}, std_root);
    const files = try arena.dupe(diagnostics.FileSrc, loaded.files);
    files[@intFromEnum(loaded.root_file)].path = path;
    if (loaded.sink.list.items.len > 0) return renderDiagnostics(arena, files, loaded.sink);

    // a clean `arithmetic … fallback(<thm>)` step was proved by CITING that manual theorem
    // (the certifier chain declined; a fallback that turns out unnecessary is a hard error
    // above) — there is no accelerant certificate to reprint. Say so, and name it.
    if (fallbackAt(file, target_offset)) |fb|
        return fail(arena, "proof by fallback: this `arithmetic` step is discharged by the manual theorem '{s}' (the certifiers declined), so there is no accelerant synthetic to reprint", .{source[fb.start..fb.end]});

    const decl = loaded.context.syntheticAt(loaded.root_file, target_offset) orelse
        return fail(arena, "no accelerant produced a theorem there (is it a `[using <tactic> …]` step?)", .{});
    const text = try renderDecl(arena, loaded.interner, source, decl);
    return .{ .text = text, .ok = true };
}

// --- token text ------------------------------------------------------------------------

/// The display text of a token that may be SYNTHETIC (accelerant-generated AST): a `.symbol`
/// token prints its entity's name (an anonymous entity as `_`); a synthetic identifier (empty
/// source span, stamped name) prints its interned bytes trimmed at the `#` hygiene mangle; a
/// real token prints its source span.
pub fn tokenText(interner: *const InternPool, source: []const u8, t: Token) []const u8 {
    if (t.tag == .symbol) {
        const nm = interner.nameOf(t.name);
        return if (nm == InternPool.Index.none) "_" else interner.stringBytes(nm);
    }
    if (t.start == t.end and t.name != InternPool.Index.none) {
        const bytes = interner.stringBytes(t.name);
        return bytes[0 .. std.mem.indexOfScalar(u8, bytes, '#') orelse bytes.len];
    }
    return source[t.start..t.end];
}

/// A declaration name with every mangle trimmed: `{hash}`/`{mN}` (accelerant naming), `#`
/// (hygiene), `$` (legacy).
fn displayName(name: []const u8) []const u8 {
    var end = name.len;
    for ([_]u8{ '{', '#', '$' }) |ch| {
        if (std.mem.indexOfScalar(u8, name, ch)) |i| end = @min(end, i);
    }
    return name[0..end];
}

// --- the AST → bpa renderer --------------------------------------------------------------

/// Render a fact declaration (theorem/axiom/hole, local or alias) as bpa source:
/// `theorem <name>[(params)]: <formula>\nproof\n  …\nqed\n`. Non-fact decls render a comment.
pub fn renderDecl(arena: Allocator, interner: *const InternPool, source: []const u8, decl: *const ast.Decl) Allocator.Error![]const u8 {
    var out: std.Io.Writer.Allocating = .init(arena);
    var r: Renderer = .{ .arena = arena, .interner = interner, .source = source, .w = &out.writer };
    r.decl(decl) catch return error.OutOfMemory;
    return out.toOwnedSlice();
}

const Error = error{ OutOfMemory, WriteFailed };

const Renderer = struct {
    arena: Allocator,
    interner: *const InternPool,
    source: []const u8,
    w: *std.Io.Writer,

    fn text(self: *const Renderer, t: Token) []const u8 {
        return tokenText(self.interner, self.source, t);
    }

    /// A step label's text without its `@` sigil (a real `@label` token spans the sigil). A
    /// SYNTHETIC label is `freshNamed` (`simplify#7`): every label of one producer shares the
    /// stem, so trimming the `#N` would collide them all — render it as the kebab label
    /// `simplify-7` instead (labels and refs admit hyphens), which is unique AND legal.
    fn label(self: *const Renderer, t: Token) Error![]const u8 {
        if (t.start == t.end and t.name != InternPool.Index.none) {
            const bytes = self.interner.stringBytes(t.name);
            if (std.mem.indexOfScalar(u8, bytes, '#')) |i| {
                return std.fmt.allocPrint(self.arena, "{s}-{s}", .{ bytes[0..i], bytes[i + 1 ..] });
            }
            return bytes;
        }
        const s = self.text(t);
        return if (s.len > 0 and s[0] == '@') s[1..] else s;
    }

    fn decl(self: *Renderer, d: *const ast.Decl) Error!void {
        switch (d.*) {
            .theorem => |t| switch (t) {
                .local => |l| {
                    try self.factHead("theorem", l.fact);
                    try self.w.writeAll("proof\n");
                    try self.steps(l.steps);
                    try self.w.writeAll("qed\n");
                },
                .alias => |a| try self.w.print("theorem {s} = {s}\n", .{ displayName(self.text(a.name)), self.text(a.target) }),
            },
            .axiom => |a| try self.factOrAlias("axiom", a),
            .hole => |a| try self.factOrAlias("hole", a),
            else => try self.w.writeAll("// (not a fact declaration)\n"),
        }
    }

    fn factOrAlias(self: *Renderer, kw: []const u8, a: ast.Axiom) Error!void {
        switch (a) {
            .local => |f| try self.factHead(kw, f),
            .alias => |al| try self.w.print("{s} {s} = {s}\n", .{ kw, displayName(self.text(al.name)), self.text(al.target) }),
        }
    }

    /// `<kw> <name>[(p: A -> B, x: S)]: <formula>\n`
    fn factHead(self: *Renderer, kw: []const u8, f: ast.Fact) Error!void {
        try self.w.print("{s} {s}", .{ kw, displayName(self.text(f.name)) });
        // a non-null but EMPTY param list is a schema with no params (a producer's context-free
        // synthetic); `()` is not grammar, so it prints as a plain fact.
        if (f.params) |ps| if (ps.len > 0) {
            try self.w.writeAll("(");
            for (ps, 0..) |prm, i| {
                if (i > 0) try self.w.writeAll(", ");
                try self.w.print("{s}: ", .{self.text(prm.name)});
                for (prm.arg_sorts) |s| try self.w.print("{s} -> ", .{self.text(s)});
                try self.w.writeAll(self.text(prm.result));
            }
            try self.w.writeAll(")");
        };
        try self.w.writeAll(": ");
        try self.expr(f.formula);
        try self.w.writeAll("\n");
    }

    /// One pending block of steps. A frame renders its `header` (a case arm's `@arm |` /
    /// `assume … {`) when first entered and its `closer` when exhausted.
    const Frame = struct {
        steps: []const ast.Step,
        idx: usize = 0,
        depth: u32,
        header: ?ast.Step.CaseBlock.Arm = null,
        closer: ?[]const u8 = null,
    };

    /// Render a proof body. ITERATIVE over block nesting (an explicit frame stack — no
    /// recursion): a block step prints its header line(s) and pushes a frame for its body.
    fn steps(self: *Renderer, top: []const ast.Step) Error!void {
        var stack: std.ArrayList(Frame) = .empty;
        try stack.append(self.arena, .{ .steps = top, .depth = 1 });
        while (stack.items.len > 0) {
            const last = stack.items.len - 1;
            const fr = stack.items[last];
            if (fr.idx == 0) if (fr.header) |arm| {
                const pad = try self.indent(fr.depth - 1);
                try self.w.print("{s}@{s} |\n{s}  assume ", .{ pad, try self.label(arm.label), pad });
                try self.expr(arm.assumption);
                try self.w.writeAll(" {\n");
            };
            if (fr.idx >= fr.steps.len) {
                if (fr.closer) |c| try self.w.writeAll(c);
                _ = stack.pop();
                continue;
            }
            stack.items[last].idx += 1;
            const s = fr.steps[fr.idx];
            const depth = fr.depth;
            const pad = try self.indent(depth);
            const closer = try std.fmt.allocPrint(self.arena, "{s}  }}\n", .{pad});
            try self.w.print("{s}@{s} |\n{s}  ", .{ pad, try self.label(s.label), pad });
            switch (s.body) {
                .claim => |c| {
                    try self.expr(c.formula);
                    try self.w.print("\n{s}  [", .{pad});
                    try self.justification(c);
                    try self.w.writeAll("]\n");
                },
                .assume => |b| {
                    try self.w.writeAll("assume ");
                    try self.expr(b.formula);
                    try self.w.writeAll(" {\n");
                    try stack.append(self.arena, .{ .steps = b.steps, .depth = depth + 1, .closer = closer });
                },
                .fix => |b| {
                    try self.w.print("fix {s}: {s} {{\n", .{ self.text(b.name), self.text(b.sort) });
                    try stack.append(self.arena, .{ .steps = b.steps, .depth = depth + 1, .closer = closer });
                },
                .unpack => |b| {
                    try self.w.print("unpack {s}: {s} from {s} {{\n", .{ self.text(b.name), self.text(b.sort), self.text(b.from) });
                    try stack.append(self.arena, .{ .steps = b.steps, .depth = depth + 1, .closer = closer });
                },
                .case => |b| {
                    try self.expr(b.goal);
                    try self.w.print("\n{s}  case {s} {{\n", .{ pad, self.text(b.disj) });
                    // the case's own closer, then its arms (reversed, so they pop in order);
                    // each arm is an assume-block one level in, its body one further.
                    try stack.append(self.arena, .{ .steps = &.{}, .depth = depth, .closer = closer });
                    const arm_pad = try self.indent(depth + 1);
                    var i: usize = b.arms.len;
                    while (i > 0) {
                        i -= 1;
                        try stack.append(self.arena, .{
                            .steps = b.arms[i].steps,
                            .depth = depth + 2,
                            .header = b.arms[i],
                            .closer = try std.fmt.allocPrint(self.arena, "{s}  }}\n", .{arm_pad}),
                        });
                    }
                },
            }
        }
    }

    /// The bracket body of a claim: `<by|using> <rule>[ SCHEMA|(theory)][(args)][ fallback(t)][ refs…]`.
    fn justification(self: *Renderer, c: ast.Step.Claim) Error!void {
        const rule = self.text(c.rule);
        try self.w.print("{s} {s}", .{ @tagName(c.kind), rule });
        if (c.schema) |s| {
            // `instantiation NAME(args)` / `specialize HEAD(args)` name their head bare; a
            // theory-parameterized tactic takes `(theory)`.
            if (std.mem.eql(u8, rule, "instantiation") or std.mem.eql(u8, rule, "specialize"))
                try self.w.print(" {s}", .{self.text(s)})
            else
                try self.w.print("({s})", .{self.text(s)});
        }
        if (c.args.len > 0) {
            try self.w.writeAll("(");
            for (c.args, 0..) |a, i| {
                if (i > 0) try self.w.writeAll(", ");
                try self.expr(a);
            }
            try self.w.writeAll(")");
        }
        if (c.fallback) |fb| try self.w.print(" fallback({s})", .{self.text(fb)});
        for (c.refs) |r| try self.w.print(" {s}", .{try self.label(r)});
    }

    /// Two spaces per depth level.
    fn indent(self: *Renderer, depth: u32) Error![]const u8 {
        const buf = try self.arena.alloc(u8, depth * 2);
        @memset(buf, ' ');
        return buf;
    }

    // -- expressions --

    const Act = union(enum) {
        text: []const u8,
        node: struct { e: *const ast.Expr, paren: bool },
    };

    /// Render an expression. ITERATIVE (an explicit action stack — no recursion): expanding a
    /// node pushes its pieces REVERSED so they pop in emission order. Parentheses follow the
    /// parser's grammar so the output re-parses: the mixed-boolean-operator rule (a different
    /// boolean operator as an operand is parenthesized), `->` right-associative, and/or/iff
    /// left-associative, a quantifier only bare as the right side of `->`.
    fn expr(self: *Renderer, e0: *const ast.Expr) Error!void {
        var stack: std.ArrayList(Act) = .empty;
        try stack.append(self.arena, .{ .node = .{ .e = e0, .paren = false } });
        while (stack.pop()) |act| switch (act) {
            .text => |s| try self.w.writeAll(s),
            .node => |n| {
                var acts: std.ArrayList(Act) = .empty;
                if (n.paren) try acts.append(self.arena, .{ .text = "(" });
                switch (n.e.*) {
                    .name => |t| try acts.append(self.arena, .{ .text = self.text(t) }),
                    .call => |c| {
                        try acts.append(self.arena, .{ .text = try std.fmt.allocPrint(self.arena, "{s}(", .{self.text(c.callee)}) });
                        for (c.args, 0..) |a, i| {
                            if (i > 0) try acts.append(self.arena, .{ .text = ", " });
                            try acts.append(self.arena, .{ .node = .{ .e = a, .paren = false } });
                        }
                        try acts.append(self.arena, .{ .text = ")" });
                    },
                    .binary => |b| {
                        try acts.append(self.arena, .{ .node = .{ .e = b.lhs, .paren = needParen(b.op, b.lhs, .left) } });
                        try acts.append(self.arena, .{ .text = opText(b.op) });
                        try acts.append(self.arena, .{ .node = .{ .e = b.rhs, .paren = needParen(b.op, b.rhs, .right) } });
                    },
                    .not => |nn| {
                        try acts.append(self.arena, .{ .text = "not " });
                        try acts.append(self.arena, .{ .node = .{ .e = nn.operand, .paren = switch (nn.operand.*) {
                            .binary, .quant, .lambda => true,
                            .name, .call, .not => false,
                        } } });
                    },
                    .quant => |q| {
                        try acts.append(self.arena, .{ .text = if (q.q == .forall) "forall " else "exists " });
                        try acts.append(self.arena, .{ .text = try self.binders(q.binders) });
                        try acts.append(self.arena, .{ .text = "; " });
                        try acts.append(self.arena, .{ .node = .{ .e = q.body, .paren = false } });
                    },
                    .lambda => |l| {
                        try acts.append(self.arena, .{ .text = "fun " });
                        try acts.append(self.arena, .{ .text = try self.binders(l.binders) });
                        try acts.append(self.arena, .{ .text = " => " });
                        try acts.append(self.arena, .{ .node = .{ .e = l.body, .paren = false } });
                    },
                }
                if (n.paren) try acts.append(self.arena, .{ .text = ")" });
                var i: usize = acts.items.len;
                while (i > 0) {
                    i -= 1;
                    try stack.append(self.arena, acts.items[i]);
                }
            },
        };
    }

    /// `x, y: S[ where g]` — a binder list shares one sort/guard by construction (the parser
    /// reads one `names: sort` group per quantifier; delaboration emits one binder per level).
    fn binders(self: *Renderer, bs: []const ast.Binder) Error![]const u8 {
        var out: std.Io.Writer.Allocating = .init(self.arena);
        const w = &out.writer;
        for (bs, 0..) |b, i| {
            if (i > 0) try w.writeAll(", ");
            try w.writeAll(self.text(b.name));
        }
        if (bs.len > 0) {
            try w.print(": {s}", .{self.text(bs[0].sort)});
            if (bs[0].guard) |g| try w.print(" where {s}", .{self.text(g)});
        }
        return out.toOwnedSlice();
    }
};

fn opText(op: ast.Expr.BinOp) []const u8 {
    return switch (op) {
        .implies => " -> ",
        .and_op => " and ",
        .or_op => " or ",
        .iff => " iff ",
        .equal => " = ",
        .not_equal => " != ",
    };
}

fn isBoolean(op: ast.Expr.BinOp) bool {
    return switch (op) {
        .implies, .and_op, .or_op, .iff => true,
        .equal, .not_equal => false,
    };
}

const Side = enum { left, right };

/// Must `child`, as the `side` operand of a binary `op`, be parenthesized to re-parse as the
/// same tree? (See `parser.parseExpr` / `requireExplicit`.)
fn needParen(op: ast.Expr.BinOp, child: *const ast.Expr, side: Side) bool {
    switch (child.*) {
        .name, .call => return false,
        .not => return isBoolean(op), // the paren rule: `not` under a boolean operator
        .quant, .lambda => return !(op == .implies and side == .right), // `->`'s rhs is a full expr
        .binary => |cb| {
            if (!isBoolean(op)) return true; // a comparison's operands are unary-level
            if (!isBoolean(cb.op)) return false; // `a = b and …`: comparisons bind tighter
            if (cb.op != op) return true; // the mixed-boolean-operator rule
            // same operator: `->` is right-associative, and/or/iff left-associative.
            return if (op == .implies) side == .left else side == .right;
        },
    }
}

// --- selector resolution -----------------------------------------------------------------

/// The rule-token offset of the first claim step whose text spans `line` (1-based): a step
/// runs from its label line through its `[by …]` line, so the user may point at the label, the
/// formula, or the justification. Walks every proof in the file; the lowest offset wins.
fn lineToStepOffset(source: []const u8, file: ast.File, line: usize) ?u32 {
    var best: ?u32 = null;
    for (file.decls) |*d| {
        const steps = declSteps(d) orelse continue;
        var it: StepIter = .{};
        var buf: [256]ast.Step = undefined;
        it.start(&buf, steps);
        while (it.next()) |s| {
            if (s.body != .claim) continue;
            const c = s.body.claim;
            const first = offsetLine(source, s.label.start);
            const last = offsetLine(source, c.rule.start);
            if (line >= first and line <= last) {
                if (best == null or c.rule.start < best.?) best = c.rule.start;
            }
        }
    }
    return best;
}

/// The rule-token offset of claim step `label` in the proof named `theorem` (a plain theorem
/// or a proof-carrying schema). A block-opening label has no single tactic → null.
fn stepLabelOffset(source: []const u8, file: ast.File, theorem: []const u8, label: []const u8) ?u32 {
    for (file.decls) |*d| {
        const nm = declName(source, d) orelse continue;
        if (!std.mem.eql(u8, nm, theorem)) continue;
        const steps = declSteps(d) orelse return null;
        var it: StepIter = .{};
        var buf: [256]ast.Step = undefined;
        it.start(&buf, steps);
        while (it.next()) |s| {
            if (!std.mem.eql(u8, stripAt(source[s.label.start..s.label.end]), label)) continue;
            return if (s.body == .claim) s.body.claim.rule.start else null;
        }
        return null;
    }
    return null;
}

/// The `fallback(<thm>)` token of the claim step whose rule token sits at `offset`, if any.
fn fallbackAt(file: ast.File, offset: u32) ?Token {
    for (file.decls) |*d| {
        const steps = declSteps(d) orelse continue;
        var it: StepIter = .{};
        var buf: [256]ast.Step = undefined;
        it.start(&buf, steps);
        while (it.next()) |s| {
            if (s.body == .claim and s.body.claim.rule.start == offset) return s.body.claim.fallback;
        }
    }
    return null;
}

/// Pre-order iteration over a proof's steps, descending into every block (assume/fix/unpack/
/// case arms). An explicit LIFO in a fixed buffer (no recursion, no allocation): a block's
/// children are pushed reversed so they pop front-to-back right after their parent. Proof
/// nesting is shallow; the buffer bounds the pending (unvisited) siblings, not the depth.
const StepIter = struct {
    buf: []ast.Step = &.{},
    len: usize = 0,

    fn start(self: *StepIter, buf: []ast.Step, steps: []const ast.Step) void {
        self.buf = buf;
        self.len = 0;
        self.pushReversed(steps);
    }

    fn pushReversed(self: *StepIter, steps: []const ast.Step) void {
        var i: usize = steps.len;
        while (i > 0) {
            i -= 1;
            if (self.len == self.buf.len) return; // pathological breadth: stop descending
            self.buf[self.len] = steps[i];
            self.len += 1;
        }
    }

    fn next(self: *StepIter) ?ast.Step {
        if (self.len == 0) return null;
        self.len -= 1;
        const s = self.buf[self.len];
        switch (s.body) {
            .claim => {},
            .assume => |b| self.pushReversed(b.steps),
            .fix => |b| self.pushReversed(b.steps),
            .unpack => |b| self.pushReversed(b.steps),
            .case => |b| {
                var i: usize = b.arms.len;
                while (i > 0) {
                    i -= 1;
                    self.pushReversed(b.arms[i].steps);
                }
            },
        }
        return s;
    }
};

fn declSteps(d: *const ast.Decl) ?[]const ast.Step {
    return switch (d.*) {
        .theorem => |t| switch (t) {
            .local => |l| l.steps,
            .alias => null,
        },
        else => null,
    };
}

fn declName(source: []const u8, d: *const ast.Decl) ?[]const u8 {
    return switch (d.*) {
        .theorem => |t| switch (t) {
            .local => |l| source[l.fact.name.start..l.fact.name.end],
            .alias => null,
        },
        else => null,
    };
}

fn stripAt(s: []const u8) []const u8 {
    return if (s.len > 0 and s[0] == '@') s[1..] else s;
}

fn offsetLine(source: []const u8, offset: u32) usize {
    var line: usize = 1;
    for (source[0..@min(offset, source.len)]) |ch| {
        if (ch == '\n') line += 1;
    }
    return line;
}

fn renderDiagnostics(arena: Allocator, files: []const diagnostics.FileSrc, sink: *diagnostics.Sink) Allocator.Error!Result {
    var out: std.Io.Writer.Allocating = .init(arena);
    sink.render(&out.writer, files) catch return error.OutOfMemory;
    return .{ .text = try out.toOwnedSlice(), .ok = false };
}

fn fail(arena: Allocator, comptime fmt: []const u8, args: anytype) Allocator.Error!Result {
    const msg = try std.fmt.allocPrint(arena, "error: " ++ fmt ++ "\n", args);
    return .{ .text = msg, .ok = false };
}

// --- tests -------------------------------------------------------------------------------

const testing = std.testing;

const test_source =
    \\sort Nat
    \\const ZERO: Nat
    \\func succ(n: Nat): Nat
    \\func add(a: Nat, b: Nat): Nat
    \\pred even(n: Nat)
    \\axiom addZeroLeft: forall b: Nat; add(ZERO, b) = b
    \\theorem shape(prop: Nat -> Prop, k: Nat): forall x, y: Nat; (even(x) and (not even(y))) -> add(x, y) != ZERO -> exists z: Nat; add(z, z) = x
    \\proof
    \\  @generalize |
    \\    fix x: Nat {
    \\      @given |
    \\        assume even(x) or (even(x) -> even(x)) {
    \\          @restated |
    \\            even(x) or (even(x) -> even(x))
    \\            [by hypothesis given]
    \\          @split |
    \\            even(x)
    \\            case restated {
    \\              @left |
    \\                assume even(x) {
    \\                  @l1 |
    \\                    even(x)
    \\                    [by hypothesis left]
    \\                }
    \\              @right |
    \\                assume even(x) -> even(x) {
    \\                  @r1 |
    \\                    even(x)
    \\                    [using arithmetic(peano) fallback(addZeroLeft) restated]
    \\                }
    \\            }
    \\          @inst |
    \\            forall b: Nat; add(ZERO, b) = b
    \\            [using instantiation addZeroLeft(fun n: Nat => even(n), succ(ZERO))]
    \\          @spec |
    \\            add(ZERO, ZERO) = ZERO
    \\            [using specialize addZeroLeft(ZERO)]
    \\          @elim |
    \\            add(ZERO, ZERO) = ZERO
    \\            [by forall_elim(ZERO) inst]
    \\        }
    \\    }
    \\qed
    \\
;

fn parseTest(arena: Allocator, source: []const u8) !ast.File {
    const sink = try arena.create(diagnostics.Sink);
    sink.* = .init(arena);
    var p: parser.Parser = .init(arena, source, sink);
    const file = try p.parseFile();
    try testing.expectEqual(@as(usize, 0), sink.list.items.len);
    return file;
}

test "tokenText: a synthetic `x#3` token prints `x`; a real token prints its source span" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var interner = try InternPool.init(arena);
    const synthetic: Token = .{ .tag = .identifier, .start = 0, .end = 0, .name = try interner.internString("x#3") };
    try testing.expectEqualStrings("x", tokenText(&interner, "unused", synthetic));
    const plain: Token = .{ .tag = .identifier, .start = 0, .end = 0, .name = try interner.internString("plain") };
    try testing.expectEqualStrings("plain", tokenText(&interner, "", plain));
    const real: Token = .{ .tag = .identifier, .start = 4, .end = 7 };
    try testing.expectEqualStrings("foo", tokenText(&interner, "abc foo", real));
}

test "renderDecl: the reprint RE-PARSES to the same tree (render ∘ parse is idempotent) and keeps every construct" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    var interner = try InternPool.init(arena);
    const file = try parseTest(arena, test_source);
    const decl = &file.decls[file.decls.len - 1];
    const once = try renderDecl(arena, &interner, test_source, decl);
    // the reprint parses clean and renders IDENTICALLY (a fixed point = no information lost
    // in either direction: precedence, parens, blocks, case arms, every justification shape).
    const again = try parseTest(arena, once);
    const twice = try renderDecl(arena, &interner, once, &again.decls[again.decls.len - 1]);
    try testing.expectEqualStrings(once, twice);
    // spot-check the shapes that need care.
    try testing.expect(std.mem.indexOf(u8, once, "theorem shape(prop: Nat -> Prop, k: Nat): forall x, y: Nat; (even(x) and (not even(y))) -> add(x, y) != ZERO -> exists z: Nat; add(z, z) = x\n") != null);
    try testing.expect(std.mem.indexOf(u8, once, "assume even(x) or (even(x) -> even(x)) {") != null);
    try testing.expect(std.mem.indexOf(u8, once, "case restated {") != null);
    try testing.expect(std.mem.indexOf(u8, once, "[using arithmetic(peano) fallback(addZeroLeft) restated]") != null);
    try testing.expect(std.mem.indexOf(u8, once, "[using instantiation addZeroLeft(fun n: Nat => even(n), succ(ZERO))]") != null);
    try testing.expect(std.mem.indexOf(u8, once, "[using specialize addZeroLeft(ZERO)]") != null);
    try testing.expect(std.mem.indexOf(u8, once, "[by forall_elim(ZERO) inst]") != null);
}

test "needParen: `->` is right-associative, and/or left-associative, mixed boolean operators and quantifiers parenthesize" {
    const a: ast.Expr = .{ .name = .{ .tag = .identifier, .start = 0, .end = 1 } };
    const imp: ast.Expr = .{ .binary = .{ .op = .implies, .tok = a.name, .lhs = &a, .rhs = &a } };
    const conj: ast.Expr = .{ .binary = .{ .op = .and_op, .tok = a.name, .lhs = &a, .rhs = &a } };
    const eq: ast.Expr = .{ .binary = .{ .op = .equal, .tok = a.name, .lhs = &a, .rhs = &a } };
    const q: ast.Expr = .{ .quant = .{ .q = .forall, .tok = a.name, .binders = &.{}, .body = &a } };
    try testing.expect(needParen(.implies, &imp, .left));
    try testing.expect(!needParen(.implies, &imp, .right));
    try testing.expect(!needParen(.and_op, &conj, .left));
    try testing.expect(needParen(.and_op, &conj, .right));
    try testing.expect(needParen(.implies, &conj, .right)); // mixed
    try testing.expect(!needParen(.and_op, &eq, .left)); // a comparison binds tighter
    try testing.expect(needParen(.equal, &eq, .left));
    try testing.expect(!needParen(.implies, &q, .right));
    try testing.expect(needParen(.implies, &q, .left));
    try testing.expect(needParen(.and_op, &q, .right));
}

test "selector: a line inside a nested block resolves to that step's rule token; a label inside fix/assume/case resolves; a block label does not" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const file = try parseTest(arena, test_source);
    // `@elim |` is the label line of the last claim; its rule token is on the line after next.
    const elim_label_line = offsetLine(test_source, @intCast(std.mem.indexOf(u8, test_source, "@elim |").?));
    const rule_off: u32 = @intCast(std.mem.indexOf(u8, test_source, "forall_elim(ZERO) inst").?);
    try testing.expectEqual(rule_off, lineToStepOffset(test_source, file, elim_label_line).?);
    try testing.expectEqual(rule_off, lineToStepOffset(test_source, file, elim_label_line + 2).?);
    try testing.expectEqual(rule_off, stepLabelOffset(test_source, file, "shape", "elim").?);
    // a case-arm step, by label.
    const r1_off: u32 = @intCast(std.mem.indexOf(u8, test_source, "arithmetic(peano)").?);
    try testing.expectEqual(r1_off, stepLabelOffset(test_source, file, "shape", "r1").?);
    // a block-opening label has no single tactic; an unknown theorem/label is a miss.
    try testing.expect(stepLabelOffset(test_source, file, "shape", "given") == null);
    try testing.expect(stepLabelOffset(test_source, file, "nope", "elim") == null);
    try testing.expect(lineToStepOffset(test_source, file, 1) == null);
    // the fallback token of the r1 step, and none on a plain step.
    const fb = fallbackAt(file, r1_off).?;
    try testing.expectEqualStrings("addZeroLeft", test_source[fb.start..fb.end]);
    try testing.expect(fallbackAt(file, rule_off) == null);
}
