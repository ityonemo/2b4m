RESOLVED 2026-10-03 — see tests/cases/model_schema_transfer.b4m for the regression guard and
README.md for what remains (the accelerant path). The original analysis is kept below because
the reasoning was partly WRONG and the correction is the useful part.

WHAT I GOT WRONG. I identified the two-space args bug correctly, then retracted it after reading
ProveTask.zig:667 ("the same map when they are the same slice — no model transfer") and
concluding that identical slices were correct for an ordinary citing proof. That comment's
parenthetical is the trap: it assumes the two spaces coincide only when there is NO transfer,
but a no-discharge cite IS a transfer (the instance runs under the cite's model) while passing
identical slices. So the retraction was wrong and the original diagnosis was right.

WHAT ALSO WASN'T THE FIX. Binding the twin by re-reading the arg in source space
(`bindSchemaArgs(..., source_space=true)`, which is what demandInstance does) does not work
here: it calls `sourceExpr`, and `source_ast` is populated only for a proof that is itself a
transfer. The author writes the lambda ONCE in target terms, so there is no source twin to read.
The working fix reuses the BOUND body and restates only the recorded sorts on the source side.

HOW IT WAS FOUND. Reading the code produced two wrong answers; instrumenting produced the right
one in one step. Printing the quantifier binder's sort alongside `self.model` and
`self.source_space` at Elab.zig:277 showed, immediately:

    [dbg] quant binder sort=Thing model=@enumFromInt(69) source_space=false
    [dbg] quant binder sort=Elem  model=.universe        source_space=true

— the source-space pass elaborating the body with no model, against a target-space lambda.

================================ ORIGINAL ANALYSIS ================================

WHY A PLAIN THEOREM TRANSFERS THROUGH A MODEL BUT A SCHEMA DID NOT
(repro: src.b4m + consumer.b4m — two theorems differing ONLY in a predicate parameter;
 probe.b4m + probe2.b4m — the same with no constants, isolating binder sorts)

THE ANSWER: a schema SHOULD transfer. Nothing structural prevents it. The mechanism is all
present and the obstacle is a bug I introduced in 7cf3c94.

A schema instance's body is re-checked at the instance (ProveTask.zig:236, `proveSteps`), and
`buildInstanceState` already sets `prove.model = task.model` with the comment "so the
monomorphized body is in target terms". Sort resolution is model-aware throughout —
`Elab.lookupIdent` and `resolveSymbolTok` both end in `applyModel`. So a transferred schema's
binder sorts DO remap.

What breaks is the ARGUMENTS. `demandInstance` (the plain-`instantiation` path) binds them
TWICE:

    const args        = bindSchemaArgs(e,  rs, c, false);  // TARGET space
    const args_source = bindSchemaArgs(sp, rs, c, true);   // SOURCE space twin

and hands the instance both, because a transferred proof runs passes in BOTH spaces — the
statement in target terms, source-space accelerant twins in source terms.

My no-discharge path in 7cf3c94 binds ONCE and passes the same map for both:

    break :blk .{ bound, bound };          // <-- the bug

So the source-space pass inside the instance receives TARGET-space args. Hence the error lands
inside the SOURCE file at a binder (`probe.b4m:12: expected sort 'Thing', got 'Elem'`) — the
body is in source terms, the substituted parameter is in target terms, and they disagree.

Confirming evidence: writing the lambda binder in SOURCE space
(`fun z: p.Elem => flagged(z)`) moves the error from inside the source file to the CITE
(`probe2.b4m:9: expected sort 'Thing', got 'Elem'`) — i.e. the target-space check now objects
instead. One map cannot satisfy both checks; that is precisely why there are two.

THE FIX: bind twice in the no-discharge path, exactly as `demandInstance` does — target-space
args plus a source-space twin via `sourceElab`/`sourceSpaceAccelerants`.

A SECOND, INDEPENDENT OBSTACLE (not a bug, a design question): the lambda cannot capture a
`fix`-bound variable. `demandSchemaTransfer` runs in the READ PASS, before step-local scope
exists, so `(fun g: Grp => op(t, g))` with `t` from an enclosing `fix` gives "unknown
identifier 't'". `demandInstance` avoids this by receiving the caller's live `Elab` as an
argument; the read-pass path has none. Fixing that means either deferring this demand to the
process pass or threading a scope-bearing Elab into the read pass — a real decision about pass
structure, separate from the two-space bug above.
