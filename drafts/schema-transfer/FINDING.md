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
