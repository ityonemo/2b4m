# Debugging a 2b4m run

`2b4m check` tells you *that* a proof failed and where. These flags and commands tell you
*why* — what the engine actually did. Reach for them when the diagnostic describes a state
you cannot account for from the source: a fact with the wrong sort, a step that fails only
in some larger run, a proof that passes alone and fails in a sweep.

## `--trace-facts` — what did this citation resolve to?

```
2b4m check --trace-facts <file | dir> [theorem]
```

Prints, for every fact citation the prover resolves, **which fact it got**: the namespace it
resolved in, the site the fact was declared at, its kind and statement, and which resolution
path produced it.

```
std/ring.b4m:212:22: cite additiveInverseUnique
    -> resolved in ns=universe, declared at std/ring.b4m:176:9
       theorem additiveInverseUnique
       forall x: Ring; forall y: Ring; add(x, y) = ZERO -> y = neg(x)
       via direct lookup
std/ring.b4m:212:22: cite additiveInverseUnique
    -> resolved in ns=model#10371, declared at std/ring.b4m:176:9
       theorem additiveInverseUnique
       forall x: Ring; forall y: Ring; add(x, y) = ZERO -> y = neg(x)
       via overlay (applyModel) under the citing task's model
```

**Why this is not answerable from the source.** A name can denote more than one fact in a
single run. Two theories may each declare a `mulIsAssociative`; more subtly, a model transfer
RE-PROVES its source theory's theorems and publishes a second copy of every one of them into
a `(model, source-file)` namespace. So "which `additiveInverseUnique` did this step cite?" has
no syntactic answer — only the run knows. The three `via` reasons:

| via | meaning |
|---|---|
| `direct lookup` | the citing task is not under a model; the name resolved in the universe |
| `overlay (applyModel) under the citing task's model` | the task IS under a model, and the name was mapped through that model's overlay — correct for a cited AXIOM (it maps to the local fact discharging it), suspicious for a theorem the citing file declares itself |
| `TRANSFER redirect …` | the cited theorem resolved to its transferred copy rather than the source |

**Reading it.** Each citation usually appears several times: the read pass and the process
pass both resolve it, and an accelerant's generated proof resolves it again. Repeats are
normal. What matters is whether the SAME citation ever resolves two different ways — that is
the shape of a collision.

The trace is buffered and printed as one block after the run, before the verdict. It has to
be: the demand engine interleaves tasks, so writing each line as it is produced shreds them
into each other. It never affects the verdict.

**The lifecycle lines.** The same flag also prints what the SCHEDULER did, interleaved in
order with the citations — because a resolution is only wrong relative to what was in
flight at that moment:

```
[parse] task#19 = std/group.b4m
[model] task#475 = model AdditiveGroup in file#120
[prove] task#447 = additiveInverseUnique in ns#10372 (model#10371)
[engine] rack task#447 (on task#43)        racked BY task#43
[engine] run task#447
[engine] park task#447 (on task#475)       suspended, waiting for task#475
[engine] wake task#447 (on task#475)       task#475 finished; #447 back on the queue
[engine] done task#447
[read pass] transferred copy of mulNegRight under model#10371: in_flight owned by ANOTHER task — …
```

`[prove]`/`[fetch]`/`[model]`/`[parse]` lines give a task number its identity (a ProveTask's
name, namespace and model; a ModelTask's model; a file's parse). `[read pass]` lines report
what a citing task's read pass saw for a transferred copy: `ABSENT -> racking`, `proven`, or
`in_flight owned by ANOTHER task` — the last is the state that must SUSPEND the citer.

**One fact to hold onto:** the run queue is a STACK. `run` pops the most recently racked or
woken task, so a root racked early (a file early in sorted order) sits at the bottom and
parses LAST, and everything that can proceed without it does — which is how a task ends up
claimed-but-unfinished for tens of thousands of trace lines while later tasks run to
completion above it. Do not reason about interleavings from source order; read the trace.
To follow a suspicious task: find its `[prove]` line, then `grep -n "task#N\b"` for its
rack/run/park/wake/done, then identify what it parks on the same way.

**Scale.** A whole-corpus sweep produces thousands of lines (`2b4m check std --trace-facts` is
~60,000 with the lifecycle lines). Narrow first — `2b4m check <file> <theorem> --trace-facts` traces one proof — or pipe
to `grep -A4 "cite <name>"`.

## `--axioms` — what does this proof rest on?

```
2b4m check <file> [theorem] --axioms
```

Every axiom the checked theorem(s) transitively bottom out in, with declaration sites. It
follows the demand graph, so it sees axioms reached through accelerant certificates,
`instantiation`, model transfers and imports — which `2b4m query uses`, a syntactic scan,
cannot. A `hole` is an axiom to the kernel, so it is listed and marked, and therefore only
appears under `--draft`. Useful beyond auditing: if a proof rests on something surprising,
the surprise is usually the bug.

## `2b4m debug accelerant` — what proof did this tactic generate?

```
2b4m debug accelerant <file> <line | theorem step-label>
```

Reprints the synthetic theorem an accelerated step produced — statement and proof, as valid
2b4m that round-trips through `check`. When a `[using arithmetic …]` step fails for reasons the
message does not explain, this shows the certificate the tactic actually built, including
which lemmas it cited by name (a frequent cause: a well-known lemma the citing file does not
have in scope).

## `2b4m debug taint` — where does trust enter?

```
2b4m debug taint <file> [theorem]
```

Per proof, every step whose rule *can* fall back to an accelerated verdict, at its
`file:line:col`. A syntactic upper bound — a flagged step may still certify — so a clean
report guarantees every step is kernel-checked, while a flagged one is only a candidate.

## `--chaos[=SEED]` — does the output depend on the schedule?

```
2b4m check --chaos=42 <file | dir>
```

Shuffles the engine's scheduling order under a fixed seed. The run does the same WORK in a
different ORDER: a different task is pulled each time, so suspensions and wakeups interleave
differently, deterministically per seed.

This exists to TEST the determinism contract: output is a function of (tree, roots), never
of scheduling — that is what the goldens encode, and what lets the engine reorder freely.
So the check is a diff:

```
2b4m check std > base.txt
for s in 1 2 3 7 42 99; do 2b4m check std --chaos=$s | diff base.txt - || echo "seed $s DIFFERS"; done
```

Any difference is a determinism BUG — something leaked task order into output (an
append-ordered list printed as-is, a count taken from scheduling, a hashmap iterated into a
message). Because it is single-threaded and seeded, the failing schedule replays exactly,
which is why this is worth reaching for BEFORE blaming a race.

Note `--trace-facts` is deliberately exempt: it is a view OF the schedule, so its output is
*expected* to change under `--chaos`. Never put it in a golden.

## Which to reach for

| symptom | tool |
|---|---|
| a fact has the wrong sort, or a name seems to mean two things | `--trace-facts` |
| passes alone, fails in a directory sweep | `--trace-facts` on the sweep, grep the name |
| "reference not found" inside a generated proof | `2b4m debug accelerant` on the step |
| a proof depends on something it shouldn't | `--axioms` |
| is this really kernel-checked? | `2b4m debug taint`, then plain `2b4m check` |
| output changed and the source didn't | `--chaos` sweep: if seeds disagree, it's a determinism bug |

## `--fast` must never error where strict does not

That is an INVARIANT (user ruling 2026-10-06), and it has been violated three distinct ways.
All three come from the same root: an ADMITTED accelerant builds no certificate, so nothing
carries the citation edges its proof would have had, and the use-all-facts walk then calls the
steps it consumed dead. Strict never notices, because there the accelerant lowers to real steps
whose refs the walk sees.

Sweep for it with:

```
for f in $(find std -name '*.b4m'); do
  2b4m check "$f" >/dev/null 2>&1 || continue          # strict must pass
  2b4m check --fast "$f" >/dev/null 2>&1 || echo "VIOLATION $f"
done
```

At the time of writing that found 6 of 98 files; all four causes below are now fixed.

**FIXED — a `specialize` head that is a local step.** `specialize HEAD(args)` carries its head
in the claim's `schema` slot, NOT `refs`, and the head may be a local step label. The admit path
seeds cited steps as roots but walked `refs` only. (`std/permutation/listing.b4m`, 3 steps.)
Gate: `tests/cases/fast_specialize_head_root.b4m`.

**FIXED — a qualified ref leaked a diagnostic.** `localName` rejects a `ns.`-qualified token by
DIAGNOSING it and returning an error; the seeding loop caught the error and continued, which
does not unwrite the diagnostic. A `simplify` whose rewrite set names `peano.mulAddDistribLeft`
then failed under `--fast` only. Fix: skip qualified tokens BEFORE the call (`seedLocalRoot`).
(`std/peano/order.b4m`, `peano/subtraction.b4m`, `integer/mod-n-product.b4m`.)

**FIXED — an admitted `import` of a re-export alias.** `[using import(I) thm]` is admitted by
α-matching `thm`'s STATED formula; a re-export (`theorem sqrtOne = sqrt_theory.sqrtOne`) has
none — identity is by ORIGIN. Fix: `factOrigin` follows the chain (as strict does via
`ProveTask.factAlias`), and the read pass drives the whole admission into a scratch pool so
every demand it raises is settled while suspending is still legal. NOTE the suspension was in
`resolveRefs` on the ORIGIN's formula, not in the parse — two wrong diagnoses before a
`std.debug.print` at the failing point settled it. Gate: `tests/cases/fast_import_alias/`.

**FIXED — a guarded-sort obligation's discharger.** Specializing a lemma whose binder is a
REFINED sort (`forall f: Perm`, i.e. `Fn where invertible`) owes `invertible(arg)`. Strict meets
it while instantiating the synthetic: `Elab.emitArgObligations` sees the refined param sort and
calls `requireKnown` → `dischargeGoal` → `refForKnown`, which appends the supplying step to
`known.reachable` — the walk's seed list. `produceSpecialize` returns at its `admit_mode`
check before resolving the head at all, so an admitted step contributes NO such edge.

The guard is meant to be FOUND, not named. It is a well-formedness side condition on a term the
author wrote, fully determined by the term plus the sort declaration; the only open question is
"is it known in scope?", which is exactly `requireKnown`'s search. (A first fix, `guards(<step>)`
syntax, was built and REVERTED: it made authors spell out hypothesis restatements the checker
can and should find — and a flat-list variant was positionally ambiguous, since 22 of 43 sites
carry both guards and hypothesis refs and some need two guards.)

So the fix is to the LINT, not the search: the use-all-facts check is a lint over a COMPLETE
citation graph, and with an admitted step in the proof the graph is incomplete, so it can only
false-positive. It now runs only on a proof with no admitted step (`Prove.zig`, at the
`checkAllStepsUsed` call). Strict always runs it, and strict is the gate.

**WHEN TO RUMMAGE (user ruling 2026-10-07).** Search for guard obligations — refined-sort
qualifiers, `requires` guards. NEVER search for an accelerant's LOGICAL INPUTS — the hyps
`specialize` discharges, `chain`'s equations, `simplify`'s rewrites, `tautology`'s premises:
those are what the inference consumes and are always named, as a plain list after the rule's own
arguments: `[using accelerant accelerator_args(...) input1 input2 …]`. The engine already draws
this line (`withGuardPremises` searches only the leading antecedents `wrapObligations` hoisted).

Minimal repro (8 declarations, no imports) — `tests/cases/guarded_sort_obligation_root.b4m`,
gated both ways:

```2b4m
sort Element
sort Fn
pred invertible(f: Fn)
sort Perm = Fn where invertible
func apply(f: Fn, x: Element) => Element
const point: Element

axiom permFixesPoint: forall f: Perm; apply(f, point) = point

// strict: OK. `--fast`: "unused fact: step 'g-invertible' is never used".
theorem aGuardDischargerIsNotDead: forall g: Fn; invertible(g) -> apply(g, point) = point
proof
  @generalize-g |
    fix g: Fn {
      @given-invertible |
        assume invertible(g) {
          @g-invertible |
            invertible(g)
            [by hypothesis given-invertible]
          @applied |
            apply(g, point) = point
            [using specialize permFixesPoint(g)]
        }
      @conclusion-implication |
        invertible(g) -> apply(g, point) = point
        [by implies_intro given-invertible]
    }
  @conclusion |
    forall g: Fn; invertible(g) -> apply(g, point) = point
    [by forall_intro generalize-g]
qed
```

TRAP met while investigating: the 8 live instances (`dihedral.b4m` ×6, `decomposition.b4m`
×1, `dihedral-orders.b4m` ×1) LOOKED like dead code, and removing one leaves the theorem count
unchanged — because the guard obligation then finds ANOTHER discharger in scope. They are
load-bearing. When `--fast` and strict disagree on an unused-fact error, `--fast` is the broken
side; do not delete the step.
