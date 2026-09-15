# Debugging a bpa run

`bpa check` tells you *that* a proof failed and where. These flags and commands tell you
*why* — what the engine actually did. Reach for them when the diagnostic describes a state
you cannot account for from the source: a fact with the wrong sort, a step that fails only
in some larger run, a proof that passes alone and fails in a sweep.

## `--trace-facts` — what did this citation resolve to?

```
bpa check --trace-facts <file | dir> [theorem]
```

Prints, for every fact citation the prover resolves, **which fact it got**: the namespace it
resolved in, the site the fact was declared at, its kind and statement, and which resolution
path produced it.

```
std/ring.bpa:212:22: cite additiveInverseUnique
    -> resolved in ns=universe, declared at std/ring.bpa:176:9
       theorem additiveInverseUnique
       forall x: Ring; forall y: Ring; add(x, y) = ZERO -> y = neg(x)
       via direct lookup
std/ring.bpa:212:22: cite additiveInverseUnique
    -> resolved in ns=model#10371, declared at std/ring.bpa:176:9
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

**Scale.** A whole-corpus sweep produces thousands of lines (`bpa check std --trace-facts` is
~8000). Narrow first — `bpa check <file> <theorem> --trace-facts` traces one proof — or pipe
to `grep -A4 "cite <name>"`.

## `--axioms` — what does this proof rest on?

```
bpa check <file> [theorem] --axioms
```

Every axiom the checked theorem(s) transitively bottom out in, with declaration sites. It
follows the demand graph, so it sees axioms reached through accelerant certificates,
`instantiation`, model transfers and imports — which `bpa query uses`, a syntactic scan,
cannot. A `hole` is an axiom to the kernel, so it is listed and marked, and therefore only
appears under `--draft`. Useful beyond auditing: if a proof rests on something surprising,
the surprise is usually the bug.

## `bpa debug accelerant` — what proof did this tactic generate?

```
bpa debug accelerant <file> <line | theorem step-label>
```

Reprints the synthetic theorem an accelerated step produced — statement and proof, as valid
bpa that round-trips through `check`. When a `[using arithmetic …]` step fails for reasons the
message does not explain, this shows the certificate the tactic actually built, including
which lemmas it cited by name (a frequent cause: a well-known lemma the citing file does not
have in scope).

## `bpa debug taint` — where does trust enter?

```
bpa debug taint <file> [theorem]
```

Per proof, every step whose rule *can* fall back to an accelerated verdict, at its
`file:line:col`. A syntactic upper bound — a flagged step may still certify — so a clean
report guarantees every step is kernel-checked, while a flagged one is only a candidate.

## Which to reach for

| symptom | tool |
|---|---|
| a fact has the wrong sort, or a name seems to mean two things | `--trace-facts` |
| passes alone, fails in a directory sweep | `--trace-facts` on the sweep, grep the name |
| "reference not found" inside a generated proof | `bpa debug accelerant` on the step |
| a proof depends on something it shouldn't | `--axioms` |
| is this really kernel-checked? | `bpa debug taint`, then plain `bpa check` |
