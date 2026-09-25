# scratch-needswork — the ℚ-CUT ℤ_n path, blocked on a model-system limitation

These files record the ONE thing about ℤ_n that is architecturally blocked: building
ℤ_n over the **ℚ-cut ℤ** (composing the tower ℤ_n → ℤ → ℚ). The template itself —
`std/integer/mod-n.b4m` — works over **standalone ℤ** and has been PROMOTED to `std/`
(and is used to build the concrete ℤ_n / U(n) structures). What remains parked here is
only the ℚ-cut compositionality, which the **namespacing refactor** must unblock.

## What's here

- **`z6.b4m`** — a concrete ℤ_6 = the (now-in-std) ℤ_n template instantiated at n = 6, via a
  minimal two-line `model Z6 { N: SIX; nPositive <- sixPositive }` (`sixPositive`
  PROVED from 6 = succ⁶0). `z6AddAssoc` and `z6IsCyclic` transfer for free.
  Strict-green.
- **`overload-multisource-blocker.b4m`** — the minimal probe that exposes the
  architectural limit. It tries to OVERLOAD ℤ_n's underlying ℤ with a *foreign* carrier
  (`MyInt`) and transfer `addAssoc`; strict check demands the ℤ axioms, then the
  `one source theory` rule forbids discharging them. This is where it breaks.
- **`q-z6.b4m`** — the CONCRETE target: ℤ_6 built over the ℚ-cut ℤ
  (`rational.Integer = Q where isInteger`), composing the tower ℤ_6 → ℤ → ℚ. Does NOT
  check — it reaches the wall on purpose. It hits TWO layers: (1) guarded **cut-closure
  obligations** (`isInteger(add a b)`, provable via rational's `isIntegerAdd` but not
  threaded automatically), and (2) the **multi-source-theory discharge** restriction
  (the `integer.<axiom> <- IntegersInRational@…` lines). The mathematics is complete
  (the ℚ-cut satisfies every obligation); only the model system stands in the way.

## Why it's parked — the architectural limit

The goal was to test whether `integer-mod-n` is honestly **parametric over "an ℤ"** —
i.e. whether ℤ_n could be built over the ℤ-cut of ℚ, composing the tower
(ℤ_n → ℤ → ℚ). The finding, in order:

1. **Sorts ARE overloadable via `model`** — even the aliased `mod_n.Int = integer.Int`
   remaps onto a foreign `MyInt`, along with its operations. (An earlier belief that it
   was "welded, unremappable" was wrong.)
2. **Strict materialization correctly DEMANDS the substrate axioms.** When you transfer
   `mod_n.addAssoc` onto the foreign carrier, strict check refuses:
   `model materialization cites axiom 'addZeroLeft', which the substitution affects but
   the model does not map; add a mapping for it`. So it is NOT unsound — the transfer
   forces every ℤ ring/order axiom the proof touches to be discharged on the new
   carrier. (`--fast` trusts the model verdict and passes; strict catches it. Good.)
3. **But the model system then FORBIDS discharging it.** `mod_n`'s proofs cite
   `integer.addZeroLeft` — an axiom of a DIFFERENT theory (`integer`) that `mod_n`
   imports. Adding `integer.addZeroLeft <- …` to the model errors with:
   `all model mappings must come from one source theory`
   (enforced at **`src/elaborate.zig:661-663`**). So the obligation the kernel *requires*
   is the very obligation the model syntax *refuses to let you express*.

That contradiction is the architectural error: a model's discharge obligations
naturally SPAN multiple source theories (a theory built on another cites the lower
theory's axioms), but the elaborator restricts all mapping sources to a single file.
Overloading the substrate is therefore impossible today — not because it's unsound, but
because the discharge can't be written.

**Resolution: the namespacing refactor.** The `one source theory` restriction is
incorrect and must go (see the `namespaces-reorg-model-decisions` note). Once a model
can discharge obligations from multiple source theories, ℤ_n-over-the-ℚ-cut-ℤ should go
through — the ℚ-cut satisfies all the ℤ axioms (via rational.b4m's guarded ℤ-model), so
each demanded axiom is dischargeable. At that point `integer-mod-n` earns a real `std/`
slot as a genuinely parametric template.

## Repro

```
2b4m check scratch-needswork/integer-mod-n.b4m      # green
2b4m check scratch-needswork/z6.b4m                 # green (ℤ_6 instance)
2b4m check scratch-needswork/overload-multisource-blocker.b4m   # the block:
                                                   # "all model mappings must come from one source theory"
```
