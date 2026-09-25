# NEXT_STEPS — status of the demand-driven prover (branch `reentrant-prover`)

The roadmap this file used to hold is complete: proving is demand-driven end to end and the
corpus (`zig build test`: std/, examples/, aata/, tests/cases/) is fully green. What landed,
in one paragraph, and what is still open.

## Landed

- **Task engine.** `ParseTask` / `FetchTask` / `ProveTask` / `ModelTask` over a run queue and a
  parked-by-blocker registry; every task suspends on what it needs and re-runs idempotently.
  Uncited files never parse; an uncited model is never built.
- **Interned entities, per-proof terms.** Named entities live in the `InternPool`; formulas are
  built in a per-`ProveTask` pool that is locally nameless and hash-consed (alpha-equal closed
  terms share one id).
- **One walk per theorem.** A `ProveTask` walks its proof's steps once, demanding non-local
  names as it meets them; obligations (refined-sort guards, `requires`, define'd guards) are
  looked up by the identity of the required proposition in what the proof has taught — never
  searched for. A statement owes nothing; a bound element owes nothing; a generated theorem
  states its preconditions as antecedents.
- **Accelerants as generated proofs.** Every `using` accelerant produces a synthetic schema
  that the ordinary pipeline proves and the kernel re-checks; `2b4m debug accelerant` prints it.
  `--fast` is a per-word admit set (accept, don't prove); `instantiation` is never admitted.
- **Models.** Structure interpretation with `:` maps and `<-` discharges, guarded targets with
  nominated dischargers, composed models for nested transfers, and schema sources discharged
  by schemas (instantiated at the citing instance's arguments).

## Open

- Cycle detection over the blocker registry (the edges exist; detection is not wired).
- Multi-threading (the KV tables have their lock discipline designed; the engine runs
  single-threaded).
- `import` as an accelerant with `--fast` parity, and the ℤ_n / model-parameter spikes — see
  the design notes (`MODEL-DESIGN.md`, `NONLINEAR-PLAN.md`) and the per-topic memory.

## Verification

`zig build test` from a clean cache is the gate. Merge to main only when it is fully green.
