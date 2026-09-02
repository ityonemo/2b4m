//! Verify — which verification layers a check run enforces. Lives standalone (it used to
//! be `elaborate.Verify`; the eager Elaborator is gone). Wired from CLI flags in main.zig
//! and threaded through Context to the demand prover.
//!
//! RED-PHASE NOTE: with accelerants/schemas/imports-trust unsupported by the demand
//! prover, only `draft` is currently consulted (the use-all-facts gate). The other bits
//! keep their meaning for the Phase-5 rebuilds.

/// `by arithmetic`/`by tautology` must produce a checkable certificate (elaborated to
/// kernel steps); an accelerated fallback is a hard error. When false, take the
/// accelerated verdict and record it (disclosed in the summary).
certify_arithmetic: bool = true,
/// re-check imported theorems' proofs. When false, imported theorem bodies are trusted
/// (declarations load, proofs are not re-verified).
recheck_imports: bool = true,
/// re-check imported schemas at each instantiation. When false, a proven imported
/// schema is trusted without re-instantiating its body.
recheck_schemas: bool = true,
/// `--draft` mode: a WIP proof. The single coarse "work in progress" bit that
/// author-hygiene checks consult to relax — NOT rejecting a proof for a dead step (a
/// fact it introduces but never uses), etc. (Holes are allowed under `--draft` too,
/// gated in main.)
draft: bool = false,
