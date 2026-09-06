//! presburger — the arithmetic-vocabulary carrier. For now this module holds ONLY the
//! `Symbols` struct: the small "which SymId is add/mul/succ/…" record the AC-reordering
//! accelerants (`assoc_commut`) thread through their flatten/build/sort substrate. The full
//! Presburger decider (quantifier elimination, Farkas certs) lands with the arithmetic
//! slice; recovering just this struct keeps the AC substrate free of that machinery while
//! preserving the shape the eager core (elaborate.zig's acPlan/buildComb/buildTower) read.
//!
//! Every field is optional: an absent symbol shrinks the fragment. The AC path reads only
//! `.add` (the reordered operator); `zero`/`succ` back the tower/comb builders (unused at
//! succs=0, kept for the eventual arithmetic reuse).

const term = @import("../../term.zig");
const SortId = term.SortId;
const SymId = term.SymId;

/// The arithmetic vocabulary, resolved by well-known name in the use site's scope. Absent
/// names shrink the fragment; a term outside it is a located error naming the term.
pub const Symbols = struct {
    nat: ?SortId = null,
    zero: ?SymId = null,
    one: ?SymId = null,
    succ: ?SymId = null,
    /// ℤ predecessor (absent for ℕ) — a negative tower offset needs it.
    prev: ?SymId = null,
    add: ?SymId = null,
    mul: ?SymId = null,
    /// additive inverse (ring theories) — polynomial's inverse-cancellation uses it.
    neg: ?SymId = null,
    /// subtraction (definitionOfSubtraction folds it away) — ring theories.
    sub: ?SymId = null,
    less_than: ?SymId = null,
};
