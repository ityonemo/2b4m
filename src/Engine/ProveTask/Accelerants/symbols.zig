//! The well-known arithmetic VOCABULARY: which symbols in scope play `add`, `mul`, `succ`,
//! `ZERO`, `ONE`, `less_than`, `nonneg`, … A plain table, resolved by name in the theory
//! scope (see `Arithmetic.read`). Shared by every engine that reasons over that vocabulary —
//! the Presburger decision, the AC/tower substrate, the polynomial canonicalizer — so it lives
//! below all of them rather than inside one.

const term = @import("../../../term.zig");
const SortId = term.SortId;
const SymId = term.SymId;

/// The arithmetic vocabulary, resolved by well-known name in the use site's
/// scope. Absent names shrink the fragment; a term outside it is a located
/// error naming the term.
pub const Symbols = struct {
    /// The arithmetic sort's anchor (used only to shape countermodels / bind
    /// binders — NOT a soundness filter: the engine is sort-blind and treats
    /// any non-well-known term as a linear variable ranging over ℤ).
    nat: ?SortId = null,
    zero: ?SymId = null,
    one: ?SymId = null,
    succ: ?SymId = null,
    /// predecessor: prev(x) = x - 1 (ℤ theories; absent for ℕ).
    prev: ?SymId = null,
    add: ?SymId = null,
    mul: ?SymId = null,
    /// unary negation neg(x) = -x and total subtraction sub(a,b) = a - b
    /// (ℤ theories; absent for ℕ, whose sub is truncated monus — NOT linear).
    neg: ?SymId = null,
    sub: ?SymId = null,
    less_than: ?SymId = null,
    /// a well-known nonnegativity predicate nonneg(x) meaning x >= 0. Its
    /// PRESENCE is a theory's request to constrain its variables nonneg: the
    /// engine reads nonneg(x) hypotheses as x >= 0, and the elaborator injects
    /// nonneg(x) per bound variable when this is set. Absent → pure ℤ (no
    /// nonnegativity assumed anywhere).
    nonneg: ?SymId = null,
};
