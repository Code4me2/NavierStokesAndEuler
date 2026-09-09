import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Data.ENat.Monoid

/-!
# The `WithTop ℕ∞` order trivialities used by the smoothness bookkeeping

`ContDiff ℝ n f` measures smoothness in `WithTop ℕ∞`, where `∞` is the coercion
of `(⊤ : ℕ∞)` and is *not* the top element (that is `ω`).  Consequently `le_top`
does not discharge `(n : WithTop ℕ∞) ≤ ∞`, and the facts below — a finite
order is at most `∞`, whether written as a cast or as a numeral, and `∞ + 1` is
still at most `∞` — have to be quoted explicitly whenever a `ContDiff ℝ ∞`
hypothesis is specialised to a finite order.

They all live in the root namespace so that every module of the development,
whatever namespace it opens, can use them under their bare names.
-/

open scoped ContDiff

/-- A finite smoothness order is at most `∞`. -/
theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- A numeral smoothness order is at most `∞`.  This is `natCast_le_infty` in
the shape the elaborator produces for a literal such as `(2 : WithTop ℕ∞)`. -/
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : WithTop ℕ∞) ≤ ∞ :=
  natCast_le_infty (OfNat.ofNat n)

/-- Losing one derivative from `∞` still leaves `∞`. -/
theorem infty_add_one_le_infty : (∞ : WithTop ℕ∞) + 1 ≤ ∞ :=
  le_of_eq ENat.coe_top_add_one
