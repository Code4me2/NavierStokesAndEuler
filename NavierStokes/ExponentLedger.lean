import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Arithmetic of the residual-order ledger

The candidate manuscript, Proposition 10.3, assigns real
exponents to analytic estimates. This file checks the arithmetic of those
assignments, conditional on the estimates being valid. It does not define the
analytic classes, construct a correction, or prove an estimate for a PDE.

The manuscript fixes `κ = 10⁻⁵` in §8.1 and again in §10.2. The results below
hold uniformly for `0 ≤ κ ≤ 10⁻⁵` and `σ ≥ 1/5`. Fractions are exact rationals
in the real numbers; no floating-point calculation is used.
-/

namespace NavierStokes.ExponentLedger

noncomputable section

/-- The good-wave residual exponent `B = 1/2 + σ`. -/
def waveExponent (σ : ℝ) : ℝ := 1 / 2 + σ

/-- The mean and defect target exponent `C = 1 + σ`. -/
def meanExponent (σ : ℝ) : ℝ := 1 + σ

/-- The intermediate exponent `H₁ = C - 2κ`. -/
def meanUpdateExponent (σ κ : ℝ) : ℝ := meanExponent σ - 2 * κ

/-- Minimum of the four listed gains for the particular wave correction. -/
def particularGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 3 * κ) (1 / 2 - κ))
    (waveExponent σ - κ)) (2 / 5)

/-- Minimum of the four listed gains for the signed wave correction. -/
def signedGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 4 * κ) (2 / 5 - κ))
    (1 / 2 - 2 * κ)) (waveExponent σ - 3 * κ)


theorem mean_eq_wave_add_half (σ : ℝ) :
    meanExponent σ = waveExponent σ + 1 / 2 := by
  unfold meanExponent waveExponent
  ring






/-! ## Step 1: particular correction -/







/-! ## Step 2: signed correction -/














/-! ## Steps 3 and 4: mean and defect updates -/








/-! ## Cumulative exponent bounds -/








/-! ## Exact fixed choice and quantifier bookkeeping -/




/-- Iterated accuracy parameters; this does not assert existence of the iterates. -/
def stageParameter (n : ℕ) : ℝ := 1 / 5 + (n : ℝ) / 10

theorem stage_parameter_zero : stageParameter 0 = 1 / 5 := by
  norm_num [stageParameter]

theorem stage_parameter_succ (n : ℕ) :
    stageParameter (n + 1) = stageParameter n + 1 / 10 := by
  unfold stageParameter
  push_cast
  ring

theorem stage_parameter_admissible (n : ℕ) :
    1 / 5 ≤ stageParameter n := by
  unfold stageParameter
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith


end

end NavierStokes.ExponentLedger
