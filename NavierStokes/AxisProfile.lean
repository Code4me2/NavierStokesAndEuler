import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic checks for the natural axis profile

These theorems concern the scaled leading equations and the two explicit
truncations in Proposition 5.1 of the candidate manuscript.  They do not
establish convergence of a formal power series, the nonlinear remainder
estimates, the contraction argument, or the full profile's cone margin.
-/

namespace NavierStokes.AxisProfile

noncomputable section


/-- The regular zero-datum formal inverse used in the scaled equations. -/
def radialInverseCoeff (m : ℕ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => f n / (((n : ℝ) + 1) * ((n : ℝ) + m))

@[simp] theorem radialInverseCoeff_zero (m : ℕ) (f : ℕ → ℝ) :
    radialInverseCoeff m f 0 = 0 := rfl


/-- The leading angular series coefficient from Proposition 5.1:
`(-χ/2)^n / (n! (n+1)!)`. -/
def profileCoeff (χ : ℝ) (n : ℕ) : ℝ :=
  (-χ / 2) ^ n / ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))

@[simp] theorem profileCoeff_zero (χ : ℝ) : profileCoeff χ 0 = 1 := by
  norm_num [profileCoeff]

/-- Exact recurrence for the displayed regular series. -/
theorem profileCoeff_recurrence (χ : ℝ) (n : ℕ) :
    2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * profileCoeff χ (n + 1) =
      -χ * profileCoeff χ n := by
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  simp only [profileCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp; ring



/-- The cubic lower truncation in the manuscript, with `t = Yχ/2`. -/
def cubicLower (t : ℝ) : ℝ := 1 - t / 2 + t ^ 2 / 12 - t ^ 3 / 144

/-- The quartic upper truncation for `f₀ + s f₀'`, in the variable `t=s/2`. -/
def quarticUpper (t : ℝ) : ℝ :=
  1 - t + t ^ 2 / 4 - t ^ 3 / 36 + t ^ 4 / 576

/-- A rational positivity certificate for the lower truncation on
`t ≤ 2.05`; the natural application also has `t ≥ 0`. -/
theorem cubicLower_gt_quarter (t : ℝ) (ht : t ≤ 41 / 20) :
    1 / 4 < cubicLower t := by
  have hd : 0 ≤ 41 / 20 - t := sub_nonneg.mpr ht
  have h2 : 0 ≤ (41 / 20 - t) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (41 / 20 - t) ^ 3 := pow_nonneg hd _
  have hidentity : cubicLower t =
      cubicLower (41 / 20) +
      (1 / 2 - (41 / 20) / 6 + (41 / 20) ^ 2 / 48) * (41 / 20 - t) +
      (1 / 12 - (41 / 20) / 48) * (41 / 20 - t) ^ 2 +
      (41 / 20 - t) ^ 3 / 144 := by
    unfold cubicLower
    ring
  norm_num [cubicLower] at hidentity
  unfold cubicLower
  nlinarith

/-- A direct rational verification of the numerical strict inequality
used for the initial cone margin. -/
theorem quarticUpper_lt_neg_eighteen_hundredths
    (t : ℝ) (hlo : 99 / 50 ≤ t) (hhi : t ≤ 2) :
    quarticUpper t < -(18 / 100) := by
  have ht : 0 ≤ t := by linarith
  have hsmall : 0 ≤ 1 - t / 2 := by linarith
  have hsmall_le : 1 - t / 2 ≤ 1 / 100 := by linarith
  have hsquare := pow_le_pow_left₀ hsmall hsmall_le 2
  have hcube := pow_le_pow_left₀ (show (0 : ℝ) ≤ 99 / 50 by norm_num) hlo 3
  have hfour := pow_le_pow_left₀ ht hhi 4
  norm_num at hsquare hcube hfour
  unfold quarticUpper
  nlinarith



/-- The leading axial profile displayed in the scaled construction. -/
def leadingAxial (Z L Y : ℝ) : ℝ := -Y * Z / (2 * L)






end

end NavierStokes.AxisProfile
