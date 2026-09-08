import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reference pulse growth

This file verifies the scalar reference growth calculation in Lemma 8.5 and
Proposition A.4 of the supplied manuscript. The denominator `(1 + u^2)^(3/2)`
is written as `(1 + u^2) * sqrt (1 + u^2)` to avoid fractional-power notation.
These results do not assert bounds on the actual variable-coefficient ODE or
on its parameter derivatives.
-/

namespace NavierStokes.PulseGrowth

/-- Scalar growth of the positive reference mode after the chosen viscous damping. -/
noncomputable def netGrowth (lam u s : ℝ) : ℝ :=
  lam / Real.sqrt (1 + s ^ 2) -
    lam * (1 + s ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

theorem one_add_sq_pos (s : ℝ) : 0 < 1 + s ^ 2 := by
  positivity

theorem radius_pos (s : ℝ) : 0 < Real.sqrt (1 + s ^ 2) :=
  Real.sqrt_pos.2 (one_add_sq_pos s)

theorem dampingDenominator_pos (u : ℝ) :
    0 < (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) :=
  mul_pos (one_add_sq_pos u) (radius_pos u)





/-- The prescribed damping exactly cancels growth at the threshold. -/
theorem netGrowth_at_threshold (lam u : ℝ) : netGrowth lam u u = 0 := by
  unfold netGrowth
  field_simp [ne_of_gt (one_add_sq_pos u), ne_of_gt (radius_pos u)]; ring

/-- Strict decrease in squared distance from zero, for a positive reference rate. -/
theorem netGrowth_strictAnti_sq {lam u s t : ℝ} (hlam : 0 < lam)
    (hst : s ^ 2 < t ^ 2) : netGrowth lam u t < netGrowth lam u s := by
  have hst' : 1 + s ^ 2 < 1 + t ^ 2 := by linarith
  have hr : Real.sqrt (1 + s ^ 2) < Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_lt_sqrt (le_of_lt (one_add_sq_pos s)) hst'
  have hg : lam / Real.sqrt (1 + t ^ 2) < lam / Real.sqrt (1 + s ^ 2) := by
    apply (div_lt_div_iff₀ (radius_pos t) (radius_pos s)).2
    exact mul_lt_mul_of_pos_left hr hlam
  have hd : lam * (1 + s ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) <
      lam * (1 + t ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hst' hlam) (dampingDenominator_pos u)
  exact sub_lt_sub hg hd

theorem netGrowth_eq_of_sq_eq {lam u s t : ℝ} (hst : s ^ 2 = t ^ 2) :
    netGrowth lam u s = netGrowth lam u t := by
  simp only [netGrowth, hst]






/-- Magnitude of either signed schedule, in the slot-time variable. -/
noncomputable def slotMagnitude (u ell v : ℝ) : ℝ := u / 2 + u * v / ell

theorem slotMagnitude_midpoint (u ell : ℝ) (hell : ell ≠ 0) :
    slotMagnitude u ell (ell / 2) = u := by
  unfold slotMagnitude
  field_simp; ring

theorem slotMagnitude_nonneg {u ell v : ℝ} (hu : 0 ≤ u) (hell : 0 < ell)
    (hv : 0 ≤ v) : 0 ≤ slotMagnitude u ell v := by
  unfold slotMagnitude
  positivity




/-- Zero reference growth at the slot midpoint. -/
theorem netGrowth_slot_midpoint (lam u ell : ℝ) (hell : ell ≠ 0) :
    netGrowth lam u (slotMagnitude u ell (ell / 2)) = 0 := by
  rw [slotMagnitude_midpoint u ell hell, netGrowth_at_threshold]


end NavierStokes.PulseGrowth
