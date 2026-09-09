import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
A jointly measurable field which represents an actual Bochner L² family belongs
to the product L² space, with exactly the same norm.  This realizes nested
space/angle or time/space estimates without changing any derivative constants.
-/

noncomputable section

namespace EulerLpBochnerRealization

open MeasureTheory Filter
open scoped ENNReal

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

theorem norm_sq_eq_integral (u : Lp E 2 μ) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp u)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _)]
  rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]


variable [SFinite ν]




variable [SFinite μ]


end EulerLpBochnerRealization
