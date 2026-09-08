import Euler.TimeLpBoundedMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong continuity of isometric spatial actions on time L²

This uses dominated convergence with the actual square-integrable time field.
It does not assume operator-norm continuity of spatial translations.
-/

noncomputable section

namespace EulerTimeLpBoundedMap

open MeasureTheory Set Filter EulerTimeLp
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise formula for the square distance between two genuine lifted fields. -/
theorem timeLift_norm_sub_sq (T : ℝ) (A B : E →L[ℝ] E) (u : TimeLp T E) :
    ‖timeLift T A u-timeLift T B u‖^2 =
      ∫ t, ‖A (u t)-B (u t)‖^2 ∂timeMeasure T := by
  refine (norm_sq_eq_integral T (timeLift T A u-timeLift T B u)).trans ?_
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (timeLift T A u) (timeLift T B u),
    timeLift_ae T A u, timeLift_ae T B u] with t hs ha hb
  simp only [Pi.sub_apply, ha, hb] at hs
  exact congrArg (fun v : E => ‖v‖^2) hs


end EulerTimeLpBoundedMap
