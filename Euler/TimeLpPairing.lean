import Euler.TimeLp

/-! Actual integral pairings and their strong limits for metric energy passage. -/

noncomputable section

namespace EulerTimeLpPairing

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution
open scoped Topology

/-- The actual scalar Bochner inner product is the integral of the literal product. -/
theorem inner_eq_integral (T : ℝ) (a b : TimeLp T ℝ) :
    ⟪a, b⟫_ℝ = ∫ t, a t*b t ∂timeMeasure T := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by simp [RCLike.inner_apply, mul_comm]

/-- Continuous-path Bochner pairings equal the ordinary interval integral. -/
theorem path_inner_eq_integral (T : ℝ) (hT : 0 ≤ T) (a b : C(Icc (0 : ℝ) T, ℝ)) :
    ⟪pathLp T hT a, pathLp T hT b⟫_ℝ =
      ∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT b t := by
  rw [inner_eq_integral]
  have he : (∫ t, pathLp T hT a t*pathLp T hT b t ∂timeMeasure T) =
      ∫ t in Icc 0 T, extendPath T hT a t * extendPath T hT b t := by
    apply integral_congr_ae
    filter_upwards [pathLp_ae T hT a, pathLp_ae T hT b] with t h1 h2
    rw [h1, h2]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]





end EulerTimeLpPairing
