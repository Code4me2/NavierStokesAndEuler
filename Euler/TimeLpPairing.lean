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






end EulerTimeLpPairing
