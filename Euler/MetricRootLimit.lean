import Euler.CylinderViscousEnergy

/-! Removal of square-root regularization in actual finite metric-energy integral inequalities. -/

noncomputable section

namespace EulerMetricRootLimit

open MeasureTheory Set Real InnerProductSpace EulerNoncompactTransport EulerFiniteMetricEnergy
open scoped Topology

/-- A regularized square root differs from the nonnegative root by at most the regularization. -/
theorem regularized_root_le (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) :
    √(q + δ ^ 2) ≤ √q + δ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (sqrt_nonneg q) hδ, ?_⟩
  have hsq := sq_sqrt hq
  have hp := mul_nonneg (sqrt_nonneg q) hδ
  nlinarith

/-- The canonical positive regularization sequence converges at every quadratic energy value. -/
theorem regularized_root_tendsto (q : ℝ) :
    Filter.Tendsto (fun n => √(q + cutoffScale n ^ 2)) Filter.atTop (𝓝 (√q)) := by
  have hq : Filter.Tendsto (fun n => q + cutoffScale n ^ 2) Filter.atTop (𝓝 q) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      (tendsto_const_nhds.add (cutoffScale_tendsto.pow 2))
  exact (continuous_sqrt.tendsto q).comp hq



end EulerMetricRootLimit
