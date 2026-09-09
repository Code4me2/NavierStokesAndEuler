import Euler.CylinderEndpointRegularity
import Euler.ParameterSobolevScaling
import Euler.ParameterSobolevLinear

/-!
Scalar amplitudes for actual terminal L² data. A unit-input estimate for a
genuine linear endpoint map gives the identical coefficient/radius guard
for every nonnegative amplitude, including zero.
-/

noncomputable section

namespace EulerLpCylinderTranslation

open ContinuousLinearMap EulerLiftedGradientSpace EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K U V ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Embedding terminal data as a constant time path has block norm at most one. -/
theorem constantPath_block_le (directions : ι → LiftTangent) (q : ℕ)
    (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => pathTranslate P b (ContinuousMap.const K Y)) n a ≤
      block directions q (fun b : LiftTangent => translate P b Y) n a := by
  have hb := block_comp_clm_le directions q
    (ContinuousLinearMap.const ℝ K : CylinderL2 P U →L[ℝ] C(K,CylinderL2 P U))
    (fun b : LiftTangent => translate P b Y) hY n a
  have hn : ‖(ContinuousLinearMap.const ℝ K : CylinderL2 P U →L[ℝ] C(K,CylinderL2 P U))‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro u
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg u)).2 (fun _ => le_rfl)
  exact hb.trans ((mul_le_mul_of_nonneg_right hn (block_nonneg directions q _ n a)).trans_eq
    (one_mul _))


end EulerLpCylinderTranslation
