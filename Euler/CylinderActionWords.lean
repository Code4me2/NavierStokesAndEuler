import Euler.IsometricActionWords
import Euler.LpCylinderOrbit
import Euler.CylinderTranslationAdjoint
import Euler.MeanPathLpBlocks

/-! Exact mixed-word invariance on cylinder L² and its time-function spaces. -/

noncomputable section

namespace EulerLpCylinderTranslation

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
  EulerTimeLp EulerTimeLpBoundedMap EulerParameterWordGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Path

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem pathTranslate_norm_map (a : LiftTangent) (f : C(K,CylinderL2 P V)) :
    ‖pathTranslate P a f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro t
    change ‖translate P a (f t)‖ ≤ ‖f‖
    rw [LinearIsometry.norm_map]
    exact f.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg (pathTranslate P a f))).2
    intro t
    rw [← (translate P a).norm_map (f t)]
    exact (pathTranslate P a f).norm_coe_le_norm t

def pathTranslateIsometry (a : LiftTangent) : C(K,CylinderL2 P V) →ₗᵢ[ℝ] C(K,CylinderL2 P V) where
  toLinearMap := (pathTranslate P a).toLinearMap
  norm_map' := pathTranslate_norm_map P a

theorem path_block_constant {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (f : C(K,CylinderL2 P V)) (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f)) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => pathTranslate P b f) n a =
      block directions q (fun b => pathTranslate P b f) n 0 :=
  EulerIsometricAction.block_orbit_constant (X := LiftTangent)
    (E := C(K,CylinderL2 P V)) (ι := ι) (pathTranslateIsometry (K := K) (V := V) P)
    (fun a b u => pathTranslate_add P a b u) (fun u => pathTranslate_zero P u) directions q f hf n a

end Path







end EulerLpCylinderTranslation
