import Euler.CylinderPathProduct
import Euler.CylinderConstantMap

/-! Literal bounded bilinear nonlinearities preserve smooth continuous cylinder L² paths. -/

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerCylinderConstantMap EulerMetricTransport
open scoped ContDiff

def component (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

theorem component_norm (i : Fin 3) : ‖component i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  change ‖u i‖ ≤ (1 : ℝ)*‖u‖
  simpa only [one_mul] using PiLp.norm_apply_le u i

def basisVector (i : Fin 3) : Space := EuclideanSpace.single i 1

theorem sum_components (u : Space) : (∑ i : Fin 3, component i u • basisVector i) = u := by
  ext i
  simp [component, basisVector, Pi.single_apply, mul_ite]


variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (B : Space →L[ℝ] Space →L[ℝ] Space) (p q : C(K,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))








end EulerCylinderPathProduct
