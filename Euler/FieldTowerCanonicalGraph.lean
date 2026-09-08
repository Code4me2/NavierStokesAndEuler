import Euler.FieldTowerGraph
import Euler.CylinderGraphRealization
import Euler.FieldTowerTimeRestriction

/-! Canonical graph restrictions need no additional representative or
regularity assumptions beyond the actual all-order tower. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerMetricTransport EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  (A : EulerAllOrderCorrectionData.FieldTower P T)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

def canonicalGraphWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  A.graphWordPath A.pointField A.pointField_smooth A.pointField_ae θ hθ n w

theorem canonicalGraphWordPath_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.canonicalGraphWordPath θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (A.pointField t) (x,θ x) :=
  A.graphWordPath_ae A.pointField A.pointField_smooth A.pointField_ae θ hθ n w t

theorem canonicalGraphWordPath_norm_sq_le (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) :
    ‖A.canonicalGraphWordPath θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization (n+1) t‖^2 :=
  A.graphWordPath_norm_sq_le A.pointField A.pointField_smooth A.pointField_ae θ hθ n w t



end EulerAllOrderCorrectionData.FieldTower
