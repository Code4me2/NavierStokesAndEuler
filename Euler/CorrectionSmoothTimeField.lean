import Euler.FieldTowerSmoothTimeField
import Euler.AllOrderDriftPressureBounds
import Euler.SmoothTimeFieldAlgebra
import Euler.LiftedSmoothTimeField

/-! The constructed all-order correction and its true time derivative
are actual smooth bounded cover coefficients. Their quantitative bounds
come from the checked weighted Sobolev estimates. -/

noncomputable section


namespace EulerAllOrderDriftCorrection

open Set EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerCylinderSobolevSpace
  EulerCylinderCoordinates EulerLiftedSmoothTimeField
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}

private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Vector3) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Vector3) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance

def Budget.correctionCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.fieldTower P).toSmoothTimeField

def Budget.correctionDerivativeCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.timeDerivativeTower P).toSmoothTimeField

theorem Budget.correctionCoefficient_timeDerivative (B : Budget P hT A) :
    SmoothTimeField.TimeDerivative T hT.le (B.correctionCoefficient P)
      (B.correctionDerivativeCoefficient P) :=
  (B.fieldTower P).toSmoothTimeField_timeDerivative_of_interior (B.timeDerivativeTower P)
    hT.le 6 (by norm_num) (B.fieldTower_hasDerivAt_timeDerivativeTower P 6 le_rfl)



end EulerAllOrderDriftCorrection
