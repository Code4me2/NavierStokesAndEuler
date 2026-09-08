import Euler.AllOrderDriftGraph
import Euler.AllOrderDriftPressureBounds
import Euler.FieldTowerPointwiseGevrey

/-! Pointwise mixed-word Gevrey estimates for the actual common
correction, its signed pressure gradient, and its actual time derivative. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerSobolevGevreyOperators EulerCylinderSobolev EulerMetricTransport
  EulerSobolevPointEvaluation

variable (P : ℝ) [Fact (0 < P)]
  {T : ℝ} {hT : 0 < T} {A : Data P T} (B : Budget P hT A)

/-- The canonical representative of the actual derivative tower is the
same time derivative already selected by the finite PDE construction. -/
theorem Budget.timeDerivativeTower_pointField (t : Icc (0 : ℝ) T) :
    (B.timeDerivativeTower P).pointField t = B.pointTimeDerivative P t := by
  funext x
  rw [(B.timeDerivativeTower P).pointField_eq_high 6 (by omega) t x,
    ← B.source_eq_timeDerivativeTower P 6 le_rfl t,
    ← B.solution_eq_realization P 6 le_rfl]
  rfl




end EulerAllOrderDriftCorrection
