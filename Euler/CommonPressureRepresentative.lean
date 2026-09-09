import Euler.AllOrderCorrectionBudget
import Euler.GevreyStabilityBudget
import Euler.ClassicalDivergence
import Euler.CorrectionSourceRestriction
import Euler.GraphPressurePotential
import Euler.SobolevJointEvaluation

/-! A canonical, jointly continuous representative of the constructed common signed pressure. -/

noncomputable section

namespace EulerCommonPressureRepresentative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData EulerAllOrderCorrectionBudget EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation EulerSmoothPressureRepresentative EulerMetricTransport
  EulerGraphPressurePotential
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]






omit [Fact (0 < period)] in
/-- The physical phase graph is a continuous map into the periodic cylinder. -/
theorem cylinderGraph_continuous (k : ℝ) (m : Vector3) :
    Continuous (cylinderGraph period k m) := by
  unfold cylinderGraph
  exact continuous_id.prodMk ((AddCircle.continuous_mk' period).comp
    (continuous_const.mul (continuous_const.inner continuous_id)))




end EulerCommonPressureRepresentative
