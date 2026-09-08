import Euler.AllOrderDriftPressureBounds

/-! The smaller-radius estimates also retain the actual residual envelope. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerGevreyMetricEstimate EulerSobolevGevreyOperators
  EulerGevreyRadiusReduction EulerGevreyCorrectionSourceBounds

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The quantitative envelope delivered by the actual finite solver. -/
def Budget.residualEnvelope (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q)
    (t : Icc (0 : ℝ) T) : ℝ :=
  2*(B.spatial q hq).full.residual*Real.exp (3*B.growthCoefficient*t.val)







end EulerAllOrderDriftCorrection
