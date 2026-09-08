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

theorem Budget.residualEnvelope_nonneg (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    0 ≤ B.residualEnvelope period q hq t := by
  have h := (B.spatial q hq).full.residual_pos
  unfold Budget.residualEnvelope
  positivity

theorem Budget.residualEnvelope_le_target (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    B.residualEnvelope period q hq t ≤ B.delta/2 := by
  have hg : 0 ≤ 3*B.growthCoefficient := by have := B.growth_pos period; positivity
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 hg)
  exact (mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2*(B.spatial q hq).full.residual by have := (B.spatial q hq).full.residual_pos; positivity)).trans
      (B.small q hq)


/-- The fixed polynomial cost when the solver's residual envelope is retained. -/
def Budget.residualSourceCost (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) : ℝ :=
  let S := (B.spatial q hq).full
  sourceBound period S.B0 S.B1 S.A0 S.A2 1
    (metricAmplification B.metric.c) ((8/B.initialRadius)*metricAmplification B.metric.c)



end EulerAllOrderDriftCorrection
