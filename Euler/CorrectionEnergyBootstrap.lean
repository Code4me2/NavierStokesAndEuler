import Euler.CorrectionEnergyScalar

/-! The actual nonlinear viscous correction closes its shrinking-radius Gevrey bootstrap from the constructed mild equation. -/

noncomputable section

namespace EulerCorrectionEnergyBootstrap

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerCorrectionOperators
  EulerSobolevCoefficientPressure EulerCorrectionLowerData EulerCorrectionEnergyData
  EulerCorrectionEnergyMajorants EulerCorrectionEnergyScalar EulerEnergyMetricPaths
  EulerGevreyMetricEstimate EulerTimeLp EulerVolterraConvolution EulerSobolevHeat
  EulerIntegralEnergyBootstrap
open scoped Topology

/-- Increasing the single scalar coefficient preserves the signed radius term in the genuine energy estimate. -/
theorem raise_energy_constant (C0 C X Y r b R B : ℝ) (hC : C0 ≤ C)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hr : 0 ≤ r) (hR : 0 ≤ R) (hB : 0 ≤ B) :
    C0*(X+X^2+r)+(b+C0*R*(B+X))*Y ≤ C*(X+X^2+r)+(b+C*R*(B+X))*Y := by
  have h1 := mul_le_mul_of_nonneg_right hC (add_nonneg (add_nonneg hX (sq_nonneg X)) hr)
  have h2 := mul_le_mul_of_nonneg_right hC (mul_nonneg (mul_nonneg hR (add_nonneg hB hX)) hY)
  nlinarith only [h1,h2]

variable (period : ℝ) [Fact (0 < period)]


end EulerCorrectionEnergyBootstrap
