import Euler.WeightedSobolevEnergy
import Euler.TimeLpPairing
import Euler.SobolevEnergyPaths

/-! The actual finite-Sobolev viscous PDE energy estimate passes to strong limits without a time derivative of a zero norm. -/

noncomputable section

namespace EulerPDEEnergyLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedSobolevEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp EulerTimeLpPairing EulerPacketWeights
open scoped Topology

/-- Equality of an actual scalar integrand with three continuous weighted paths identifies its interval integral. -/
theorem integral_eq_three_paths (T : ℝ) (hT : 0 ≤ T)
    (a b c X Y Z : C(Icc (0 : ℝ) T, ℝ)) (f : ℝ → ℝ)
    (hf : ∀ r ∈ Icc 0 T, f r = extendPath T hT a r * extendPath T hT X r +
      extendPath T hT b r * extendPath T hT Y r + extendPath T hT c r * extendPath T hT Z r) :
    (∫ r in (0 : ℝ)..T, f r) =
      (∫ r in (0 : ℝ)..T, extendPath T hT a r * extendPath T hT X r) +
      (∫ r in (0 : ℝ)..T, extendPath T hT b r * extendPath T hT Y r) +
      ∫ r in (0 : ℝ)..T, extendPath T hT c r * extendPath T hT Z r := by
  rw [← integral_three_paths T hT a b c X Y Z]
  apply intervalIntegral.integral_congr
  intro r hr
  exact hf r (by simpa only [uIcc_of_le hT] using hr)

variable (period : ℝ) [Fact (0 < period)]


end EulerPDEEnergyLimit
