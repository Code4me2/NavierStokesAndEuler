import Euler.SobolevViscousEnergy
import Euler.WeightedCylinderEnergy
import Euler.TimeLpPairing
import Euler.SobolevEnergyPaths
import Euler.TimeLpSubinterval

/-! Genuine finite-Sobolev PDE energy passage on every time subinterval. -/

noncomputable section

namespace EulerPDESubintervalEnergyLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp EulerTimeLpPairing EulerPacketWeights EulerTimeLpSubinterval
open scoped Topology

/-- Three continuous weighted paths identify the actual scalar integral on an arbitrary time subinterval. -/
theorem integral_eq_three_subinterval_paths (T : ℝ) (hT : 0 ≤ T) (s t : ℝ) (hst : s ≤ t)
    (a b c X Y Z : C(Icc (0 : ℝ) T, ℝ)) (f : ℝ → ℝ)
    (hf : ∀ r ∈ Icc s t, f r = extendPath T hT a r * extendPath T hT X r +
      extendPath T hT b r * extendPath T hT Y r + extendPath T hT c r * extendPath T hT Z r) :
    (∫ r in s..t, f r) =
      (∫ r in s..t, extendPath T hT a r * extendPath T hT X r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT Y r) +
      ∫ r in s..t, extendPath T hT c r * extendPath T hT Z r := by
  have ha := ((extendPath_continuous T hT a).mul (extendPath_continuous T hT X)).intervalIntegrable (μ := volume) s t
  have hb := ((extendPath_continuous T hT b).mul (extendPath_continuous T hT Y)).intervalIntegrable (μ := volume) s t
  have hc := ((extendPath_continuous T hT c).mul (extendPath_continuous T hT Z)).intervalIntegrable (μ := volume) s t
  change IntervalIntegrable (fun r => extendPath T hT a r * extendPath T hT X r) volume s t at ha
  change IntervalIntegrable (fun r => extendPath T hT b r * extendPath T hT Y r) volume s t at hb
  change IntervalIntegrable (fun r => extendPath T hT c r * extendPath T hT Z r) volume s t at hc
  rw [← intervalIntegral.integral_add ha hb, ← intervalIntegral.integral_add (ha.add hb) hc]
  apply intervalIntegral.integral_congr
  intro r hr
  exact hf r (by simpa only [uIcc_of_le hst] using hr)

variable (period : ℝ) [Fact (0 < period)]


end EulerPDESubintervalEnergyLimit
