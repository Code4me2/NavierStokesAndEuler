import Euler.MetricPathConvergence
import Euler.WeightedForcingTime
import Euler.TimeLpPairing
import Euler.SobolevViscousEnergy

/-! Genuine continuous energy paths and their weighted strong limits. -/

noncomputable section

namespace EulerSobolevEnergyPaths

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerMetricPathConvergence EulerWeightedForcingTime EulerTimeLpPairing EulerTimeLp
  EulerVolterraConvolution EulerPacketWeights EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]




omit [Fact (0 < period)] in
/-- The actual factorial Gevrey weight along a continuous radius path. -/
def gevreyWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => weight (ρ t) n, (ρ.continuous.pow n).div_const ((n.factorial : ℝ)^2)⟩

omit [Fact (0 < period)] in
/-- The actual radius-loss weight along the same radius path. -/
def gevreyLossWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  (n : ℝ) • gevreyWeightPath T ρ n



end EulerSobolevEnergyPaths
