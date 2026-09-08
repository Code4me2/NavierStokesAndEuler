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

/-- Underlying L² values of a finite actual Sobolev family form a bounded linear map. -/
def familyValueOperator (q : ℕ) {I : Type*} :
    (I → SobolevSpace period q) →L[ℝ] (I → LiftL2 period) :=
  ContinuousLinearMap.pi (fun i => (valueOperator period q).comp (ContinuousLinearMap.proj i))



omit [Fact (0 < period)] in
/-- The actual factorial Gevrey weight along a continuous radius path. -/
def gevreyWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => weight (ρ t) n, (ρ.continuous.pow n).div_const ((n.factorial : ℝ)^2)⟩

omit [Fact (0 < period)] in
/-- The actual radius-loss weight along the same radius path. -/
def gevreyLossWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  (n : ℝ) • gevreyWeightPath T ρ n



end EulerSobolevEnergyPaths
