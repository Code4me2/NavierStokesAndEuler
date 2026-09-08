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

/-- The genuine L² field-family path underlying an actual Sobolev family path. -/
def familyValuePath (q : ℕ) {I : Type*} (T : ℝ)
    (u : C(Icc (0 : ℝ) T, I → SobolevSpace period q)) : C(Icc (0 : ℝ) T, I → LiftL2 period) :=
  (familyValueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) u


omit [Fact (0 < period)] in
/-- The actual factorial Gevrey weight along a continuous radius path. -/
def gevreyWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => weight (ρ t) n, (ρ.continuous.pow n).div_const ((n.factorial : ℝ)^2)⟩

omit [Fact (0 < period)] in
/-- The actual radius-loss weight along the same radius path. -/
def gevreyLossWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  (n : ℝ) • gevreyWeightPath T ρ n

/-- A continuous-path weighted forcing integral is exactly its genuine Bochner forcing pairing. -/
theorem forcing_integral_eq {A I : Type*} [Fintype A] [Fintype I]
    (T : ℝ) (hT : 0 ≤ T) (c : C(Icc (0 : ℝ) T, ℝ))
    (w : A → C(Icc (0 : ℝ) T, ℝ)) (F : A → C(Icc (0 : ℝ) T, I → LiftL2 period)) :
    (∫ t, pathLp T hT c t * weightedForcingTime T hT w (fun i => pathLp T hT (F i)) t ∂timeMeasure T) =
      ∫ t in (0 : ℝ)..T, extendPath T hT c t * extendPath T hT (weightedForcingPath T w F) t := by
  rw [weightedForcingTime_pathLp, ← inner_eq_integral, path_inner_eq_integral]


end EulerSobolevEnergyPaths
