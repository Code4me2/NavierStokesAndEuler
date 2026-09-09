import Euler.GevreyPressureTransport
import Euler.SmoothInequalityTransfer

/-! Cutoff-independent nonlinear pressure bounds for actual finite-Sobolev transport sources. -/

noncomputable section

namespace EulerGevreyPressureTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevTransport EulerSobolevL2Product EulerFunctionalVelocity
  EulerH6Nonlinear EulerVectorCylinder EulerSobolevTransportCommutator EulerSobolevCoefficientPressure
  EulerSobolevGevreyProduct EulerSobolevHeat EulerSmoothInequalityTransfer
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

local instance shiftedTransportGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance shiftedTransportSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The shifted actual H⁶ pressure sum stops one derivative below the velocity cutoff. -/
def shiftedPressureNorm {s : ℕ} (N : ℕ) (ρ : ℝ) (p : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ)*weight ρ (n+1)*blockNorm period (toJet period p) 6 n

/-- Continuity on the genuine Sobolev domain of the shifted pressure norm. -/
theorem continuous_shiftedPressureNorm {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) :
    Continuous (shiftedPressureNorm period (s := s) N ρ) := by
  apply continuous_finsetSum
  intro n hn
  exact (continuous_blockNorm period (by have := Finset.mem_range.mp hn; omega : n+6 ≤ s)).const_mul _




end EulerGevreyPressureTransport
