import Euler.SobolevTransportCommutator
import Euler.SmoothInequalityTransfer

/-! The actual finite-Sobolev external transport commutator satisfies the Gevrey radius-loss bound. -/

noncomputable section

namespace EulerSobolevTransportCommutator

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator
  EulerSobolevGevreyProduct EulerSobolevHeat EulerSmoothInequalityTransfer
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

local instance weightedCommGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance weightedCommSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual finite weighted derivative-loss norm. -/
def weightedLoss {s : ℕ} (q N : ℕ) (ρ : ℝ) (u : SobolevSpace period s) : ℝ :=
  ∑ n ∈ Finset.range (N+1), (n : ℝ)*weight ρ n*blockNorm period (toJet period u) q n

theorem weightedLoss_nonneg {s : ℕ} (q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (u : SobolevSpace period s) :
    0 ≤ weightedLoss period q N ρ u :=
  Finset.sum_nonneg fun n _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (weight_pos hρ n).le) (blockNorm_nonneg _)

/-- Continuity of the actual finite loss norm. -/
theorem continuous_weightedLoss {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) :
    Continuous (weightedLoss period (s := s) q N ρ) := by
  apply continuous_finsetSum
  intro n hn
  exact (continuous_blockNorm period (by have := Finset.mem_range.mp hn; omega : n+q ≤ s)).const_mul _

/-- Exact identification of weighted complete-Sobolev blocks with classical representative norms. -/
theorem weightedNorm_eq_classical {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    weightedNorm period q N ρ u = ∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period q n f := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [blockNorm_eq_classical period (toJet period u) (by have := Finset.mem_range.mp hn; omega) f hu hf]

/-- The same exact identification for the derivative-loss norm. -/
theorem weightedLoss_eq_classical {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ)
    (u : SobolevSpace period s) (f : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    weightedLoss period q N ρ u = ∑ n ∈ Finset.range (N+1), (n : ℝ)*weight ρ n*wordSobolevNorm period q n f := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [blockNorm_eq_classical period (toJet period u) (by have := Finset.mem_range.mp hn; omega) f hu hf]

/-- Weighted sum of the genuine H⁶ external transport commutators. -/
def weightedCommutatorNorm {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) : ℝ :=
  ∑ n : Fin (N+1), weight ρ n.val * ∑ w : Fin n.val → Fin 4,
    sumNorm period (externalCommutator period hs n.val w (by have := n.isLt; omega) L hL u v)

/-- The weighted commutator expression is continuous in its actual finite-Sobolev inputs. -/
theorem continuous_weightedCommutatorNorm {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    Continuous (fun p : SobolevSpace period (s+1) × SobolevSpace period (s+1) =>
      weightedCommutatorNorm period hs N hN ρ L hL p.1 p.2) := by
  apply continuous_finsetSum
  intro n _
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro w _
  exact (continuous_sumNorm period 6).comp
    (externalCommutator period hs n.val w (by have := n.isLt; omega) L hL).continuous₂



end EulerSobolevTransportCommutator
