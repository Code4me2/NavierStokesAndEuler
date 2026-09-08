import Euler.SobolevDriftNorm
import Euler.DriftPreservingTransport
import Euler.SmoothInequalityTransfer

/-! Sharp drift-preserving transport and pressure estimates for actual finite Sobolev fields. -/

noncomputable section

namespace EulerSobolevDriftTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator
  EulerSobolevGevreyProduct EulerSobolevHeat EulerSobolevTransportCommutator
  EulerSobolevCoefficientPressure EulerGevreyPressureTransport EulerSobolevDriftNorm EulerDriftPreservingTransport
  EulerSmoothInequalityTransfer
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine finite-Sobolev commutator retains the actual small drift norm in its radius-loss factor. -/
theorem weightedCommutator_drift_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    weightedCommutatorNorm period hs N hN ρ L hL u v ≤
      (productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6 N ρ (velocityMap L) u*weightedLoss period 6 N ρ v := by
  have hW : Continuous (weightedDriftNorm period (s := s+1) 6 N ρ (velocityMap L)) := continuous_weightedDriftNorm period 6 N (by omega) ρ (velocityMap L)
  have hY : Continuous (weightedLoss period (s := s+1) 6 N ρ) := continuous_weightedLoss period 6 N (by omega) ρ
  refine binary_le_of_smooth period
    (fun p => weightedCommutatorNorm period hs N hN ρ L hL p.1 p.2)
    (fun p => (productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6 N ρ (velocityMap L) p.1*
      weightedLoss period 6 N ρ p.2)
    (continuous_weightedCommutatorNorm period hs N hN ρ L hL)
    (((hW.comp continuous_fst).const_mul ((productConstant period 3)*ρ⁻¹)).mul (hY.comp continuous_snd))
    (fun a b f g hf hg hfs hgs hfL hgL => ?_) u v
  rw [weightedDriftNorm_eq_classical period 6 N (by omega) ρ (velocityMap L) a f hf hfs]
  exact weightedCommutator_drift_smooth period hs N hN ρ hρ L hL a b f g hf hg hfs hgs hfL hgL

/-- The actual rough finite-Sobolev pressure estimate retains the small drift norm. -/
theorem transportPressure_shifted_drift {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (4*M*productConstant period 3)*weightedDriftNorm period 6 (N+1) ρ (velocityMap L) u*weightedLoss period 6 (N+1) ρ v := by
  have hW : Continuous (weightedDriftNorm period (s := s+1) 6 (N+1) ρ (velocityMap L)) := continuous_weightedDriftNorm period 6 (N+1) (by omega) ρ (velocityMap L)
  have hY : Continuous (weightedLoss period (s := s+1) 6 (N+1) ρ) := continuous_weightedLoss period 6 (N+1) (by omega) ρ
  refine binary_le_of_smooth period
    (fun p => shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL p.1 p.2))
    (fun p => (4*M*productConstant period 3)*weightedDriftNorm period 6 (N+1) ρ (velocityMap L) p.1*
      weightedLoss period 6 (N+1) ρ p.2)
    ((continuous_shiftedPressureNorm period N hN ρ).comp
      (transportPressure_continuous period hs K κ m c hc hpos L hL))
    (((hW.comp continuous_fst).const_mul (4*M*productConstant period 3)).mul (hY.comp continuous_snd))
    (fun a b f g hf hg hfs hgs hfL hgL => ?_) u v
  rw [weightedDriftNorm_eq_classical period 6 (N+1) (by omega) ρ (velocityMap L) a f hf hfs]
  exact transportPressure_shifted_drift_smooth period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase hsmall hcoeff
    L hL a b f g hf hg hfs hgs hfL hgL

end EulerSobolevDriftTransport
