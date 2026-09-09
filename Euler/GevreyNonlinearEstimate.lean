import Euler.GevreyCorrectionBound

/-! The scalar polynomial majorant derived from the actual nonlinear Euler correction forcing. -/

noncomputable section

namespace EulerGevreyNonlinearEstimate

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy EulerGevreyRestriction EulerGevreyOrderZero
  EulerGevreyCorrectionBound

variable (period : ℝ) [Fact (0 < period)]

/-- Uniform bounds on the actual background and coefficient paths give the source's residual-linear-quadratic majorant. -/
theorem orderZeroSource_uniform {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (z e : SobolevSpace period (s+1)) (r : SobolevSpace period s)
    (B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hB0 : weightedNorm period 6 N ρ z ≤ B0)
    (hB1 : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hA0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hA : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hR : weightedNorm period 6 N ρ r ≤ R) :
    weightedNorm period 6 N ρ (orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)) ≤
      R+(productConstant period 3*B1+A0+2*A2*productConstant period 3*B0)*weightedNorm period 6 N ρ e+
        A2*productConstant period 3*(weightedNorm period 6 N ρ e)^2 := by
  have h := orderZeroSource_bound period hs N hN ρ hρ L hL C0 K0 C K z r (truncateOperator period s e)
  simp only [weightedNorm_truncate period 6 N hN ρ] at h
  have hP := productConstant_nonneg period 3
  have hE := weightedNorm_nonneg period 6 N ρ hρ e
  have hZ := weightedNorm_nonneg period 6 N ρ hρ z
  have hquad := mul_le_mul_of_nonneg_right hA hP
  have hcross := mul_le_mul hquad hB0 hZ (mul_nonneg hA2 hP)
  have hlin := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB1 hP) hA0)
    (mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 2))
  have hlin' : productConstant period 3*(∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z))+
      weightedCoefficient period K0 6 N ρ+
      2*(∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ)*productConstant period 3*weightedNorm period 6 N ρ z ≤
      productConstant period 3*B1+A0+2*A2*productConstant period 3*B0 := by
    nlinarith only [hlin]
  exact h.trans (add_le_add (add_le_add hR (mul_le_mul_of_nonneg_right hlin' hE))
    (mul_le_mul_of_nonneg_right hquad (sq_nonneg _)))



end EulerGevreyNonlinearEstimate
