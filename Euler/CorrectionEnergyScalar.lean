import Euler.CorrectionEnergyMajorants
import Euler.CorrectionEnergyRestriction
import Euler.MildMajorantEnergy
import Euler.IntegralEnergyBootstrap

/-! The actual correction energy right-hand side has the scalar shrinking-radius form, including its exact zero initial trace. -/

noncomputable section

namespace EulerCorrectionEnergyScalar

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerNonlinearEnergyConstants
  EulerTimeLpSubintervalBound EulerTimeLp EulerVolterraConvolution EulerSobolevHeat
  EulerGevreyMetricComparison EulerGevreyDifferentiatedEquation EulerWeightedCylinderEnergy
  EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]


/-- Zero is exactly zero in the genuine finite metric energy. -/
theorem energyNorm_zero {q : ℕ} (N : ℕ) (hN : N+6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) : energyNorm period N hN ρ K (0 : SobolevSpace period q) = 0 := by
  unfold energyNorm weightedMetricSum
  apply Finset.sum_eq_zero
  intro I _
  have hzero : energyValues period 6 N hN (0 : SobolevSpace period q) I = fun _ => 0 := by
    funext a
    rw [← energyWordOperator_apply, map_zero]
  rw [hzero]
  simp [familyMetricNorm, familyEnergy]

/-- The actual zero-initial mild formula has zero trace, without a separately assumed initial-value identity. -/
theorem zero_mild_trace {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T, e t = heatOperator period (q+1) (2*ν*t.val).toNNReal 0 +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    e ⟨0,le_rfl,hT⟩ = 0 := by
  have h := hsol ⟨0,le_rfl,hT⟩
  simpa only [map_zero, intervalIntegral.integral_same, add_zero] using h

/-- A prescribed affine radius has its genuine time derivative at every interior point after clamped extension. -/
theorem affine_radius_derivative (T : ℝ) (hT : 0 ≤ T) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (ρ0 A : ℝ) (hR : ∀ t, R t = ρ0-A*t.val) (hRdot : ∀ t, Rdot t = -A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t := by
  have hm : HasDerivAt (fun r : ℝ => A*r) A t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul A
  have ha : HasDerivAt (fun r : ℝ => ρ0-A*r) (-A) t := HasDerivAt.const_sub ρ0 hm
  have he : extendPath T hT R =ᶠ[𝓝 t] fun r => ρ0-A*r := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    change R (projIcc 0 T hT r) = _
    rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
    exact hR ⟨r,hr.1.le,hr.2.le⟩
  exact (ha.congr_of_eventuallyEq he).congr_deriv (hRdot (projIcc 0 T hT t)).symm

end EulerCorrectionEnergyScalar
