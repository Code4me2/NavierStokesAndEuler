import NavierStokes.R3.CompactEnergy
import NavierStokes.R3.ComparisonSetup
import NavierStokes.R3.LocalizedLaplacian
import NavierStokes.R3.LocalizedTransport
import NavierStokes.WithTopLemmas

/-!
# The compactly weighted difference-energy identity on R³

The cutoff alone has compact support. Both velocities and both pressures may
be arbitrary smooth fields on the time slab. Every integral below is an
ordinary Lebesgue volume integral on Euclidean three-space.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.LocalizedDifferenceEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (weightedEnergy weightedEnergyRate weightedDissipation gradientSq)

/-- A continuous factor needs no decay when multiplied by the compact cutoff. -/
theorem integrable_cutoff_mul {χ f : Space → ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (hf : Continuous f) :
    Integrable (fun x => χ x * f x) :=
  (hχ.mul hf).integrable_of_hasCompactSupport hcχ.mul_right

theorem integrable_weighted_energy {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : Continuous (fun x : Space => w (t, x))) :
    Integrable (fun x : Space => χ x * ‖w (t, x)‖ ^ 2) :=
  integrable_cutoff_mul hχ hcχ (hw.norm.pow 2)



theorem weightedDissipation_nonneg {χ : Space → ℝ} (hχ : ∀ x, 0 ≤ χ x)
    (w : VelocityField) (t : ℝ) : 0 ≤ weightedDissipation χ w t :=
  integral_nonneg (fun x => mul_nonneg (hχ x)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Energy is continuous on the closed slab, including its initial time. -/
theorem weightedEnergy_continuousOn {a b : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) :
    ContinuousOn (weightedEnergy χ w) (Icc a b) := by
  have hF : ContinuousOn (fun z : SpaceTime => χ z.2 * ‖w z‖ ^ 2)
      (Icc a b ×ˢ univ) :=
    (hχ.comp continuous_snd).continuousOn.mul (hw.continuousOn.norm.pow 2)
  apply CompactTimeIntegral.continuousOn_integral hcχ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Joint smoothness and the cutoff justify differentiation under the integral. -/
theorem weightedEnergy_hasDerivAt {a b t : ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab a b)) (ht : t ∈ Ioo a b) :
    HasDerivAt (weightedEnergy χ w) (weightedEnergyRate χ w t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => χ z.2 * ‖w z‖ ^ 2)
      (Icc a b ×ˢ univ) :=
    (((hχ.comp contDiff_snd).contDiffOn).mul (hw.norm_sq ℝ)).of_le (natCast_le_infty 1)
  refine CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt hcχ hF ?_ ht ?_
  · intro r hr x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro x
    exact (energy_density_derivative (time_differentiable_at_interior hw ht x)).const_mul (χ x)


/-- The localized balance follows from equality of the actual Navier--Stokes
residuals. No integrability or support condition is imposed on either velocity. -/
theorem difference_energy_balance {χ : Space → ℝ} {u v : VelocityField}
    {p q : PressureField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x : Space, DifferentiableAt ℝ (fun r => u (r, x)) t)
    (htv : ∀ x : Space, DifferentiableAt ℝ (fun r => v (r, x)) t)
    (hdivu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdivv : ∀ x : Space, spatialDivergence v t x = 0)
    (hNS : ∀ x : Space, ProblemStatement.navierStokesResidual 1 u p t x =
      ProblemStatement.navierStokesResidual 1 v q t x) :
    (1 / 2 : ℝ) * weightedEnergyRate χ (u - v) t + weightedDissipation χ (u - v) t =
      -(∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) +
      ∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x)) := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hπ : ContDiff ℝ ∞ (fun x : Space => (p - q) (t, x)) := hp.sub hq
  have hdivw : ∀ x : Space, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdivu x, hdivv x, sub_self]
  have hiL : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hiC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hu.fderiv_right infty_add_one_le_infty).clm_apply hw)).continuous
  have hiT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ
      (hw.inner ℝ ((hw.fderiv_right infty_add_one_le_infty).clm_apply hv)).continuous
  have hiP : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) :=
    integrable_cutoff_mul hχ.continuous hcχ (hw.inner ℝ (pressureGradient_contDiff hπ)).continuous
  have hiLC : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) :=
    hiL.sub hiC
  have hiLCT : Integrable (fun x : Space =>
      χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
      χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) :=
    hiLC.sub hiT
  have hEq : (fun x : Space => χ x *
      (2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)) =
      (fun x : Space => 2 * (
        χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ)) := by
    funext x
    rw [difference_equation hu hv hp hq (htu x) (htv x) (by simpa using hNS x)]
    simp only [inner_sub_right]
    ring
  have hRate : weightedEnergyRate χ (u - v) t = 2 * (
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ) -
      (∫ x : Space, χ x * ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) -
      ∫ x : Space, χ x * ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) := by
    unfold weightedEnergyRate
    rw [hEq, integral_const_mul, integral_sub hiLCT hiP,
      integral_sub hiLC hiT, integral_sub hiL hiC]
  have hL := integral_weighted_spatialLaplacian hχ hw hcχ
  have hT := integral_weighted_transport hχ hw hv hcχ hdivv
  have hP : (∫ x : Space, χ x *
      ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) =
      -(∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) := by
    simp_rw [inner_pressureGradient]
    exact integral_weighted_pressure hχ hπ hw hcχ hdivw
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ) =
      -weightedDissipation χ (u - v) t +
      (1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        ∑ i : Fin 3, spatialPartial i (spatialPartial i χ) x) at hL
  change (∫ x : Space, χ x *
    ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ) =
      -(1 / 2 : ℝ) * (∫ x : Space, ‖(u - v) (t, x)‖ ^ 2 *
        fderiv ℝ χ x (v (t, x))) at hT
  rw [hL, hT, hP] at hRate
  rw [hRate]
  ring


end NavierStokesR3.LocalizedDifferenceEnergy
