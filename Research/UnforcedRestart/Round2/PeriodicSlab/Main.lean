import Research.UnforcedRestart.«energy-comparison».Main
import Research.UnforcedRestart.«gronwall-threshold».Main
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedRestart.Round2.PeriodicSlab
open NavierStokes.ProblemStatement NavierStokes.SolutionDifference
open NavierStokes.PeriodicIntegration NavierStokes.PeriodicUniqueness

/-- The source is the actual cube squared norm, not a primitive assumption. -/
theorem force_energy_continuousOn {S : ℝ} {f : VelocityField}
    (hf : ContinuousOn f (slab 0 S)) :
    ContinuousOn (fun t => cubeIntegral (fun x => ‖f (t, x)‖ ^ 2)) (Icc 0 S) := by
  exact cubeIntegral_continuousOn_Icc (hf.norm.pow 2)

/-- Derivative and inequality are outputs of joint regularity and both PDEs. -/
theorem slab_energy_derivative_le {S t B : ℝ}
    {u v f : VelocityField} {p q : PressureField}
    (hu : ContDiffOn ℝ ∞ u (slab 0 S))
    (hv : ContDiffOn ℝ ∞ v (slab 0 S))
    (hp : ContDiffOn ℝ ∞ p (slab 0 S))
    (hq : ContDiffOn ℝ ∞ q (slab 0 S))
    (hf : ContinuousOn f (slab 0 S))
    (hpu : UnitSpatialPeriodsOn (Icc 0 S) u)
    (hpv : UnitSpatialPeriodsOn (Icc 0 S) v)
    (hpp : UnitSpatialPeriodsOn (Icc 0 S) p)
    (hpq : UnitSpatialPeriodsOn (Icc 0 S) q)
    (hdu : ∀ s ∈ Ioo 0 S, ∀ x, spatialDivergence u s x = 0)
    (hdv : ∀ s ∈ Ioo 0 S, ∀ x, spatialDivergence v s x = 0)
    (hNSu : ∀ s ∈ Ioo 0 S, ∀ x, navierStokesResidual u p s x = f (s, x))
    (hNSv : ∀ s ∈ Ioo 0 S, ∀ x, navierStokesResidual v q s x = 0)
    (hB : ∀ s ∈ Icc 0 S, ∀ y ∈ cube,
      ‖spatialDerivative u s (toSpace y)‖ ≤ B)
    (ht : t ∈ Ioo 0 S) :
    HasDerivAt (energy u v) (energyRate u v t) t ∧
      energyRate u v t ≤ (2 * B + 1) * energy u v t +
        cubeIntegral (fun x => ‖f (t, x)‖ ^ 2) := by
  have ht' : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le⟩
  have hft : Continuous (fun x : Space => f (t, x)) := by
    rw [← continuousOn_univ]
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨ht', mem_univ x⟩)
  have hres (x : Space) :
      navierStokesResidual u p t x - navierStokesResidual v q t x = f (t, x) := by
    rw [hNSu t ht x, hNSv t ht x, sub_zero]
  have hr := UnforcedRestart.EnergyComparison.forced_energy_rate_le
    (spatial_smooth hu ht') (spatial_smooth hv ht')
    (spatial_smooth hp ht') (spatial_smooth hq ht')
    (hpu t ht') (hpv t ht') (hpp t ht') (hpq t ht')
    (hdu t ht) (hdv t ht)
    (time_differentiable_at_interior hu ht)
    (time_differentiable_at_interior hv ht) hft hres (hB t ht')
  refine ⟨energy_hasDerivAt hu hv ht, ?_⟩
  have hd := dissipation_nonneg (u - v) t
  linarith

/-- FTC on the closed slab, with no assumptions outside it. -/
theorem primitive_on_slab {S : ℝ} (hS : 0 < S) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Icc 0 S)) :
    ContinuousOn (fun s => ∫ r in 0..s, c r) (Icc 0 S) ∧
    (∀ t ∈ Ioo 0 S, HasDerivAt (fun s => ∫ r in 0..s, c r) (c t) t) ∧
    (∀ s ∈ Icc 0 S, IntervalIntegrable c MeasureTheory.volume 0 s) := by
  have hi (s : ℝ) (hs : s ∈ Icc 0 S) :
      IntervalIntegrable c MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact hc.mono (fun _ hx => ⟨hx.1, hx.2.trans hs.2⟩)
  refine ⟨?_, ?_, hi⟩
  · have hc' : ContinuousOn c (uIcc 0 S) := by
      simpa only [uIcc_of_le hS.le] using hc
    simpa only [uIcc_of_le hS.le] using
      intervalIntegral.continuousOn_primitive_interval hc'.integrableOn_uIcc
  · intro t ht
    exact intervalIntegral.integral_hasDerivAt_right (hi t ⟨ht.1.le, ht.2.le⟩)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hc.mono Ioo_subset_Icc_self) t ht)
      ((hc t ⟨ht.1.le, ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- Genuine periodic forced/unforced finite-slab comparison, with a derived
constant gradient majorant and literal FTC integrals. No existence or evaluation claim. -/
theorem periodic_slab_comparison {S : ℝ} (hS : 0 < S)
    {u v f : VelocityField} {p q : PressureField} {a : Space → Space}
    (hu : ContDiffOn ℝ ∞ u (slab 0 S))
    (hv : ContDiffOn ℝ ∞ v (slab 0 S))
    (hp : ContDiffOn ℝ ∞ p (slab 0 S))
    (hq : ContDiffOn ℝ ∞ q (slab 0 S))
    (hf : ContinuousOn f (slab 0 S))
    (hpu : UnitSpatialPeriodsOn (Icc 0 S) u)
    (hpv : UnitSpatialPeriodsOn (Icc 0 S) v)
    (hpp : UnitSpatialPeriodsOn (Icc 0 S) p)
    (hpq : UnitSpatialPeriodsOn (Icc 0 S) q)
    (hdu : ∀ s ∈ Ioo 0 S, ∀ x, spatialDivergence u s x = 0)
    (hdv : ∀ s ∈ Ioo 0 S, ∀ x, spatialDivergence v s x = 0)
    (hNSu : ∀ s ∈ Ioo 0 S, ∀ x, navierStokesResidual u p s x = f (s, x))
    (hNSv : ∀ s ∈ Ioo 0 S, ∀ x, navierStokesResidual v q s x = 0)
    (hu0 : ∀ x, u (0, x) = a x) (hv0 : ∀ x, v (0, x) = a x) :
    ∃ B : ℝ, 0 < B ∧
      (∀ s ∈ Icc 0 S, ∀ y ∈ cube, ‖spatialDerivative u s (toSpace y)‖ ≤ B) ∧
      ∀ s ∈ Icc 0 S,
        energy u v s ≤ Real.exp (∫ _r in 0..s, (2 * B + 1 : ℝ)) *
          ∫ r in 0..s, Real.exp (-(∫ _z in 0..r, (2 * B + 1 : ℝ))) *
            cubeIntegral (fun x => ‖f (r, x)‖ ^ 2) := by
  obtain ⟨B, hBpos, hB⟩ := exists_gradient_bound hS hu isCompact_cubeImage
  have hbound : ∀ s ∈ Icc 0 S, ∀ y ∈ cube,
      ‖spatialDerivative u s (toSpace y)‖ ≤ B :=
    fun s hs y hy => hB s hs (toSpace y) ⟨y, hy, rfl⟩
  refine ⟨B, hBpos, hbound, ?_⟩
  let A : ℝ → ℝ := fun s => ∫ r in 0..s, (2 * B + 1 : ℝ)
  let g : ℝ → ℝ := fun s => cubeIntegral (fun x => ‖f (s, x)‖ ^ 2)
  obtain ⟨hAc, hAd, _⟩ := primitive_on_slab hS
    (continuousOn_const : ContinuousOn (fun _ : ℝ => 2 * B + 1) (Icc 0 S))
  have hgc : ContinuousOn g (Icc 0 S) := force_energy_continuousOn hf
  obtain ⟨hPc, hPd, _⟩ := primitive_on_slab hS
    ((Real.continuous_exp.comp_continuousOn hAc.neg).mul hgc)
  have hd (t : ℝ) (ht : t ∈ Ioo 0 S) :=
    slab_energy_derivative_le hu hv hp hq hf hpu hpv hpp hpq
      hdu hdv hNSu hNSv hbound ht
  have hw := UnforcedRestart.GronwallThreshold.weighted_budget hS.le
    (energy_continuousOn hu hv) hAc hPc (fun t ht => (hd t ht).1)
    hAd hPd (fun t ht => (hd t ht).2)
  have hz : energy u v 0 = 0 := energy_initial_zero (fun x => (hu0 x).trans (hv0 x).symm)
  intro s hs
  have hh : Real.exp (-A s) * energy u v s ≤
      ∫ r in 0..s, Real.exp (-A r) * g r := by
    simpa only [A, Function.comp_apply, Pi.mul_apply, Pi.neg_apply,
      hz, mul_zero, zero_add, intervalIntegral.integral_same, sub_zero]
      using hw s hs
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (A s)).le
  have he : Real.exp (A s) * Real.exp (-A s) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul] using hm

end UnforcedRestart.Round2.PeriodicSlab

#print axioms UnforcedRestart.Round2.PeriodicSlab.force_energy_continuousOn
#print axioms UnforcedRestart.Round2.PeriodicSlab.slab_energy_derivative_le
#print axioms UnforcedRestart.Round2.PeriodicSlab.primitive_on_slab
#print axioms UnforcedRestart.Round2.PeriodicSlab.periodic_slab_comparison
