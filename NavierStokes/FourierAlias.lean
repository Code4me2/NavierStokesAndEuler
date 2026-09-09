import NavierStokes.TransportPrimitive
import NavierStokes.SmoothFourierData
import NavierStokes.ParametricTorusInverse
import NavierStokes.ChartScales
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import NavierStokes.Flatness

/-!
# Exact radial aliases and Fourier suppression

The compactification defect is retained as an actual function. Its averaging
and integration-by-parts identities concern genuine Bochner integrals.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Interval Topology BigOperators

namespace NavierStokes.FourierAlias

open TorusInverse

abbrev State := ℝ × Plane

section Averages

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integer translation invariance of an actual function on the universal cover. -/
noncomputable def TorusPeriodic (f : Plane → F) : Prop :=
  ∀ Y : Plane, ∀ k : Frequency, f (Y + ((k.1 : ℝ), (k.2 : ℝ))) = f Y

/-- The actual normalized unit-square average. -/
noncomputable def torusMean (f : Plane → F) : F :=
  ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)

noncomputable def sliceMean (f : State → F) (U : ℝ) : F := torusMean (fun Y => f (U, Y))


omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem torusPeriodic_first {f : Plane → F} (hp : TorusPeriodic f) (y : ℝ) :
    Periodic (fun x => f (x, y)) 1 := by
  intro x
  simpa using hp (x, y) (1, 0)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem torusPeriodic_second {f : Plane → F} (hp : TorusPeriodic f) (x : ℝ) :
    Periodic (fun y => f (x, y)) 1 := by
  intro y
  simpa using hp (x, y) (0, 1)

theorem periodic_integral_translate {g : ℝ → F} (hg : Periodic g 1) (c : ℝ) :
    (∫ x in (0 : ℝ)..1, g (x + c)) = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hg.intervalIntegral_add_eq c 0

/-- Averaging is invariant under any real torus translation. -/
theorem torusMean_translate {f : Plane → F} (hp : TorusPeriodic f) (Y : Plane) :
    torusMean (fun Z => f (Z + Y)) = torusMean f := by
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, f (x + Y.1, y + Y.2)) =
      ∫ x in (0 : ℝ)..1, f (x, y + Y.2) :=
    periodic_integral_translate (torusPeriodic_first hp (y + Y.2)) Y.1
  have hy : Periodic (fun y => ∫ x in (0 : ℝ)..1, f (x, y)) 1 := by
    intro y
    apply intervalIntegral.integral_congr
    intro x _
    exact torusPeriodic_second hp x y
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x + Y.1, y + Y.2)) = _
  simp_rw [hx]
  exact periodic_integral_translate hy Y.2

theorem torusMean_smul (c : ℝ) (f : Plane → F) :
    torusMean (fun Y => c • f Y) = c • torusMean f := by
  simp only [torusMean, intervalIntegral.integral_smul]

/-- Fubini on two compact real intervals. -/
theorem intervalIntegral_comm {g : Plane → F} (hg : Continuous g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ y in c..d, ∫ x in a..b, g (x, y)) = ∫ x in a..b, ∫ y in c..d, g (x, y) := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply (integral_integral_swap ?_).symm
  change Integrable g ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d)))
  rw [Measure.prod_restrict]
  exact (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem continuous_parameter_interval {H : Type} [TopologicalSpace H]
    [FirstCountableTopology H] [LocallyCompactSpace H] {g : H × ℝ → F}
    (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun x => ∫ u in a..b, g (x, u)) := by
  have heq : (fun x => ∫ u in a..b, g (x, u)) =
      (fun x => ∫ u in Icc a b, g (x, u)) := by
    funext x
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact continuous_parametric_integral_of_continuous (f := fun x u => g (x, u)) hg isCompact_Icc

theorem torusMean_const [CompleteSpace F] (c : F) : torusMean (fun _ => c) = c := by
  simp [torusMean]

theorem torusMean_neg (f : Plane → F) : torusMean (fun Y => -f Y) = -torusMean f := by
  simp only [torusMean, intervalIntegral.integral_neg]

theorem torusMean_add {f g : Plane → F} (hf : Continuous f) (hg : Continuous g) :
    torusMean (fun Y => f Y + g Y) = torusMean f + torusMean g := by
  have hcf : Continuous (fun y => ∫ x in (0 : ℝ)..1, f (x, y)) :=
    continuous_parameter_interval (g := fun p : ℝ × ℝ => f (p.2, p.1))
      (hf.comp (continuous_snd.prodMk continuous_fst)) (by norm_num)
  have hcg : Continuous (fun y => ∫ x in (0 : ℝ)..1, g (x, y)) :=
    continuous_parameter_interval (g := fun p : ℝ × ℝ => g (p.2, p.1))
      (hg.comp (continuous_snd.prodMk continuous_fst)) (by norm_num)
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, f (x, y) + g (x, y)) =
      (∫ x in (0 : ℝ)..1, f (x, y)) + ∫ x in (0 : ℝ)..1, g (x, y) :=
    intervalIntegral.integral_add
      ((hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      ((hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  unfold torusMean
  simp_rw [hx]
  exact intervalIntegral.integral_add (hcf.intervalIntegrable _ _) (hcg.intervalIntegrable _ _)

theorem torusMean_sub {f g : Plane → F} (hf : Continuous f) (hg : Continuous g) :
    torusMean (fun Y => f Y - g Y) = torusMean f - torusMean g := by
  simp only [sub_eq_add_neg]
  rw [torusMean_add hf hg.fun_neg, torusMean_neg]

/-- The torus and radial averages commute as actual iterated integrals. -/
theorem torusMean_intervalIntegral {g : State → F} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    torusMean (fun Y => ∫ s in a..b, g (s, Y)) = ∫ s in a..b, sliceMean g s := by
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, ∫ s in a..b, g (s, (x, y))) =
      ∫ s in a..b, ∫ x in (0 : ℝ)..1, g (s, (x, y)) := by
    exact intervalIntegral_comm (g := fun p : Plane => g (p.1, (p.2, y)))
      (hg.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) hab (by norm_num)
  have hc : Continuous (fun p : Plane => ∫ x in (0 : ℝ)..1, g (p.1, (x, p.2))) := by
    exact continuous_parameter_interval (g := fun p : Plane × ℝ => g (p.1.1, (p.2, p.1.2)))
      (hg.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)))
      (by norm_num : (0 : ℝ) ≤ 1)
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ∫ s in a..b, g (s, (x, y))) = _
  simp_rw [hx]
  exact intervalIntegral_comm hc hab (by norm_num)










variable [CompleteSpace F]




end Averages

section IntegrationByParts





end IntegrationByParts

section ActualFourierInverse

open ParametricTorusInverse

/-- Remove the actual full torus mean at each fixed radial coordinate. -/
noncomputable def nonbarPart (f : State → ℂ) (z : State) : ℂ := f z - mean f z.1

theorem nonbarPart_smooth {f : State → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nonbarPart f) :=
  hf.sub ((coefficient_smooth hf 0).comp contDiff_fst)


theorem nonbarPart_zeroMean {f : State → ℂ} (hf : ContDiff ℝ ∞ f) :
    ZeroMean (nonbarPart f) := by
  intro U
  rw [mean_eq_integral]
  change torusMean (fun Y => f (U, Y) - mean f U) = 0
  rw [torusMean_sub (f := fun Y => f (U, Y)) (g := fun _ => mean f U)
    (hf.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const, torusMean_const]
  change sliceMean f U - mean f U = 0
  have heq : sliceMean f U = mean f U := (mean_eq_integral f U).symm
  rw [heq, sub_self]













end ActualFourierInverse

section SmallScale






end SmallScale

end NavierStokes.FourierAlias
