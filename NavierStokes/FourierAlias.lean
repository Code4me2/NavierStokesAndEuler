import NavierStokes.TransportPrimitive
import NavierStokes.SmoothFourierData
import NavierStokes.ParametricTorusInverse
import NavierStokes.ChartScales
import NavierStokes.Flatness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

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

/-- The exact defect in `D Ic = f - cutoffAlias`. -/
noncomputable def cutoffAlias (χ : ℝ → ℝ) (M : ℝ) (v : Plane) (f : State → F) (z : State) : F :=
  deriv χ z.1 • TransportPrimitive.totalIntegral M v f z

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







/-- The alias is an exact term in the constructed inverse identity. -/
theorem transport_compact_eq_sub_alias [CompleteSpace F] {a b M : ℝ} {v : Plane}
    {f : State → F} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (z : State) :
    TransportPrimitive.fixedDeriv (1, M • v) (TransportPrimitive.compactIntegral χ M v f) z =
      f z - cutoffAlias χ M v f z :=
  TransportPrimitive.transport_compactIntegral hχ hf hs z

theorem iteratedFDeriv_periodic {f : State → F}
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y))) (n : ℕ) :
    ∀ U, TorusPeriodic (fun Y => iteratedFDeriv ℝ n f (U, Y)) := by
  intro U Y k
  have heq : (fun z : State => f (z + (0, ((k.1 : ℝ), (k.2 : ℝ))))) = f := by
    funext z
    change f (z.1 + 0, z.2 + ((k.1 : ℝ), (k.2 : ℝ))) = f z
    simpa only [add_zero] using hp z.1 z.2 k
  have h := congrArg (fun g : State → F => iteratedFDeriv ℝ n g (U, Y)) heq
  rw [iteratedFDeriv_comp_add_right] at h
  simpa only [Prod.mk_add_mk, add_zero] using h

/-- Actual smooth periodic fields have bounded finite prefixes of full Fréchet
jets on every compact radial slab. -/
theorem periodic_finiteJet_bound {f : State → F} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ U, TorusPeriodic (fun Y => f (U, Y))) (a b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ U ∈ Icc a b, ∀ Y : Plane,
      ‖iteratedFDeriv ℝ j f (U, Y)‖ ≤ C := by
  let K : Set State := Icc a b ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hc : Continuous (fun z : State => ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j f z‖) :=
    continuous_finsetSum _ (fun j _ => (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous.norm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro j hj U hU Y
  let k : Frequency := (-⌊Y.1⌋, -⌊Y.2⌋)
  let Z : Plane := Y + ((k.1 : ℝ), (k.2 : ℝ))
  have hZ : Z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [Z, k, Prod.fst_add, Prod.fst, Int.cast_neg, ← sub_eq_add_neg, Int.fract]
        using (show Int.fract Y.1 ∈ Icc (0 : ℝ) 1 from
          ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
    · simpa only [Z, k, Prod.snd_add, Prod.snd, Int.cast_neg, ← sub_eq_add_neg, Int.fract]
        using (show Int.fract Y.2 ∈ Icc (0 : ℝ) 1 from
          ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  have hperiod : iteratedFDeriv ℝ j f (U, Z) = iteratedFDeriv ℝ j f (U, Y) :=
    iteratedFDeriv_periodic hp j U Y k
  rw [← hperiod]
  have hj' : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i f (U, Z)‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) hj'
    _ ≤ ‖∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i f (U, Z)‖‖ := Real.le_norm_self _
    _ ≤ C := hC (U, Z) ⟨hU, hZ⟩
    _ ≤ max C 0 := le_max_left _ _

variable [CompleteSpace F]


theorem cutoffAlias_supported {a b M : ℝ} {v : Plane} {f : State → F} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) :
    RadialAlias.RadiallySupported a b (cutoffAlias χ M v f) := by
  have hsc := TransportPrimitive.compactIntegral_supported (M := M) (v := v)
    hf.continuous hs hleft hright
  have hsd := TransportPrimitive.fixedDeriv_supported hsc (1, M • v)
  intro z hz
  by_contra hzn
  have hfz : f z = 0 := by
    by_contra hfz
    exact hzn (hs hfz)
  have hdz : TransportPrimitive.fixedDeriv (1, M • v)
      (TransportPrimitive.compactIntegral χ M v f) z = 0 := by
    by_contra hdz
    exact hzn (hsd hdz)
  have heq := transport_compact_eq_sub_alias (M := M) (v := v) hχ hf hs z
  have ha : -cutoffAlias χ M v f z = 0 := by simpa [hfz, hdz] using heq.symm
  exact hz (neg_eq_zero.mp ha)


end Averages

section IntegrationByParts

theorem sourceJet_smooth (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ)
    (hf : ContDiff ℝ ∞ f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n))) :
    ContDiff ℝ ∞ (RadialAlias.sourceJet J f p) := by
  cases p with
  | zero => exact hf
  | succ p =>
    rw [RadialAlias.sourceJet_succ]
    exact TransportPrimitive.fixedDeriv_contDiff (hJ p (Nat.lt_succ_self p)) (1, 0)

/-- The existing repeated IBP identity, now for the actual U-dependent total
integral. No alias is discarded. -/
theorem totalIntegral_sourceJet {a b M : ℝ} {v : Plane}
    (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ) (hM : M ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hsf : RadialAlias.RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n)))
    (hsJ : ∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n)))
    (hr : ∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
      RadialAlias.sourceJet J f n) (z : State) :
    TransportPrimitive.totalIntegral M v f z = (-M⁻¹) ^ p •
      TransportPrimitive.totalIntegral M v (RadialAlias.sourceJet J f p) z := by
  rw [TransportPrimitive.totalIntegral_eq_wholeAlias hf.continuous hsf,
    TransportPrimitive.totalIntegral_eq_wholeAlias (sourceJet_smooth J f p hf hJ).continuous
      (RadialAlias.sourceJet_radiallySupported J f p hsf hsJ)]
  exact RadialAlias.wholeAlias_sourceJet J f p hM
    (fun n hn => (hJ n hn).of_le (by simp)) hsJ hr

theorem cutoffAlias_sourceJet {a b M : ℝ} {v : Plane}
    (χ : ℝ → ℝ) (J : (State → ℂ) → State → ℂ) (f : State → ℂ) (p : ℕ) (hM : M ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hsf : RadialAlias.RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n)))
    (hsJ : ∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n)))
    (hr : ∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
      RadialAlias.sourceJet J f n) (z : State) :
    cutoffAlias χ M v f z = (-M⁻¹) ^ p • cutoffAlias χ M v (RadialAlias.sourceJet J f p) z := by
  rw [cutoffAlias, totalIntegral_sourceJet J f p hM hf hsf hJ hsJ hr]
  exact smul_comm _ _ _


end IntegrationByParts

section ActualFourierInverse

open ParametricTorusInverse

/-- Remove the actual full torus mean at each fixed radial coordinate. -/
noncomputable def nonbarPart (f : State → ℂ) (z : State) : ℂ := f z - mean f z.1

theorem nonbarPart_smooth {f : State → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nonbarPart f) :=
  hf.sub ((coefficient_smooth hf 0).comp contDiff_fst)

theorem nonbarPart_periodic {f : State → ℂ} (hp : ParametricTorusInverse.Periodic f) :
    ParametricTorusInverse.Periodic (nonbarPart f) := by
  intro U Y k
  exact congrArg (fun q => q - mean f U) (hp U Y k)

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




/-- The successive slow derivatives of actual directional Fourier inverses. -/
noncomputable def fourierSourceJet (d : Direction) (f : State → ℂ) (p : ℕ) : State → ℂ :=
  RadialAlias.sourceJet (inverse d) f p


theorem inverse_radiallySupported (d : Direction) {a b : ℝ} {f : State → ℂ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (inverse d f) := by
  have hh : ∀ U, U ∉ Icc a b → ∀ Y, f (U, Y) = 0 := by
    intro U hU Y
    by_contra hn
    exact hU (hs hn)
  have hi := inverse_preserves_parameter_support d f (Icc a b) hh
  intro z hz
  by_contra hn
  exact hz (hi z.1 hn z.2)

theorem fourierSourceJet_properties (d : Direction) {a b : ℝ} {f : State → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : ParametricTorusInverse.Periodic f)
    (hm : ZeroMean f) (hs : RadialAlias.RadiallySupported a b f) (p : ℕ) :
    ContDiff ℝ ∞ (fourierSourceJet d f p) ∧
      ParametricTorusInverse.Periodic (fourierSourceJet d f p) ∧
      ZeroMean (fourierSourceJet d f p) ∧
      RadialAlias.RadiallySupported a b (fourierSourceJet d f p) := by
  induction p with
  | zero => exact ⟨hf, hp, hm, hs⟩
  | succ p ih =>
    have heq : fourierSourceJet d f (p + 1) = parameterPartial (inverse d (fourierSourceJet d f p)) :=
      RadialAlias.sourceJet_succ (inverse d) f p
    rw [heq]
    have hi := inverse_smooth d ih.1 ih.2.1
    exact ⟨parameterPartial_smooth hi, parameterPartial_periodic (inverse_periodic d _),
      parameterPartial_zeroMean hi (inverse_zeroMean d ih.1 ih.2.1),
      RadialAlias.radialSupport_slowDeriv (inverse_radiallySupported d ih.2.2.2)⟩






end ActualFourierInverse

section SmallScale

/-- The actual chart slow scale is subpower relative to epsilon. Consequently
an arbitrary fixed slow loss can be absorbed into half of a positive epsilon
gain. The reciprocal-frequency premise alone would not imply this for an
unrestricted scale `S`. -/
theorem inverse_frequency_eventually_small {M : ℕ → ℝ} {h κ A growth : ℝ}
    (hh : 0 < h) (hκ : 0 < κ)
    (hbound : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) :
    ∀ᶠ n in atTop, |M n|⁻¹ ≤ ChartScales.epsilon h n ^ (κ / 2) := by
  have ht : Tendsto (fun n : ℕ => A * (ChartScales.S n ^ growth *
      ChartScales.epsilon h n ^ (κ / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ChartScales.slow_power_epsilon_tendsto_zero h hh growth (κ / 2) (half_pos hκ)).const_mul A
  have hs : ∀ᶠ n : ℕ in atTop, A * (ChartScales.S n ^ growth *
      ChartScales.epsilon h n ^ (κ / 2)) < 1 :=
    (tendsto_order.1 ht).2 1 zero_lt_one
  filter_upwards [hbound, hs] with n hn hsn
  have he : ChartScales.epsilon h n ^ κ =
      ChartScales.epsilon h n ^ (κ / 2) * ChartScales.epsilon h n ^ (κ / 2) := by
    rw [← Real.rpow_add (ChartScales.epsilon_pos h n)]
    congr 1
    ring
  calc
    _ ≤ A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth := hn
    _ = (A * (ChartScales.S n ^ growth * ChartScales.epsilon h n ^ (κ / 2))) *
        ChartScales.epsilon h n ^ (κ / 2) := by rw [he]; ring
    _ ≤ 1 * ChartScales.epsilon h n ^ (κ / 2) :=
      mul_le_mul_of_nonneg_right hsn.le (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _)
    _ = _ := one_mul _





end SmallScale

end NavierStokes.FourierAlias
