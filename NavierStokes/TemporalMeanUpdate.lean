import NavierStokes.ParametricTorusInverse
import NavierStokes.SmoothFamilyTorusInverse
import NavierStokes.PressureStream
import NavierStokes.ChartScales
import NavierStokes.TorusAverages
import NavierStokes.UniformFourierAlias

/-!
# The exact temporal mean update

The native-to-absolute inverse identity is derived from the actual covering
map, Fourier coefficients, and uniqueness for the zero-mean periodic
directional equation. Band factors remain explicit.
-/

noncomputable section

namespace NavierStokes.TemporalMeanUpdate

open Set Filter MeasureTheory Function
open TorusInverse
open scoped Topology ContDiff BigOperators Interval

noncomputable def partialY (f : Plane → ℂ) (z : Plane) : ℂ := fderiv ℝ f z (0, 1)
noncomputable def timeDerivative (f : Plane → ℂ) (z : Plane) : ℂ :=
  fderiv ℝ f z (vector .temporal)

theorem partialY_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialY f) :=
  (ContinuousLinearMap.apply ℝ ℂ (0, 1)).contDiff.comp (hf.fderiv_right (by simp))

theorem coefficient_const_mul (c : ℂ) (f : Plane → ℂ) (k : Frequency) :
    SmoothFourierData.coefficient (fun z => c * f z) k = c * SmoothFourierData.coefficient f k := by
  simp only [SmoothFourierData.coefficient, SmoothFourierData.unitCoeff_const_mul]

theorem coefficient_add {f g : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (k : Frequency) :
    SmoothFourierData.coefficient (fun z => f z + g z) k =
      SmoothFourierData.coefficient f k + SmoothFourierData.coefficient g k := by
  let K := SmoothFourierData.kernel k
  have hK : ContDiff ℝ ∞ K := ParametricTorusInverse.kernel_smooth k
  have hif : ContDiff ℝ ∞ (fun y : ℝ => ∫ x in (0 : ℝ)..1, K (x, y) * f (x, y)) :=
    TransportPrimitive.parameterIntegral_contDiff
      ((hK.mul hf).comp (contDiff_snd.prodMk contDiff_fst)) 0 1
  have hig : ContDiff ℝ ∞ (fun y : ℝ => ∫ x in (0 : ℝ)..1, K (x, y) * g (x, y)) :=
    TransportPrimitive.parameterIntegral_contDiff
      ((hK.mul hg).comp (contDiff_snd.prodMk contDiff_fst)) 0 1
  have hi (y : ℝ) : (∫ x in (0 : ℝ)..1, K (x, y) * (f (x, y) + g (x, y))) =
      (∫ x in (0 : ℝ)..1, K (x, y) * f (x, y)) + (∫ x in (0 : ℝ)..1, K (x, y) * g (x, y)) := by
    simp_rw [mul_add]
    exact intervalIntegral.integral_add
      (((hK.mul hf).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)
      (((hK.mul hg).continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)
  simp only [SmoothFourierData.coefficient_eq_doubleIntegral]
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, K (x, y) * (f (x, y) + g (x, y))) = _
  simp_rw [hi]
  exact intervalIntegral.integral_add (hif.continuous.intervalIntegrable 0 1)
    (hig.continuous.intervalIntegrable 0 1)

/-- Fourier differentiation, including the zero first frequency. -/
theorem coefficient_partialX {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (k : Frequency) :
    SmoothFourierData.coefficient (SmoothFourierData.partialX f) k =
      (omega * (k.1 : ℂ)) * SmoothFourierData.coefficient f k := by
  by_cases hk : k.1 = 0
  · have hi (y : ℝ) : SmoothFourierData.unitCoeff
        (fun x => SmoothFourierData.partialX f (x, y)) 0 = 0 := by
      rw [SmoothFourierData.unitCoeff_eq_integral]
      simp only [neg_zero, fourier_zero, one_mul]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => SmoothFourierData.hasDerivAt_slice ((hf.differentiable (by simp)) (x, y)))
        (((SmoothFourierData.partialX_smooth hf).continuous.comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)]
      have he : f (1, y) = f (0, y) := by simpa using hp (0, y) (1, 0)
      rw [he, sub_self]
    simp only [SmoothFourierData.coefficient, hk, hi, Int.cast_zero, mul_zero, zero_mul]
    simp [SmoothFourierData.unitCoeff_eq_integral]
  · have hden : omega * (k.1 : ℂ) ≠ 0 := mul_ne_zero omega_ne_zero (by exact_mod_cast hk)
    rw [SmoothFourierData.coefficient_partialX hf hp hk, ← mul_assoc, mul_inv_cancel₀ hden, one_mul]

theorem swap_partialY {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    SmoothFourierData.swapFunction (partialY f) =
      SmoothFourierData.partialX (SmoothFourierData.swapFunction f) := by
  funext z
  let L : Plane →L[ℝ] Plane := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap
  have h := ((hf.differentiable (by simp)) (z.2, z.1)).hasFDerivAt.comp z L.hasFDerivAt
  change fderiv ℝ f (z.2, z.1) (0, 1) = fderiv ℝ (f ∘ L) z (1, 0)
  rw [h.fderiv]
  rfl

theorem coefficient_partialY {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (k : Frequency) :
    SmoothFourierData.coefficient (partialY f) k =
      (omega * (k.2 : ℂ)) * SmoothFourierData.coefficient f k := by
  rw [SmoothFourierData.coefficient_swap (partialY_smooth hf).continuous k, swap_partialY hf,
    coefficient_partialX (SmoothFourierData.swapFunction_smooth hf)
      (SmoothFourierData.swapFunction_periodic hp)]
  rw [← SmoothFourierData.coefficient_swap hf.continuous k]

theorem timeDerivative_eq_partials (f : Plane → ℂ) (z : Plane) :
    timeDerivative f z = ((vector .temporal).1 : ℂ) * SmoothFourierData.partialX f z +
      ((vector .temporal).2 : ℂ) * partialY f z := by
  have hv : vector .temporal = (vector .temporal).1 • ((1, 0) : Plane) +
      (vector .temporal).2 • ((0, 1) : Plane) := by ext <;> simp
  conv_lhs => rw [timeDerivative, hv, map_add, map_smul, map_smul]
  simp only [Complex.real_smul, SmoothFourierData.partialX, partialY]

/-- The temporal Fourier symbol is the actual multiplier of the derivative. -/
theorem coefficient_timeDerivative {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (k : Frequency) :
    SmoothFourierData.coefficient (timeDerivative f) k =
      (omega * (symbol .temporal k : ℂ)) * SmoothFourierData.coefficient f k := by
  have heq : timeDerivative f = fun z => ((vector .temporal).1 : ℂ) * SmoothFourierData.partialX f z +
      ((vector .temporal).2 : ℂ) * partialY f z := funext (timeDerivative_eq_partials f)
  rw [heq, coefficient_add (contDiff_const.mul (SmoothFourierData.partialX_smooth hf))
    (contDiff_const.mul (partialY_smooth hf)), coefficient_const_mul, coefficient_const_mul,
    coefficient_partialX hf hp, coefficient_partialY hf hp]
  have hs : (symbol .temporal k : ℂ) =
      (k.1 : ℂ) * ((vector .temporal).1 : ℂ) + (k.2 : ℂ) * ((vector .temporal).2 : ℂ) := by
    exact_mod_cast symbol_formula .temporal k
  rw [hs]
  ring

/-- Uniqueness for the smooth periodic temporal equation with a prescribed
mean. The proof uses actual Fourier differentiation and reconstruction. -/
theorem timeDerivative_unique {f g : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : SmoothFourierData.UnitPeriodic f) (hpg : SmoothFourierData.UnitPeriodic g)
    (hD : timeDerivative f = timeDerivative g)
    (hm : TorusAverages.squareAverage f = TorusAverages.squareAverage g) : f = g := by
  have hc : SmoothFourierData.coefficient f = SmoothFourierData.coefficient g := by
    funext k
    by_cases hk : k = 0
    · subst k
      simpa only [SmoothFourierData.coefficient_zero_eq_integral, TorusAverages.squareAverage] using hm
    · have he := congrArg (fun q => SmoothFourierData.coefficient q k) hD
      rw [coefficient_timeDerivative hf hpf, coefficient_timeDerivative hg hpg] at he
      exact mul_left_cancel₀ (mul_ne_zero omega_ne_zero
        (Complex.ofReal_ne_zero.mpr (symbol_ne_zero .temporal hk))) he
  funext z
  rw [← SmoothFourierData.series_coefficient hf hpf z,
    ← SmoothFourierData.series_coefficient hg hpg z, hc]

/-- The actual integer covering as a continuous linear map. -/
noncomputable def coverLinear : Plane →L[ℝ] Plane :=
  ((3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ + (5 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem coverLinear_apply (z : Plane) : coverLinear z = TorusAverages.covering z := by
  simp [coverLinear, TorusAverages.covering]

noncomputable def coverMap : ℕ → Plane →L[ℝ] Plane
  | 0 => ContinuousLinearMap.id ℝ Plane
  | n + 1 => coverLinear.comp (coverMap n)

theorem coverMap_eq_iterate (n : ℕ) (z : Plane) :
    coverMap n z = TorusAverages.covering^[n] z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change coverLinear (coverMap n z) = _
      rw [coverLinear_apply, ih, Function.iterate_succ_apply']

theorem coverLinear_temporal :
    coverLinear (vector .temporal) = ChartScales.Tg • vector .temporal := by
  rw [coverLinear_apply]
  ext <;> dsimp [TorusAverages.covering, vector, ChartScales.Tg, SlotColoring.coverGrowth]
  · nlinarith [DiophantineGraph.sqrt_two_square]
  · ring

theorem coverMap_temporal (n : ℕ) :
    coverMap n (vector .temporal) = ChartScales.Tg ^ n • vector .temporal := by
  induction n with
  | zero => simp [coverMap]
  | succ n ih =>
      change coverLinear (coverMap n (vector .temporal)) = _
      rw [ih, map_smul, coverLinear_temporal, smul_smul, pow_succ]

theorem coverLinear_lattice (k : Frequency) :
    coverLinear ((k.1 : ℝ), (k.2 : ℝ)) =
      (((DiophantineGraph.coveringFrequency k).1 : ℝ),
        ((DiophantineGraph.coveringFrequency k).2 : ℝ)) := by
  rw [coverLinear_apply]
  simp [TorusAverages.covering, DiophantineGraph.coveringFrequency]

theorem coverMap_lattice (n : ℕ) (k : Frequency) :
    coverMap n ((k.1 : ℝ), (k.2 : ℝ)) =
      (((DiophantineGraph.coveringFrequency^[n] k).1 : ℝ),
        ((DiophantineGraph.coveringFrequency^[n] k).2 : ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change coverLinear (coverMap n ((k.1 : ℝ), (k.2 : ℝ))) = _
      rw [ih, coverLinear_lattice, Function.iterate_succ_apply']

theorem periodic_coverMap {f : Plane → ℂ} (hp : SmoothFourierData.UnitPeriodic f) (n : ℕ) :
    SmoothFourierData.UnitPeriodic (fun z => f (coverMap n z)) := by
  intro z k
  change f (coverMap n (z + ((k.1 : ℝ), (k.2 : ℝ)))) = f (coverMap n z)
  rw [map_add, coverMap_lattice]
  exact hp _ _

theorem timeDerivative_coverMap {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (z : Plane) :
    timeDerivative (fun x => f (coverMap n x)) z =
      ChartScales.Tg ^ n • timeDerivative f (coverMap n z) := by
  have hd := ((hf.differentiable (by simp)) (coverMap n z)).hasFDerivAt.comp z
    (coverMap n).hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [timeDerivative, hd.fderiv]
  change fderiv ℝ f (coverMap n z) (coverMap n (vector .temporal)) = _
  rw [coverMap_temporal, map_smul]
  rfl

noncomputable def absoluteInverse (f : Plane → ℂ) : Plane → ℂ :=
  directionalInverse .temporal (SmoothFourierData.coefficient f)

theorem absoluteInverse_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) : ContDiff ℝ ∞ (absoluteInverse f) :=
  contDiff_directionalInverse .temporal (SmoothFourierData.rapid_coefficient hf hp)

theorem absoluteInverse_periodic (f : Plane → ℂ) :
    SmoothFourierData.UnitPeriodic (absoluteInverse f) := by
  intro z k
  exact directionalInverse_periodic .temporal (SmoothFourierData.coefficient f) z k.1 k.2

theorem absoluteInverse_zeroMean {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) : TorusAverages.squareAverage (absoluteInverse f) = 0 := by
  have ha := SmoothFourierData.rapid_coefficient hf hp
  let g : C(Torus, ℂ) := ⟨torusSeries (inverseCoeff .temporal (SmoothFourierData.coefficient f)),
    continuous_torusSeries (ha.inverseCoeff .temporal)⟩
  have hg : SmoothFourierData.torusLift g = absoluteInverse f := by
    funext Y
    exact (series_eq_torusSeries (inverseCoeff .temporal (SmoothFourierData.coefficient f)) Y).symm
  rw [← hg, TorusAverages.squareAverage_torusLift]
  exact inverse_zero_mean .temporal ha

theorem absoluteInverse_solves {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (hm : TorusAverages.squareAverage f = 0) :
    timeDerivative (absoluteInverse f) = f := by
  funext z
  exact SmoothFourierData.inverse_solves_smooth_periodic .temporal hf hp hm z

/-- The native factor is forced by the covering derivative and zero-mean
uniqueness. Both sides are the actual Fourier-defined inverse. -/
theorem absoluteInverse_coverMap {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : SmoothFourierData.UnitPeriodic f) (hm : TorusAverages.squareAverage f = 0) (n : ℕ) :
    absoluteInverse (fun z => f (coverMap n z)) =
      fun z => (ChartScales.Tg ^ n)⁻¹ • absoluteInverse f (coverMap n z) := by
  have hfc : ContDiff ℝ ∞ (fun z => f (coverMap n z)) := hf.comp (coverMap n).contDiff
  have hpc := periodic_coverMap hp n
  have hmc : TorusAverages.squareAverage (fun z => f (coverMap n z)) = 0 := by
    simp_rw [coverMap_eq_iterate]
    exact (TorusAverages.squareAverage_covering_iterate hf.continuous hp n).trans hm
  have hi := absoluteInverse_smooth hf hp
  have hip := absoluteInverse_periodic f
  have hright : ContDiff ℝ ∞ (fun z => (ChartScales.Tg ^ n)⁻¹ • absoluteInverse f (coverMap n z)) :=
    (hi.comp (coverMap n).contDiff).const_smul _
  apply timeDerivative_unique (absoluteInverse_smooth hfc hpc) hright
    (absoluteInverse_periodic _) (fun z k => congrArg ((ChartScales.Tg ^ n)⁻¹ • ·)
      (periodic_coverMap hip n z k))
  · rw [absoluteInverse_solves hfc hpc hmc]
    funext z
    have hs := (((hi.comp (coverMap n).contDiff).differentiable (by simp)) z).hasFDerivAt.fun_const_smul
      ((ChartScales.Tg ^ n)⁻¹)
    simp only [Function.comp_def] at hs
    symm
    rw [timeDerivative, hs.fderiv]
    change (ChartScales.Tg ^ n)⁻¹ • timeDerivative (fun x => absoluteInverse f (coverMap n x)) z = _
    rw [timeDerivative_coverMap hi, absoluteInverse_solves hf hp hm, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ChartScales.Tg_pos.ne'), one_smul]
  · rw [absoluteInverse_zeroMean hfc hpc]
    simp only [TorusAverages.squareAverage, intervalIntegral.integral_smul]
    change 0 = (ChartScales.Tg ^ n)⁻¹ • TorusAverages.squareAverage
      (fun z => absoluteInverse f (coverMap n z))
    simp_rw [coverMap_eq_iterate]
    rw [TorusAverages.squareAverage_covering_iterate hi.continuous hip n,
      absoluteInverse_zeroMean hf hp, smul_zero]

/-- The native chart prefactor, including the physical velocity rescaling. -/
noncomputable def chartPrefactor (h : ℝ) (n : ℕ) : ℝ :=
  (ChartScales.timeCoefficient h n)⁻¹

theorem chartPrefactor_pos (h : ℝ) (n : ℕ) : 0 < chartPrefactor h n :=
  inv_pos.mpr (ChartScales.timeCoefficient_pos h n)


/-- The exponential-looking native factors together cost just one power of
the slow band scale. -/
theorem chartPrefactor_bound (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    ‖chartPrefactor h n‖ ≤ ChartScales.Tg * ChartScales.S n := by
  rw [Real.norm_eq_abs, abs_of_pos (chartPrefactor_pos h n)]
  exact ChartScales.timeCoefficient_inv_upper h hh hn



/-- Finite initial bands are absorbed into an explicit constant. The native
indices are unchanged; the slow scale may be `max 1 (S n)`. -/
theorem chartPrefactor_bandBound_all {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (s : WeightedClasses.StripData D) (h : ℝ) (hh : 0 ≤ h)
    (hs : ∀ n, ChartScales.S n ≤ s.slow n) :
    WeightedClasses.BandBound s 0 (chartPrefactor h) := by
  let A := ∑ i ∈ Finset.range 4, chartPrefactor h i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => (chartPrefactor_pos h i).le)
  have hK : 0 ≤ ChartScales.Tg + A := add_nonneg ChartScales.Tg_pos.le hA
  refine ⟨ChartScales.Tg + A, hK, 1, ?_⟩
  intro n
  simp only [Real.rpow_zero, mul_one, pow_one]
  by_cases hn : 4 ≤ n
  · exact (chartPrefactor_bound h hh hn).trans
      (mul_le_mul (le_add_of_nonneg_right hA) (hs n)
        (sq_nonneg (n : ℝ)) hK)
  · rw [Real.norm_eq_abs, abs_of_pos (chartPrefactor_pos h n)]
    have hnA : chartPrefactor h n ≤ A :=
      Finset.single_le_sum (fun i _ => (chartPrefactor_pos h i).le)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    exact hnA.trans ((le_add_of_nonneg_left ChartScales.Tg_pos.le).trans
      (le_mul_of_one_le_right hK (s.one_le_slow n)))

theorem meanClass_chartPrefactor_all {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : WeightedClasses.StripData D} {α h : ℝ} {f : ℕ → D → E}
    (hh : 0 ≤ h) (hs : ∀ n, ChartScales.S n ≤ s.slow n)
    (hf : WeightedClasses.MeanClass s α f) :
    WeightedClasses.MeanClass s α (fun n z => chartPrefactor h n • f n z) := by
  unfold WeightedClasses.MeanClass
  simpa only [add_zero] using hf.band_smul (chartPrefactor_bandBound_all s h hh hs)

section CenteredSource

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Remove exactly the auxiliary torus average, retaining every slow parameter. -/
noncomputable def centered (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  f z - PressureStream.torusAverage f (z.1, z.2.1)

theorem centered_smooth {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (centered f) :=
  hf.sub ((PressureStream.torusAverage_contDiff hf).comp
    (contDiff_fst.prodMk contDiff_snd.fst))

theorem centered_zeroMean {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : ℝ × S) : PressureStream.torusAverage (centered f) p = 0 := by
  change PressureStream.torusAverage (fun z => f z - PressureStream.torusAverage f (z.1, z.2.1)) p = 0
  rw [PressureStream.torusAverage_sub_slow hf, sub_self]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem centered_periodic {f : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) : PressureStream.TorusPeriodicLift (centered f) := by
  intro r s Y k
  simp only [centered]
  have he := hp r s Y k
  dsimp at he
  rw [he]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem centered_supported {a b : ℝ} {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (centered f) := by
  intro z hz
  by_contra hout
  have hf0 : f z = 0 := by
    by_contra hn
    exact hout (hs hn)
  have hm0 : PressureStream.torusAverage f (z.1, z.2.1) = 0 := by
    by_contra hn
    exact hout (PressureStream.torusAverage_supported hs hn)
  exact hz (by simp [centered, hf0, hm0])

end CenteredSource

/-- Taking a real part commutes with the actual double integral. -/
theorem squareAverage_re {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    TorusAverages.squareAverage (fun z => (f z).re) = (TorusAverages.squareAverage f).re := by
  have hi : ContDiff ℝ ∞ (fun y : ℝ => ∫ x in (0 : ℝ)..1, f (x, y)) :=
    TransportPrimitive.parameterIntegral_contDiff
      (hf.comp (contDiff_snd.prodMk contDiff_fst)) 0 1
  have hxs (y : ℝ) : IntervalIntegrable (fun x => f (x, y)) volume 0 1 :=
    (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, (f (x, y)).re) =
      (∫ x in (0 : ℝ)..1, f (x, y)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hxs y)
  unfold TorusAverages.squareAverage
  simp_rw [show ∀ y : ℝ, (∫ x in (0 : ℝ)..1, (f (x, y)).re) =
      (∫ x in (0 : ℝ)..1, f (x, y)).re from fun y => hx y]
  exact Complex.reCLM.intervalIntegral_comp_comm (hi.continuous.intervalIntegrable 0 1)

section FamilyInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The source in joint slow-parameter/torus coordinates, with the real
source embedded isometrically in the complex Fourier construction. -/
noncomputable def sourceToFamily (f : PressureStream.Lift S → ℝ)
    (z : (ℝ × S) × Plane) : ℂ := f (z.1.1, (z.1.2, z.2))

theorem sourceToFamily_smooth {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sourceToFamily f) :=
  Complex.ofRealCLM.contDiff.comp
    (hf.comp (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).toContinuousLinearEquiv.contDiff)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceToFamily_periodic {f : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift f) : SmoothFamilyTorusInverse.Periodic (sourceToFamily f) := by
  intro p Y k
  exact congrArg Complex.ofReal (hp p.1 p.2 Y k)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceToFamily_mean (f : PressureStream.Lift S → ℝ) (p : ℝ × S) :
    SmoothFamilyTorusInverse.mean (sourceToFamily f) p =
      (PressureStream.torusAverage f p : ℂ) := by
  rw [SmoothFamilyTorusInverse.mean_eq_integral]
  simp only [sourceToFamily, PressureStream.torusAverage, PressureStream.torusInner,
    ← intervalIntegral.integral_ofReal]

/-- The actual normalized temporal Fourier inverse on a real joint family. -/
noncomputable def temporalInverse (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f) ((z.1, z.2.1), z.2.2)).re

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalInverse_periodic (f : PressureStream.Lift S → ℝ) :
    PressureStream.TorusPeriodicLift (temporalInverse f) := by
  intro r s Y k
  exact congrArg Complex.re
    (SmoothFamilyTorusInverse.inverse_periodic .temporal (sourceToFamily f) (r, s) Y k)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalInverse_supported {a b : ℝ} {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (temporalInverse f) := by
  have hsource : ∀ p : ℝ × S, p ∉ Prod.fst ⁻¹' Icc a b → ∀ Y : Plane,
      sourceToFamily f (p, Y) = 0 := by
    intro p hp Y
    have hf0 : f (p.1, (p.2, Y)) = 0 := by
      by_contra hn
      exact hp (hs hn)
    simp only [sourceToFamily, hf0, Complex.ofReal_zero]
  intro z hz
  by_contra hn
  have hi := SmoothFamilyTorusInverse.inverse_preserves_parameter_support .temporal
    (sourceToFamily f) (Prod.fst ⁻¹' Icc a b) hsource (z.1, z.2.1) hn z.2.2
  exact hz (by simp only [temporalInverse, hi, Complex.zero_re])

variable [FiniteDimensional ℝ S]

theorem temporalInverse_smooth {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) : ContDiff ℝ ∞ (temporalInverse f) :=
  (Complex.reCLM.contDiff.comp (SmoothFamilyTorusInverse.inverse_smooth .temporal
    (sourceToFamily_smooth hf) (sourceToFamily_periodic hp))).comp
    (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv.contDiff

theorem temporalInverse_zeroMean {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (temporalInverse f) p = 0 := by
  have hi := SmoothFamilyTorusInverse.inverse_smooth .temporal
    (sourceToFamily_smooth hf) (sourceToFamily_periodic hp)
  have hm := SmoothFamilyTorusInverse.inverse_zeroMean .temporal
    (sourceToFamily_smooth hf) (sourceToFamily_periodic hp) p
  rw [SmoothFamilyTorusInverse.mean_eq_integral] at hm
  change TorusAverages.squareAverage
    (fun Y => (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f) (p, Y)).re) = 0
  have hs : ContDiff ℝ ∞ (fun Y => SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f) (p, Y)) :=
    SmoothFamilyTorusInverse.slice_smooth hi p
  rw [squareAverage_re hs]
  exact (congrArg Complex.re hm).trans rfl

/-- The real joint inverse solves the genuine Fréchet directional equation. -/
theorem temporalInverse_solves {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hm : ∀ p, PressureStream.torusAverage f p = 0) (z : PressureStream.Lift S) :
    PressureStream.graphDz ((0 : S), vector .temporal) (temporalInverse f) z = f z := by
  have hfs := sourceToFamily_smooth hf
  have hps := sourceToFamily_periodic hp
  have hms : SmoothFamilyTorusInverse.ZeroMean (sourceToFamily f) := by
    intro p
    rw [sourceToFamily_mean, hm p, Complex.ofReal_zero]
  let q : (ℝ × S) × Plane := ((z.1, z.2.1), z.2.2)
  let L := (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hi := SmoothFamilyTorusInverse.inverse_smooth .temporal hfs hps
  have hD := (Complex.reCLM.hasFDerivAt.comp q
    (((hi.differentiable (by simp)) q).hasFDerivAt)).comp z L.hasFDerivAt
  change HasFDerivAt (temporalInverse f) _ z at hD
  rw [PressureStream.graphDz, hD.fderiv]
  change (fderiv ℝ (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f)) q
    (0, vector .temporal)).re = f z
  have he := congrFun (SmoothFamilyTorusInverse.inverse_solves .temporal hfs hps hms) q
  change fderiv ℝ (SmoothFamilyTorusInverse.inverse .temporal (sourceToFamily f)) q
    (0, vector .temporal) = sourceToFamily f q at he
  rw [he]
  rfl

end FamilyInverse

section ExactUpdate

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] in
/-- Fiberwise native-to-absolute covariance for the actual real family inverse. -/
theorem temporalInverse_coverMap {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hm : ∀ p, PressureStream.torusAverage f p = 0) (n : ℕ) (z : PressureStream.Lift S) :
    temporalInverse (fun p => f (p.1, (p.2.1, coverMap n p.2.2))) z =
      (ChartScales.Tg ^ n)⁻¹ * temporalInverse f (z.1, (z.2.1, coverMap n z.2.2)) := by
  let q : Plane → ℂ := fun Y => sourceToFamily f ((z.1, z.2.1), Y)
  have hq : ContDiff ℝ ∞ q := SmoothFamilyTorusInverse.slice_smooth (sourceToFamily_smooth hf) _
  have hqp : SmoothFourierData.UnitPeriodic q := sourceToFamily_periodic hp _
  have hqm : TorusAverages.squareAverage q = 0 := by
    change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      sourceToFamily f ((z.1, z.2.1), (x, y))) = 0
    rw [← SmoothFamilyTorusInverse.mean_eq_integral, sourceToFamily_mean, hm, Complex.ofReal_zero]
  change (absoluteInverse (fun Y => q (coverMap n Y)) z.2.2).re =
    (ChartScales.Tg ^ n)⁻¹ * (absoluteInverse q (coverMap n z.2.2)).re
  rw [absoluteInverse_coverMap hq hqp hqm n]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The desired angular or axial mean increment in its native chart. -/
noncomputable def desiredIncrement (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  -chartPrefactor h n * temporalInverse (centered f) z

/-- The actual fast-time derivative, including its chart coefficient. -/
noncomputable def fastDerivative (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  ChartScales.timeCoefficient h n * PressureStream.graphDz ((0 : S), vector .temporal) f z

theorem desiredIncrement_smooth (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    ContDiff ℝ ∞ (desiredIncrement h n f) :=
  contDiff_const.mul (temporalInverse_smooth (centered_smooth hf) (centered_periodic hp))


omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem desiredIncrement_supported (h : ℝ) (n : ℕ) {a b : ℝ} {f : PressureStream.Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (desiredIncrement h n f) := by
  intro z hz
  apply temporalInverse_supported (centered_supported hs)
  intro hi
  exact hz (by simp only [desiredIncrement, hi, mul_zero])

theorem desiredIncrement_zeroMean (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (desiredIncrement h n f) p = 0 := by
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    -chartPrefactor h n * temporalInverse (centered f) (p.1, (p.2, (x, y)))) = 0
  simp_rw [intervalIntegral.integral_const_mul]
  change -chartPrefactor h n * PressureStream.torusAverage (temporalInverse (centered f)) p = 0
  rw [temporalInverse_zeroMean (centered_smooth hf) (centered_periodic hp), mul_zero]




end ExactUpdate

section NativePullback

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def pullbackCover (i : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ := f (z.1, (z.2.1, coverMap i z.2.2))



theorem torusAverage_pullbackCover (i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (pullbackCover i f) p = PressureStream.torusAverage f p := by
  change TorusAverages.squareAverage (fun Y => f (p.1, (p.2, coverMap i Y))) =
    TorusAverages.squareAverage (fun Y => f (p.1, (p.2, Y)))
  simp_rw [coverMap_eq_iterate]
  exact TorusAverages.squareAverage_covering_iterate_real
    (hf.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hp p.1 p.2) i



end NativePullback

section AxialReconstruction

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def axialPotential (d a b M : ℝ) (v : Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.streamPotential d a b M ((0 : S), v) (desiredIncrement h n f)

noncomputable def axialUpdate (d a b M : ℝ) (v : Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : S), v)
    (axialPotential d a b M v h n f)

noncomputable def radialUpdate (d a b M : ℝ) (v : Plane) (w : S × Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.streamBeta w (axialPotential d a b M v h n f)


/-- The retained compactification alias, with its physical `1/r` factor. -/
noncomputable def axialAlias (d a b M : ℝ) (v : Plane) (h : ℝ) (n : ℕ)
    (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  PressureStream.divideRadius (RadialPullback.physicalAlias d a b M ((0 : S), v)
    (PressureStream.weightedSource (desiredIncrement h n f)))










/-- No compactification error is removed from the reconstructed axial field. -/
theorem axialUpdate_eq_desired_sub_alias {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane) (h : ℝ) (n : ℕ)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (hs : RadialAlias.RadiallySupported a b f) :
    axialUpdate d a b M v h n f = fun z => desiredIncrement h n f z - axialAlias d a b M v h n f z := by
  funext z
  exact PressureStream.streamGamma_eq_desired_sub_alias_global ha hab hd (0, v)
    (desiredIncrement_smooth h n hf hp) (desiredIncrement_supported h n hs) z





end AxialReconstruction

section WeightedStream

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]





end WeightedStream

section AliasPullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def aliasFactor (d a r : ℝ) : ℝ :=
  RadialPullback.radialJacobian d (RadialPullback.positiveRadius (a / 4) r) /
    RadialPullback.positiveRadius (a / 4) r


/-- The physical divided alias is exactly a fixed radial multiplier times
the normalized transport alias pulled through the power chart. -/
theorem dividedAlias_eq_pullback {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : E) (g : ℝ × E → ℝ) :
    PressureStream.divideRadius (RadialPullback.physicalAlias d a b M v g) =
      fun z => aliasFactor d a z.1 * UniformFourierAlias.exactAlias
        (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) M v (RadialPullback.normalizeSource d a g)
          (RadialPullback.liftChart (RadialPullback.powerChart d a) z) := by
  funext z
  by_cases hr : a ≤ z.1
  · dsimp [PressureStream.divideRadius, RadialPullback.physicalAlias, UniformFourierAlias.exactAlias,
      RadialPullback.liftChart, aliasFactor]
    rw [RadialPullback.positiveRadius_eq_self (show 0 < a / 4 by positivity) (by linarith)]
    ring
  · have hχ := RadialPullback.deriv_interiorCutoff_zero_left
      (Real.rpow_lt_rpow ha.le hab hd) (RadialPullback.powerChart_lt_left ha hd (lt_of_not_ge hr)).le
    simp only [PressureStream.divideRadius, RadialPullback.physicalAlias, UniformFourierAlias.exactAlias,
      RadialPullback.liftChart, hχ, mul_zero, zero_smul, zero_div]


end AliasPullback

section WeightedTemporal

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


theorem meanClass_centered {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => centered (f n)) :=
  UniformFourierAlias.meanClass_realCenterSource ha hcL hcR ε R hε hεone hR hf hfc hp





end WeightedTemporal

section PhysicalAliasSuperflat

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem normalizeSource_periodic (d a : ℝ) {g : PressureStream.Lift S → ℝ}
    (hp : PressureStream.TorusPeriodicLift g) :
    PressureStream.TorusPeriodicLift (RadialPullback.normalizeSource d a g) := by
  intro r s Y k
  dsimp [RadialPullback.normalizeSource, RadialPullback.liftChart]
  have he := hp (RadialPullback.inverseChart d a r) s Y k
  dsimp at he
  rw [he]

omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem normalizeSource_torusAverage (d a : ℝ) (g : PressureStream.Lift S → ℝ) (p : ℝ × S) :
    PressureStream.torusAverage (RadialPullback.normalizeSource d a g) p =
      RadialPullback.sourceMultiplier d a p.1 *
        PressureStream.torusAverage g (RadialPullback.inverseChart d a p.1, p.2) := by
  simp only [PressureStream.torusAverage, PressureStream.torusInner,
    RadialPullback.normalizeSource, RadialPullback.liftChart, smul_eq_mul,
    intervalIntegral.integral_const_mul]




omit [FiniteDimensional ℝ S] [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem timeCoefficient_norm_le_one {h : ℝ} (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    ‖ChartScales.timeCoefficient h n‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (ChartScales.timeCoefficient_pos h n)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hS : 1 ≤ ChartScales.S n := by dsimp [ChartScales.S]; nlinarith
  exact (ChartScales.timeCoefficient_bounds h hh hn).2.trans
    (by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS)


end PhysicalAliasSuperflat

section InteriorAliasClass

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem interiorCutoff_deriv_zero_left {a b U : ℝ} (hab : a < b)
    (hU : U < (2 * a + b) / 3) : deriv (TransportPrimitive.interiorCutoff a b) U = 0 := by
  have he : TransportPrimitive.interiorCutoff a b =ᶠ[𝓝 U] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds hU] with u hu
    exact TransportPrimitive.interiorCutoff_zero hab hu.le
  exact ((hasDerivAt_const U (0 : ℝ)).congr_of_eventuallyEq he).deriv

theorem interiorCutoff_deriv_zero_right {a b U : ℝ} (hab : a < b)
    (hU : (a + 2 * b) / 3 < U) : deriv (TransportPrimitive.interiorCutoff a b) U = 0 := by
  have he : TransportPrimitive.interiorCutoff a b =ᶠ[𝓝 U] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hU] with u hu
    exact TransportPrimitive.interiorCutoff_one hab hu.le
  exact ((hasDerivAt_const U (1 : ℝ)).congr_of_eventuallyEq he).deriv



end InteriorAliasClass

section CompleteWeightedUpdate

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]





end CompleteWeightedUpdate

end NavierStokes.TemporalMeanUpdate
