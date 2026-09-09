import NavierStokes.ScaledActualParticularControl
import NavierStokes.LocalizedGaussianBounds

/-!
# Gaussian coverage for the actual scaled particular solves

The cutoff used by the inverse is the separate Gaussian slot cutoff times
the padded native-clock cutoff.  The dyadic, radial, and slow source masks
remain in the source and amplitude.  Whole-path support, rather than a
pointwise zero of the source, supplies zero germs for the actual Volterra
solution.
-/

noncomputable section

namespace NavierStokes.ActualGaussianCoverage

open Set Function Filter WeightedClasses
open CommonCoverSolve TorusInverse ParticularWaveBounds PrimaryPulseBounds
open PeriodizedWaveBounds HarmonicCalculus
open scoped Topology ContDiff BigOperators

/-! ## The normalized clock and the actual envelope -/

theorem normalized_clock {L c : ℝ} (hL : L ≠ 0) (_hc : c ≠ 0) (v : ℝ) :
    c * v / L = v / (L / c) := by
  field_simp


noncomputable def gaussianRate (lam u : ℝ) : ℝ :=
  u * GaussianEnvelope.referenceMinSlope lam u / 2

theorem gaussianRate_pos {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    0 < gaussianRate lam u :=
  div_pos (mul_pos hu (GaussianEnvelope.referenceMinSlope_pos hlam hu)) (by norm_num)

theorem gaussianRate_mono {a b u : ℝ} (hu : 0 < u) (hab : a ≤ b) :
    gaussianRate a u ≤ gaussianRate b u := by
  unfold gaussianRate GaussianEnvelope.referenceMinSlope
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab hu.le)
        (PulseGrowth.dampingDenominator_pos u).le) hu.le) (by norm_num)

theorem referenceP_scaled_bound {lam u L c : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) (hc : 0 < c)
    {v : ℝ} (hv : v ∈ Icc 0 (L / c)) :
    referenceP lam u L (c * v) ≤
      Real.exp (-(gaussianRate lam u * c) * (v / (L / c) - 1 / 2) ^ 2 * (L / c)) := by
  have hcv : c * v ∈ Icc 0 L :=
    ⟨mul_nonneg hc.le hv.1, by simpa only [mul_comm] using (le_div_iff₀ hc).mp hv.2⟩
  have htheta : c * v / L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hcv.1 hL.le, (div_le_one hL).mpr hcv.2⟩
  have hb := GaussianTailFlat.referenceSlotEnvelope_bound hlam hu hL (c * v / L)
  rw [GaussianTailFlat.referenceSlotEnvelope, ite_eq_left htheta] at hb
  have htime : L * (c * v / L) = c * v := by field_simp
  rw [htime] at hb
  change referenceP lam u L (c * v) ≤ Real.exp
    (-gaussianRate lam u * (c * v / L - 1 / 2) ^ 2 * L) at hb
  refine hb.trans_eq ?_
  congr 1
  rw [normalized_clock hL.ne' hc.ne']
  field_simp

section ScaledEnvelope

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)

noncomputable def theta (l : Label) (n : ℕ) (v : ℝ) : ℝ :=
  clock.value l n * v / F.L (l, n)

theorem theta_eq (l : Label) (n : ℕ) (v : ℝ) :
    theta F clock l n v = v / ScaledActualParticularControl.length F clock l n :=
  normalized_clock (F.L_pos (l, n)).ne' (clock.value_pos l n).ne' v

theorem envelope_uniform_bound {lam0 u0 : ℝ} (_hlam0 : 0 < lam0) (hu0 : 0 < u0)
    (hlam : ∀ l n, lam0 ≤ F.lam (l, n)) (hu : ∀ l n, F.u (l, n) = u0)
    (l : Label) (n : ℕ) {v : ℝ}
    (hv : v ∈ Icc 0 (ScaledActualParticularControl.length F clock l n)) :
    ScaledActualParticularControl.envelope F clock l n v ≤
      Real.exp (-(gaussianRate lam0 u0 * clock.lower) * (theta F clock l n v - 1 / 2) ^ 2 *
        ScaledActualParticularControl.length F clock l n) := by
  have hb := referenceP_scaled_bound (F.lam_pos (l, n)) (F.u_pos (l, n))
    (F.L_pos (l, n)) (clock.value_pos l n) hv
  change ScaledActualParticularControl.envelope F clock l n v ≤ _ at hb
  rw [hu l n] at hb
  change ScaledActualParticularControl.envelope F clock l n v ≤
    Real.exp (-(gaussianRate (F.lam (l,n)) u0 * clock.value l n) *
      (v / ScaledActualParticularControl.length F clock l n - 1 / 2) ^ 2 *
        ScaledActualParticularControl.length F clock l n) at hb
  rw [← theta_eq F clock] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hcoeff : gaussianRate lam0 u0 * clock.lower ≤
      gaussianRate (F.lam (l, n)) u0 * clock.value l n :=
    mul_le_mul (gaussianRate_mono hu0 (hlam l n)) (clock.bounds l n).1
      clock.lower_pos.le (gaussianRate_pos (F.lam_pos (l, n)) hu0).le
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (theta F clock l n v - 1 / 2)))
    (ScaledActualParticularControl.length_pos F clock l n).le
  nlinarith


end ScaledEnvelope

/-! ## Compact whole-path zero germs for the genuine Volterra solve -/

section PathGerms

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem whole_path_zero_germ (g : Geometry) (k : Frequency) {a b : ℝ}
    {f : P × Plane → ComplexVector} {x : P × Plane}
    (hf : ∀ v ∈ Icc a b, f =ᶠ[𝓝 (x.1, g.path k x.2 v)] fun _ => 0) :
    ∀ᶠ y in 𝓝 x, ∀ v ∈ Icc a b, f (y.1, g.path k y.2 v) = 0 := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro v hv
  exact (hf v hv).comp_tendsto (g.pathArgument_contDiff k).continuous.continuousAt

theorem complexCopyVelocity_zero_germ (t : TangentData P ProblemStatement.Space)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency)
    {f : P × Plane → ComplexVector} {x : P × Plane}
    (hf : ∀ v ∈ Icc a b, f =ᶠ[𝓝 (x.1, g.path k x.2 v)] fun _ => 0) :
    complexCopyVelocity t f g hab k =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [whole_path_zero_germ g k hf] with y hy
  exact complexCopyVelocity_zero_of_path t f g hab k y.1 y.2 hy

end PathGerms

/-! ## The separate Gaussian cutoff and its genuine outer padding -/

noncomputable def padding (r L : ℝ) : ℝ := min r L / 16

theorem padding_pos {r L : ℝ} (hr : 0 < r) (hL : 0 < L) : 0 < padding r L :=
  div_pos (lt_min hr hL) (by norm_num)

noncomputable def referenceWindow (r L : ℝ) (hr : 0 < r) (hL : 0 < L) :
    PeriodicPhaseAssembly.ClockWindow where
  lower := (-r, 0)
  upper := (r, L)
  padding := padding r L
  padding_pos := padding_pos hr hL


/-- This cutoff is separate from every dyadic, radial and slow source
mask.  The outer padding is transported together with the Gaussian. -/
noncomputable def nativeCutoff (r L : ℝ) (hr : 0 < r) (hL : 0 < L) (c : ℝ) : Plane → ℝ :=
  fun z => (referenceWindow r L hr hL).cutoff (CopySolveCompatibility.nativeTimeMap 0 c z) *
    GaussianTailFlat.slotCutoff L (c * z.2)

noncomputable def outerCell (r L c : ℝ) : Set Plane :=
  Icc (-r - 2 * padding r L) (r + 2 * padding r L) ×ˢ
    Icc ((-2 * padding r L) / c) ((L + 2 * padding r L) / c)

/-- The support inherited from a Gaussian slot profile has a strict
temporal margin at both ends of the full Volterra integration interval. -/
noncomputable def sourceCell (r L c : ℝ) : Set Plane :=
  Icc (-r) r ×ˢ Icc ((L / c) / 6) (5 * (L / c) / 6)

theorem outerCell_compact (r L c : ℝ) : IsCompact (outerCell r L c) :=
  isCompact_Icc.prod isCompact_Icc

theorem sourceCell_compact (r L c : ℝ) : IsCompact (sourceCell r L c) :=
  isCompact_Icc.prod isCompact_Icc

theorem mem_outerCell {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) (z : Plane) :
    z ∈ outerCell r L c ↔
      CopySolveCompatibility.nativeTimeMap 0 c z ∈ (referenceWindow r L hr hL).outer := by
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [ mem_Icc, CopySolveCompatibility.nativeTimeMap, referenceWindow, zero_sub, zero_add,
    div_le_iff₀ hc, le_div_iff₀ hc, mul_comm, neg_mul]

theorem sourceCell_time {r L c : ℝ} (hL : 0 < L) (hc : 0 < c) {z : Plane}
    (hz : z ∈ sourceCell r L c) : z.2 ∈ Ioo 0 (L / c) := by
  have hp := div_pos hL hc
  exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem sourceCell_subset_outer {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) :
    sourceCell r L c ⊆ outerCell r L c := by
  intro z hz
  apply (mem_outerCell hr hL hc z).mpr
  apply (referenceWindow r L hr hL).core_subset_outer
  have ht := sourceCell_time hL hc hz
  simp only [referenceWindow, PeriodicPhaseAssembly.ClockWindow.core,
    CopySolveCompatibility.nativeTimeMap, zero_add, mem_prod]
  change z.1 ∈ Icc (-r) r ∧ c * z.2 ∈ Icc 0 L
  exact ⟨hz.1, mul_nonneg hc.le ht.1.le,
    by simpa only [mul_comm] using (le_div_iff₀ hc).mp ht.2.le⟩

theorem nativeCutoff_support {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) :
    support (nativeCutoff r L hr hL c) ⊆ outerCell r L c := by
  intro z hz
  apply (mem_outerCell hr hL hc z).mpr
  exact (referenceWindow r L hr hL).cutoff_support (mul_ne_zero_iff.mp hz).1

theorem nativeCutoff_central_germ {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    {z : Plane} (hz : z ∈ WaveEnvelopeTransport.rectangle r (L / c))
    (hcentral : |z.2 / (L / c) - 1 / 2| < 1 / 5) :
    nativeCutoff r L hr hL c =ᶠ[𝓝 z] fun _ => 1 := by
  have hm : CopySolveCompatibility.nativeTimeMap 0 c z ∈ (referenceWindow r L hr hL).core := by
    simp only [referenceWindow, PeriodicPhaseAssembly.ClockWindow.core,
      CopySolveCompatibility.nativeTimeMap, zero_add, mem_prod]
    exact ⟨hz.1, mul_nonneg hc.le hz.2.1,
      by simpa only [mul_comm] using (le_div_iff₀ hc).mp hz.2.2⟩
  have ho := ((referenceWindow r L hr hL).cutoff_germ hm).comp_tendsto
    (CopySolveCompatibility.nativeTimeMap_continuous 0 c).continuousAt
  have ht : Continuous (fun y : Plane => c * y.2 / L) :=
    (continuous_const.mul continuous_snd).div_const L
  have hg := (GaussianTailFlat.profile_eventually_one
    (by simpa only [normalized_clock hL.ne' hc.ne'] using hcentral)).comp_tendsto ht.continuousAt
  filter_upwards [ho, hg] with y hy hgy
  dsimp only [Function.comp_def] at hy hgy
  simp only [nativeCutoff, GaussianTailFlat.slotCutoff, hy, hgy, mul_one]

theorem nativeCutoff_time_zero_germ {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    {z : Plane} (hz : z.2 ∉ Ioo 0 (L / c)) :
    nativeCutoff r L hr hL c =ᶠ[𝓝 z] fun _ => 0 := by
  have hlen := div_pos hL hc
  have hdist : 1 / 3 < |z.2 / (L / c) - 1 / 2| := by
    by_cases hlo : z.2 ≤ 0
    · rw [abs_of_nonpos (by linarith [div_nonpos_of_nonpos_of_nonneg hlo hlen.le])]
      linarith [div_nonpos_of_nonpos_of_nonneg hlo hlen.le]
    · have hhi : L / c ≤ z.2 := le_of_not_gt (fun h => hz ⟨lt_of_not_ge hlo, h⟩)
      have hdiv : 1 ≤ z.2 / (L / c) := (le_div_iff₀ hlen).mpr (by simpa using hhi)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hd : 1 / 3 < |c * z.2 / L - 1 / 2| := by
    rw [normalized_clock hL.ne' hc.ne']
    exact hdist
  have ht : Continuous (fun y : Plane => c * y.2 / L) :=
    (continuous_const.mul continuous_snd).div_const L
  have hg := (GaussianTailFlat.profile_eventually_zero hd).comp_tendsto ht.continuousAt
  filter_upwards [hg] with y hy
  dsimp only [Function.comp_def] at hy
  simp only [nativeCutoff, GaussianTailFlat.slotCutoff, hy, mul_zero]

/-! ## Source support controls the entire native path -/

theorem coordinates_path_outer (g : Geometry) (k : Frequency) {Y : Plane}
    {r L c v : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hY : g.coordinates k Y ∈ outerCell r L c) (hv : v ∈ Icc 0 (L / c)) :
    g.coordinates k (g.path k Y v) ∈ outerCell r L c := by
  rw [g.coordinates_path]
  refine ⟨hY.1, ?_, ?_⟩
  · exact (div_nonpos_of_nonpos_of_nonneg (by nlinarith [padding_pos hr hL]) hc.le).trans hv.1
  · exact hv.2.trans (div_le_div_of_nonneg_right (by linarith [padding_pos hr hL]) hc.le)

theorem other_sourceCell_excluded (g : Geometry) {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' outerCell r L c))
    {k : Frequency} {Y : Plane} (hY : g.coordinates k Y ∈ outerCell r L c)
    (hn : g.coordinates k Y ∉ sourceCell r L c) :
    ∀ i, g.coordinates i Y ∉ sourceCell r L c := by
  intro i hi
  have he := ParticularWaveAssembly.native_copy_unique g hinj hY
    (sourceCell_subset_outer hr hL hc hi)
  subst i
  exact hn hi

theorem path_sourceCell_excluded (g : Geometry) {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' outerCell r L c))
    {k : Frequency} {Y : Plane} (hY : g.coordinates k Y ∈ outerCell r L c)
    (hxi : (g.coordinates k Y).1 ∉ Icc (-r) r) :
    ∀ v ∈ Icc 0 (L / c), ∀ i, g.coordinates i (g.path k Y v) ∉ sourceCell r L c := by
  intro v hv
  apply other_sourceCell_excluded g hr hL hc hinj (coordinates_path_outer g k hr hL hc hY hv)
  intro hs
  rw [g.coordinates_path] at hs
  exact hxi hs.1

section ActualSource

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def sourceRegion (S : Set P) (g : Geometry) (r L rate : ℝ) : Set (P × Plane) :=
  Prod.fst ⁻¹' S ∩ HarmonicSourceSupport.nativeUnion g (sourceCell r L rate)

omit [NormedSpace ℝ P] in
theorem sourceRegion_closed {S : Set P} (hS : IsClosed S) (g : Geometry) (r L rate : ℝ) :
    IsClosed (sourceRegion S g r L rate) :=
  (hS.preimage continuous_fst).inter
    (HarmonicSourceSupport.nativeUnion_closed g (sourceCell_compact r L rate))

theorem sourceFamily_zero_germ
    (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    {U : Set (P × Plane)} {K : ℕ → Set (P × Plane)} (hU : IsOpen U)
    (hK : ∀ n, IsClosed (K n)) (hs : HarmonicSourceSupport.InputSupportOn U K b G A)
    (j : ℤ) (n : ℕ) {x : (P × ℝ) × Plane}
    (hx : (x.1.1, x.2) ∈ U) (hn : (x.1.1, x.2) ∉ K n) :
    ParticularWaveAssembly.sourceFamily ctx u b G A j n =ᶠ[𝓝 x] fun _ => 0 :=
  (HarmonicSourceSupport.residualSource_zero_germ_on ctx u b G A hU hK hs j n hx hn).comp_tendsto
    (continuous_fst.fst.prodMk continuous_snd).continuousAt


end ActualSource

theorem transported_outer_injective (g : Geometry) (gap : ℕ) {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' (referenceWindow r L hr hL).outer)) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (CopySolveCompatibility.transportGeometry g gap 0 c hc.ne').center +
        (CopySolveCompatibility.transportGeometry g gap 0 c hc.ne').basis z) '' outerCell r L c) := by
  apply hinj.mono
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨CopySolveCompatibility.nativeTimeMap 0 c z, (mem_outerCell hr hL hc z).mp hz, ?_⟩
  simp only [CopySolveCompatibility.nativeTimeMap, CopySolveCompatibility.transportGeometry,
    CopySolveCompatibility.refineGeometry, CopySolveCompatibility.timeGeometry,
    CommonCoverClass.scaledBasis_apply, zero_add, Prod.mk_zero_zero, map_zero, add_zero]


/-! ## One literal family of scaled solves and cutoffs -/

section Family

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)



noncomputable def sourceRegions (S : Label → ℕ → Set P) (l : Label) (n : ℕ) : Set (P × Plane) :=
  sourceRegion (S l n) (ScaledActualParticularControl.geometry reference gap clock l n)
    (r l n) (F.L (l,n)) (clock.value l n)


variable (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)




variable (s : StripData P) (S : Label → ℕ → Set P) (hS : ∀ l n, IsClosed (S l n))
  (hsupport : ∀ l, HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
    (sourceRegions F clock reference gap r S l) (b l) (G l) (A l))

include hS hsupport





end Family

/-! ## Uniform jets of the actual Gaussian clock cutoff -/

section AffineJets

variable {X Label I : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Translated native copies share the same constants: only the linear
part of their normalized clock enters the estimate. -/
theorem affine_profile_uniform_jets (s : StripData X)
    (C : Label → ℕ → I → Set X) (A : Label → ℕ → X →L[ℝ] ℝ)
    (b : Label → ℕ → I → ℝ)
    (hA : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ l n, ‖A l n‖ ≤ K * s.slow n ^ p) :
    UniformLocalJets s (fun _ _ _ => 1) 0 C
      (fun l n i x => GaussianTailFlat.profile (b l n i + A l n x)) := by
  obtain ⟨K, hK, p, hA⟩ := hA
  refine ⟨fun l n i _ _ _ =>
    (GaussianTailFlat.profile_contDiff.comp (contDiff_const.add (A l n).contDiff)).contDiffAt, ?_⟩
  intro m
  obtain ⟨B, hB, hb⟩ := GaussianTailFlat.finite_jet_bounds GaussianTailFlat.profile_jet_bounded m
  refine ⟨B * K ^ m, by positivity, p * m, ?_⟩
  intro l n i x hx hi j hj
  have hbase : 1 ≤ K * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ (s.one_le_growth n x))
  have hAn : ‖A l n‖ ≤ K * s.growth n x ^ p :=
    (hA l n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
      (zero_le_one.trans hK))
  calc
    _ ≤ ‖iteratedFDeriv ℝ j GaussianTailFlat.profile (b l n i + A l n x)‖ * ‖A l n‖ ^ j :=
      GaussianTailFlat.norm_affine_comp_jet_le GaussianTailFlat.profile_contDiff (A l n) (b l n i) x j
    _ ≤ B * (K * s.growth n x ^ p) ^ m :=
      mul_le_mul (hb j hj _) ((pow_le_pow_left₀ (norm_nonneg _) hAn j).trans
        (pow_le_pow_right₀ hbase hj)) (pow_nonneg (norm_nonneg _) _) hB
    _ = majorant s (fun _ _ => 1) 0 (B * K ^ m) (p * m) n x := by
      simp only [majorant, Real.rpow_zero, mul_one, mul_pow, ← pow_mul]
      ring

end AffineJets

section ClockJets

variable {P Label : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)

/-- The primitive rate bound for the selected phase family controls the
inverse transported slot length without any loss in the copy index. -/
theorem inverse_length_bound {u0 : ℝ} (hu0 : 0 < u0)
    (hu : ∀ l n, F.u (l,n) = u0) (l : Label) (n : ℕ) :
    (ScaledActualParticularControl.length F clock l n)⁻¹ ≤ clock.upper * F.M / u0 := by
  have hp : 0 ≤ u0 / F.L (l,n) := (div_pos hu0 (F.L_pos (l,n))).le
  have hb : u0 / F.L (l,n) ≤ F.M := by
    calc
      _ ≤ u0 / F.L (l,n) * D.scale (l,n) :=
        le_mul_of_one_le_right hp (D.one_le_scale (l,n))
      _ ≤ F.M := by simpa only [hu l n, abs_of_nonneg hp] using F.rate_bound (l,n)
  have hmul := mul_le_mul_of_nonneg_left hb (clock.upper_one.trans' zero_le_one)
  have hr := mul_le_mul_of_nonneg_right (clock.bounds l n).2 hp
  have hh := div_le_div_of_nonneg_right (hr.trans hmul) hu0.le
  convert! hh using 1
  dsimp only [ScaledActualParticularControl.length]
  field_simp [hu0.ne', (F.L_pos (l,n)).ne', (clock.value_pos l n).ne']

noncomputable def normalizedLinear (g : Geometry) (L : ℝ) : (P × Plane) →L[ℝ] ℝ :=
  L⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P Plane)))

theorem normalizedLinear_apply (g : Geometry) (L : ℝ) (x : P × Plane) :
    normalizedLinear (P := P) g L x = (g.coordinateLinear x.2).2 / L := by
  change L⁻¹ * (g.coordinateLinear x.2).2 = (g.coordinateLinear x.2).2 / L
  ring

theorem normalized_coordinate_affine (g : Geometry) (L : ℝ) (k : Frequency) (x : P × Plane) :
    (g.coordinates k x.2).2 / L = (g.coordinates k 0).2 / L + normalizedLinear (P := P) g L x := by
  rw [g.coordinates_eq_affine, normalizedLinear_apply]
  simp only [Prod.snd_add, add_div]

theorem normalizedLinear_norm (g : Geometry) {L : ℝ} (hL : 0 < L) :
    ‖normalizedLinear (P := P) g L‖ ≤ L⁻¹ * CommonCoverClass.argumentCost g := by
  have hc : ‖g.coordinateLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    have h : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (inv_nonneg.mpr hL.le) (zero_le_one.trans (CommonCoverClass.one_le_argumentCost g)))
  intro x
  rw [normalizedLinear_apply, norm_div,
    show ‖L‖ = L by simp only [Real.norm_eq_abs, abs_of_pos hL]]
  calc
    _ ≤ ‖g.coordinateLinear x.2‖ / L := div_le_div_of_nonneg_right (norm_snd_le _) hL.le
    _ ≤ (‖g.coordinateLinear‖ * ‖x.2‖) / L :=
      div_le_div_of_nonneg_right (g.coordinateLinear.le_opNorm _) hL.le
    _ ≤ (CommonCoverClass.argumentCost g * ‖x‖) / L :=
      div_le_div_of_nonneg_right (mul_le_mul hc (norm_snd_le _) (norm_nonneg _)
        (zero_le_one.trans (CommonCoverClass.one_le_argumentCost g))) hL.le
    _ = _ := by ring

theorem gaussian_clock_uniform_jets
    (s : StripData (P × Plane)) (C : Label → ℕ → Frequency → Set (P × Plane))
    (g : Label → ℕ → Geometry) {u0 : ℝ} (hu0 : 0 < u0) (hu : ∀ l n, F.u (l,n) = u0)
    (hcost : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ,
      ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ K * s.slow n ^ p) :
    UniformLocalJets s (fun _ _ _ => 1) 0 C
      (fun l n k x => GaussianTailFlat.profile
        (theta F clock l n ((g l n).coordinates k x.2).2)) := by
  obtain ⟨K, hK, p, hcost⟩ := hcost
  have hc : 0 ≤ clock.upper * F.M / u0 :=
    div_nonneg (mul_nonneg (zero_le_one.trans clock.upper_one)
      (zero_le_one.trans F.one_le_M)) hu0.le
  have hA : ∃ A : ℝ, 1 ≤ A ∧ ∃ p : ℕ, ∀ l n,
      ‖normalizedLinear (P := P) (g l n) (ScaledActualParticularControl.length F clock l n)‖ ≤
        A * s.slow n ^ p := by
    refine ⟨1 + (clock.upper * F.M / u0) * K,
      le_add_of_nonneg_right (mul_nonneg hc (zero_le_one.trans hK)), p, fun l n => ?_⟩
    calc
      _ ≤ (ScaledActualParticularControl.length F clock l n)⁻¹ *
          CommonCoverClass.argumentCost (g l n) :=
        normalizedLinear_norm (g l n) (ScaledActualParticularControl.length_pos F clock l n)
      _ ≤ (clock.upper * F.M / u0) * (K * s.slow n ^ p) :=
        mul_le_mul (inverse_length_bound F clock hu0 hu l n) (hcost l n)
          (zero_le_one.trans (CommonCoverClass.one_le_argumentCost _)) hc
      _ ≤ (1 + (clock.upper * F.M / u0) * K) * s.slow n ^ p := by
        nlinarith [pow_nonneg (zero_le_one.trans (s.one_le_slow n)) p]
  have hj := affine_profile_uniform_jets s C
    (fun l n => normalizedLinear (P := P) (g l n) (ScaledActualParticularControl.length F clock l n))
    (fun l n k => ((g l n).coordinates k 0).2 / ScaledActualParticularControl.length F clock l n) hA
  convert! hj using 1
  funext l n k x
  rw [theta_eq, normalized_coordinate_affine]

end ClockJets

section CutoffJets

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)
  (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)



end CutoffJets

/-! ## The actual complex solve inherits the modal amplitude estimates -/

section ModalAmplitude

variable {P Label : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Countable Label] [Nonempty Label]


end ModalAmplitude

/-! ## The all-powers bound for the assembled, actual Gaussian error -/

section AllGains

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)





variable [Countable Label] [Nonempty Label]
  (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)


end AllGains

section CurrentSourceJets

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}


end CurrentSourceJets

/-! ## Bindings to the selected reference window and primary family -/




theorem mem_sourceCell_clock {r L c : ℝ} (hc : 0 < c) (z : Plane) :
    z ∈ sourceCell r L c ↔
      CopySolveCompatibility.nativeTimeMap 0 c z ∈ sourceCell r L 1 := by
  simp only [sourceCell, mem_prod, mem_Icc, CopySolveCompatibility.nativeTimeMap, zero_add, div_one]
  have hlo : L / c / 6 = (L / 6) / c := by ring
  have hhi : 5 * (L / c) / 6 = (5 * L / 6) / c := by ring
  rw [hlo, hhi, div_le_iff₀ hc, le_div_iff₀ hc]
  simp only [mul_comm]

section ActualWindow

variable {D h : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem D h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)

theorem actual_slot_length_pos (m : ℕ) : 0 < ChartScales.slotLength sys.radius h m :=
  div_pos (mul_pos (by norm_num) sys.radius_pos) (ChartScales.timeCoefficient_pos h m)


/-- The actual slot system supplies the geometric injectivity needed
for finite periodization cells, including their outer padding. -/
theorem actual_outer_injective (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1)
    (gap : ℕ) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (ActualSignedGeometry.slotGeometry sys hdet l gap).center +
        (ActualSignedGeometry.slotGeometry sys hdet l gap).basis z) ''
        (referenceWindow sys.radius (ChartScales.slotLength sys.radius h l.1) sys.radius_pos
          (actual_slot_length_pos sys l.1)).outer) :=
  ActualSignedGeometry.clockWindow_injective sys hdet hh hl gap


end ActualWindow

section ActualParametersAndMasks

variable {profile : OutgoingProfile.Profile} {W : NominalProfile.Witness profile}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0) (hr0 : 0 < r0)

theorem prepared_lambda_lower (sign : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    a.M⁻¹ ≤ (PrimaryGeometryAssembly.construction H v a hr0 sign).lam L := by
  rw [PrimaryGeometryAssembly.construction_lambda]
  exact ((a.parameters L).positive_lower a.one_le_M
    (a.radius_pos L _ (PrimaryGeometryAssembly.representative_in_carrier W L)) (a.cone L)).2.2.1

theorem prepared_gaussian_rate_pos : 0 < gaussianRate a.M⁻¹ a.u :=
  gaussianRate_pos (inv_pos.mpr (zero_lt_one.trans_le a.one_le_M)) a.u_pos

/-- The closed slow support is the actual one-mesh primary mask.
Its inclusion in the two-mesh analytic phase cell has a genuine margin. -/
noncomputable def actualSlowCore (L : PrimaryGeometryAssembly.Index W a.N) : Set PhaseCalculus.Slow :=
  tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
    (PrimaryGeometryAssembly.label W L).2)

theorem actualSlowCore_closed (L : PrimaryGeometryAssembly.Index W a.N) :
    IsClosed (actualSlowCore H v a L) := isClosed_tsupport _

theorem actualSlowCore_inside (L : PrimaryGeometryAssembly.Index W a.N) {p : PhaseCalculus.Slow}
    (hp : p ∈ actualSlowCore H v a L) (ht : 0 < p.2.2) :
    p ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L :=
  PrimaryGeometryAssembly.native_support_in_carrier W L ⟨hp, ht⟩

noncomputable def actualSourceCore (L : PrimaryGeometryAssembly.Index W a.N) : Set ActualSignedGeometry.Native :=
  actualSlowCore H v a L ×ˢ sourceCell r0
    (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L)) 1





variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]




end ActualParametersAndMasks

/-! ## A weighted companion for physical edge estimates -/

section WeightedGaussian

open LocalizedWaveBounds GaussianTailFlat

variable {X E I Label : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only the dyadic exponent is absorbed. The flat edge weight is retained
for the subsequent physical extension estimate. -/
theorem gaussian_epsilon_shift (s : StripData X) (scales : BandScaleControl s)
    {c : ℝ} (hc : 0 < c) (α β : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n,
      s.epsilon n ^ α * Real.exp (-c * ChartScales.S n) ≤ B * s.epsilon n ^ β := by
  obtain ⟨B, hB, hb⟩ := gaussian_beats_Q_power hc 0 (scales.power * (β - α))
  refine ⟨B, hB, fun n => ?_⟩
  have hQ := ChartScales.Q_pos n
  have hg : Real.exp (-c * ChartScales.S n) ≤ B * ChartScales.Q n ^ (scales.power * (β - α)) := by
    simpa only [pow_zero, one_mul] using hb n
  rw [scales.epsilon_eq, ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
  calc
    _ ≤ ChartScales.Q n ^ (scales.power * α) *
        (B * ChartScales.Q n ^ (scales.power * (β - α))) :=
      mul_le_mul_of_nonneg_left hg (Real.rpow_pos_of_pos hQ _).le
    _ = B * (ChartScales.Q n ^ (scales.power * α) *
        ChartScales.Q n ^ (scales.power * (β - α))) := by ring
    _ = _ := by rw [← Real.rpow_add hQ]; congr 2; ring

/-- The Gaussian gain preserves `sqrt(zeta)` exactly. Unlike the
unweighted absorption theorem, this estimate retains its original
polynomial inverse-edge degree; the positive edge weight remains
available to absorb that degree in physical coordinates. -/
theorem indexed_gaussian_weighted_all_gains {s : StripData X} {K : ℕ → I → Set X}
    {W : ℕ → I → X → ℝ} {α c : ℝ} {f : ℕ → I → X → E}
    (hf : LocalWave s K W α f) (scales : BandScaleControl s)
    (θ : ℕ → I → X → ℝ) (L : ℕ → I → ℝ) (hL : ∀ n i, 0 < L n i)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n i, ell * ChartScales.S n ≤ L n i) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n i x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n i))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (β : ℝ) : LocalClass s K (fun _ _ x => Real.sqrt (s.zeta x)) β f := by
  refine ⟨fun _ _ _ _ => Real.sqrt_nonneg _, hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  obtain ⟨B, hB, hshift⟩ := gaussian_epsilon_shift s scales
    (by positivity : 0 < c * ell / 25) α β
  refine ⟨A * B, mul_nonneg hA hB.le, p, ?_⟩
  intro n i x hx hi j hj
  by_cases hm : |θ n i x - 1 / 2| < 1 / 5
  · rw [jets_eq_of_germ (hzero n i x hx hi hm) j]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
      majorant_nonneg s (fun _ x => Real.sqrt (s.zeta x)) β (mul_nonneg hA hB.le) p n x
        (Real.sqrt_nonneg _)
  have htail : 1 / 5 ≤ |θ n i x - 1 / 2| := le_of_not_gt hm
  have hsq : (1 / 25 : ℝ) ≤ (θ n i x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : W n i x ≤ Real.exp (-(c * ell / 25) * ChartScales.S n) := by
    apply (hW n i x hx hi).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (hLell n i))
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (hL n i).le)]
  have hweight : s.epsilon n ^ α * W n i x ≤ B * s.epsilon n ^ β :=
    (mul_le_mul_of_nonneg_left hPg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le).trans (hshift n)
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * W n i x) α A p n x := hb n i x hx hi j hj
    _ = (A * s.growth n x ^ p * Real.sqrt (s.zeta x)) * (s.epsilon n ^ α * W n i x) := by
      unfold majorant; ring
    _ ≤ (A * s.growth n x ^ p * Real.sqrt (s.zeta x)) * (B * s.epsilon n ^ β) :=
      mul_le_mul_of_nonneg_left hweight
        (mul_nonneg (mul_nonneg hA (pow_nonneg (s.growth_nonneg n x) p)) (Real.sqrt_nonneg _))
    _ = majorant s (fun _ x => Real.sqrt (s.zeta x)) β (A * B) p n x := by
      unfold majorant; ring

/-- Weighted counterpart of the frozen LGB gluing theorem. The source
complement retains the same edge weight and still occurs exactly once. -/
theorem uniform_globalGaussian_weighted_from_supported_native
    (a : Label → CopyData X I) (K : Label → Cells X I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData X} (d : LinearWaveBounds.GraphDirections X) (C : Label → ℕ → I → Set X)
    {W : Label → ℕ → X → ℝ} {α c : ℝ}
    (hWnonneg : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hfast : BandBound s 0 d.fastScale)
    (hu : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l => (a l).amplitude))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n _ => (a l).source n))
    (scales : BandScaleControl s)
    (θ : Label → ℕ → I → X → ℝ) (length : Label → ℕ → ℝ)
    (hL : ∀ l n, 0 < length l n) (ell : ℝ) (hell : 0 < ell)
    (hLell : ∀ l n, ell * ChartScales.S n ≤ length l n) (hc : 0 < c)
    (hW : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      W l n x ≤ Real.exp (-c * (θ l n i x - 1 / 2) ^ 2 * length l n))
    (hcentral : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → |θ l n i x - 1 / 2| < 1 / 5 →
      ((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∉ C l n i →
      (((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ)
    (hcomplement : LocalizedGaussianBounds.UniformComplementJets s
      (fun _ _ x => Real.sqrt (s.zeta x)) β (fun l => (K l).carrier) (fun l => (a l).source)) :
    LabelSumBounds.UniformClass s (fun _ _ x => Real.sqrt (s.zeta x)) β
      (fun l => (a l).globalGaussian d) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hWnonneg l n x hx)
  have he : LocalWave s (fun n (li : Label × I) => C li.1 n li.2)
      (fun n li x => W li.1 n x) α (fun n li => (a li.1).localGaussian d n li.2) :=
    LocalizedGaussianBounds.indexedCutoffError_wave_class d
      (LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hψ) hfast
      (LocalClass.of_uniformLocalJets hw hu) (LocalClass.of_uniformLocalJets hw hf)
  have hflat := indexed_gaussian_weighted_all_gains he scales
    (fun n li => θ li.1 n li.2) (fun n li => length li.1 n)
    (fun n li => hL li.1 n) ell hell (fun n li => hLell li.1 n) hc
    (fun n li x hx hi => hW li.1 n li.2 x hx hi)
    (fun n li x hx hi hm => by
      rcases hcentral li.1 n li.2 x hx hi hm with ho | ⟨hu,hf⟩
      · exact (a li.1).localGaussian_zero_of_cutoff_one d ho
      · exact (a li.1).localGaussian_zero_of_fields d hu hf) β
  have hlarge : LocalClass s (fun n (li : Label × I) => (K li.1).carrier n li.2)
      (fun _ _ x => Real.sqrt (s.zeta x)) β (fun n li => (a li.1).localGaussian d n li.2) := by
    apply hflat.enlarge
    intro n li x hx hi
    by_cases hh : x ∈ C li.1 n li.2
    · exact Or.inl hh
    · exact Or.inr (LocalizedGaussianBounds.localGaussian_zero_of_inactive (a li.1) d
        (houtside li.1 n li.2 x hx hi hh))
  exact LocalizedGaussianBounds.uniform_globalGaussian_class_with_complement a K hs d
    (fun _ _ _ _ => Real.sqrt_nonneg _) hlarge.to_uniformLocalJets hcomplement

end WeightedGaussian

section ActualWeighted

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

variable [Countable Label] [Nonempty Label]
  (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)


end ActualWeighted

end NavierStokes.ActualGaussianCoverage
