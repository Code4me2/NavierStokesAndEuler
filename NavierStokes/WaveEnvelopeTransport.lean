import NavierStokes.GaussianTailFlat
import NavierStokes.CommonCoverClass

/-!
# Source envelopes along an entire common-cover slot path

The common-cover envelope is an actual sum over native copies. Injectivity
of the padded native rectangle identifies the one copy met by a slot path.
The source itself is not assumed periodic on the native torus.
-/

noncomputable section

namespace NavierStokes.WaveEnvelopeTransport

open Set Function Filter
open scoped ContDiff Topology BigOperators
open CommonCoverSolve CommonCoverClass TorusInverse

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- The full padded integration rectangle, including both time endpoints. -/
noncomputable def rectangle (r L : ℝ) : Set Plane := Icc (-r) r ×ˢ Icc 0 L

noncomputable def nativeRegion (g : Geometry) (r L : ℝ) : Set Plane :=
  (fun z => g.center + g.basis z) '' rectangle r L

/-- A geometric injectivity condition, independent of all source fields. -/
noncomputable def Separated (g : Geometry) (r L : ℝ) : Prop :=
  InjOn TorusAverages.quotientPoint (nativeRegion g r L)

theorem native_coordinate_lattice (g : Geometry) (k : Frequency) (Y : Plane) :
    g.center + g.basis (g.coordinates k Y) =
      TorusAverages.latticePoint (-k) + coverPower g.gap Y := by
  have hneg : TorusAverages.latticePoint (-k) = -TorusAverages.latticePoint k := by
    ext <;> simp [TorusAverages.latticePoint]
  rw [Geometry.coordinates, ContinuousLinearEquiv.apply_symm_apply, hneg]
  abel

theorem copy_unique {g : Geometry} {r L : ℝ} (hsep : Separated g r L)
    {k l : Frequency} {Y : Plane} (hk : g.coordinates k Y ∈ rectangle r L)
    (hl : g.coordinates l Y ∈ rectangle r L) : k = l := by
  have hkm : TorusAverages.latticePoint (-k) + coverPower g.gap Y ∈ nativeRegion g r L := by
    rw [← native_coordinate_lattice]
    exact ⟨g.coordinates k Y, hk, rfl⟩
  have hlm : TorusAverages.latticePoint (-l) + coverPower g.gap Y ∈ nativeRegion g r L := by
    rw [← native_coordinate_lattice]
    exact ⟨g.coordinates l Y, hl, rfl⟩
  exact neg_injective (TorusAverages.latticeTranslate_unique hsep hkm hlm)

/-- The envelope of the grouped label on the common cover. The summands
are nonzero only on their own native integration rectangles. -/
noncomputable def copyEnvelope (g : Geometry) (r L : ℝ) (W : ℝ → ℝ) (Y : Plane) : ℝ := by
  classical
  exact ∑' k : Frequency, if g.coordinates k Y ∈ rectangle r L then W (g.coordinates k Y).2 else 0

theorem copyEnvelope_nonneg (g : Geometry) (r L : ℝ) {W : ℝ → ℝ}
    (hW : ∀ s, 0 ≤ W s) (Y : Plane) : 0 ≤ copyEnvelope g r L W Y := by
  classical
  apply tsum_nonneg
  intro k
  split_ifs
  · exact hW _
  · exact le_rfl

theorem copyEnvelope_eq_copy {g : Geometry} {r L : ℝ} (hsep : Separated g r L)
    (W : ℝ → ℝ) {k : Frequency} {Y : Plane} (hk : g.coordinates k Y ∈ rectangle r L) :
    copyEnvelope g r L W Y = W (g.coordinates k Y).2 := by
  classical
  unfold copyEnvelope
  rw [tsum_eq_single k]
  · simp only [ite_eq_left hk]
  · intro l hl
    split_ifs with hmem
    · exact (hl (copy_unique hsep hmem hk)).elim
    · rfl

theorem coordinates_path_in_rectangle (g : Geometry) (k : Frequency) (Y : Plane)
    {r L s : ℝ} (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) (hs : s ∈ Icc 0 L) :
    g.coordinates k (g.path k Y s) ∈ rectangle r L := by
  rw [g.coordinates_path]
  exact ⟨hξ, hs⟩

/-- Exact envelope identification at every integration time, including
the entry and exit. No bound at the current point is extrapolated. -/
theorem copyEnvelope_path {g : Geometry} {r L : ℝ} (hsep : Separated g r L)
    (W : ℝ → ℝ) (k : Frequency) (Y : Plane)
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) {s : ℝ} (hs : s ∈ Icc 0 L) :
    copyEnvelope g r L W (g.path k Y s) = W s := by
  rw [copyEnvelope_eq_copy hsep W (coordinates_path_in_rectangle g k Y hξ hs),
    g.coordinates_path]


theorem path_transverse (g : Geometry) (k : Frequency) (Y : Plane) (s : ℝ) :
    (g.coordinates k (g.path k Y s)).1 = (g.coordinates k Y).1 := by
  rw [g.coordinates_path]


section SlowCoordinates

variable {P : Type} {V : Type*}




end SlowCoordinates


theorem reference_envelope_on_path {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (lam u : ℝ) (k : Frequency) (Y : Plane)
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) {s : ℝ} (hs : s ∈ Icc 0 L) :
    copyEnvelope g r L (GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2))
      (g.path k Y s) =
      GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2) s :=
  copyEnvelope_path hsep _ k Y hξ hs


/-- A concrete geometric criterion, uniform in the band and covering gap.
After multiplying slot time by `ci`, the full rectangle has transverse
half-width `r0`, so its injectivity does not deteriorate as `L` grows. -/
theorem separated_bandGeometry (B : Plane ≃L[ℝ] Plane) (h : ℝ) (n gap : ℕ)
    (center : Plane) {r r0 R : ℝ} (hr : r < R) (hr0 : r0 < R)
    (hsmall : ‖(B : Plane →L[ℝ] Plane)‖ * R < 1 / 2) :
    Separated (bandGeometry B h n gap center) r (ChartScales.slotLength r0 h n) := by
  apply (TorusAverages.quotientPoint_injOn_small_chart B (center + B (0, r0)) R hsmall).mono
  rintro Y ⟨z, hz, rfl⟩
  have hci := ChartScales.timeCoefficient_pos h n
  have htime : 0 ≤ ChartScales.timeCoefficient h n * z.2 ∧
      ChartScales.timeCoefficient h n * z.2 ≤ 2 * r0 := by
    refine ⟨mul_nonneg hci.le hz.2.1, ?_⟩
    have ht := (le_div_iff₀ hci).1 hz.2.2
    simpa only [mul_comm] using ht
  refine ⟨(z.1, ChartScales.timeCoefficient h n * z.2 - r0), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff,
      Real.norm_eq_abs, Real.norm_eq_abs]
    constructor
    · exact (abs_le.mpr hz.1).trans_lt hr
    · apply (abs_le.mpr ?_).trans_lt hr0
      dsimp only
      constructor <;> linarith [htime.1, htime.2]
  · change (center + B (0, r0)) + B (z.1, ChartScales.timeCoefficient h n * z.2 - r0) =
      center + scaledBasis B _ _ z
    rw [scaledBasis_apply, add_assoc, ← map_add]
    congr 2
    ext <;> simp


section GroupedSources

open WeightedClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def copyCell (g : Geometry) (r L : ℝ) (k : Frequency) : Set (P × Plane) :=
  {z | g.coordinates k z.2 ∈ rectangle r L}

omit [NormedSpace ℝ P] in
theorem copyCell_closed (g : Geometry) (r L : ℝ) (k : Frequency) :
    IsClosed (copyCell (P := P) g r L k) :=
  (isClosed_Icc.prod isClosed_Icc).preimage
    ((g.coordinates_contDiff k).continuous.comp continuous_snd)

omit [NormedSpace ℝ P] in
theorem copyCell_locallyFinite (g : Geometry) (r L : ℝ) :
    LocallyFinite (copyCell (P := P) g r L) := by
  classical
  let κ : Plane → ℝ := (rectangle r L).indicator (fun _ => 1)
  have hκ : HasCompactSupport κ :=
    HasCompactSupport.intro' (K := rectangle r L) (isCompact_Icc.prod isCompact_Icc)
      (isClosed_Icc.prod isClosed_Icc) (fun z hz => by simp [κ, hz])
  intro z
  obtain ⟨s, hs⟩ := g.finite_copy_cutoffs hκ (‖z.2‖ + 1)
  refine ⟨{y : P × Plane | ‖y.2‖ < ‖z.2‖ + 1},
    (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simp), ?_⟩
  apply s.finite_toSet.subset
  intro k hk
  obtain ⟨y, hy, hnorm⟩ := hk
  by_contra hnot
  have hh := hs y.2 hnorm.le k hnot
  change g.coordinates k y.2 ∈ rectangle r L at hy
  simp [κ, hy] at hh

/-- Coefficients may differ in every native copy. This is an actual sum
of common-cover fields, with no substitution of a native-periodic source. -/
noncomputable def grouped (F : Frequency → P × Plane → V) (z : P × Plane) : V :=
  ∑' k : Frequency, F k z

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_eventually_eq_copy {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    {k : Frequency} {z : P × Plane} (hz : z ∈ copyCell g r L k) :
    grouped F =ᶠ[𝓝 z] F k := by
  classical
  have hn := (copyCell_locallyFinite (P := P) g r L).iInter_compl_mem_nhds
    (copyCell_closed g r L) z
  filter_upwards [hn] with y hy
  apply tsum_eq_single k
  intro l hl
  have hznot : z ∉ copyCell g r L l := fun hzl => hl (copy_unique hsep hzl hz)
  have hynot := mem_iInter₂.mp hy l hznot
  by_contra hne
  exact hynot (hsupport l hne)

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_eventually_zero {g : Geometry} {r L : ℝ}
    (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    {z : P × Plane} (hz : ∀ k, z ∉ copyCell g r L k) :
    grouped F =ᶠ[𝓝 z] fun _ => 0 := by
  classical
  have hn := (copyCell_locallyFinite (P := P) g r L).iInter_compl_mem_nhds
    (copyCell_closed g r L) z
  filter_upwards [hn] with y hy
  have hzero : ∀ k, F k y = 0 := by
    intro k
    by_contra hne
    exact (mem_iInter₂.mp hy k (hz k)) (hsupport k hne)
  simp only [grouped, hzero, tsum_zero]

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem grouped_on_entire_path {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    (k : Frequency) (p : P) (Y : Plane)
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) :
    ∀ v ∈ Icc 0 L, grouped F (p, g.path k Y v) = F k (p, g.path k Y v) := by
  intro v hv
  have hmem : (p, g.path k Y v) ∈ copyCell g r L k :=
    coordinates_path_in_rectangle g k Y hξ hv
  exact (grouped_eventually_eq_copy hsep F hsupport hmem).self_of_nhds

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
/-- A transverse support exclusion for the actual copy coefficient excludes
the entire grouped source on the entire integration path. -/
theorem grouped_path_zero_of_transverse_support {g : Geometry} {r L : ℝ}
    (hsep : Separated g r L) (F : Frequency → P × Plane → V)
    (hsupport : ∀ k, support (F k) ⊆ copyCell g r L k)
    (k : Frequency) (p : P) (Y : Plane) (T : Set ℝ)
    (htransverse : support (F k) ⊆ {z | (g.coordinates k z.2).1 ∈ T})
    (hξ : (g.coordinates k Y).1 ∈ Icc (-r) r) (hξT : (g.coordinates k Y).1 ∉ T) :
    ∀ v ∈ Icc 0 L, grouped F (p, g.path k Y v) = 0 := by
  intro v hv
  rw [grouped_on_entire_path hsep F hsupport k p Y hξ v hv]
  by_contra hne
  have hh := htransverse hne
  exact hξT (by simpa only [Set.mem_ofPred_eq, path_transverse] using hh)


private theorem jet_congr {f g : P × Plane → V} {x : P × Plane}
    (he : f =ᶠ[𝓝 x] g) (j : ℕ) : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
  have he' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using
    he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j


end GroupedSources

section SourceJetTransport

open WeightedClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Full joint derivatives of the actual source along every point of the
slot. The inverse-edge factor remains frozen in `s.growth n z.1`.
The source may depend on the common coordinate in any way allowed by its
actual WaveClass; native periodicity is not a premise. -/
theorem waveClass_sourceArgument_bound
    (s : StripData P) (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    (gapBound : ℕ) (band gap : ℕ → ℕ) (center : ℕ → Plane) (r L : ℕ → ℝ)
    (hband : ∀ n, 4 ≤ band n) (hgap : ∀ n, gap n ≤ gapBound)
    (hslow : ∀ n, s.slow n = ChartScales.S (band n))
    (hsep : ∀ n, Separated (bandGeometry B h (band n) (gap n) (center n)) (r n) (L n))
    (W : ℕ → ℝ → ℝ) (hW : ∀ n v, 0 ≤ W n v)
    {α : ℝ} {f : ℕ → P × Plane → V}
    (hf : WaveClass (sourceStrip s)
      (fun n z => copyEnvelope (bandGeometry B h (band n) (gap n) (center n)) (r n) (L n) (W n) z.2)
      α f) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n (k : Frequency) (z : P × Plane), z.1 ∈ s.domain →
      ((bandGeometry B h (band n) (gap n) (center n)).coordinates k z.2).1 ∈ Icc (-(r n)) (r n) →
      ∀ v ∈ Icc 0 (L n), ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j
        (fun x : Joint P => f n (sourceArgument (bandGeometry B h (band n) (gap n) (center n)) k x))
        (z, v)‖ ≤
      C * s.growth n z.1 ^ d * (s.epsilon n ^ α * Real.sqrt (s.zeta z.1)) * W n v := by
  obtain ⟨A, hA, p, ha⟩ := hf.bounds N
  let K := bandArgumentCost B gapBound
  have hK : 1 ≤ K := bandArgumentCost_one_le B gapBound
  refine ⟨A * K ^ N, by positivity, p + N, ?_⟩
  intro n k z hz hξ v hv j hj
  let g := bandGeometry B h (band n) (gap n) (center n)
  have hmap : sourceArgument g k (z, v) ∈ (sourceStrip s).domain := hz
  have hlocal : sourceArgument g k 0 + sourceLinear P g (z, v) ∈ (sourceStrip s).domain := by
    rw [← sourceArgument_affine]
    exact hmap
  have hjet := CommonCoverClass.norm_affine_jet_le_on (sourceStrip s).isOpen_domain
    (hf.smooth n) (sourceLinear P g) (sourceArgument g k 0) hlocal j
  simp_rw [← sourceArgument_affine] at hjet
  have hsrc := ha n (sourceArgument g k (z, v)) hmap j hj
  change ‖iteratedFDeriv ℝ j (f n) (sourceArgument g k (z, v))‖ ≤
    A * s.epsilon n ^ α * s.growth n z.1 ^ p *
      (Real.sqrt (s.zeta z.1) * copyEnvelope g (r n) (L n) (W n) (g.path k z.2 v)) at hsrc
  rw [copyEnvelope_path (hsep n) (W n) k z.2 hξ hv] at hsrc
  have hG := s.one_le_growth n z.1
  have hGn := s.growth_nonneg n z.1
  have hlin : ‖sourceLinear P g‖ ≤ K * s.growth n z.1 := by
    apply (norm_sourceLinear_le g).trans
    apply (bandGeometry_argumentCost_le B hh (hband n) (hgap n) (center n)).trans
    rw [← hslow n]
    exact mul_le_mul_of_nonneg_left (s.slow_le_growth n z.1) (zero_le_one.trans hK)
  have hpow : ‖sourceLinear P g‖ ^ j ≤ K ^ N * s.growth n z.1 ^ N := by
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hlin j).trans
      (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hK hG) hj)
  have hw := hW n v
  have he := s.epsilon_pos n
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n) (sourceArgument g k (z, v))‖ *
        ‖sourceLinear P g‖ ^ j := hjet
    _ ≤ (A * s.epsilon n ^ α * s.growth n z.1 ^ p * (Real.sqrt (s.zeta z.1) * W n v)) *
        (K ^ N * s.growth n z.1 ^ N) :=
      mul_le_mul hsrc hpow (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SourceJetTransport

section ForcingJetTransport

open WeightedClasses

variable {X P V H : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem clm_apply_jet_bound_on {U : Set X} (hU : IsOpen U)
    {A : X → V →L[ℝ] H} {f : X → V} (hA : ContDiffOn ℝ ∞ A U)
    (hf : ContDiffOn ℝ ∞ f U) {x : X} (hx : x ∈ U) (N : ℕ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAj : ∀ j ≤ N, ‖iteratedFDeriv ℝ j A x‖ ≤ C)
    (hfj : ∀ j ≤ N, ‖iteratedFDeriv ℝ j f x‖ ≤ D) (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun y => A y (f y)) x‖ ≤ (2 : ℝ) ^ N * C * D := by
  have hb := norm_iteratedFDerivWithin_clm_apply hA hf hU.uniqueDiffOn hx (nat_le_infty j)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at hb
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hAj i (hij.trans hj)) (Nat.cast_nonneg _))
        (hfj (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = (2 : ℝ) ^ j * C * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hC) hD


end ForcingJetTransport

section NativePathAndSupport

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]



end NativePathAndSupport

end NavierStokes.WaveEnvelopeTransport
