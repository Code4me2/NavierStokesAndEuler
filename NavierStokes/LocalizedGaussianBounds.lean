import NavierStokes.HarmonicSourceSupport
import NavierStokes.LocalizedWaveBounds

/-!
# Gaussian cutoff errors from support-local primitive estimates

The analytic phase patch may be smaller than the closed periodization
cell.  Only primitive amplitude/source/cutoff jets on that patch enter
the Gaussian estimate.  On the remainder of the cell, actual input zero
germs imply a zero germ of the two-term cutoff error.  The global source
complement is retained once, exactly as in `CopyData.globalGaussian`.
-/

noncomputable section

namespace NavierStokes.LocalizedGaussianBounds

open Set Function Filter WeightedClasses PeriodizedWaveBounds
open HarmonicCalculus LinearWaveBounds GaussianTailFlat
open scoped Topology ContDiff BigOperators

section LocalGerms

variable {D E I : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


end LocalGerms

section CopyBounds

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable (a : CopyData D I)

/-- A zero cutoff alone leaves the source.  Both zero germs are used. -/
theorem localGaussian_zero_of_cutoff_source (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0)
    (hf : a.source n =ᶠ[𝓝 x] fun _ => 0) :
    a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [a.localTail_zero_germ d hψ, hf] with y hy hfy
  rw [a.localGaussian_eq, hy, hfy, smul_zero, add_zero]

theorem localGaussian_zero_of_inactive (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (h : ((a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)) ∨
      ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0))) :
    a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0 := by
  rcases h with ⟨hψ, hf⟩ | ⟨hu, hf⟩
  · exact localGaussian_zero_of_cutoff_source a d hψ hf
  · exact a.localGaussian_zero_of_fields d hu hf




end CopyBounds

/-! ## Gaussian absorption with an arbitrary extra index -/

section IndexedEstimates

open LocalizedWaveBounds

variable {D E J : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The index may be the pair (spatial label, lattice copy).  Both the
Gaussian envelope and the native length are allowed to depend on it. -/
theorem indexed_gaussian_tail_bound {s : StripData D} {K : ℕ → J → Set D}
    {W : ℕ → J → D → ℝ} {α c : ℝ} {f : ℕ → J → D → E}
    (hf : LocalWave s K W α f) (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → J → D → ℝ) (L : ℕ → J → ℝ) (hL : ∀ n i, 0 < L n i)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n i, ell * ChartScales.S n ≤ L n i) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n i x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n i))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ n i x, x ∈ s.domain → x ∈ K n i →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f n i) x‖ ≤
        A * (1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n) := by
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  obtain ⟨B, hB, hweight⟩ := edges.uniform_weight p
  have hconstant := scales.constant_one_le
  have hdec : 0 < c * ell / 25 := by positivity
  obtain ⟨C, hC, hgauss⟩ := fixed_power_gaussian_bound hdec (scales.power * α)
  refine ⟨A * B * scales.constant ^ p * C, by positivity, scales.degree * p, ?_⟩
  intro n i x hx hi j hj
  have hQ := ChartScales.Q_pos n
  by_cases hmid : |θ n i x - 1 / 2| < 1 / 5
  · rw [jets_eq_of_germ (hzero n i x hx hi hmid) j]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hS : 0 ≤ ChartScales.S n := sq_nonneg _
    positivity
  have htail : 1 / 5 ≤ |θ n i x - 1 / 2| := le_of_not_gt hmid
  have hsq : (1 / 25 : ℝ) ≤ (θ n i x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : W n i x ≤ Real.exp (-(c * ell / 25) * ChartScales.S n) := by
    apply (hW n i x hx hi).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (hLell n i))
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (hL n i).le)]
  have hslow0 : 0 ≤ s.slow n := zero_le_one.trans (s.one_le_slow n)
  have hK0 : 0 ≤ scales.constant := zero_le_one.trans scales.constant_one_le
  have hslowp : s.slow n ^ p ≤
      scales.constant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p) := by
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ hslow0 (scales.slow_le n) p
  have hmajor : majorant s (fun n x => Real.sqrt (s.zeta x) * W n i x) α A p n x ≤
      (A * B * scales.constant ^ p) * ChartScales.Q n ^ (scales.power * α) *
        ((1 + ChartScales.S n) ^ (scales.degree * p) *
          Real.exp (-(c * ell / 25) * ChartScales.S n)) := by
    rw [majorant, StripData.growth, mul_pow, scales.epsilon_eq, ← Real.rpow_mul hQ.le]
    calc
      _ = (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) * W n i x := by ring
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) *
            Real.exp (-(c * ell / 25) * ChartScales.S n) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) * B *
            Real.exp (-(c * ell / 25) * ChartScales.S n) := by
        gcongr
        exact hweight x hx
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) *
          (scales.constant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p))) * B *
            Real.exp (-(c * ell / 25) * ChartScales.S n) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * W n i x) α A p n x := hb n i x hx hi j hj
    _ ≤ _ := hmajor
    _ = (A * B * scales.constant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (ChartScales.Q n ^ (scales.power * α) *
          Real.exp (-(c * ell / 25) * ChartScales.S n)) := by ring
    _ ≤ (A * B * scales.constant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (C * Real.exp (-((c * ell / 25) / 2) * ChartScales.S n)) := by
      have hS : 0 ≤ ChartScales.S n := sq_nonneg _
      exact mul_le_mul_of_nonneg_left (hgauss n) (by positivity)
    _ = _ := by
      rw [show c * ell / 25 / 2 = c * ell / 50 by ring]
      ring

theorem indexed_gaussian_all_gains {s : StripData D} {K : ℕ → J → Set D}
    {W : ℕ → J → D → ℝ} {α c : ℝ} {f : ℕ → J → D → E}
    (hf : LocalWave s K W α f) (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → J → D → ℝ) (L : ℕ → J → ℝ) (hL : ∀ n i, 0 < L n i)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n i, ell * ChartScales.S n ≤ L n i) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n i x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n i))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (β : ℝ) : LocalUnweighted s K β f := by
  refine ⟨fun _ _ _ _ => zero_le_one, hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := indexed_gaussian_tail_bound hf edges scales θ L hL
    ell hell hLell hc hW hzero m
  obtain ⟨B, hB, hflat⟩ := gaussian_beats_Q_power (by positivity : 0 < c * ell / 50) p (scales.power * β)
  refine ⟨A * B, mul_nonneg hA hB.le, 0, ?_⟩
  intro n i x hx hi j hj
  have ht := (hb n i x hx hi j hj).trans
    (show A * (1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n) ≤
      (A * B) * ChartScales.Q n ^ (scales.power * β) by
        calc
          _ = A * ((1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n)) := by ring
          _ ≤ A * (B * ChartScales.Q n ^ (scales.power * β)) :=
            mul_le_mul_of_nonneg_left (hflat n) hA
          _ = _ := by ring)
  simpa only [majorant, pow_zero, mul_one, scales.epsilon_eq,
    ← Real.rpow_mul (ChartScales.Q_pos n).le] using ht

end IndexedEstimates

section UniformGluing

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E L I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual source jets on the uncovered set, with constants chosen
before the spatial label as well as the band and point. -/
structure UniformComplementJets (s : StripData D) (w : L → ℕ → D → ℝ) (α : ℝ)
    (K : L → ℕ → I → Set D) (f : L → ℕ → D → E) : Prop where
  smooth : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → ContDiffAt ℝ ∞ (f l n) x
  bounds : ∀ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ,
    ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ majorant s (w l) α A p n x

namespace UniformComplementJets

theorem each {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f : L → ℕ → D → E}
    (hf : UniformComplementJets s w α K f) (l : L) : ComplementJets s (w l) α (K l) (f l) := by
  refine ⟨hf.smooth l, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  exact ⟨A, hA, p, hb l⟩

theorem of_zero_germs (s : StripData D) (w : L → ℕ → D → ℝ) (α : ℝ)
    (K : L → ℕ → I → Set D) (f : L → ℕ → D → E)
    (hg : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → f l n =ᶠ[𝓝 x] fun _ => 0) :
    UniformComplementJets s w α K f := by
  constructor
  · intro l n x hx hn
    exact contDiffAt_const.congr_of_eventuallyEq (hg l n x hx hn)
  · intro m
    refine ⟨0, le_rfl, 0, ?_⟩
    intro l n x hx hn j hj
    rw [jets_eq_of_germ (hg l n x hx hn) j]
    simp [majorant]


end UniformComplementJets

theorem uniformClass_of_local_and_complement_germs
    {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f : L → ℕ → I → D → E} {f₀ F : L → ℕ → D → E}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hlocal : UniformLocalJets s w α K f) (houtside : UniformComplementJets s w α K f₀)
    (hactive : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → F l n =ᶠ[𝓝 x] f l n i)
    (hinactive : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → F l n =ᶠ[𝓝 x] f₀ l n) :
    LabelSumBounds.UniformClass s w α F := by
  classical
  refine ⟨hw, ?_, ?_⟩
  · intro l
    exact (memClass_of_local_and_complement_germs (hw l) (hlocal.each l)
      (houtside.each l) (hactive l) (hinactive l)).smooth
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hlocal.bounds m
    obtain ⟨B, hB, q, hb₀⟩ := houtside.bounds m
    refine ⟨A + B, add_nonneg hA hB, max p q, ?_⟩
    intro l n x hx j hj
    by_cases h : ∃ i, x ∈ K l n i
    · obtain ⟨i, hi⟩ := h
      rw [jets_eq_of_germ (hactive l n i x hx hi) j]
      exact (hb l n i x hx hi j hj).trans
        ((majorant_mono_degree s (w l) α hA (le_max_left _ _) n x (hw l n x hx)).trans
          (majorant_mono_constant s (w l) α (le_add_of_nonneg_right hB) _ n x (hw l n x hx)))
    · rw [jets_eq_of_germ (hinactive l n x hx (not_exists.mp h)) j]
      exact (hb₀ l n x hx (not_exists.mp h) j hj).trans
        ((majorant_mono_degree s (w l) α hB (le_max_right _ _) n x (hw l n x hx)).trans
          (majorant_mono_constant s (w l) α (le_add_of_nonneg_left hA) _ n x (hw l n x hx)))

end UniformGluing

/-! ## Primitive cutoff errors, uniformly over spatial labels -/

section UniformCopyBounds

open LocalizedWaveBounds

variable {D I L : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable def indexedCutoffError (d : GraphDirections D)
    (ψ : ℕ → I → D → ℝ) (u f : ℕ → I → D → ComplexVector)
    (n : ℕ) (i : I) (x : D) : ComplexVector :=
  d.Dfast (fun n => ψ n i) n x • u n i x + (1 - ψ n i x) • f n i x

theorem indexedCutoffError_wave_class {s : StripData D} (d : GraphDirections D)
    {K : ℕ → I → Set D} {w : ℕ → I → D → ℝ} {α : ℝ}
    {ψ : ℕ → I → D → ℝ} {u f : ℕ → I → D → ComplexVector}
    (hψ : LocalUnweighted s K 0 ψ) (hfast : BandBound s 0 d.fastScale)
    (hu : LocalClass s K w α u) (hf : LocalClass s K w α f) :
    LocalClass s K w α (indexedCutoffError d ψ u f) := by
  have hD : LocalUnweighted s K 0 (fun n i => d.Dfast (fun n => ψ n i) n) := by
    have hh : LocalUnweighted s K 0
        (fun n i x => d.fastScale n * fderiv ℝ (ψ n i) x d.fast) := by
      simpa using
      (LocalClass.band_const (K := K) hfast).smul (hψ.directional d.fast)
    convert! hh using 1
    funext n i x
    simp [GraphDirections.Dfast, GraphDirections.fastField, HarmonicCalculus.along]
  have hminus : LocalUnweighted s K 0 (fun n i x => 1 - ψ n i x) :=
    (local_const (s := s) (K := K) (1 : ℝ)).sub hψ
  have he := (unweighted_smul hD hu).add (unweighted_smul hminus hf)
  simp only [zero_add] at he
  exact he

theorem uniform_localGaussian_all_gains_from_supported_native
    (a : L → CopyData D I) {s : StripData D} (d : GraphDirections D)
    (C K : L → ℕ → I → Set D) {W : L → ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hfast : BandBound s 0 d.fastScale)
    (hu : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l => (a l).amplitude))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n _ => (a l).source n))
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : L → ℕ → I → D → ℝ) (length : L → ℕ → ℝ)
    (hL : ∀ l n, 0 < length l n) (ell : ℝ) (hell : 0 < ell)
    (hLell : ∀ l n, ell * ChartScales.S n ≤ length l n) (hc : 0 < c)
    (hW : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      W l n x ≤ Real.exp (-c * (θ l n i x - 1 / 2) ^ 2 * length l n))
    (hcentral : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → |θ l n i x - 1 / 2| < 1 / 5 →
      ((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → x ∉ C l n i →
      (((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ) : UniformLocalJets s (fun _ _ _ => 1) β K (fun l => (a l).localGaussian d) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hWnonneg l n x hx)
  have hψ' := LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hψ
  have hu' := LocalClass.of_uniformLocalJets hw hu
  have hf' := LocalClass.of_uniformLocalJets hw hf
  have he : LocalWave s (fun n (ji : L × I) => C ji.1 n ji.2)
      (fun n ji x => W ji.1 n x) α (fun n ji => (a ji.1).localGaussian d n ji.2) :=
    indexedCutoffError_wave_class d hψ' hfast hu' hf'
  have hflat := indexed_gaussian_all_gains he edges scales
    (fun n ji => θ ji.1 n ji.2) (fun n ji => length ji.1 n)
    (fun n ji => hL ji.1 n) ell hell (fun n ji => hLell ji.1 n) hc
    (fun n ji x hx hi => hW ji.1 n ji.2 x hx hi)
    (fun n ji x hx hi hm => by
      rcases hcentral ji.1 n ji.2 x hx hi hm with hOne | ⟨hU, hF⟩
      · exact (a ji.1).localGaussian_zero_of_cutoff_one d hOne
      · exact (a ji.1).localGaussian_zero_of_fields d hU hF) β
  apply LocalClass.to_uniformLocalJets
  apply hflat.enlarge
  intro n ji x hx hi
  by_cases hC : x ∈ C ji.1 n ji.2
  · exact Or.inl hC
  · exact Or.inr (localGaussian_zero_of_inactive (a ji.1) d
      (houtside ji.1 n ji.2 x hx hi hC))

theorem uniform_globalGaussian_class_with_complement
    (a : L → CopyData D I) (K : L → Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} (d : GraphDirections D) {w : L → ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hg : UniformLocalJets s w α (fun l => (K l).carrier) (fun l => (a l).localGaussian d))
    (hf : UniformComplementJets s w α (fun l => (K l).carrier) (fun l => (a l).source)) :
    LabelSumBounds.UniformClass s w α (fun l => (a l).globalGaussian d) :=
  uniformClass_of_local_and_complement_germs hw hg hf
    (fun l n _ _ _ hx => (a l).globalGaussian_germ (K l) (hs l) d n hx)
    (fun l _ _ _ hx => (a l).globalGaussian_uncovered_germ (K l) (hs l) d hx)

/-- The constants precede every spatial label, band and native copy.
The uncovered source is included with its own equally uniform jet bound. -/
theorem uniform_globalGaussian_all_gains_from_supported_native
    (a : L → CopyData D I) (K : L → Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} (d : GraphDirections D) (C : L → ℕ → I → Set D)
    {W : L → ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hfast : BandBound s 0 d.fastScale)
    (hu : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l => (a l).amplitude))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n _ => (a l).source n))
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : L → ℕ → I → D → ℝ) (length : L → ℕ → ℝ)
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
    (hcomplement : UniformComplementJets s (fun _ _ _ => 1) β
      (fun l => (K l).carrier) (fun l => (a l).source)) :
    LabelSumBounds.UniformClass s (fun _ _ _ => 1) β (fun l => (a l).globalGaussian d) :=
  uniform_globalGaussian_class_with_complement a K hs d (fun _ _ _ _ => zero_le_one)
    (uniform_localGaussian_all_gains_from_supported_native a d C (fun l => (K l).carrier)
      hWnonneg hψ hfast hu hf edges scales θ length hL ell hell hLell hc hW hcentral houtside β)
    hcomplement



end UniformCopyBounds

/-! ## The literal harmonic residual supplies the complement -/

section HarmonicSource

open CommonCoverSolve TorusInverse ParticularWaveAssembly HarmonicSourceSupport

variable {P L : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


theorem uniform_source_complement_of_harmonicSupport
    (a : L → CopyData ((P × ℝ) × Plane) Frequency)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : L → CorrectionState.HarmonicBlock (P × Plane))
    (G A : L → HarmonicResidual.BlockCoefficients (P × Plane))
    (g : L → ℕ → Geometry) (K : L → ℕ → Set Plane) (hK : ∀ l n, IsCompact (K l n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hs : ∀ l, InputSupportOn U (fun n => nativeUnion (g l n) (K l n)) (b l) (G l) (A l))
    (s : StripData ((P × ℝ) × Plane))
    (hdom : ∀ x, x ∈ s.domain → (x.1.1, x.2) ∈ U)
    (j : L → ℤ) (hsource : ∀ l, (a l).source = sourceFamily c u (b l) (G l) (A l) (j l))
    (β : ℝ) : UniformComplementJets s (fun _ _ _ => 1) β
      (fun l n => nativeCell (g l n) (K l n)) (fun l => (a l).source) := by
  apply UniformComplementJets.of_zero_germs
  intro l n x hx hn
  rw [hsource l]
  exact sourceFamily_zero_germ_on c u (b l) (G l) (A l) (g l) (K l) (hK l) hU
    (hs l) (j l) n (hdom x hx) hn


end HarmonicSource

end NavierStokes.LocalizedGaussianBounds
