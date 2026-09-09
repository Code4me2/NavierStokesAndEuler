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




end UniformCopyBounds

/-! ## The literal harmonic residual supplies the complement -/

section HarmonicSource

open CommonCoverSolve TorusInverse ParticularWaveAssembly HarmonicSourceSupport

variable {P L : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]




end HarmonicSource

end NavierStokes.LocalizedGaussianBounds
