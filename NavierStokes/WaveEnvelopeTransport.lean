import NavierStokes.GaussianTailFlat
import NavierStokes.CommonCoverClass
import NavierStokes.WithTopLemmas

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




section SlowCoordinates

variable {P : Type} {V : Type*}




end SlowCoordinates






section GroupedSources

open WeightedClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]










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
  have hb := norm_iteratedFDerivWithin_clm_apply hA hf hU.uniqueDiffOn hx (natCast_le_infty j)
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
