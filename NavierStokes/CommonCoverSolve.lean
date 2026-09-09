import NavierStokes.TorusAverages
import NavierStokes.SlotGeometry
import NavierStokes.SmoothPathFamily
import NavierStokes.JointODE
import NavierStokes.WeightedODEJets

/-!
# Actual slot solves on a common torus

The source is evaluated on the lifted copy path. Only periodicity on the
coarsest torus is used; finer native periodicity is not an input.
-/

noncomputable section

namespace NavierStokes.CommonCoverSolve

open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
open TorusInverse

noncomputable def coverEquiv : Plane ≃L[ℝ] Plane :=
  TorusAverages.slotChart (3, 1) (1, 5) (by norm_num)

theorem coverEquiv_apply (Y : Plane) : coverEquiv Y = SlotGeometry.cover Y := by
  rw [coverEquiv, TorusAverages.slotChart_apply, SlotGeometry.cover_apply]
  ext <;> simp [mul_comm]

noncomputable def coverPower : ℕ → Plane ≃L[ℝ] Plane
  | 0 => ContinuousLinearEquiv.refl ℝ Plane
  | d + 1 => (coverPower d).trans coverEquiv

theorem coverPower_apply (d : ℕ) (Y : Plane) :
    coverPower d Y = (SlotGeometry.cover ^ d) Y := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change coverEquiv (coverPower d Y) = _
      rw [coverEquiv_apply, ih, pow_succ', _root_.mul_apply_eq_comp]

noncomputable def indexMap (k : Frequency) : Frequency :=
  (3 * k.1 + k.2, k.1 + 5 * k.2)

noncomputable def coverIndex (d : ℕ) (k : Frequency) : Frequency := indexMap^[d] k

theorem coverEquiv_lattice (k : Frequency) :
    coverEquiv (TorusAverages.latticePoint k) = TorusAverages.latticePoint (indexMap k) := by
  rw [coverEquiv_apply, SlotGeometry.cover_apply]
  ext <;> simp [TorusAverages.latticePoint, indexMap]

theorem coverPower_lattice (d : ℕ) (k : Frequency) :
    coverPower d (TorusAverages.latticePoint k) =
      TorusAverages.latticePoint (coverIndex d k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change coverEquiv (coverPower d (TorusAverages.latticePoint k)) = _
      rw [ih, coverEquiv_lattice]
      simp only [coverIndex, Function.iterate_succ_apply']

theorem norm_coverPower_le (d : ℕ) (Y : Plane) :
    ‖coverPower d Y‖ ≤ (6 : ℝ) ^ d * ‖Y‖ := by
  rw [coverPower_apply]
  exact SlotGeometry.norm_cover_pow_le d Y


/-- Fixed geometry for a level whose gap above the common coarsest level is
`gap`. The columns of `basis` are the native radial and transverse vectors. -/
structure Geometry where
  gap : ℕ
  basis : Plane ≃L[ℝ] Plane
  center : Plane

namespace Geometry

variable (g : Geometry)

noncomputable def coordinates (k : Frequency) (Y : Plane) : Plane :=
  g.basis.symm (coverPower g.gap Y - g.center - TorusAverages.latticePoint k)

noncomputable def point (k : Frequency) (z : Plane) : Plane :=
  (coverPower g.gap).symm (g.center + TorusAverages.latticePoint k + g.basis z)

theorem coordinates_point (k : Frequency) (z : Plane) :
    g.coordinates k (g.point k z) = z := by
  unfold coordinates point
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have h : g.center + TorusAverages.latticePoint k + g.basis z - g.center -
      TorusAverages.latticePoint k = g.basis z := by abel
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

theorem point_coordinates (k : Frequency) (Y : Plane) :
    g.point k (g.coordinates k Y) = Y := by
  unfold point coordinates
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have h : g.center + TorusAverages.latticePoint k +
      (coverPower g.gap Y - g.center - TorusAverages.latticePoint k) = coverPower g.gap Y := by abel
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

theorem point_add (k : Frequency) (z h : Plane) :
    g.point k (z + h) = g.point k z + (coverPower g.gap).symm (g.basis h) := by
  simp only [point, map_add, add_assoc]

noncomputable def path (k : Frequency) (Y : Plane) (eta : ℝ) : Plane :=
  g.point k ((g.coordinates k Y).1, eta)

theorem coordinates_path (k : Frequency) (Y : Plane) (eta : ℝ) :
    g.coordinates k (g.path k Y eta) = ((g.coordinates k Y).1, eta) :=
  g.coordinates_point k _

theorem path_current (k : Frequency) (Y : Plane) :
    g.path k Y (g.coordinates k Y).2 = Y := by
  exact g.point_coordinates k Y

theorem path_path (k : Frequency) (Y : Plane) (eta eta' : ℝ) :
    g.path k (g.path k Y eta) eta' = g.path k Y eta' := by
  unfold path
  rw [g.coordinates_point]

/-- The manuscript's copy-path formula, in the common coarsest coordinates.
The final native basis vector is `v_t`. -/
theorem path_eq_shift (k : Frequency) (Y : Plane) (eta : ℝ) :
    g.path k Y eta = Y + (coverPower g.gap).symm
      ((eta - (g.coordinates k Y).2) • g.basis (0, 1)) := by
  let z := g.coordinates k Y
  have hz : (z.1, eta) = z + (eta - z.2) • (0, 1) := by
    ext <;> simp [z]
  change g.point k (z.1, eta) = _
  rw [hz, g.point_add, map_smul]
  rw [g.point_coordinates]

theorem point_deck (k n : Frequency) (z : Plane) :
    g.point (k + coverIndex g.gap n) z = g.point k z + TorusAverages.latticePoint n := by
  have h : g.center + TorusAverages.latticePoint (k + coverIndex g.gap n) + g.basis z =
      (g.center + TorusAverages.latticePoint k + g.basis z) +
        coverPower g.gap (TorusAverages.latticePoint n) := by
    rw [TorusAverages.latticePoint_add, coverPower_lattice]
    abel
  unfold point
  rw [h, map_add, ContinuousLinearEquiv.symm_apply_apply]

theorem coordinates_deck (k n : Frequency) (Y : Plane) :
    g.coordinates (k + coverIndex g.gap n) (Y + TorusAverages.latticePoint n) =
      g.coordinates k Y := by
  have h : g.point (k + coverIndex g.gap n) (g.coordinates k Y) =
      Y + TorusAverages.latticePoint n := by
    rw [g.point_deck, g.point_coordinates]
  rw [← h, g.coordinates_point]

theorem path_deck (k n : Frequency) (Y : Plane) (eta : ℝ) :
    g.path (k + coverIndex g.gap n) (Y + TorusAverages.latticePoint n) eta =
      g.path k Y eta + TorusAverages.latticePoint n := by
  unfold path
  rw [g.coordinates_deck, g.point_deck]

theorem coordinates_contDiff (k : Frequency) : ContDiff ℝ ∞ (g.coordinates k) :=
  g.basis.symm.contDiff.comp
    (((coverPower g.gap).contDiff.sub contDiff_const).sub contDiff_const)

theorem point_contDiff (k : Frequency) : ContDiff ℝ ∞ (g.point k) :=
  (coverPower g.gap).symm.contDiff.comp (contDiff_const.add g.basis.contDiff)

theorem path_contDiff (k : Frequency) :
    ContDiff ℝ ∞ (fun z : Plane × ℝ => g.path k z.1 z.2) :=
  (g.point_contDiff k).comp
    (((g.coordinates_contDiff k).comp contDiff_fst).fst.prodMk contDiff_snd)

end Geometry

/-! ## Actual forced linear equations on the copy paths -/

/-- Native coefficients and a native linear conversion of an ambient source.
The source itself is a function on the common coarsest coordinates. This
allows the tangent-frame projection to depend on the native slot. -/
structure LinearData (P V E : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  coefficient : P × Plane → E →L[ℝ] E
  forcingMap : P × Plane → V →L[ℝ] E
  source : P × Plane → V

def PeriodicAt {P V : Type} (f : P × Plane → V) (p : P) : Prop :=
  ∀ Y : Plane, ∀ n : Frequency,
    f (p, Y + TorusAverages.latticePoint n) = f (p, Y)

section Paths

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace LinearData

variable (d : LinearData P V E) (g : Geometry)

noncomputable def coefficientAlong (k : Frequency) (w : (P × Plane) × ℝ) : E →L[ℝ] E :=
  d.coefficient (w.1.1, ((g.coordinates k w.1.2).1, w.2))

noncomputable def forcingAlong (k : Frequency) (w : (P × Plane) × ℝ) : E :=
  d.forcingMap (w.1.1, ((g.coordinates k w.1.2).1, w.2))
    (d.source (w.1.1, g.path k w.1.2 w.2))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem coefficientAlong_deck (k n : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    d.coefficientAlong g (k + coverIndex g.gap n) ((p, Y + TorusAverages.latticePoint n), s) =
      d.coefficientAlong g k ((p, Y), s) := by
  simp only [coefficientAlong, g.coordinates_deck]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem forcingAlong_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p)
    (Y : Plane) (s : ℝ) :
    d.forcingAlong g (k + coverIndex g.gap n) ((p, Y + TorusAverages.latticePoint n), s) =
      d.forcingAlong g k ((p, Y), s) := by
  simp only [forcingAlong, g.coordinates_deck, g.path_deck]
  rw [hp (g.path k Y s) n]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem coefficientAlong_reanchor (k : Frequency) (p : P) (Y : Plane) (eta s : ℝ) :
    d.coefficientAlong g k ((p, g.path k Y eta), s) =
      d.coefficientAlong g k ((p, Y), s) := by
  simp only [coefficientAlong, g.coordinates_path]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem forcingAlong_reanchor (k : Frequency) (p : P) (Y : Plane) (eta s : ℝ) :
    d.forcingAlong g k ((p, g.path k Y eta), s) = d.forcingAlong g k ((p, Y), s) := by
  simp only [forcingAlong, g.coordinates_path, g.path_path]

end LinearData

theorem pathFamily_congr_slice {Q W : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {a b : ℝ}
    (F G : Q × ℝ → W) (p q : Q)
    (h : ∀ t : Icc a b, F (p, t) = G (q, t)) :
    SmoothPathFamily.pathFamily (a := a) (b := b) F p =
      SmoothPathFamily.pathFamily G q := by
  have heq : (fun t : Icc a b => F (p, t)) = (fun t : Icc a b => G (q, t)) := funext h
  by_cases hF : Continuous (fun t : Icc a b => F (p, t))
  · have hG : Continuous (fun t : Icc a b => G (q, t)) := heq ▸ hF
    ext t
    rw [SmoothPathFamily.pathFamily_apply F p hF, SmoothPathFamily.pathFamily_apply G q hG]
    exact h t
  · have hG : ¬ Continuous (fun t : Icc a b => G (q, t)) := by
      intro hG
      exact hF (heq.symm ▸ hG)
    simp only [SmoothPathFamily.pathFamily, dite_eq_right hF, dite_eq_right hG]

namespace LinearData

variable [CompleteSpace E] {a b : ℝ}
variable (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

noncomputable def coefficientPath (k : Frequency) (p : P × Plane) :
    ParametricODE.Coefficient a b E := SmoothPathFamily.pathFamily (d.coefficientAlong g k) p

noncomputable def forcingPath (k : Frequency) (p : P × Plane) :
    ParametricODE.Curve a b E := SmoothPathFamily.pathFamily (d.forcingAlong g k) p

/-- The genuine Volterra solution, with zero entry data, evaluated along the
copy path anchored at the current common coordinate. -/
noncomputable def anchoredSolve (k : Frequency) (p : P × Plane) (s : ℝ) : E :=
  ParametricODE.solutionExtension hab (d.coefficientPath g k p) 0 (d.forcingPath g k p) s

/-- Value of the constructed solution at the current native slot coordinate. -/
noncomputable def copySolve (k : Frequency) (p : P × Plane) : E :=
  d.anchoredSolve g hab k p (g.coordinates k p.2).2

omit [CompleteSpace E] in
theorem coefficientPath_deck (k n : Frequency) (p : P) (Y : Plane) :
    d.coefficientPath (a := a) (b := b) g (k + coverIndex g.gap n)
        (p, Y + TorusAverages.latticePoint n) = d.coefficientPath g k (p, Y) := by
  apply pathFamily_congr_slice
  intro s
  exact d.coefficientAlong_deck g k n p Y s

omit [CompleteSpace E] in
theorem forcingPath_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p) (Y : Plane) :
    d.forcingPath (a := a) (b := b) g (k + coverIndex g.gap n)
        (p, Y + TorusAverages.latticePoint n) = d.forcingPath g k (p, Y) := by
  apply pathFamily_congr_slice
  intro s
  exact d.forcingAlong_deck g k n p hp Y s

theorem anchoredSolve_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p)
    (Y : Plane) (s : ℝ) :
    d.anchoredSolve g hab (k + coverIndex g.gap n) (p, Y + TorusAverages.latticePoint n) s =
      d.anchoredSolve g hab k (p, Y) s := by
  unfold anchoredSolve
  rw [d.coefficientPath_deck, d.forcingPath_deck g k n p hp]

theorem copySolve_deck (k n : Frequency) (p : P) (hp : PeriodicAt d.source p) (Y : Plane) :
    d.copySolve g hab (k + coverIndex g.gap n) (p, Y + TorusAverages.latticePoint n) =
      d.copySolve g hab k (p, Y) := by
  unfold copySolve
  rw [g.coordinates_deck, d.anchoredSolve_deck g hab k n p hp]

theorem anchoredSolve_reanchor (k : Frequency) (p : P) (Y : Plane) (eta s : ℝ) :
    d.anchoredSolve g hab k (p, g.path k Y eta) s = d.anchoredSolve g hab k (p, Y) s := by
  have hA : d.coefficientPath (a := a) (b := b) g k (p, g.path k Y eta) =
      d.coefficientPath g k (p, Y) :=
    pathFamily_congr_slice _ _ _ _ (fun t => d.coefficientAlong_reanchor g k p Y eta t)
  have hf : d.forcingPath (a := a) (b := b) g k (p, g.path k Y eta) =
      d.forcingPath g k (p, Y) :=
    pathFamily_congr_slice _ _ _ _ (fun t => d.forcingAlong_reanchor g k p Y eta t)
  unfold anchoredSolve
  rw [hA, hf]

theorem copySolve_path (k : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    d.copySolve g hab k (p, g.path k Y s) = d.anchoredSolve g hab k (p, Y) s := by
  unfold copySolve
  rw [g.coordinates_path, d.anchoredSolve_reanchor g hab]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem anchoredSolve_initial (k : Frequency) (p : P × Plane) :
    d.anchoredSolve g hab k p a = 0 := by
  simp [anchoredSolve, ParametricODE.solutionExtension]


end LinearData

theorem solutionExtension_zero {a b : ℝ} (hab : a ≤ b)
    (A : ParametricODE.Coefficient a b E) [CompleteSpace E] (s : ℝ) :
    ParametricODE.solutionExtension hab A 0 0 s = 0 := by
  have hsol : ParametricODE.solution hab A 0 0 = 0 := by
    simp [ParametricODE.solution, ParametricODE.source]
  have happ : ParametricODE.applyCoefficient A 0 = 0 := by
    ext t
    simp [ParametricODE.applyCoefficient]
  simp [ParametricODE.solutionExtension, hsol, happ, ParametricODE.extend]

namespace LinearData

variable [CompleteSpace E] {a b : ℝ}
variable (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

omit [CompleteSpace E] in
theorem forcingPath_zero_of_source_zero (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ s ∈ Icc a b, d.source (p, g.path k Y s) = 0) :
    d.forcingPath (a := a) (b := b) g k (p, Y) = 0 := by
  have h : d.forcingPath (a := a) (b := b) g k (p, Y) =
      SmoothPathFamily.pathFamily (a := a) (b := b) (fun _ : (P × Plane) × ℝ => (0 : E))
        (p, Y) := by
    apply pathFamily_congr_slice
    intro s
    simp only [forcingAlong, hf s s.2, map_zero]
  rw [h]
  ext t
  rw [SmoothPathFamily.pathFamily_apply _ _ continuous_const]
  rfl

/-- Vanishing along the entire source path forces the constructed zero-entry
solution to vanish. No vanishing assumption on the output is used. -/
theorem anchoredSolve_zero_of_source_zero (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ s ∈ Icc a b, d.source (p, g.path k Y s) = 0) (eta : ℝ) :
    d.anchoredSolve g hab k (p, Y) eta = 0 := by
  unfold anchoredSolve
  rw [d.forcingPath_zero_of_source_zero g k p Y hf]
  exact solutionExtension_zero hab _ eta

theorem copySolve_zero_of_source_zero (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ s ∈ Icc a b, d.source (p, g.path k Y s) = 0) :
    d.copySolve g hab k (p, Y) = 0 := d.anchoredSolve_zero_of_source_zero g hab k p Y hf _



end LinearData

namespace Geometry


theorem pathArgument_contDiff (g : Geometry) (k : Frequency) :
    ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ => (w.1.1, g.path k w.1.2 w.2)) := by
  have hp : ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ => w.1.1) := contDiff_fst.fst
  have ht : ContDiff ℝ ∞ (fun w : (P × Plane) × ℝ => ((g.coordinates k w.1.2).1, w.2)) :=
    ((g.coordinates_contDiff k).comp contDiff_fst.snd).fst.prodMk contDiff_snd
  exact hp.prodMk ((g.point_contDiff k).comp ht)

end Geometry

namespace LinearData

variable (d : LinearData P V E) (g : Geometry) {U : Set P}





variable [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)




end LinearData

/-! ## Localization and the actual common-torus field -/

namespace Geometry

theorem cutoff_as_translate (g : Geometry) (κ : Plane → ℝ) (k : Frequency) (Y : Plane) :
    κ (g.coordinates k Y) = TorusAverages.nativeField g.basis g.center κ
      (TorusAverages.latticePoint (-k) + coverPower g.gap Y) := by
  have hneg : TorusAverages.latticePoint (-k) = -TorusAverages.latticePoint k := by
    ext <;> simp [TorusAverages.latticePoint]
  unfold coordinates TorusAverages.nativeField
  rw [hneg]
  congr 2
  abel

theorem finite_copy_cutoffs (g : Geometry) {κ : Plane → ℝ}
    (hκ : HasCompactSupport κ) (R : ℝ) :
    ∃ s : Finset Frequency, ∀ Y : Plane, ‖Y‖ ≤ R →
      ∀ k : Frequency, k ∉ s → κ (g.coordinates k Y) = 0 := by
  classical
  obtain ⟨s, hs⟩ := TorusAverages.finite_translates_on_ball
    (TorusAverages.nativeField_hasCompactSupport g.basis g.center hκ) ((6 : ℝ) ^ g.gap * R)
  refine ⟨s.image Neg.neg, ?_⟩
  intro Y hY k hk
  rw [g.cutoff_as_translate κ k Y]
  apply hs _ ((norm_coverPower_le g.gap Y).trans
    (mul_le_mul_of_nonneg_left hY (by positivity))) (-k)
  intro hneg
  exact hk (Finset.mem_image.mpr ⟨-k, hneg, neg_neg k⟩)

end Geometry

namespace LinearData

variable [CompleteSpace E] {a b : ℝ}
variable (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)

noncomputable def localizedCopy (κ : Plane → ℝ) (k : Frequency) (p : P × Plane) : E :=
  κ (g.coordinates k p.2) • d.copySolve g hab k p

/-- The actual sum of localized copy solves. Sources in different native
copies are evaluated at their own absolute-lift points. -/
noncomputable def commonSolve (κ : Plane → ℝ) (p : P × Plane) : E :=
  ∑' k : Frequency, d.localizedCopy g hab κ k p







end LinearData

end Paths

/-! ## A function on the quotient torus, not merely a periodic lift -/









namespace LinearData

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)



/-! Joint regularity is derived from the actual ODE construction. -/






end LinearData

/-! ## Bounded covering gaps and actual derivative costs -/

noncomputable def coveringBound (D : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D + 1),
    (‖(coverPower d : Plane →L[ℝ] Plane)‖ + ‖((coverPower d).symm : Plane →L[ℝ] Plane)‖)

theorem coveringBound_pos (D : ℕ) : 0 < coveringBound D := by
  unfold coveringBound
  positivity

theorem coveringNorm_le_bound {d D : ℕ} (hd : d ≤ D) :
    ‖(coverPower d : Plane →L[ℝ] Plane)‖ ≤ coveringBound D := by
  have hm : d ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hs := Finset.single_le_sum
    (f := fun i => ‖(coverPower i : Plane →L[ℝ] Plane)‖ +
      ‖((coverPower i).symm : Plane →L[ℝ] Plane)‖)
    (fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hm
  exact ((le_add_of_nonneg_right (norm_nonneg ((coverPower d).symm : Plane →L[ℝ] Plane))).trans hs).trans
    (le_add_of_nonneg_left zero_le_one)

theorem inverseCoveringNorm_le_bound {d D : ℕ} (hd : d ≤ D) :
    ‖((coverPower d).symm : Plane →L[ℝ] Plane)‖ ≤ coveringBound D := by
  have hm : d ∈ Finset.range (D + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hs := Finset.single_le_sum
    (f := fun i => ‖(coverPower i : Plane →L[ℝ] Plane)‖ +
      ‖((coverPower i).symm : Plane →L[ℝ] Plane)‖)
    (fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hm
  exact ((le_add_of_nonneg_left (norm_nonneg (coverPower d : Plane →L[ℝ] Plane))).trans hs).trans
    (le_add_of_nonneg_left zero_le_one)

namespace Geometry

variable (g : Geometry)

noncomputable def coordinateLinear : Plane →L[ℝ] Plane :=
  (g.basis.symm : Plane →L[ℝ] Plane).comp (coverPower g.gap : Plane →L[ℝ] Plane)

noncomputable def pointLinear : Plane →L[ℝ] Plane :=
  ((coverPower g.gap).symm : Plane →L[ℝ] Plane).comp (g.basis : Plane →L[ℝ] Plane)



theorem coordinates_eq_affine (k : Frequency) (Y : Plane) :
    g.coordinates k Y = g.coordinates k 0 + g.coordinateLinear Y := by
  simp only [coordinates, coordinateLinear, ContinuousLinearMap.comp_apply, map_sub, map_zero]
  simp only [ContinuousLinearEquiv.coe_coe]
  abel



theorem norm_coordinateLinear_le {D : ℕ} (hd : g.gap ≤ D) :
    ‖g.coordinateLinear‖ ≤ ‖(g.basis.symm : Plane →L[ℝ] Plane)‖ * coveringBound D :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (coveringNorm_le_bound hd) (norm_nonneg _))

theorem norm_pointLinear_le {D : ℕ} (hd : g.gap ≤ D) :
    ‖g.pointLinear‖ ≤ coveringBound D * ‖(g.basis : Plane →L[ℝ] Plane)‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (inverseCoveringNorm_le_bound hd) (norm_nonneg _))






end Geometry




/-! ## Concrete projected tangent equation -/

noncomputable def negativeTangentProjection {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (n : H) : H →L[ℝ] H :=
  -(ContinuousLinearMap.id ℝ H - (innerSL ℝ n).smulRight ((⟪n, n⟫_ℝ)⁻¹ • n))

theorem negativeTangentProjection_apply {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (n x : H) :
    negativeTangentProjection n x = -TangentProjection.tangentProj n x := by
  simp only [negativeTangentProjection, _root_.neg_apply,
    _root_.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
    TangentProjection.tangentProj, div_eq_mul_inv]

/-- All quantities in the actual projected tangent equation, before solving.
The native normal and its slot derivative are explicit input fields. -/
structure TangentData (P H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  normal : P × Plane → H
  normalDot : P × Plane → H
  action : P × Plane → H →L[ℝ] H
  damping : P × Plane → ℝ
  source : P × Plane → H

namespace TangentData

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (t : TangentData P H) (g : Geometry) {a b : ℝ} (hab : a ≤ b)

noncomputable def linearData : LinearData P H H where
  coefficient z := TangentODE.projectedOperator (t.normal z) (t.normalDot z)
    (t.action z) (t.damping z)
  forcingMap z := negativeTangentProjection (t.normal z)
  source := t.source



end TangentData

end NavierStokes.CommonCoverSolve
