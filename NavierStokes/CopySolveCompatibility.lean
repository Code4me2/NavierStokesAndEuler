import NavierStokes.CommonCoverClass

/-!
# Compatibility of the actual copy-path solve with a common-cover change

The native slot is held fixed while the common cover is refined.  Sources
are pulled back along the covering map.  Equality is proved first for the
actual coefficient/forcing paths and then for the constructed Volterra
inverse; no native periodicity of an inhomogeneous solution is assumed.
-/

noncomputable section

namespace NavierStokes.CopySolveCompatibility

open Set Function Filter
open scoped ContDiff Topology BigOperators
open TorusInverse CommonCoverSolve

theorem coverPower_add (d k : ℕ) (Y : Plane) :
    coverPower (d + k) Y = coverPower d (coverPower k Y) := by
  simp only [coverPower_apply, pow_add, _root_.mul_apply_eq_comp]

noncomputable def refineGeometry (g : Geometry) (k : ℕ) : Geometry :=
  { g with gap := g.gap + k }

theorem coordinates_refine (g : Geometry) (k : ℕ) (j : Frequency) (Y : Plane) :
    (refineGeometry g k).coordinates j Y = g.coordinates j (coverPower k Y) := by
  simp only [Geometry.coordinates, refineGeometry, coverPower_add]

theorem point_refine (g : Geometry) (k : ℕ) (j : Frequency) (z : Plane) :
    coverPower k ((refineGeometry g k).point j z) = g.point j z := by
  apply (coverPower g.gap).injective
  change coverPower g.gap (coverPower k ((coverPower (g.gap + k)).symm _)) =
    coverPower g.gap ((coverPower g.gap).symm _)
  rw [← coverPower_add, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem path_refine (g : Geometry) (k : ℕ) (j : Frequency) (Y : Plane) (s : ℝ) :
    coverPower k ((refineGeometry g k).path j Y s) = g.path j (coverPower k Y) s := by
  simp only [Geometry.path, coordinates_refine, point_refine]


/-- This includes cutoff indicators and copy envelopes, with no regularity
assumption on the native function. -/
theorem native_copy_sum_refine {E : Type} [NormedAddCommGroup E] (g : Geometry) (k : ℕ)
    (f : Plane → E) (Y : Plane) :
    (∑' j : Frequency, f ((refineGeometry g k).coordinates j Y)) =
      ∑' j : Frequency, f (g.coordinates j (coverPower k Y)) := by
  apply tsum_congr
  intro j
  rw [coordinates_refine]

section Paths

variable {P Q V E : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Input data transported through a slow-parameter map and a refinement of
the common cover. All native coefficients retain their native arguments. -/
noncomputable def transformData (d : LinearData P V E) (φ : Q → P) (k : ℕ) :
    LinearData Q V E where
  coefficient z := d.coefficient (φ z.1, z.2)
  forcingMap z := d.forcingMap (φ z.1, z.2)
  source z := d.source (φ z.1, coverPower k z.2)


theorem coefficientAlong_transform (d : LinearData P V E) (φ : Q → P)
    (g : Geometry) (k : ℕ) (j : Frequency) (q : Q) (Y : Plane) (s : ℝ) :
    (transformData d φ k).coefficientAlong (refineGeometry g k) j ((q, Y), s) =
      d.coefficientAlong g j ((φ q, coverPower k Y), s) := by
  simp only [LinearData.coefficientAlong, transformData, coordinates_refine]

theorem forcingAlong_transform (d : LinearData P V E) (φ : Q → P)
    (g : Geometry) (k : ℕ) (j : Frequency) (q : Q) (Y : Plane) (s : ℝ) :
    (transformData d φ k).forcingAlong (refineGeometry g k) j ((q, Y), s) =
      d.forcingAlong g j ((φ q, coverPower k Y), s) := by
  simp only [LinearData.forcingAlong, transformData, coordinates_refine, path_refine]

omit [NormedSpace ℝ E] in
/-- Equality of input paths may compare different parameter spaces. The
canonical zero branch for a noncontinuous slice is respected as well. -/
theorem pathFamily_congr {a b : ℝ} (F : P × ℝ → E) (G : Q × ℝ → E)
    (p : P) (q : Q) (h : ∀ s : Icc a b, F (p, s) = G (q, s)) :
    SmoothPathFamily.pathFamily (a := a) (b := b) F p =
      SmoothPathFamily.pathFamily G q := by
  have he : (fun s : Icc a b => F (p, s)) = (fun s : Icc a b => G (q, s)) := funext h
  by_cases hF : Continuous (fun s : Icc a b => F (p, s))
  · have hG : Continuous (fun s : Icc a b => G (q, s)) := he ▸ hF
    ext s
    rw [SmoothPathFamily.pathFamily_apply F p hF, SmoothPathFamily.pathFamily_apply G q hG]
    exact h s
  · have hG : ¬ Continuous (fun s : Icc a b => G (q, s)) := fun hc => hF (he.symm ▸ hc)
    simp only [SmoothPathFamily.pathFamily, dite_eq_right hF, dite_eq_right hG]

theorem coefficientPath_transform {a b : ℝ} (d : LinearData P V E) (φ : Q → P)
    (g : Geometry) (k : ℕ) (j : Frequency) (q : Q) (Y : Plane) :
    (transformData d φ k).coefficientPath (a := a) (b := b) (refineGeometry g k) j (q, Y) =
      d.coefficientPath g j (φ q, coverPower k Y) := by
  apply pathFamily_congr
  intro s
  exact coefficientAlong_transform d φ g k j q Y s

theorem forcingPath_transform {a b : ℝ} (d : LinearData P V E) (φ : Q → P)
    (g : Geometry) (k : ℕ) (j : Frequency) (q : Q) (Y : Plane) :
    (transformData d φ k).forcingPath (a := a) (b := b) (refineGeometry g k) j (q, Y) =
      d.forcingPath g j (φ q, coverPower k Y) := by
  apply pathFamily_congr
  intro s
  exact forcingAlong_transform d φ g k j q Y s

variable [CompleteSpace E] {a b : ℝ}

theorem anchoredSolve_transform (d : LinearData P V E) (φ : Q → P)
    (g : Geometry) (hab : a ≤ b) (k : ℕ) (j : Frequency) (q : Q) (Y : Plane) (s : ℝ) :
    (transformData d φ k).anchoredSolve (refineGeometry g k) hab j (q, Y) s =
      d.anchoredSolve g hab j (φ q, coverPower k Y) s := by
  unfold LinearData.anchoredSolve
  rw [coefficientPath_transform, forcingPath_transform]

theorem copySolve_transform (d : LinearData P V E) (φ : Q → P)
    (g : Geometry) (hab : a ≤ b) (k : ℕ) (j : Frequency) (q : Q) (Y : Plane) :
    (transformData d φ k).copySolve (refineGeometry g k) hab j (q, Y) =
      d.copySolve g hab j (φ q, coverPower k Y) := by
  unfold LinearData.copySolve
  rw [coordinates_refine, anchoredSolve_transform]






end Paths

/-! ## Changing the integer representative of the native slot center -/





section Recenter

variable {P V E : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}





end Recenter

/-! ## Physical units: scaling the actual source scales the actual solution -/

section SourceScale

variable {P V E : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

noncomputable def scaleSource (d : LinearData P V E) (c : ℝ) : LinearData P V E :=
  { d with source := fun x => c • d.source x }

omit [CompleteSpace E] in
theorem pathFamily_smul (F : P × ℝ → E) (p : P) (c : ℝ) :
    SmoothPathFamily.pathFamily (a := a) (b := b) (fun x => c • F x) p =
      c • SmoothPathFamily.pathFamily F p := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_smul]
    simp only [SmoothPathFamily.pathFamily, dite_eq_left continuous_const]
    rfl
  by_cases hF : Continuous (fun s : Icc a b => F (p, s))
  · have hCF : Continuous (fun s : Icc a b => c • F (p, s)) := continuous_const.smul hF
    ext s
    rw [SmoothPathFamily.pathFamily_apply _ _ hCF, ContinuousMap.smul_apply,
      SmoothPathFamily.pathFamily_apply _ _ hF]
  · have hCF : ¬ Continuous (fun s : Icc a b => c • F (p, s)) := by
      intro hh
      have h : Continuous (fun s : Icc a b => c⁻¹ • (c • F (p, s))) := continuous_const.smul hh
      apply hF
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
    simp only [SmoothPathFamily.pathFamily, dite_eq_right hF, dite_eq_right hCF, smul_zero]

theorem solution_zero_smul (hab : a ≤ b) (A : ParametricODE.Coefficient a b E)
    (f : ParametricODE.Curve a b E) (c : ℝ) :
    ParametricODE.solution hab A 0 (c • f) = c • ParametricODE.solution hab A 0 f := by
  simp only [ParametricODE.solution, ParametricODE.source, map_zero, zero_add, map_smul]

theorem solutionExtension_zero_smul (hab : a ≤ b) (A : ParametricODE.Coefficient a b E)
    (f : ParametricODE.Curve a b E) (c s : ℝ) :
    ParametricODE.solutionExtension hab A 0 (c • f) s =
      c • ParametricODE.solutionExtension hab A 0 f s := by
  have he : ParametricODE.applyCoefficient A (c • ParametricODE.solution hab A 0 f) + c • f =
      c • (ParametricODE.applyCoefficient A (ParametricODE.solution hab A 0 f) + f) := by
    ext t
    simp only [ParametricODE.applyCoefficient, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.coe_mk, map_smul, smul_add]
  simp only [ParametricODE.solutionExtension, solution_zero_smul, he, zero_add,
    ParametricODE.extend, ContinuousMap.smul_apply, intervalIntegral.integral_smul]

theorem anchoredSolve_scaleSource (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (c : ℝ) (j : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    (scaleSource d c).anchoredSolve g hab j (p, Y) s =
      c • d.anchoredSolve g hab j (p, Y) s := by
  have hf : (scaleSource d c).forcingPath (a := a) (b := b) g j (p, Y) =
      c • d.forcingPath g j (p, Y) := by
    unfold LinearData.forcingPath
    have hh : (scaleSource d c).forcingAlong g j = fun x => c • d.forcingAlong g j x := by
      funext x
      simp only [LinearData.forcingAlong, scaleSource, map_smul]
    rw [hh, pathFamily_smul]
  change ParametricODE.solutionExtension hab (d.coefficientPath g j (p, Y)) 0
    ((scaleSource d c).forcingPath g j (p, Y)) s = _
  rw [hf, solutionExtension_zero_smul]
  rfl

theorem copySolve_scaleSource (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
    (c : ℝ) (j : Frequency) (p : P) (Y : Plane) :
    (scaleSource d c).copySolve g hab j (p, Y) = c • d.copySolve g hab j (p, Y) := by
  simp only [LinearData.copySolve, anchoredSolve_scaleSource]



end SourceScale

/-! ## Transporting the native clock, its anchor, and its cutoff together -/

noncomputable def nativeTimeMap (τ rate : ℝ) (z : Plane) : Plane :=
  (z.1, τ + rate * z.2)

theorem nativeTimeMap_continuous (τ rate : ℝ) : Continuous (nativeTimeMap τ rate) :=
  continuous_fst.prodMk (continuous_const.add (continuous_const.mul continuous_snd))

noncomputable def timeGeometry (g : Geometry) (τ rate : ℝ) (hrate : rate ≠ 0) : Geometry where
  gap := g.gap
  basis := CommonCoverClass.scaledBasis g.basis rate hrate
  center := g.center + g.basis (0, τ)

theorem point_timeGeometry (g : Geometry) (τ rate : ℝ) (hrate : rate ≠ 0)
    (j : Frequency) (z : Plane) :
    (timeGeometry g τ rate hrate).point j z = g.point j (nativeTimeMap τ rate z) := by
  simp only [Geometry.point, timeGeometry, CommonCoverClass.scaledBasis_apply, nativeTimeMap]
  have hv : (z.1, τ + rate * z.2) = (0, τ) + (z.1, rate * z.2) := by
    ext <;> simp
  rw [hv, map_add g.basis]
  congr 1
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem coordinates_timeGeometry (g : Geometry) (τ rate : ℝ) (hrate : rate ≠ 0)
    (j : Frequency) (Y : Plane) :
    nativeTimeMap τ rate ((timeGeometry g τ rate hrate).coordinates j Y) = g.coordinates j Y := by
  have h := point_timeGeometry g τ rate hrate j ((timeGeometry g τ rate hrate).coordinates j Y)
  rw [Geometry.point_coordinates] at h
  have hh := congrArg (g.coordinates j) h
  rw [g.coordinates_point] at hh
  exact hh.symm

theorem coordinates_timeGeometry_fst (g : Geometry) (τ rate : ℝ) (hrate : rate ≠ 0)
    (j : Frequency) (Y : Plane) :
    ((timeGeometry g τ rate hrate).coordinates j Y).1 = (g.coordinates j Y).1 := by
  simpa only [nativeTimeMap] using
    congrArg Prod.fst (coordinates_timeGeometry g τ rate hrate j Y)

theorem path_timeGeometry (g : Geometry) (τ rate : ℝ) (hrate : rate ≠ 0)
    (j : Frequency) (Y : Plane) (s : ℝ) :
    (timeGeometry g τ rate hrate).path j Y s = g.path j Y (τ + rate * s) := by
  simp only [Geometry.path, point_timeGeometry, nativeTimeMap, coordinates_timeGeometry_fst]

theorem time_interval_mono {a b rate : ℝ} (τ : ℝ) (hrate : 0 < rate) (hab : a ≤ b) :
    τ + rate * a ≤ τ + rate * b := add_le_add_right (mul_le_mul_of_nonneg_left hab hrate.le) τ

section TimeData

variable {P V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def timeData (d : LinearData P V E) (τ rate : ℝ) : LinearData P V E where
  coefficient z := rate • d.coefficient (z.1, nativeTimeMap τ rate z.2)
  forcingMap z := rate • d.forcingMap (z.1, nativeTimeMap τ rate z.2)
  source := d.source

theorem coefficientAlong_timeData (d : LinearData P V E) (g : Geometry)
    (τ rate : ℝ) (hrate : rate ≠ 0) (j : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    (timeData d τ rate).coefficientAlong (timeGeometry g τ rate hrate) j ((p, Y), s) =
      rate • d.coefficientAlong g j ((p, Y), τ + rate * s) := by
  simp only [LinearData.coefficientAlong, timeData, nativeTimeMap, coordinates_timeGeometry_fst]

theorem forcingAlong_timeData (d : LinearData P V E) (g : Geometry)
    (τ rate : ℝ) (hrate : rate ≠ 0) (j : Frequency) (p : P) (Y : Plane) (s : ℝ) :
    (timeData d τ rate).forcingAlong (timeGeometry g τ rate hrate) j ((p, Y), s) =
      rate • d.forcingAlong g j ((p, Y), τ + rate * s) := by
  simp only [LinearData.forcingAlong, timeData, nativeTimeMap,
    coordinates_timeGeometry_fst, path_timeGeometry, _root_.smul_apply]

variable [NormedAddCommGroup P] [NormedSpace ℝ P]



variable [CompleteSpace E] {a b : ℝ}





end TimeData

/-! ## A single output represented in all transported charts -/

section PhysicalCompatibility

variable {P Q V E X I : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def transportData (d : LinearData P V E) (φ : Q → P) (k : ℕ)
    (τ rate amplitude : ℝ) : LinearData Q V E :=
  scaleSource (transformData (timeData d τ rate) φ k) amplitude

noncomputable def transportGeometry (g : Geometry) (k : ℕ) (τ rate : ℝ) (hrate : rate ≠ 0) :
    Geometry := refineGeometry (timeGeometry g τ rate hrate) k





end PhysicalCompatibility

section ConcreteBandChart

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ}


end ConcreteBandChart

/-! ## Binding existing chart data through primitive input identities -/

section InputCompatibility

variable {P Q V E X I : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- These are identities of the coefficient and converted source before
any integration. They allow different source/map scalings with the same
product, and impose no assertion about solved fields. -/
structure SameInputsAt (d e : LinearData P V E) (p : P) : Prop where
  coefficient : ∀ z, d.coefficient (p, z) = e.coefficient (p, z)
  forcing : ∀ z Y, d.forcingMap (p, z) (d.source (p, Y)) =
    e.forcingMap (p, z) (e.source (p, Y))

variable [CompleteSpace E] {a b : ℝ}

theorem anchoredSolve_eq_of_sameInputs (d e : LinearData P V E) (g : Geometry)
    (hab : a ≤ b) (p : P) (hi : SameInputsAt d e p) (j : Frequency) (Y : Plane) (s : ℝ) :
    d.anchoredSolve g hab j (p, Y) s = e.anchoredSolve g hab j (p, Y) s := by
  have hA : d.coefficientPath (a := a) (b := b) g j (p, Y) =
      e.coefficientPath g j (p, Y) := by
    apply pathFamily_congr
    intro t
    exact hi.coefficient _
  have hf : d.forcingPath (a := a) (b := b) g j (p, Y) = e.forcingPath g j (p, Y) := by
    apply pathFamily_congr
    intro t
    exact hi.forcing _ _
  simp only [LinearData.anchoredSolve, hA, hf]

theorem commonSolve_eq_of_sameInputs (d e : LinearData P V E) (g : Geometry)
    (hab : a ≤ b) (p : P) (hi : SameInputsAt d e p) (κ : Plane → ℝ) (Y : Plane) :
    d.commonSolve g hab κ (p, Y) = e.commonSolve g hab κ (p, Y) := by
  apply tsum_congr
  intro j
  simp only [LinearData.localizedCopy, LinearData.copySolve,
    anchoredSolve_eq_of_sameInputs d e g hab p hi]

variable [NormedAddCommGroup P] [NormedSpace ℝ P]



end InputCompatibility

/-! ## Why the anchor must be transported as input data -/




end NavierStokes.CopySolveCompatibility
