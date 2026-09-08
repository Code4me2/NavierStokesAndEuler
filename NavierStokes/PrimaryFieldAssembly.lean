import NavierStokes.PrimaryPulseBounds
import NavierStokes.LinearWaveBounds

/-!
# Assembly of the actual primary tangent field

The native vector pulse, its integer periodization and covering, and its
complex harmonic use the same `PairData` as the covariance calculation.
The exact curl correction remains a separate field.
-/

noncomputable section

namespace NavierStokes.PrimaryFieldAssembly

open Set Function PartitionedCovariance HarmonicCalculus
open scoped BigOperators Topology

abbrev Vector := Fin 3 → ℝ
abbrev SignedIndex := UnsignedLabel × Fin 2

/-- The three components of one literal native pulse. -/
noncomputable def pulseVector (P : Pulse) (r : ℝ) (z : Plane) : Vector :=
  Fin.cases (P.radialProfile r z) (fun i => P.tangentProfile r i z)

@[simp] theorem pulseVector_zero (P : Pulse) (r : ℝ) (z : Plane) :
    pulseVector P r z 0 = P.radialProfile r z := rfl

@[simp] theorem pulseVector_succ (P : Pulse) (r : ℝ) (z : Plane) (i : Fin 2) :
    pulseVector P r z i.succ = P.tangentProfile r i z := rfl

private theorem compact_vector {f : Plane → Vector}
    (hf : ∀ i, HasCompactSupport (fun z => f z i)) : HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_iUnion (fun i => (hf i).isCompact))
  intro z hz
  funext i
  by_contra hi
  apply hz
  exact mem_iUnion.mpr ⟨i, subset_tsupport (fun z => f z i) hi⟩

variable {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}

/-- The vector is placed at the actual signed slot center, with exactly the
native chart and transverse stretch used in `PairData.rawRadial`. -/
noncomputable def nativeVector {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) : Plane → Vector :=
  TorusAverages.nativeField (TorusAverages.slotChart vr vt hdet)
    (slotCenter h (signedLabel U j))
    (TorusAverages.transverseStretch (P.ci j) sys.radius
      (pulseVector (P.pulses j) sys.radius))

@[simp] theorem nativeVector_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) :
    nativeVector P hdet j Y 0 = P.rawRadial hdet j Y := rfl

@[simp] theorem nativeVector_succ {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) (i : Fin 2) :
    nativeVector P hdet j Y i.succ = P.rawTangent hdet j i Y := rfl

theorem nativeVector_compact {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    HasCompactSupport (nativeVector P hdet j) := by
  apply compact_vector
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact P.rawRadial_compact hdet j
  · exact P.rawTangent_compact hdet j k

/-- Evaluation commutes with the actual lattice sum because its support is
finite at the evaluation point. -/
theorem periodize_apply {f : Plane → Vector} (hf : HasCompactSupport f)
    (Y : Plane) (i : Fin 3) :
    TorusAverages.periodize f Y i =
      TorusAverages.periodize (fun z => f z i) Y := by
  obtain ⟨s, hs⟩ := TorusAverages.finite_translates_on_ball hf ‖Y‖
  have hv : TorusAverages.periodize f Y =
      ∑ k ∈ s, f (TorusAverages.latticePoint k + Y) :=
    tsum_eq_sum (hs Y le_rfl)
  have hi : TorusAverages.periodize (fun z => f z i) Y =
      ∑ k ∈ s, f (TorusAverages.latticePoint k + Y) i := by
    apply tsum_eq_sum
    intro k hk
    change f (TorusAverages.latticePoint k + Y) i = 0
    rw [hs Y le_rfl k hk]
    rfl
  rw [hv, hi]
  simp only [Finset.sum_apply]

/-- The covering is the same integer linear map as the slot construction. -/
noncomputable def coveredVector {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) : Vector :=
  TorusAverages.periodize (nativeVector P hdet j)
    ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y)

@[simp] theorem coveredVector_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) :
    coveredVector P hdet j Y 0 =
      covered (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) Y := by
  unfold coveredVector covered
  rw [periodize_apply (nativeVector_compact P hdet j), cover_power_eq_iterate]
  rfl

@[simp] theorem coveredVector_succ {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : Plane) (i : Fin 2) :
    coveredVector P hdet j Y i.succ =
      covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) Y := by
  unfold coveredVector covered
  rw [periodize_apply (nativeVector_compact P hdet j), cover_power_eq_iterate]
  rfl

/-- The square roots, signed-label mask, and physical outer factor are
literal; no fresh choice of amplitudes is made when assembling the field. -/
noncomputable def slotAmplitude {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) : ComplexVector :=
  fun i => ((outer * amplitude ε (mask D U q x) P.matrix T j *
    coveredVector P hdet j Y i : ℝ) : ℂ)

noncomputable def slotPhase {U : UnsignedLabel} (P : PairData sys U)
    (j : Fin 2) (z : Plane × ℝ) : ℝ := (P.modes j : ℝ) * z.2 + P.phases j z.1

/-- Real part of the actual complex harmonic carrying the periodized vector
pulse. Frequency one here records the full phase; `mode_identification`
below also accepts a frequency kept separately from its phase. -/
noncomputable def slotVelocity {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) : Vector :=
  fun i => (vectorMode 1 (slotPhase P j)
    (fun z => slotAmplitude P hdet outer ε T q x j z.1) (Y, θ) i).re

theorem real_vectorMode {X : Type*} (κ : ℝ) (Φ : X → ℝ) (a : X → Vector)
    (x : X) (i : Fin 3) :
    (vectorMode κ Φ (fun z j => (a z j : ℂ)) x i).re =
      a x i * Real.cos (κ * Φ x) := by
  simp [vectorMode, mode, carrier, phaseFactor, Complex.exp_re,
    Complex.mul_re, Complex.mul_im]

theorem slotVelocity_formula {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) (i : Fin 3) :
    slotVelocity P hdet outer ε T q x j Y θ i =
      outer * amplitude ε (mask D U q x) P.matrix T j *
        coveredVector P hdet j Y i * Real.cos ((P.modes j : ℝ) * θ + P.phases j Y) := by
  unfold slotVelocity slotAmplitude
  rw [real_vectorMode]
  simp only [one_mul, slotPhase]

@[simp] theorem slotVelocity_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y θ 0 =
      P.radialWave hdet outer ε T q x j Y θ := by
  rw [slotVelocity_formula, coveredVector_zero]
  rfl

@[simp] theorem slotVelocity_succ {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) (i : Fin 2) :
    slotVelocity P hdet outer ε T q x j Y θ i.succ =
      P.tangentWave hdet outer ε T q x j i Y θ := by
  rw [slotVelocity_formula, coveredVector_succ]
  rfl

theorem slotVelocity_mask_zero {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (hm : mask D U q x = 0)
    (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y θ = 0 := by
  funext i
  simp [slotVelocity_formula, amplitude, hm]

/-- The same finite set of signed labels works for all auxiliary points
and all angles at a positive physical point. -/
theorem finite_active_slots (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q)
    (x : SlotColoring.Position) :
    ∃ F : Finset SignedIndex, ∀ a : SignedIndex, a ∉ F →
      mask D (tailLabel N a.1) q x = 0 := by
  classical
  let hs := finite_active_masks D N hq x
  refine ⟨hs.toFinset.product Finset.univ, ?_⟩
  intro a ha
  by_contra hm
  exact ha (Finset.mem_product.mpr ⟨hs.mem_toFinset.mpr hm, Finset.mem_univ _⟩)

private theorem finsum_vector_apply {ι : Type*} (f : ι → Vector) (s : Finset ι)
    (hf : ∀ a, a ∉ s → f a = 0) (i : Fin 3) :
    (∑ᶠ a, f a) i = ∑ᶠ a, f a i := by
  classical
  have hv : (∑ᶠ a, f a) = ∑ a ∈ s, f a := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    by_contra hn
    exact ha (hf a hn)
  have hi : (∑ᶠ a, f a i) = ∑ a ∈ s, f a i := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    by_contra hn
    exact ha (by change f a i = 0; rw [hf a hn]; rfl)
  rw [hv, hi]
  simp only [Finset.sum_apply]

noncomputable def principalField {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) : Vector :=
  ∑ᶠ a : SignedIndex,
    slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ

theorem principalField_finite {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) :
    ∃ F : Finset SignedIndex, ∀ Y θ,
      principalField P hdet outer ε T q x Y θ =
        ∑ a ∈ F, slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ := by
  classical
  obtain ⟨F, hF⟩ := finite_active_slots D N hq x
  refine ⟨F, ?_⟩
  intro Y θ
  apply finsum_eq_sum_of_support_subset
  intro a ha
  by_contra hn
  exact ha (slotVelocity_mask_zero (P a.1) hdet _ _ _ q x (hF a hn) _ Y θ)

theorem principalField_apply {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) (i : Fin 3) :
    principalField P hdet outer ε T q x Y θ i =
      ∑ᶠ a : SignedIndex,
        slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ i := by
  obtain ⟨F, hF⟩ := finite_active_slots D N hq x
  exact finsum_vector_apply _ F
    (fun a ha => slotVelocity_mask_zero (P a.1) hdet _ _ _ q x (hF a ha) _ Y θ) i

theorem principalField_components {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) :
    principalField P hdet outer ε T q x Y θ 0 =
      assembledRadial P hdet outer ε T q x Y θ ∧
    ∀ i : Fin 2, principalField P hdet outer ε T q x Y θ i.succ =
      assembledTangent P hdet outer ε T q x i Y θ := by
  constructor
  · simp only [principalField_apply P hdet outer ε T hq x, slotVelocity_zero,
      assembledRadial]
  · intro i
    simp only [principalField_apply P hdet outer ε T hq x, slotVelocity_succ,
      assembledTangent]


/-! ## A single cutoff, before periodization -/



/-- Identification with any actual frequency/phase presentation of the
same harmonic, including the frequency convention of `WaveCoefficients`. -/
theorem mode_identification {X : Type*} (κ : ℝ) (Φ : X → ℝ)
    (a : X → ComplexVector) (z : X) {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ)
    (ha : a z = slotAmplitude P hdet outer ε T q x j Y)
    (hphase : κ * Φ z = slotPhase P j (Y, θ)) :
    (fun i => (vectorMode κ Φ a z i).re) =
      slotVelocity P hdet outer ε T q x j Y θ := by
  funext i
  have ha' := congrFun ha i
  rw [slotVelocity_formula]
  unfold vectorMode mode
  dsimp only
  rw [ha']
  change (((outer * amplitude ε (mask D U q x) P.matrix T j *
    coveredVector P hdet j Y i : ℝ) : ℂ) * carrier κ Φ z).re = _
  have hr := real_vectorMode κ Φ
    (fun _ => fun k => outer * amplitude ε (mask D U q x) P.matrix T j *
      coveredVector P hdet j Y k) z i
  change (((outer * amplitude ε (mask D U q x) P.matrix T j *
    coveredVector P hdet j Y i : ℝ) : ℂ) * carrier κ Φ z).re = _ at hr
  rw [hr, hphase]
  rfl



/-! ## The exact curl retains its covariance error -/

section CurlCorrection

open LinearWaveBounds WeightedClasses

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

noncomputable def cutoffVelocity (a : WaveCoefficients X) (ψ : ℕ → X → ℝ)
    (n : ℕ) (x : X) : Vector :=
  fun i => (vectorMode (a.frequency n) (a.phase n)
    ((a.withCutoff ψ).amplitude n) x i).re





end CurlCorrection

noncomputable def covarianceError (V R : Plane → ℝ → Vector) (i : Fin 2)
    (Y : Plane) (θ : ℝ) : ℝ :=
  V Y θ 0 * R Y θ i.succ + R Y θ 0 * V Y θ i.succ + R Y θ 0 * R Y θ i.succ


private theorem continuous_angularMean {f : Plane → ℝ → ℝ}
    (hf : Continuous f.uncurry) : Continuous (fun Y => SmoothLoop.angularMean (f Y)) :=
  (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf
    0 (2 * Real.pi)).div_const _

private theorem squareAverage_add {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g) :
    TorusAverages.squareAverage (fun Y => f Y + g Y) =
      TorusAverages.squareAverage f + TorusAverages.squareAverage g := by
  rw [TorusAverages.squareAverage_eq_setIntegral (hf.fun_add hg),
    TorusAverages.squareAverage_eq_setIntegral hf, TorusAverages.squareAverage_eq_setIntegral hg]
  apply MeasureTheory.integral_add
  · exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  · exact (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)



/-! ## Canonical source data: actual ODE pulses and the same matrix -/

section Source

open PrimaryPulseBounds

variable {Q : Type} [NormedAddCommGroup Q]

/-- Primitive data for a signed pair of actual ODE pulses. No local field,
matrix, or covariance identity is a field of this structure. -/
structure SourcePair (Q : Type) [NormedAddCommGroup Q]
    {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt) (U : UnsignedLabel) where
  domain : Set Q
  point : Q
  point_mem : point ∈ domain
  frame : Fin 2 → PrimaryODE.FrameData Q
  lam : Fin 2 → ℝ
  rate : Fin 2 → ℝ
  length : Fin 2 → ℝ
  length_pos : ∀ j, 0 < length j
  coefficient_continuous : ∀ j,
    ContinuousOn ((frame j).coefficient 1) (domain ×ˢ Icc 0 (length j))
  kinematics : ∀ j, (frame j).Kinematics point (Icc 0 (length j))
  stretch : Vec2
  stretch_pos : ∀ j, 0 < stretch j
  fits : ∀ j, length j ≤ 2 * sys.radius / stretch j
  mode : Fin 2 → ℤ
  mode_ne : ∀ j, mode j ≠ 0
  phase : Fin 2 → Plane → ℝ

namespace SourcePair

variable {U : UnsignedLabel} (A : SourcePair Q sys U)

noncomputable def pairData : PairData sys U where
  pulses := fun j => canonicalPrimaryPulse (A.frame j) (A.lam j) (A.rate j)
    (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j)
  ci := A.stretch
  ci_pos := A.stretch_pos
  fits := by
    intro j t ht
    have hmem : t ∈ Icc 0 (A.length j) := by
      by_contra hn
      exact ht (slotCutoff_zero_of_not_mem_Icc (A.length_pos j) hn)
    exact ⟨hmem.1, hmem.2.trans (A.fits j)⟩
  modes := A.mode
  modes_ne := A.mode_ne
  phases := A.phase

/-- The matrix is computed directly from the normalized ODE fundamentals,
with the exact determinant, transverse scale, and slot-length prefactor. -/
noncomputable def sourceMatrix : Mat2 :=
  primaryCovariance
    (fun j (_ : Unit) => nativePrefactor vr vt sys.radius * A.stretch j * A.length j)
    (fun j _ => A.frame j) (fun j _ => A.lam j) (fun j _ => A.rate j)
    (fun j _ => A.length j) () A.point

theorem sourceMatrix_eq : A.sourceMatrix = A.pairData.matrix := by
  exact primaryCovariance_eq_canonicalPairMatrix _ _ _ _ _ () A.domain A.point A.point_mem
    A.length_pos A.coefficient_continuous A.kinematics vr vt sys.radius A.stretch
    (fun _ => rfl)

theorem pulseVector_eq (j : Fin 2) (z : Plane) :
    pulseVector (A.pairData.pulses j) sys.radius z =
      fun i => localPrimaryProfile (A.frame j) (A.lam j) (A.rate j)
        (A.length j) sys.radius A.point z i := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact canonicalPrimaryPulse_radialProfile (A.frame j) (A.lam j) (A.rate j) sys.radius
      (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j) z
  · exact canonicalPrimaryPulse_tangentProfile (A.frame j) (A.lam j) (A.rate j) sys.radius
      (A.length_pos j) A.domain (A.coefficient_continuous j) A.point A.point_mem (A.kinematics j) z k

/-- The source vector is evaluated from `cutoffPulse`, rather than from
arbitrarily supplied radial and tangent component functions. -/
noncomputable def nativeSource (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (j : Fin 2) : Plane → Vector :=
  TorusAverages.nativeField (TorusAverages.slotChart vr vt hdet)
    (slotCenter h (signedLabel U j))
    (TorusAverages.transverseStretch (A.stretch j) sys.radius
      (fun z i => localPrimaryProfile (A.frame j) (A.lam j) (A.rate j)
        (A.length j) sys.radius A.point z i))

theorem nativeSource_eq (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    A.nativeSource hdet j = nativeVector A.pairData hdet j := by
  funext Y
  symm
  exact A.pulseVector_eq j _

/-- The native complex coefficient has the literal inverse-square-root
amplitude and a single local Gaussian cutoff. -/
noncomputable def nativeCoefficient (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) : ComplexVector :=
  fun i => ((outer * amplitude ε (mask D U q x) A.sourceMatrix T j *
    A.nativeSource hdet j Y i : ℝ) : ℂ)

noncomputable def actualAmplitude (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) : ComplexVector :=
  TorusAverages.periodize (A.nativeCoefficient hdet outer ε T q x j)
    ((SlotGeometry.cover ^ SlotColoring.nativeIndex h U.1) Y)

end SourcePair

private theorem periodize_scaled_real_vector {f : Plane → Vector}
    (hf : HasCompactSupport f) (c : ℝ) (Y : Plane) (i : Fin 3) :
    TorusAverages.periodize (fun z => fun j => ((c * f z j : ℝ) : ℂ)) Y i =
      ((c * TorusAverages.periodize f Y i : ℝ) : ℂ) := by
  obtain ⟨s, hs⟩ := TorusAverages.finite_translates_on_ball hf ‖Y‖
  have hreal : TorusAverages.periodize f Y =
      ∑ k ∈ s, f (TorusAverages.latticePoint k + Y) := tsum_eq_sum (hs Y le_rfl)
  have hcomplex : TorusAverages.periodize (fun z => fun j => ((c * f z j : ℝ) : ℂ)) Y =
      ∑ k ∈ s, fun j => ((c * f (TorusAverages.latticePoint k + Y) j : ℝ) : ℂ) := by
    apply tsum_eq_sum
    intro k hk
    funext j
    simp [hs Y le_rfl k hk]
  rw [hreal, hcomplex]
  simp [Finset.sum_apply, Finset.mul_sum]

namespace SourcePair

variable {U : UnsignedLabel} (A : SourcePair Q sys U)

/-- The actual periodized complex coefficient equals the coefficient used
in the radial/tangent covariance assembly. -/
theorem actualAmplitude_eq (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) :
    A.actualAmplitude hdet outer ε T q x j Y =
      slotAmplitude A.pairData hdet outer ε T q x j Y := by
  unfold actualAmplitude nativeCoefficient
  rw [A.sourceMatrix_eq, A.nativeSource_eq]
  funext i
  exact periodize_scaled_real_vector (nativeVector_compact A.pairData hdet j) _ _ i

noncomputable def actualVelocity (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) (θ : ℝ) : Vector :=
  fun i => (vectorMode 1 (slotPhase A.pairData j)
    (fun z => A.actualAmplitude hdet outer ε T q x j z.1) (Y, θ) i).re

theorem actualVelocity_eq (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position)
    (j : Fin 2) (Y : Plane) (θ : ℝ) :
    A.actualVelocity hdet outer ε T q x j Y θ =
      slotVelocity A.pairData hdet outer ε T q x j Y θ := by
  apply mode_identification 1 (slotPhase A.pairData j)
    (fun z => A.actualAmplitude hdet outer ε T q x j z.1) (Y, θ)
  · exact A.actualAmplitude_eq hdet outer ε T q x j Y
  · simp

end SourcePair

noncomputable def sourceField {N : ℕ}
    (A : (U : UnsignedLabel) → SourcePair Q sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (Y : Plane) (θ : ℝ) : Vector :=
  ∑ᶠ a : SignedIndex,
    (A a.1).actualVelocity hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ



end Source

/-! ## Adapter to the actual `WaveCoefficients.withCutoff` field -/

section CoefficientAssembly

open LinearWaveBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Q : Type} [NormedAddCommGroup Q]





end CoefficientAssembly

/-! ## The angular covariance is a genuine function on the auxiliary torus -/

private noncomputable def latticeCover (k : TorusInverse.Frequency) : TorusInverse.Frequency :=
  (3 * k.1 + k.2, k.1 + 5 * k.2)

private theorem covering_add_lattice (Y : Plane) (k : TorusInverse.Frequency) :
    TorusAverages.covering (Y + TorusAverages.latticePoint k) =
      TorusAverages.covering Y + TorusAverages.latticePoint (latticeCover k) := by
  ext <;> simp [TorusAverages.covering, TorusAverages.latticePoint, latticeCover] <;> ring

private theorem covering_iterate_add_lattice (n : ℕ) (Y : Plane) (k : TorusInverse.Frequency) :
    TorusAverages.covering^[n] (Y + TorusAverages.latticePoint k) =
      TorusAverages.covering^[n] Y + TorusAverages.latticePoint (latticeCover^[n] k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, covering_add_lattice,
        Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem covered_periodic (n : ℕ) (f : Plane → ℝ) (Y : Plane) (k : TorusInverse.Frequency) :
    covered n f (Y + TorusAverages.latticePoint k) = covered n f Y := by
  unfold covered
  rw [covering_iterate_add_lattice, TorusAverages.periodize_periodic]

theorem slot_cross_zero {N : ℕ} (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position)
    {a b : SignedIndex} (hab : a ≠ b) (Y : Plane) (θ : ℝ) (i : Fin 2) :
    slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ 0 *
      slotVelocity (P b.1) hdet (outer b.1) (ε b.1) (T b.1) q x b.2 Y θ i.succ = 0 := by
  have hlevel (c : SignedIndex) : 1 ≤ (signedTailLabel N c).1 := by
    change 1 ≤ c.1.1 + N
    omega
  have hne : signedTailLabel N a ≠ signedTailLabel N b :=
    fun he => hab ((signedTailLabel_injective N) he)
  have hz := sys.wave_cross_zero (hlevel a) (hlevel b) hne
    ((P a.1).rawRadial_support hdet a.2) ((P b.1).rawTangent_support hdet b.2 i) hq x Y θ
    (outer a.1 * Real.sqrt (ε a.1) * SmoothCovariance.amplitudes (P a.1).matrix (T a.1) a.2)
    (outer b.1 * Real.sqrt (ε b.1) * SmoothCovariance.amplitudes (P b.1).matrix (T b.1) b.2)
    ((P a.1).modes a.2) ((P b.1).modes b.2) ((P a.1).phases a.2) ((P b.1).phases b.2)
  simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave, PairData.tangentWave,
    signedTailLabel, physicalMask_signedLabel, amplitude, mul_assoc] at hz ⊢
  exact hz

noncomputable def diagonalCovariance {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position)
    (a : SignedIndex) (i : Fin 2) (Y : Plane) : ℝ :=
  (outer a.1 * amplitude (ε a.1) (mask D (tailLabel N a.1) q x) (P a.1).matrix (T a.1) a.2) ^ 2 *
    covered (SlotColoring.nativeIndex h (tailLabel N a.1).1) ((P a.1).rawRadial hdet a.2) Y *
      covered (SlotColoring.nativeIndex h (tailLabel N a.1).1) ((P a.1).rawTangent hdet a.2 i) Y * (1 / 2)

/-- Both off-diagonal elimination and angular integration are performed
on the actual finite active family, before descending to the torus. -/
theorem angular_principal_finite {N : ℕ} (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (i : Fin 2) :
    ∃ F : Finset SignedIndex, ∀ Y,
      SmoothLoop.angularMean (fun θ => principalField P hdet outer ε T q x Y θ 0 *
        principalField P hdet outer ε T q x Y θ i.succ) =
      ∑ a ∈ F, diagonalCovariance P hdet outer ε T q x a i Y := by
  classical
  obtain ⟨F, hF⟩ := principalField_finite P hdet outer ε T hq x
  refine ⟨F, ?_⟩
  intro Y
  have hprod (θ : ℝ) : principalField P hdet outer ε T q x Y θ 0 *
      principalField P hdet outer ε T q x Y θ i.succ =
      ∑ a ∈ F, slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ 0 *
        slotVelocity (P a.1) hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ i.succ := by
    simp only [hF Y θ, Finset.sum_apply]
    apply sum_product_diagonal
    intro a _ b _ hab
    exact slot_cross_zero hN P hdet outer ε T hq x hab Y θ i
  simp_rw [hprod]
  rw [angularMean_sum F]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave, PairData.tangentWave]
    exact angularMean_wave_product _ _ _ _ _ ((P a.1).modes_ne a.2) _ _
  · intro a _
    simp only [slotVelocity_zero, slotVelocity_succ, PairData.radialWave, PairData.tangentWave]
    exact (wave_continuous_theta _ _ _ _ _ _).mul (wave_continuous_theta _ _ _ _ _ _)




theorem nativeVector_continuous {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    Continuous (nativeVector P hdet j) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact P.rawRadial_continuous hdet j
  · exact P.rawTangent_continuous hdet j k







/-! ## Explicit conversion from chart velocity to physical velocity -/

theorem slotVelocity_outer_scale {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (T : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (Y : Plane) (θ : ℝ) :
    slotVelocity P hdet outer ε T q x j Y θ = outer • slotVelocity P hdet 1 ε T q x j Y θ := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, slotVelocity_formula]
  ring


section PhysicalCoefficientAssembly

open LinearWaveBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Q : Type} [NormedAddCommGroup Q]





end PhysicalCoefficientAssembly

end NavierStokes.PrimaryFieldAssembly
