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

/-- The three components of one literal native pulse. -/
noncomputable def pulseVector (P : Pulse) (r : ℝ) (z : Plane) : Vector :=
  Fin.cases (P.radialProfile r z) (fun i => P.tangentProfile r i z)



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






end CurlCorrection







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




end Source

/-! ## Adapter to the actual `WaveCoefficients.withCutoff` field -/

section CoefficientAssembly

open LinearWaveBounds

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Q : Type} [NormedAddCommGroup Q]





end CoefficientAssembly

/-! ## The angular covariance is a genuine function on the auxiliary torus -/


















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
