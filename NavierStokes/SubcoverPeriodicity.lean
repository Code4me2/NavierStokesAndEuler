import NavierStokes.ParticularWaveBounds

/-!
# A single deck shift of the actual particular solve

Only invariance under the specified lattice vector is assumed.  Equality of
the actual anchored coefficient and forcing paths gives equality of the
Volterra solves, and a bijective copy reindexing gives the same symmetry of
the periodized velocity and pressure.
-/

noncomputable section

namespace NavierStokes.SubcoverPeriodicity

open Set Function CommonCoverSolve TorusInverse HarmonicCalculus ParticularWaveBounds
open scoped Topology BigOperators

section LinearSolve

variable {P V E : Type}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem forcingAlong_shift (d : LinearData P V E) (g : Geometry)
    (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) (s : ℝ) :
    d.forcingAlong g (j + coverIndex g.gap K) ((p, Y + TorusAverages.latticePoint K), s) =
      d.forcingAlong g j ((p,Y),s) := by
  simp only [LinearData.forcingAlong, g.coordinates_deck, g.path_deck, hf]

theorem forcingPath_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) :
    d.forcingPath (a := a) (b := b) g (j + coverIndex g.gap K)
        (p, Y + TorusAverages.latticePoint K) = d.forcingPath g j (p,Y) := by
  apply pathFamily_congr_slice
  intro s
  exact forcingAlong_shift d g j K p hf Y s

variable [CompleteSpace E]

theorem anchoredSolve_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) (s : ℝ) :
    d.anchoredSolve g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) s =
      d.anchoredSolve g hab j (p,Y) s := by
  unfold LinearData.anchoredSolve
  rw [d.coefficientPath_deck, forcingPath_shift d g j K p hf]

theorem copySolve_shift (d : LinearData P V E) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, d.source (p, Y + TorusAverages.latticePoint K) = d.source (p,Y))
    (Y : Plane) :
    d.copySolve g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      d.copySolve g hab j (p,Y) := by
  unfold LinearData.copySolve
  rw [g.coordinates_deck, anchoredSolve_shift d g hab j K p hf]

end LinearSolve

section ParticularCopies

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem copyVelocity_shift (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, t.source (p, Y + TorusAverages.latticePoint K) = t.source (p,Y))
    (Y : Plane) :
    copyVelocity t g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      copyVelocity t g hab j (p,Y) := by
  unfold copyVelocity
  rw [copySolve_shift t.linearData g hab j K p hf]

theorem copyPressure_shift (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (j K : Frequency) (frequency : ℝ) (p : P)
    (hf : ∀ Y : Plane, t.source (p, Y + TorusAverages.latticePoint K) = t.source (p,Y))
    (Y : Plane) :
    copyPressure t g hab (j + coverIndex g.gap K) frequency (p, Y + TorusAverages.latticePoint K) =
      copyPressure t g hab j frequency (p,Y) := by
  simp only [copyPressure, copyPressureReal, nativePoint, g.coordinates_deck,
    copySolve_shift t.linearData g hab j K p hf Y, hf Y]

theorem complexCopyVelocity_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (j K : Frequency) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyVelocity t f g hab (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) =
      complexCopyVelocity t f g hab j (p,Y) := by
  have hr : ∀ Y : Plane, (realData t f).source (p, Y + TorusAverages.latticePoint K) =
      (realData t f).source (p,Y) := fun Y => congrArg realPart (hf Y)
  have hi : ∀ Y : Plane, (imagData t f).source (p, Y + TorusAverages.latticePoint K) =
      (imagData t f).source (p,Y) := fun Y => congrArg imagPart (hf Y)
  simp only [complexCopyVelocity, copyVelocity_shift _ g hab j K p hr Y,
    copyVelocity_shift _ g hab j K p hi Y]

theorem complexCopyPressure_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (j K : Frequency) (frequency : ℝ) (p : P)
    (hf : ∀ Y : Plane, f (p, Y + TorusAverages.latticePoint K) = f (p,Y)) (Y : Plane) :
    complexCopyPressure t f g hab (j + coverIndex g.gap K) frequency
        (p, Y + TorusAverages.latticePoint K) =
      complexCopyPressure t f g hab j frequency (p,Y) := by
  have hr : ∀ Y : Plane, (realData t f).source (p, Y + TorusAverages.latticePoint K) =
      (realData t f).source (p,Y) := fun Y => congrArg realPart (hf Y)
  have hi : ∀ Y : Plane, (imagData t f).source (p, Y + TorusAverages.latticePoint K) =
      (imagData t f).source (p,Y) := fun Y => congrArg imagPart (hf Y)
  simp only [complexCopyPressure, copyPressure_shift _ g hab j K frequency p hr Y,
    copyPressure_shift _ g hab j K frequency p hi Y]



end ParticularCopies

section PeriodizedCopies

variable {P H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Translation of the copy index is a bijection; there is no multiplicity
factor when passing from the individual solves to the common field. -/
theorem periodizedCopies_shift (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (K : Frequency) (p : P)
    (hF : ∀ j Y, F (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) = F j (p,Y))
    (Y : Plane) :
    periodizedCopies g κ F (p, Y + TorusAverages.latticePoint K) =
      periodizedCopies g κ F (p,Y) := by
  unfold periodizedCopies
  calc
    _ = ∑' j : Frequency,
        κ (g.coordinates (j + coverIndex g.gap K) (Y + TorusAverages.latticePoint K)) •
          F (j + coverIndex g.gap K) (p, Y + TorusAverages.latticePoint K) :=
      ((Equiv.addRight (coverIndex g.gap K)).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro j
      rw [g.coordinates_deck, hF j Y]

end PeriodizedCopies

section CommonFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]




end CommonFields

/-! ## The inherited sublattice, without a unit-lattice assertion -/


/-- The actual inverse-cover pullback of a source. -/
noncomputable def inverseCoverSource {P V : Type} (d : ℕ) (f : P × Plane → V) : P × Plane → V :=
  fun x => f (x.1, (coverPower d).symm x.2)




section SubcoverFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]







end SubcoverFields

end NavierStokes.SubcoverPeriodicity
