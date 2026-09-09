import NavierStokes.ParticularWaveBounds
import NavierStokes.NormalScaling

/-!
# Normal and clock transport of the actual tangent inverse

The native clock, its zero-entry anchor, the normal and the source are
transported together.  Velocity and pressure below are outputs of the
actual copy-path Volterra inverse, with no output compatibility hypothesis.
-/

noncomputable section

namespace NavierStokes.ScaledTangentTransport

open Set Function CommonCoverSolve TorusInverse ParticularWaveBounds HarmonicCalculus
open scoped Topology ContDiff InnerProductSpace


section Geometry

theorem coordinates_transport (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) (copy : Frequency) (Y : Plane) :
    CopySolveCompatibility.nativeTimeMap shift rate
      ((CopySolveCompatibility.transportGeometry g gap shift rate hrate).coordinates copy Y) =
        g.coordinates copy (coverPower gap Y) := by
  rw [CopySolveCompatibility.transportGeometry, CopySolveCompatibility.coordinates_refine, CopySolveCompatibility.coordinates_timeGeometry]


theorem slotDirection_transport (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : rate ≠ 0) :
    coverPower gap (slotDirection (CopySolveCompatibility.transportGeometry g gap shift rate hrate)) =
      rate • slotDirection g := by
  apply (coverPower g.gap).injective
  change coverPower g.gap
      (coverPower gap ((coverPower (g.gap + gap)).symm
        ((CommonCoverClass.scaledBasis g.basis rate hrate) (0, 1)))) = _
  rw [← CopySolveCompatibility.coverPower_add, ContinuousLinearEquiv.apply_symm_apply,
    CommonCoverClass.scaledBasis_transverse]
  simp only [slotDirection, map_smul, ContinuousLinearEquiv.apply_symm_apply]

theorem current_slot_iff (g : Geometry) (gap : ℕ) (shift rate : ℝ)
    (hrate : 0 < rate) (copy : Frequency) (Y : Plane) (a b : ℝ) :
    ((CopySolveCompatibility.transportGeometry g gap shift rate hrate.ne').coordinates copy Y).2 ∈ Icc a b ↔
      (g.coordinates copy (coverPower gap Y)).2 ∈
        Icc (shift + rate * a) (shift + rate * b) := by
  have he := congrArg Prod.snd (coordinates_transport g gap shift rate hrate.ne' copy Y)
  change shift + rate * _ = _ at he
  rw [← he]
  constructor
  · intro h
    exact ⟨CopySolveCompatibility.time_interval_mono shift hrate h.1,
      CopySolveCompatibility.time_interval_mono shift hrate h.2⟩
  · intro h
    constructor <;> nlinarith [h.1, h.2]


end Geometry

section Inputs

variable {P Q H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The velocity scale is `amplitude`.  The actual source scale is
`rate * amplitude`, and the moving normal acquires both normal and clock
scales in its slot derivative. -/
noncomputable def transportTangent (t : TangentData P H) (parameter : Q → P)
    (gap : ℕ) (shift rate amplitude normalScale : ℝ) : TangentData Q H where
  normal z := normalScale • t.normal (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  normalDot z := (normalScale * rate) •
    t.normalDot (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  action z := rate • t.action (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  damping z := rate * t.damping (parameter z.1, CopySolveCompatibility.nativeTimeMap shift rate z.2)
  source z := (rate * amplitude) • t.source (parameter z.1, coverPower gap z.2)

/-- The ambient complex source undergoes the same rate and velocity
scalings as the real tangent source. -/
noncomputable def transportSource (f : P × Plane → ComplexVector) (parameter : Q → P)
    (gap : ℕ) (rate amplitude : ℝ) : Q × Plane → ComplexVector :=
  fun z => (rate * amplitude) • f (parameter z.1, coverPower gap z.2)


end Inputs

section CopyInputCompatibility

variable {P Q V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]


end CopyInputCompatibility

section TangentTransport

variable {P Q H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace H] in
/-- Normal scaling changes neither tangent projection nor the resulting
ODE.  Moving the clock factor from the forcing map into the source
preserves its actual converted forcing. -/
theorem transportTangent_sameInputs (t : TangentData P H) (parameter : Q → P)
    (gap : ℕ) (shift rate amplitude normalScale : ℝ) (hnormal : normalScale ≠ 0) (q : Q) :
    CopySolveCompatibility.SameInputsAt
      (transportTangent t parameter gap shift rate amplitude normalScale).linearData
      (CopySolveCompatibility.transportData t.linearData parameter gap shift rate amplitude) q := by
  constructor
  · intro z
    exact NormalScaling.projectedOperator_rescale _ _ _ rate _ hnormal
  · intro z Y
    change negativeTangentProjection (normalScale • t.normal
        (parameter q, CopySolveCompatibility.nativeTimeMap shift rate z))
        ((rate * amplitude) • t.source (parameter q, coverPower gap Y)) =
      (rate • negativeTangentProjection (t.normal
        (parameter q, CopySolveCompatibility.nativeTimeMap shift rate z)))
        (amplitude • t.source (parameter q, coverPower gap Y))
    rw [NormalScaling.negativeTangentProjection_smul _ hnormal]
    simp only [_root_.smul_apply, map_smul, smul_smul, mul_comm rate amplitude]





end TangentTransport

section LocalizedTransport

variable {P Q E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



end LocalizedTransport

section ComplexTransport

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem realData_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) :
    realData (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude) =
        transportTangent (realData t f) parameter gap shift rate amplitude normalScale := by
  unfold realData transportTangent transportSource
  congr 1
  funext z
  exact map_smul realPart (rate * amplitude) _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem imagData_transport (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (parameter : Q → P) (gap : ℕ)
    (shift rate amplitude normalScale : ℝ) :
    imagData (transportTangent t parameter gap shift rate amplitude normalScale)
      (transportSource f parameter gap rate amplitude) =
        transportTangent (imagData t f) parameter gap shift rate amplitude normalScale := by
  unfold imagData transportTangent transportSource
  congr 1
  funext z
  exact map_smul imagPart (rate * amplitude) _






end ComplexTransport

section ZeroEntry

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem interval_congr {E : Type} (F : (a b : ℝ) → a ≤ b → E)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    F a b hab = F c d hcd := by
  subst_vars
  rfl



end ZeroEntry

end NavierStokes.ScaledTangentTransport
