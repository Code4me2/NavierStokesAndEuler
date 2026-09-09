import NavierStokes.SignedCovariance
import NavierStokes.SignedStressPrimitive
import NavierStokes.PrimaryPulseBounds
import NavierStokes.ParticularWaveBounds
import NavierStokes.ErrorHarmonics
import NavierStokes.MeanMomentBounds
import NavierStokes.CopyAngularInvariance

/-!
# Constructed signed wave increments

The signed coefficient is the inverse of the same integrated primary matrix,
divided by twice the same positive primary amplitude.  Its sign is unrestricted.
The homogeneous pressure, exact curl, signed square, and slot-cutoff error are
retained as actual fields.
-/

noncomputable section

namespace NavierStokes.SignedWaveUpdate

open Set Function Filter MeasureTheory Matrix
open WeightedClasses HarmonicCalculus
open scoped ContDiff Topology BigOperators ComplexConjugate InnerProductSpace


abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2
abbrev Space := ProblemStatement.Space

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The requested stress is the negative primitive of the actual state -/





/-! ## Inverse jets and the signed quotient -/

theorem weights_smul (H : Mat2) (T : Vec2) (a : ℝ) (j : Fin 2) :
    SmoothCovariance.weights H (a • T) j = a * SmoothCovariance.weights H T j := by
  fin_cases j <;>
    simp [SmoothCovariance.weights, SmoothCovariance.cramerNumerator, smul_eq_mul] <;> ring

/-- Only primitive matrix/target jets and zeroth-order primary margins occur
in this record. There is no assumption on an inverse or a signed output. -/
structure CovarianceControl (s : StripData D) (H : ℕ → D → Mat2)
    (T : ℕ → D → Vec2) where
  matrix_jets : ∀ i j, PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s)
    (fun n x => H n x i j)
  target_jets : ∀ i, MeanClass s 0 (fun n x => T n x i)
  zeta_pos : ∀ x ∈ s.domain, 0 < s.zeta x
  b : ℝ
  M : ℝ
  c : ℝ
  b_pos : 0 < b
  M_one : 1 ≤ M
  c_pos : 0 < c
  determinant : ∀ n x, x ∈ s.domain →
    b ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H n x)).det|
  entries : ∀ n x, x ∈ s.domain → ∀ i j,
    |Real.sqrt (s.slow n) * H n x i j| ≤ M
  lower : ∀ n x, x ∈ s.domain → ∀ j,
    c * s.zeta x ≤ SmoothCovariance.weights (H n x) (T n x) j

namespace CovarianceControl

variable {s : StripData D} {H : ℕ → D → Mat2} {T : ℕ → D → Vec2}

theorem cone (h : CovarianceControl s H T) (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    SmoothCovariance.StrictCone (H n x) (T n x) :=
  (SmoothCovariance.weights_pos_iff _ _).mp
    (fun j => (mul_pos h.c_pos (h.zeta_pos x hx)).trans_le (h.lower n x hx j))

/-- Cramer's actual formula preserves every band exponent, including signed
targets. Its denominator estimates are taken from the same primary matrix. -/
theorem inverse_class (h : CovarianceControl s H T) {R : ℕ → D → Vec2} {β : ℝ}
    (hR : ∀ i, MeanClass s β (fun n x => R n x i)) (j : Fin 2) :
    MeanClass s β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j) := by
  have hR0 (i : Fin 2) : MeanClass s 0 (fun n x => s.epsilon n ^ (-β) * R n x i) := by
    simpa only [smul_eq_mul, add_neg_cancel] using (hR i).band_smul (bandBound_rpow s (-β))
  have h0 := PrimaryPulseBounds.covariance_weights_class
    (PrimaryPulseBounds.sqrt_slow_polynomial s)
    (fun n => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (s.one_le_slow n))).ne')
    h.matrix_jets hR0 h.b_pos h.M_one h.determinant h.entries j
  have hβ := h0.band_smul (bandBound_rpow s β)
  apply LinearWaveBounds.class_congr (by simpa only [zero_add] using hβ)
  intro n x hx
  dsimp only
  rw [SmoothCovariance.inverse_formula _ _ (h.cone n hx).det_ne_zero]
  change s.epsilon n ^ β * SmoothCovariance.weights (H n x)
    (s.epsilon n ^ (-β) • R n x) j = _
  rw [weights_smul, ← mul_assoc, ← Real.rpow_add (s.epsilon_pos n),
    add_neg_cancel, Real.rpow_zero, one_mul]

theorem inverse_control (h : CovarianceControl s H T) (j : Fin 2) :
    SignedCovariance.InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j) := by
  apply SignedCovariance.inverseControl_of_lower
    (fun n x hx => (PartitionedCovariance.amplitudes_are_inverse_weights (h.cone n hx) j).1)
    h.c_pos 0
  intro n x hx
  simpa only [pow_zero, div_one, SmoothCovariance.inverse_formula _ _ (h.cone n hx).det_ne_zero]
    using h.lower n x hx j

theorem increment_class (h : CovarianceControl s H T) {R : ℕ → D → Vec2} {β : ℝ}
    (hR : ∀ i, MeanClass s β (fun n x => R n x i)) (j : Fin 2) :
    WaveClass s (fun _ _ => 1) β
      (fun n x => SignedCovariance.increment (H n x) (T n x) (R n x) j) :=
  SignedCovariance.increment_wave_class j h.zeta_pos (fun n _ hx => h.cone n hx)
    (h.inverse_class h.target_jets j) (h.inverse_class hR j) (h.inverse_control j)

end CovarianceControl

noncomputable def signedScalar (s : StripData D) (H : ℕ → D → Mat2)
    (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ) (j : Fin 2) : ℕ → D → ℝ :=
  fun n x => Real.sqrt (s.epsilon n) * SignedCovariance.increment (H n x) (T n x) (R n x) j * mask n x

noncomputable def signedVector (s : StripData D) (H : ℕ → D → Mat2)
    (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ) (v : ℕ → D → Space) (j : Fin 2) :
    ℕ → D → Space := fun n x => signedScalar s H T R mask j n x • v n x

theorem signedScalar_class {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    {mask : ℕ → D → ℝ} {β : ℝ} (h : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (j : Fin 2) :
    WaveClass s (fun _ _ => 1) (β + 1 / 2) (signedScalar s H T R mask j) := by
  have hi := h.increment_class hR j
  have hh := (LinearWaveBounds.unweighted_smul hm (show MemClass s (fun _ x => Real.sqrt (s.zeta x)) β
    (fun n x => SignedCovariance.increment (H n x) (T n x) (R n x) j) from by
      simpa only [WaveClass, mul_one] using hi))
  have hh' := hh.band_smul (bandBound_rpow s (1 / 2))
  apply LinearWaveBounds.class_congr (by simpa only [WaveClass, mul_one, zero_add] using hh')
  intro n x _
  simp only [signedScalar, smul_eq_mul, ← Real.sqrt_eq_rpow]
  ring

theorem signedVector_class {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    {mask : ℕ → D → ℝ} {v : ℕ → D → Space} {P : ℕ → D → ℝ} {β : ℝ}
    (h : CovarianceControl s H T) (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v) (j : Fin 2) :
    WaveClass s P (β + 1 / 2) (signedVector s H T R mask v j) := by
  have hs := signedScalar_class h hR hm j
  have h := hs.smul hv
  simp only [mul_one, add_zero] at h
  exact h

/-! ## The same homogeneous fundamental and its constructed pressure -/

noncomputable def homogeneousCoefficients (a : LinearWaveBounds.WaveCoefficients D)
    (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space) :
    LinearWaveBounds.WaveCoefficients D :=
  { a with
    amplitude := fun n x => CurlClassBounds.complexify (v n x)
    pressure := fun n => ParticularWaveBounds.projectedPressure (a.frequency n)
      (a.normal s d n) (Ndot n) (v n) (fun x => A n x (v n x)) (fun _ => 0) }

noncomputable def coefficients (a : LinearWaveBounds.WaveCoefficients D)
    (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space) (j : Fin 2) :
    LinearWaveBounds.WaveCoefficients D :=
  homogeneousCoefficients a s d (signedVector s H T R mask v j) Ndot A

/-- Every signed amplitude and pressure bound is obtained from the actual
inverse quotient and the primitive homogeneous fundamental. The input wave
bound supplies only the already fixed background geometry. -/
theorem coefficients_inputBounds
    {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
    {a : LinearWaveBounds.WaveCoefficients D} {P₀ P : ℕ → D → ℝ} {α₀ β κ : ℝ}
    (hbase : LinearWaveBounds.InputBounds s P₀ α₀ κ d a)
    {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2} {mask : ℕ → D → ℝ}
    {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
    (hcov : CovarianceControl s H T)
    (hR : ∀ i, MeanClass s β (fun n x => R n x i))
    (hm : UnweightedClass s 0 mask) (hv : MemClass s P 0 v)
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s d))
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s d n x‖)
    (hhi : ∀ n x, x ∈ s.domain → ‖a.normal s d n x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / a.frequency n)) (j : Fin 2) :
    LinearWaveBounds.InputBounds s P (β + 1 / 2) κ d
      (coefficients a s d H T R mask v Ndot A j) := by
  have hs := signedVector_class hcov hR hm hv j
  have ha := hs.map CurlClassBounds.complexify
  have hp := ParticularWaveBounds.pressure_class hN hNdot hA hs
    (MemClass.zero hs.weight_nonneg) hb hlo hhi hK
  exact { hbase with
    amplitude := fun i => CurlClassBounds.class_component ha i
    pressure := hp }

/-- Equality along an actual straight fast orbit, imposed on the primitive
slow data, not on the signed solve or its derivatives. -/
def FrozenAlong (v : D) (f : ℕ → D → E) : Prop :=
  ∀ n x (t : ℝ), f n (x + t • v) = f n x

theorem FrozenAlong.derivative {v : D} {f : ℕ → D → E}
    (hf : FrozenAlong v f) (n : ℕ) {x : D} (hd : DifferentiableAt ℝ (f n) x) :
    fderiv ℝ (f n) x v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hh : HasDerivAt (fun t : ℝ => f n (x + t • v)) (fderiv ℝ (f n) x v) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hl
    simpa only [zero_smul, add_zero] using hd.hasFDerivAt
  have he : (fun t : ℝ => f n (x + t • v)) = fun _ => f n x := funext (hf n x)
  rw [he] at hh
  exact hh.unique (hasDerivAt_const (0 : ℝ) (f n x))

theorem signedScalar_frozen {s : StripData D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
    {mask : ℕ → D → ℝ} {v : D}
    (hH : FrozenAlong v H) (hT : FrozenAlong v T) (hR : FrozenAlong v R)
    (hm : FrozenAlong v mask) (j : Fin 2) :
    FrozenAlong v (signedScalar s H T R mask j) := by
  intro n x t
  simp only [signedScalar, hH n x t, hT n x t, hR n x t, hm n x t]

theorem along_smul (V : D → D) {f : D → ℝ} {g : D → E} {x : D}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    along V (fun y => f y • g y) x = along V f x • g x + f x • along V g x := by
  simp only [along, fderiv_fun_smul hf hg, _root_.add_apply,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
  exact add_comm _ _

theorem projectedRhs_smul (N Ndot v Av : Space) (δ c : ℝ) :
    TangentProjection.projectedRhs N Ndot (c • v) (c • Av) 0 δ =
      c • TangentProjection.projectedRhs N Ndot v Av 0 δ := by
  ext i
  simp [TangentProjection.projectedRhs, TangentProjection.tangentProj,
    inner_smul_right, PiLp.smul_apply]
  ring

theorem shear_smul (R F G : D → ℝ) (Vr : D → D) (v : D → ComplexVector)
    (c : D → ℝ) (x : D) :
    LinearWaveResidual.shear R F G Vr (fun y => c y • v y) x =
      c x • LinearWaveResidual.shear R F G Vr v x := by
  ext i
  fin_cases i <;> simp [LinearWaveResidual.shear, Complex.real_smul] <;> ring


/-! ## Instantiation with the constructed primary phase and pulse -/

noncomputable def phaseMatrix {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) : ℕ → D → Mat2 :=
  PrimaryPulseBounds.chartCovariance pref (fun j => (F j).frame)
    (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L) χ

noncomputable def phaseFundamental {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ℕ → D → Space :=
  fun n x => PrimaryPulseBounds.normalizedPulse ((F j).frame n)
    ((F j).lam n) ((F j).u n) ((F j).L n) (χ n x)

noncomputable def phaseEnvelope {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ℕ → D → ℝ :=
  fun n x => PrimaryPulseBounds.referenceP ((F j).lam n) ((F j).u n)
    ((F j).L n) ((F j).L n * (χ n x).2)

theorem phaseFundamental_class {s : StripData D}
    {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PrimaryPulseBounds.PhaseConstruction U)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ n, U.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (PrimaryPulseBounds.phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → χ n x ∈ U.carrier n ×ˢ Ioo (0 : ℝ) 1)
    (j : Fin 2) : MemClass s (phaseEnvelope F χ j) 0 (phaseFundamental F χ j) := by
  have hp := (F j).pulse_jets.comp hχ hscale hmap
  exact hp.memClass s (fun _ => rfl) (fun _ => rfl)




/-! ## Literal harmonic blocks, with the same carrier metadata -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem conjugatePair_apply (a : D → ℂ) (j : ℤ) (x : D) :
    ErrorHarmonics.conjugatePair 1 a j x =
      (if j = 1 then a x / 2 else 0) + conj (if -j = 1 then a x / 2 else 0) := by
  classical
  change Finsupp.single (1 : ℤ) (fun x => a x / 2) j x +
    conj (Finsupp.single (1 : ℤ) (fun x => a x / 2) (-j) x) = _
  by_cases hj : j = 1 <;> by_cases hjn : -j = 1 <;>
    simp [hj, hjn, eq_comm]

noncomputable def coefficientBlock (frequency : ℕ → ℝ) (phase : ℕ → D → ℝ)
    (angularFrequency : ℕ → ℤ) (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    CorrectionState.HarmonicBlock D where
  velocity n i := ErrorHarmonics.conjugatePair 1 (fun x => v n x i)
  pressure n := ErrorHarmonics.conjugatePair 1 (p n)
  frequency := frequency
  phase := phase
  angularFrequency := angularFrequency

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_band (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (coefficientBlock k Φ kp v p).BandLimited 1 :=
  ⟨fun n i => ErrorHarmonics.band_conjugatePair 1 (fun x => v n x i),
    fun n => ErrorHarmonics.band_conjugatePair 1 (p n)⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_symmetric (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (∀ n i, HarmonicFields.ConjugateSymmetric ((coefficientBlock k Φ kp v p).velocity n i)) ∧
    ∀ n, HarmonicFields.ConjugateSymmetric ((coefficientBlock k Φ kp v p).pressure n) :=
  ⟨fun n i => ErrorHarmonics.conjugatePair_symmetric 1 (fun x => v n x i),
    fun n => ErrorHarmonics.conjugatePair_symmetric 1 (p n)⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_zero_coefficient (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) :
    (∀ n i, (coefficientBlock k Φ kp v p).velocity n i 0 = 0) ∧
    ∀ n, (coefficientBlock k Φ kp v p).pressure n 0 = 0 := by
  constructor
  · intro n i
    ext x
    simp only [coefficientBlock, conjugatePair_apply]
    norm_num
  · intro n
    ext x
    simp only [coefficientBlock, conjugatePair_apply]
    norm_num

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_velocity (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (coefficientBlock k Φ kp v p).oscillation n x i =
      (v n x.1 i * HarmonicFields.character 1 (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  exact ErrorHarmonics.pairedBlock_evaluation 1 k Φ kp v n x i

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficientBlock_pressure (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (v : ℕ → D → ComplexVector) (p : ℕ → D → ℂ) (n : ℕ) (x : D × ℝ) :
    (coefficientBlock k Φ kp v p).oscillatoryPressure n x =
      (p n x.1 * HarmonicFields.character 1 (k n * Φ n x.1 + (kp n : ℝ) * x.2)).re := by
  have h := congrArg Complex.re (ErrorHarmonics.field_conjugatePair 1 (p n) (k n) (Φ n) (kp n) x)
  simp only [Complex.ofReal_re] at h
  exact h

theorem conjugatePair_class {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {a : ℕ → D → ℂ} (ha : MemClass s w α a) (j : ℤ) :
    MemClass s w α (fun n x => ErrorHarmonics.conjugatePair 1 (a n) j x) := by
  have hp := LinearWaveBounds.constant_complex_mul ha (1 / 2)
  have hn := hp.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  by_cases hj : j = 1
  · subst j
    simpa [conjugatePair_apply, div_eq_mul_inv,
      mul_comm] using hp
  by_cases hjn : -j = 1
  · simpa [conjugatePair_apply, hj, hjn, div_eq_mul_inv, mul_comm] using hn
  · simpa [conjugatePair_apply, hj, hjn] using
      (MemClass.zero (E := ℂ) (α := α) ha.weight_nonneg)

theorem coefficientBlock_classes {s : StripData D} {P : ℕ → D → ℝ} {α γ : ℝ}
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    {v : ℕ → D → ComplexVector} {p : ℕ → D → ℂ}
    (hv : WaveClass s P α v) (hp : WaveClass s P γ p) :
    (coefficientBlock k Φ kp v p).WaveBounds s P α ∧
    (coefficientBlock k Φ kp v p).PressureBounds s P γ := by
  exact ⟨fun i j _ => conjugatePair_class (CurlClassBounds.class_component hv i) j,
    fun j _ => conjugatePair_class hp j⟩

/-- The full cylindrical construction is evaluated at angle zero to obtain
the coefficient algebra. Its physical angle is reintroduced by the unchanged
integer carrier, as proved in `blockOfCoefficients_represents`. -/
noncomputable def blockOfCoefficients (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (kp : ℕ → ℤ) : CorrectionState.HarmonicBlock D :=
  coefficientBlock a.frequency (fun n x => a.phase n (x,0)) kp
    (fun n x => a.amplitude n (x,0)) (fun n x => a.pressure n (x,0))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem blockOfCoefficients_represents
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ℕ → ℤ)
    (ha : ErrorHarmonics.AngleIndependent a.amplitude)
    (hp : ErrorHarmonics.AngleIndependent a.pressure)
    (hphase : ∀ n x θ, a.frequency n * a.phase n (x,θ) =
      a.frequency n * a.phase n (x,0) + (kp n : ℝ) * θ) :
    (blockOfCoefficients a kp).oscillation =
      (fun n x i => (vectorMode (a.frequency n) (a.phase n) (a.amplitude n) x i).re) ∧
    (blockOfCoefficients a kp).oscillatoryPressure =
      (fun n x => (mode (a.frequency n) (a.phase n) (a.pressure n) x).re) := by
  constructor
  · funext n x i
    rw [blockOfCoefficients, coefficientBlock_velocity]
    have hc := HarmonicFields.character_eq_carrier 1 (a.frequency n) (a.phase n) x
    simp only [Int.cast_one, mul_one] at hc
    rw [← hphase, hc]
    simp only [vectorMode, mode, ha n x.1 x.2]
  · funext n x
    rw [blockOfCoefficients, coefficientBlock_pressure]
    have hc := HarmonicFields.character_eq_carrier 1 (a.frequency n) (a.phase n) x
    simp only [Int.cast_one, mul_one] at hc
    rw [← hphase, hc]
    simp only [mode, hp n x.1 x.2]

/-! ## The bar operation preserves the actual flat mean class -/



theorem sigma_liftedTorusAverage (p : SignedStressPrimitive.Patch) (e : ℕ)
    (f : PressureStream.Lift E → ℝ) (x : PressureStream.Lift E) :
    SignedStressPrimitive.sigma p e (MeanMomentBounds.liftedTorusAverage f) x =
      SignedStressPrimitive.barSigma p e f (x.1, x.2.1) := by
  rcases x with ⟨r,z,Y⟩
  simp only [SignedStressPrimitive.sigma, SignedStressPrimitive.barSigma,
    SignedStressPrimitive.primitive, TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral, TransportPrimitive.totalIntegral,
    SignedStressPrimitive.weightedSource, MeanMomentBounds.liftedTorusAverage,
    TransportPrimitive.shift, zero_mul, zero_smul, Prod.mk_add_mk, add_zero]





/-! ## Angular independence is proved before taking a zero-angle section -/

structure AngularInputs (s : StripData D) (d : LinearWaveBounds.GraphDirections D)
    (a : LinearWaveBounds.WaveCoefficients D) (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2)
    (mask : ℕ → D → ℝ) (v Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (ψ : ℕ → D → ℝ) (m : ℕ → ℝ) : Prop where
  radius : FrozenAlong d.angular a.radius
  radial_base : FrozenAlong d.angular a.radialBase
  frequency_base : FrozenAlong d.angular a.frequencyBase
  axial_base : FrozenAlong d.angular a.axialBase
  radial_profile : CopyAngularInvariance.Invariant d.angular d.radialProfile
  phase : ∀ n, CopyAngularInvariance.AffinePhase d.angular (m n) (a.phase n)
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain
  matrix : FrozenAlong d.angular H
  primary_target : FrozenAlong d.angular T
  signed_target : FrozenAlong d.angular R
  mask : FrozenAlong d.angular mask
  fundamental : FrozenAlong d.angular v
  normal_motion : FrozenAlong d.angular Ndot
  action : FrozenAlong d.angular A
  cutoff : FrozenAlong d.angular ψ

namespace AngularInputs

variable {s : StripData D} {d : LinearWaveBounds.GraphDirections D}
  {a : LinearWaveBounds.WaveCoefficients D} {H : ℕ → D → Mat2} {T R : ℕ → D → Vec2}
  {mask : ℕ → D → ℝ} {v Ndot : ℕ → D → Space} {A : ℕ → D → Space →L[ℝ] Space}
  {ψ : ℕ → D → ℝ} {m : ℕ → ℝ}

theorem radialField (h : AngularInputs s d a H T R mask v Ndot A ψ m) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (d.radialField n) := by
  intro x t
  simp only [LinearWaveBounds.GraphDirections.radialField, h.radial_profile x t]

theorem normal (h : AngularInputs s d a H T R mask v Ndot A ψ m) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.normal s d n) :=
  CopyAngularInvariance.phaseNormal_invariant (h.radius n) (h.radialField n)
    (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _) (h.phase n)

theorem amplitude (h : AngularInputs s d a H T R mask v Ndot A ψ m) (j : Fin 2) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular ((coefficients a s d H T R mask v Ndot A j).amplitude n) := by
  intro x t
  simp only [coefficients, homogeneousCoefficients, signedVector, signedScalar,
    h.matrix n x t, h.primary_target n x t, h.signed_target n x t,
    h.mask n x t, h.fundamental n x t]

theorem pressure (h : AngularInputs s d a H T R mask v Ndot A ψ m) (j : Fin 2) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular ((coefficients a s d H T R mask v Ndot A j).pressure n) := by
  intro x t
  simp only [coefficients, homogeneousCoefficients, ParticularWaveBounds.projectedPressure,
    signedVector, signedScalar, h.matrix n x t, h.primary_target n x t,
    h.signed_target n x t, h.mask n x t, h.fundamental n x t, h.action n x t,
    h.normal_motion n x t, h.normal n x t]




end AngularInputs


/-! ## Restriction of actual coefficient jets to the angular section -/

noncomputable def zeroSection : D →L[ℝ] (D × ℝ) := (ContinuousLinearMap.id ℝ D).prod 0

theorem zeroSection_norm_le : ‖zeroSection (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [zeroSection, Prod.norm_def]

noncomputable def sectionStrip (s : StripData (D × ℝ)) : StripData D where
  domain := (zeroSection (D := D)) ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage (zeroSection (D := D)).continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (zeroSection x)
  delta_pos := fun _ hx => s.delta_pos _ hx
  zeta := fun x => s.zeta (zeroSection x)
  zeta_smooth := s.zeta_smooth.comp (zeroSection (D := D)).contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg := fun _ hx => s.zeta_nonneg _ hx

theorem class_zeroSection {s : StripData (D × ℝ)} {w : ℕ → D × ℝ → ℝ} {α : ℝ}
    {f : ℕ → D × ℝ → E} (hf : MemClass s w α f) :
    MemClass (sectionStrip s) (fun n x => w n (x,0)) α (fun n x => f n (x,0)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n _ hx,
    fun n => (hf.smooth n).comp (zeroSection (D := D)).contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hc := PhaseJetBounds.norm_jet_comp_linear s.isOpen_domain (hf.smooth n)
    (zeroSection (D := D)) hx j
  have hpow : ‖zeroSection (D := D)‖ ^ j ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) zeroSection_norm_le
  have hh := hc.trans (mul_le_of_le_one_right (norm_nonneg _) hpow)
  exact hh.trans (hb n (x,0) hx j hj)

theorem blockOfCoefficients_classes
    {s : StripData (D × ℝ)} {P : ℕ → D × ℝ → ℝ} {α γ : ℝ}
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) (kp : ℕ → ℤ)
    (ha : WaveClass s P α a.amplitude) (hp : WaveClass s P γ a.pressure) :
    (blockOfCoefficients a kp).WaveBounds (sectionStrip s) (fun n x => P n (x,0)) α ∧
    (blockOfCoefficients a kp).PressureBounds (sectionStrip s) (fun n x => P n (x,0)) γ :=
  coefficientBlock_classes a.frequency (fun n x => a.phase n (x,0)) kp
    (class_zeroSection ha) (class_zeroSection hp)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularAverage_re_field (c : HarmonicFields.Coefficients D) (k : ℝ)
    (Φ : D → ℝ) (kp : ℤ) (x : D) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, (HarmonicFields.field c k Φ kp (x,θ)).re) / (2 * Real.pi) =
      (HarmonicFields.angularMean (fun θ => HarmonicFields.field c k Φ kp (x,θ))).re := by
  have hi := Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
    ((HarmonicFields.field_angular_continuous c k Φ kp x).intervalIntegrable (0 : ℝ) (2 * Real.pi))
  change (∫ θ in (0 : ℝ)..2 * Real.pi, (HarmonicFields.field c k Φ kp (x,θ)).re) =
    (∫ θ in (0 : ℝ)..2 * Real.pi, HarmonicFields.field c k Φ kp (x,θ)).re at hi
  rw [hi]
  simp [HarmonicFields.angularMean, HarmonicFields.period, Complex.mul_re, div_eq_mul_inv,
    ← Complex.ofReal_inv, mul_comm]


/-! ## Actual homogeneous ODE under the native clock -/




/-! ## The constructed curl, pressure, and retained linear error -/



theorem normalDot_complexify (N v : Space) :
    normalDot N (CurlClassBounds.complexify v) = (⟪N,v⟫_ℝ : ℂ) := by
  simp [normalDot, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]




/-! ## The same native pulse blocks in the exact covariance identity -/

section NativeBlocks

open PartitionedCovariance

noncomputable def nativeUnit {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) (Y : TorusInverse.Plane) : Space :=
  !₂[covered (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) Y,
    covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j 0) Y,
    covered (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j 1) Y]

noncomputable def nativeTangentBlock {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {U : UnsignedLabel} (P : PairData sys U)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (a : Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) :
    CorrectionState.HarmonicBlock TorusInverse.Plane :=
  coefficientBlock (fun _ => 1) (fun _ => P.phases j) (fun _ => P.modes j)
    (fun _ Y => CurlClassBounds.complexify
      ((outer * (Real.sqrt ε * a j * mask D U q x)) • nativeUnit P hdet j Y)) 0




noncomputable def nativeAssembly {D h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) :
    TorusInverse.Plane → ℝ → Fin 3 → ℝ := fun Y θ i =>
  ∑ᶠ v : UnsignedLabel × Fin 2,
    (nativeTangentBlock (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2).oscillation 0 (Y,θ) i





end NativeBlocks


/-! ## Canonical pulse binding for the matrix and the native blocks -/




/-! ## Exported blocks for the correction state -/






/-! The realization hypothesis below concerns only the already constructed
unit pulse and chart. It never identifies or bounds a signed output. The
canonical unit pulse and its matrix are identified by the two preceding
canonical-pulse theorems. -/


end NavierStokes.SignedWaveUpdate
