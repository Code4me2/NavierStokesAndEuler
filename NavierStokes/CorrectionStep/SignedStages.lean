import NavierStokes.CorrectionStep.Fields

/-!
# Exact field bookkeeping for one correction cycle: signed stages

Second part of `NavierStokes.CorrectionStep`.  It covers the physical residual
decomposition, the wave/mean residual of a single stage, the signed stage
parameters and their linear coefficient bridge, the gauge rank mean, and the
moving-support, moving-mean-pressure, periodized and particular constructions.
-/

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds
open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-! The zero mean triple, its neutrality for `updated`, and the effect of a
pressure change on the axial residual are declared in
`NavierStokes.SignedMeanGain`; they are re-exported here. -/
export SignedMeanGain (zeroTriple updated_zeroTriple axialResidual_pressure_change)

section SourceCoefficientCompatibility

open CorrectionState HarmonicFields MeasureTheory



end SourceCoefficientCompatibility

section WaveMeanResidual

open CorrectionState VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Insert the actual oscillation and its actual excluded error, then
reconstruct pressure from the resulting literal covariance. -/
noncomputable def gaugeWaveStage (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S)) :
    State (PressureStream.Lift S) :=
  reconstructState g c (u.addIncrement zeroTriple 0 w q e)

noncomputable def gaugeWavePressureChange (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) := (gaugeWaveStage g c u w q e).pressure - u.pressure

theorem gaugeWaveStage_mean (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S)) :
    (gaugeWaveStage g c u w q e).mean = u.mean := updated_zeroTriple u.mean

theorem gaugeWaveStage_cumulative {s : StripData (PressureStream.Lift S)} {α : ℝ}
    (g : GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : ExcludedErrors (PressureStream.Lift S))
    (hm : CorrectionState.CumulativeBounds s u)
    (hδp : MeanClass s α (gaugeWavePressureChange g c u w q e)) (hα : 9 / 10 ≤ α) :
    CorrectionState.CumulativeBounds s (gaugeWaveStage g c u w q e) := by
  constructor
  · rw [gaugeWaveStage_mean]
    exact hm.velocity
  · have he : (gaugeWaveStage g c u w q e).pressure =
        u.pressure + gaugeWavePressureChange g c u w q e := by unfold gaugeWavePressureChange; abel
    rw [he]
    exact hm.pressure.add (hδp.mono_exponent hα)

end WaveMeanResidual

section SignedParameters

open CorrectionState

/-- Fixed primitive data of one primary signed slot. No output field,
output estimate, or state transition is stored in this record. -/
structure SignedParameters (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  base : LinearWaveBounds.WaveCoefficients (D × ℝ)
  directions : LinearWaveBounds.GraphDirections (D × ℝ)
  matrix : ℕ → D × ℝ → SignedWaveUpdate.Mat2
  target : ℕ → D × ℝ → SignedWaveUpdate.Vec2
  mask : ℕ → D × ℝ → ℝ
  fundamental : ℕ → D × ℝ → ProblemStatement.Space
  normalMotion : ℕ → D × ℝ → ProblemStatement.Space
  action : ℕ → D × ℝ → ProblemStatement.Space →L[ℝ] ProblemStatement.Space
  cutoff : ℕ → D × ℝ → ℝ
  angularFrequency : ℕ → ℤ
  column : Fin 2

noncomputable def SignedParameters.coefficients (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
  SignedWaveUpdate.coefficients p.base (HarmonicWaveInteraction.productStrip s) p.directions
    p.matrix p.target request p.mask p.fundamental p.normalMotion p.action p.column





theorem sectionStrip_productStrip (s : StripData D) :
    SignedWaveUpdate.sectionStrip (HarmonicWaveInteraction.productStrip s) = s := by
  cases s
  rfl







structure SignedParameters.Control (p : SignedParameters D) (s : StripData D)
    (P₀ : ℕ → D × ℝ → ℝ) (P : ℕ → D → ℝ) (α₀ κ : ℝ) where
  baseBounds : LinearWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s) P₀ α₀ κ
    p.directions p.base
  kappa_le_half : κ ≤ 1 / 2
  covariance : SignedWaveUpdate.CovarianceControl (HarmonicWaveInteraction.productStrip s) p.matrix p.target
  mask : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.mask
  fundamental : MemClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) 0 p.fundamental
  normal : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain (HarmonicWaveInteraction.productStrip s))
    (p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions)
  normalMotion : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.normalMotion
  action : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.action
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  norm_lower : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    lower ≤ ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖
  norm_upper : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ≤ upper
  inverseFrequency : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
    (fun n => 1 / p.base.frequency n)
  radius : D × ℝ → ℝ
  radius_eq : p.base.radius = fun _ => radius
  cutoff : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 p.cutoff


end SignedParameters

section LinearCoefficientBridge

open CorrectionState

/-- The actual real linearized cylindrical residual of a block, evaluated
with the carrier of the old spatial label. -/
noncomputable def linearBlockField (c : Context D) (a b : HarmonicBlock D) : Oscillation D :=
  fun n x i => (LinearWaveResidual.linearResidual (c.operators.epsilon n)
    (fun y : D × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
    (axialDirection c n) (timeDirection c n) (complexBase c n)
    (LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n))
    (fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ)) x i).re

theorem linearCoefficients_field {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b : HarmonicBlock D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) {x : D × ℝ}
    (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    (HarmonicFields.field (HarmonicWaveInteraction.linearCoefficients c a b n i)
      (a.frequency n) (a.phase n) (a.angularFrequency n) x).re = linearBlockField c a b n x i := by
  have he := HarmonicResidual.field_linearResidual hU (HarmonicResidual.contextFrame c n)
    hr hz (fun l => HarmonicResidual.smoothCoefficients_constant (hB l))
    (fun l => (hb l).realCoefficients) hp.realCoefficients hΦ
    (a.frequency n) (a.angularFrequency n) hx
  change HarmonicResidual.vectorField
    (HarmonicWaveInteraction.linearCoefficients c a b n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) x = _ at he
  have hbase : HarmonicResidual.vectorField
      (fun l => HarmonicFields.constantCoefficient (fun y => HarmonicResidual.contextBase c n y l))
      (a.frequency n) (a.phase n) (a.angularFrequency n) = complexBase c n := by
    funext y l
    exact HarmonicResidual.field_constant _ _ _ _ y
  have hamp : HarmonicResidual.vectorField
      (fun l => HarmonicResidual.realCoefficients (b.velocity n l))
      (a.frequency n) (a.phase n) (a.angularFrequency n) =
        LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n) := by
    funext y l
    exact HarmonicResidual.field_realCoefficients _ _ _ _ y
  have hpress : HarmonicFields.field (HarmonicResidual.realCoefficients (b.pressure n))
      (a.frequency n) (a.phase n) (a.angularFrequency n) =
        fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ) := by
    funext y
    exact HarmonicResidual.field_realCoefficients _ _ _ _ y
  rw [hbase, hamp, hpress] at he
  exact congrArg Complex.re (congrFun he i)

/-- An actual field cancellation determines every nonzero coefficient.
The Gaussian is subtracted only after its full field is retained in the
identity. The conclusion uses the literal `linearGoodBlock`. -/
theorem linearGoodBlock_cancel {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b source good : HarmonicBlock D)
    (g : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial U)
    (hz : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => HarmonicResidual.contextBase c n y i) U)
    (hb : ∀ i, HarmonicResidual.SmoothCoefficients U (b.velocity n i))
    (hp : HarmonicResidual.SmoothCoefficients U (b.pressure n))
    (hΦ : ContDiffOn ℝ ∞ (a.phase n) U) (hkp : a.angularFrequency n ≠ 0)
    (hs : ∀ i, HarmonicFields.ConjugateSymmetric (source.velocity n i))
    (hg : ∀ i, HarmonicFields.ConjugateSymmetric (good.velocity n i))
    {x : D} (hx : x ∈ U) (j : ℤ) (hj : j ≠ 0) (i : Fin 3)
    (hcancel : ∀ θ, linearBlockField c a b n (x, θ) i +
      (HarmonicWaveInteraction.withCarrier a source).oscillation n (x, θ) i =
      (HarmonicWaveInteraction.withCarrier a good).oscillation n (x, θ) i +
      (HarmonicFields.field (g n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ)).re) :
    source.velocity n i j x + (HarmonicWaveInteraction.linearGoodBlock c a b g).velocity n i j x =
      good.velocity n i j x := by
  have he : (source.velocity n i + HarmonicResidual.realCoefficients
      (HarmonicWaveInteraction.linearCoefficients c a b n i - g n i)) j x =
        good.velocity n i j x := by
    apply HarmonicWaveInteraction.coefficient_eq_of_field_eq_at _ _
      (a.frequency n) (a.phase n) hkp j x
    intro θ
    rw [HarmonicResidual.field_add, HarmonicResidual.field_realCoefficients,
      HarmonicResidual.field_sub, Complex.sub_re,
      linearCoefficients_field hU c a b n hr hz hB hb hp hΦ ⟨hx, trivial⟩ i,
      ← HarmonicFields.field_real (hs i), ← HarmonicFields.field_real (hg i)]
    have hc := hcancel θ
    change linearBlockField c a b n (x, θ) i +
      (HarmonicFields.field (source.velocity n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ)).re =
      (HarmonicFields.field (good.velocity n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ)).re + _ at hc
    have hh : (HarmonicFields.field (source.velocity n i) (a.frequency n) (a.phase n)
        (a.angularFrequency n) (x, θ)).re +
        (linearBlockField c a b n (x, θ) i -
          (HarmonicFields.field (g n i) (a.frequency n) (a.phase n) (a.angularFrequency n) (x, θ)).re) =
        (HarmonicFields.field (good.velocity n i) (a.frequency n) (a.phase n)
          (a.angularFrequency n) (x, θ)).re := by linarith
    exact_mod_cast hh
  simpa only [HarmonicWaveInteraction.linearGoodBlock,
    HarmonicMeanInteraction.nonconstant_apply_of_ne _ hj, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, Pi.add_apply] using he


end LinearCoefficientBridge

section ConstructedSignedLinear

open CorrectionState

noncomputable def contextRealBase (c : Context D) (n : ℕ) (x : D × ℝ) : Fin 3 → ℝ :=
  ![c.base.radial n x.1, c.base.angular n x.1, c.base.axial n x.1]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem complexBase_eq_realLift (c : Context D) (n : ℕ) :
    complexBase c n = LinearWaveResidual.realLift (contextRealBase c n) := by
  funext x i
  fin_cases i <;> rfl

theorem contextRealBase_smooth {U : Set D} {c : Context D}
    (hB : SmoothTriple U c.base) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => contextRealBase c n x i) (HarmonicResidual.liftDomain U) := by
  fin_cases i
  · exact (hB.radial n).comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  · exact (hB.angular n).comp contDiff_fst.contDiffOn (fun _ hx => hx.1)
  · exact (hB.axial n).comp contDiff_fst.contDiffOn (fun _ hx => hx.1)

theorem linearBlockField_eq_real {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b : HarmonicBlock D) (n : ℕ)
    (hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain U))
    (hz : ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain U))
    (hB : SmoothTriple U c.base)
    (hb : ∀ i, ContDiffOn ℝ ∞
      (fun x => (HarmonicWaveInteraction.withCarrier a b).oscillation n x i)
      (HarmonicResidual.liftDomain U))
    (hp : ContDiffOn ℝ ∞ ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n)
      (HarmonicResidual.liftDomain U))
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) :
    linearBlockField c a b n x =
      LinearWaveResidual.realComponentLinearResidual (c.operators.epsilon n)
        (fun y : D × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
        (axialDirection c n) (timeDirection c n) (contextRealBase c n)
        ((HarmonicWaveInteraction.withCarrier a b).oscillation n)
        ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n) x := by
  have hU' := HarmonicResidual.liftDomain_open hU
  have he := LinearWaveResidual.realMap_linearResidual Complex.reCLM
    (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1) (timeDirection c n)
    (Vθ := angularDirection)
    (B := contextRealBase c n)
    (a := LinearWaveResidual.realLift ((HarmonicWaveInteraction.withCarrier a b).oscillation n))
    (p := fun y => ((HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n y : ℂ))
    hU' hr contDiffOn_const hz
    (fun i => Complex.ofRealCLM.contDiff.comp_contDiffOn (hb i))
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt (hU'.mem_nhds hx)).differentiableAt (by simp))
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn hp).contDiffAt
      (hU'.mem_nhds hx)).differentiableAt (by simp)) hx
  rw [← complexBase_eq_realLift] at he
  simp only [ LinearWaveResidual.realLift, Complex.reCLM_apply,
    Complex.ofReal_re] at he ⊢
  exact he

/-- Primitive equality of the direction and background data. This record
contains no residual identity and no statement about a corrected field. -/
structure WaveFrameMatch (c : Context D) (s : StripData (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) : Prop where
  epsilon : ∀ n, s.epsilon n = c.operators.epsilon n
  radius : ∀ n, a.radius n = fun y : D × ℝ => c.operators.radius y.1
  radial : ∀ n, d.radialField n = radialDirection c n
  angular : d.angular = (0,1)
  axial : ∀ n, d.axialField s n = axialDirection c n
  time : ∀ n, LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow) =
    timeDirection c n
  radialBase : ∀ n x, a.radialBase n x = c.base.radial n x.1
  angularBase : ∀ n x, a.radius n x * a.frequencyBase n x = c.base.angular n x.1
  axialBase : ∀ n x, a.axialBase n x = c.base.axial n x.1

theorem WaveFrameMatch.base {c : Context D} {s : StripData (D × ℝ)}
    {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} (h : WaveFrameMatch c s d a) (n : ℕ) :
    LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n) =
      complexBase c n := by
  funext x i
  fin_cases i <;> simp [LinearWaveResidual.complexBase, LinearWaveResidual.base, complexBase,
    h.radialBase n x, h.angularBase n x, h.axialBase n x]

theorem WaveFrameMatch.harmonicResidual {c : Context D} {s : StripData (D × ℝ)}
    {d : LinearWaveBounds.GraphDirections (D × ℝ)}
    {z : LinearWaveBounds.WaveCoefficients (D × ℝ)} (h : WaveFrameMatch c s d z) (n : ℕ) :
    z.harmonicResidual s d n =
      LinearWaveResidual.linearResidual (c.operators.epsilon n)
        (fun y : D × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
        (axialDirection c n) (timeDirection c n) (complexBase c n)
        (HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n))
        (HarmonicCalculus.mode (z.frequency n) (z.phase n) (z.pressure n)) := by
  unfold LinearWaveBounds.WaveCoefficients.harmonicResidual
  rw [h.base, h.time, h.epsilon, h.radius, h.radial, h.axial, h.angular]
  rfl

theorem linearBlockField_eq_modeResidual {U : Set D} (hU : IsOpen U)
    (c : Context D) (a b : HarmonicBlock D) (s : StripData (D × ℝ))
    (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (z : LinearWaveBounds.WaveCoefficients (D × ℝ)) (hm : WaveFrameMatch c s d z)
    (n : ℕ) (hB : SmoothTriple U c.base)
    (hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain U))
    (hz : ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain U))
    (hphase : ContDiffOn ℝ ∞ (z.phase n) (HarmonicResidual.liftDomain U))
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => z.amplitude n x i) (HarmonicResidual.liftDomain U))
    (hp : ContDiffOn ℝ ∞ (z.pressure n) (HarmonicResidual.liftDomain U))
    (hvel : (HarmonicWaveInteraction.withCarrier a b).oscillation n =
      fun x i => (HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n) x i).re)
    (hpress : (HarmonicWaveInteraction.withCarrier a b).oscillatoryPressure n =
      fun x => (HarmonicCalculus.mode (z.frequency n) (z.phase n) (z.pressure n) x).re)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) :
    linearBlockField c a b n x = fun i => (z.harmonicResidual s d n x i).re := by
  have hU' := HarmonicResidual.liftDomain_open hU
  have hv' i : ContDiffOn ℝ ∞
      (fun y => HarmonicCalculus.vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i)
      (HarmonicResidual.liftDomain U) := HarmonicCalculus.contDiffOn_mode _ hphase (hv i)
  have hp' := HarmonicCalculus.contDiffOn_mode (z.frequency n) hphase hp
  have he := LinearWaveResidual.realMap_linearResidual Complex.reCLM
    (c.operators.epsilon n) (fun y : D × ℝ => c.operators.radius y.1) (timeDirection c n)
    (Vθ := angularDirection)
    (B := contextRealBase c n)
    hU' hr contDiffOn_const hz hv'
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt (hU'.mem_nhds hx)).differentiableAt (by simp))
    ((hp'.contDiffAt (hU'.mem_nhds hx)).differentiableAt (by simp)) hx
  rw [← complexBase_eq_realLift, ← hm.harmonicResidual] at he
  simp only [Complex.reCLM_apply] at he
  rw [← hvel, ← hpress] at he
  rw [linearBlockField_eq_real hU c a b n hr hz hB
    (fun i => by rw [hvel]; exact Complex.reCLM.contDiff.comp_contDiffOn (hv' i))
    (by rw [hpress]; exact Complex.reCLM.contDiff.comp_contDiffOn hp') hx]
  exact he.symm




/-- The ODE and phase data of the fixed primary column, before performing
any signed update. All equalities concern primitive inputs. -/
structure SignedParameters.Dynamics (p : SignedParameters D) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) where
  slope : ℕ → ℝ
  angular : SignedWaveUpdate.AngularInputs (HarmonicWaveInteraction.productStrip s) p.directions
    p.base p.matrix p.target request p.mask p.fundamental p.normalMotion p.action p.cutoff slope
  angular_direction : p.directions.angular = (0,1)
  angular_frequency : ∀ n, p.base.frequency n * slope n = (p.angularFrequency n : ℝ)
  angular_nonzero : ∀ n, p.angularFrequency n ≠ 0
  geometry : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
    (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
    (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n)
  matrix_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast p.matrix
  target_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast p.target
  request_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast request
  mask_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast p.mask
  frequency_nonzero : ∀ n, p.base.frequency n ≠ 0
  ode : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    HarmonicCalculus.along (p.directions.fastField n) (p.fundamental n) x =
      TangentProjection.projectedRhs (p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x)
        (p.normalMotion n x) (p.fundamental n x) (p.action n x (p.fundamental n x)) 0
        (s.epsilon n * p.base.frequency n ^ 2 *
          ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ^ 2)
  action_eq : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    CurlClassBounds.complexify (p.action n x (p.fundamental n x)) =
      LinearWaveResidual.shear (p.base.radius n) (p.base.frequencyBase n) (p.base.axialBase n)
        (p.directions.radialField n) (fun y => CurlClassBounds.complexify (p.fundamental n y)) x
  cutoff_smooth : ∀ n, ContDiff ℝ ∞ (p.cutoff n)





theorem productStrip_domain (s : StripData D) :
    (HarmonicWaveInteraction.productStrip s).domain = HarmonicResidual.liftDomain s.domain := by
  ext x
  simp [HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip,
    HarmonicWaveInteraction.projection, HarmonicResidual.liftDomain]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem withCarrier_of_same {a b : HarmonicBlock D} (h : SameCarrier a b) :
    HarmonicWaveInteraction.withCarrier a b = b := by
  rcases a with ⟨av,ap,ak,aΦ,akp⟩
  rcases b with ⟨bv,bp,bk,bΦ,bkp⟩
  rcases h with ⟨hk,hΦ,hkp⟩
  simp only at hk hΦ hkp
  subst bk
  subst bΦ
  subst bkp
  rfl







end ConstructedSignedLinear

section ConstructedSignedInvariants

open CorrectionState
open scoped InnerProductSpace

/-- Primitive localization data for the already chosen signed cutoff. -/
structure SignedParameters.GaussianControl (p : SignedParameters D) (s : StripData D)
    (P : ℕ → D → ℝ) where
  slot : GaussianTailFlat.SlotFamily (HarmonicWaveInteraction.productStrip s)
  cutoff : p.cutoff = slot.cutoff
  fast : ∀ n, slot.linear n (p.directions.fastScale n • p.directions.fast) = (slot.length n)⁻¹
  edges : GaussianTailFlat.FlatEdges (HarmonicWaveInteraction.productStrip s)
  scales : GaussianTailFlat.BandScaleControl (HarmonicWaveInteraction.productStrip s)
  rate : ℝ
  rate_pos : 0 < rate
  envelope : ∀ n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    P n x.1 ≤ Real.exp (-rate * (slot.coordinate n x - 1 / 2) ^ 2 * slot.length n)





end ConstructedSignedInvariants

section GaugeRankMean

open CorrectionState VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] in
theorem slow_directional_zero_on {s : StripData (PressureStream.Lift S)} {U : Set S}
    (hU : ∀ x ∈ s.domain, x.2.1 ∈ U)
    {f : ScalarField (PressureStream.Lift S)} (hf : SmoothOn s.domain f)
    (hslow : LocalRankDefect.IsSlowOn U f) (v : PressureStream.Plane)
    (n : ℕ) {x : PressureStream.Lift S} (hx : x ∈ s.domain) :
    fderiv ℝ (f n) x (0, (0, v)) = 0 := by
  apply directional_zero_of_line_const ((hf.at_point s.isOpen_domain n hx).differentiableAt (by simp))
  intro t
  rcases x with ⟨R, p, Y⟩
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  rw [hslow n R p (hU _ hx), hslow n R p (hU _ hx)]

/-- Slow rank increments preserve an already subtracted temporal alias.
The slow axial identity comes from the constructed zero-mass stream. -/
theorem gaugeRankStage_mean_gain {s : StripData (PressureStream.Lift S)}
    {U : Set S} (hU : IsOpen U) (hSU : ∀ x ∈ s.domain, x.2.1 ∈ U)
    (g : GaugeData S) (r : RankData S) (axial : S × PressureStream.Plane)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (hg : LocalRankDefect.RankGeometry g r U c u)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hleft : ∀ n p, p ∈ U → a ≤ r.length n p * r.inner)
    (hright : ∀ n p, p ∈ U → r.length n p * r.outer ≤ b)
    {H κ β : ℝ} (v : PressureStream.Plane) (hfast : c.operators.vT = (0, (0, v)))
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hi : IncrementBounds s H (rankIncrementState g r axial c u))
    (hdp : MeanClass s H (gaugeRankPressureChange g r axial c u))
    (hW : ∀ i j, SmoothOn s.domain (u.covariance i j))
    (A : ScalarField (PressureStream.Lift S))
    (hθ : MeanClass s β (u.thetaResidual c))
    (hz : MeanClass s β (u.axialResidual c - A))
    (hH : 9 / 10 ≤ H) (hβ : β ≤ H + 1 - 2 * κ) :
    MeanClass s β ((rankStageState g r axial c u).thetaResidual c) ∧
      MeanClass s β ((rankStageState g r axial c u).axialResidual c - A) := by
  have hslowθ : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrementState g r axial c u).angular n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero_on hSU hi.angular.smooth
      (LocalRankDefect.rank_angular_slow g r axial U c u) v n hx
  have hslowz : ∀ n x, x ∈ s.domain →
      fderiv ℝ ((rankIncrementState g r axial c u).axial n) x c.operators.vT = 0 := by
    intro n x hx
    rw [hfast]
    exact slow_directional_zero_on hSU hi.axial.smooth
      (hg.axial_slow ha hab hU hleft hright axial) v n hx
  have hδθ := thetaResidual_change_slow_mem ho hb hu.velocity hi hH
    u.covariance hW c.virtualTheta hslowθ
  have hδz := axialResidual_change_slow_mem ho hb hu.velocity hi hH
    u.covariance hW u.pressure (gaugeRankPressureChange g r axial c u)
    c.virtualAxial hu.pressure.smooth hdp hslowz
  have hpressure : u.pressure + gaugeRankPressureChange g r axial c u =
      (rankStageState g r axial c u).pressure := by
    unfold gaugeRankPressureChange
    abel
  have hnewθ : (rankStageState g r axial c u).thetaResidual c =
      MeanIncrementBounds.thetaResidual c.operators c.base (updated u.mean (rankIncrementState g r axial c u))
        u.covariance c.virtualTheta := by
    change MeanIncrementBounds.thetaResidual c.operators c.base _ _ _ = _
    rw [gaugeRankStage_covariance]
    rfl
  have hnewz : (rankStageState g r axial c u).axialResidual c =
      MeanIncrementBounds.axialResidual c.operators c.base (updated u.mean (rankIncrementState g r axial c u))
        u.covariance (u.pressure + gaugeRankPressureChange g r axial c u) c.virtualAxial := by
    rw [hpressure]
    change MeanIncrementBounds.axialResidual c.operators c.base _ _ _ _ = _
    rw [gaugeRankStage_covariance]
    rfl
  constructor
  · apply class_congr (hθ.add (hδθ.mono_exponent hβ))
    intro n x hx
    rw [hnewθ]
    change _ = u.thetaResidual c n x + (_ - u.thetaResidual c n x)
    ring
  · apply class_congr (hz.add (hδz.mono_exponent hβ))
    intro n x hx
    rw [hnewz]
    change _ - _ = (u.axialResidual c n x - A n x) + (_ - u.axialResidual c n x)
    ring


end GaugeRankMean


section MovingSupport

open CorrectionState VariableGaugeMean

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

def GaugeSupported (a b : ℝ) (ell : S → ℝ) (U : Set S)
    (f : ScalarField (PressureStream.Lift S)) : Prop :=
  ∀ n, SupportedGauge a b ell U (f n)

namespace GaugeSupported

variable {a b : ℝ} {ell : S → ℝ} {U : Set S}
  {f g : ScalarField (PressureStream.Lift S)}

section
omit [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem zero : GaugeSupported a b ell U (0 : ScalarField (PressureStream.Lift S)) := by
  intro n x hx hn
  exact (hn rfl).elim

theorem add (hf : GaugeSupported a b ell U f) (hg : GaugeSupported a b ell U g) :
    GaugeSupported a b ell U (f + g) := by
  intro n x hx hn
  by_cases hzero : f n x = 0
  · exact hg n x hx (by simpa only [Pi.add_apply, hzero, zero_add] using hn)
  · exact hf n x hx hzero

theorem neg (hf : GaugeSupported a b ell U f) : GaugeSupported a b ell U (-f) := by
  intro n x hx hn
  exact hf n x hx (neg_ne_zero.mp hn)

theorem sub (hf : GaugeSupported a b ell U f) (hg : GaugeSupported a b ell U g) :
    GaugeSupported a b ell U (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul_right (hf : GaugeSupported a b ell U f) (g : ScalarField (PressureStream.Lift S)) :
    GaugeSupported a b ell U (f * g) := by
  intro n x hx hn
  exact hf n x hx (left_ne_zero_of_mul hn)

theorem mul_left (hf : GaugeSupported a b ell U f) (g : ScalarField (PressureStream.Lift S)) :
    GaugeSupported a b ell U (g * f) := by
  intro n x hx hn
  exact hf n x hx (right_ne_zero_of_mul hn)

theorem smul (hf : GaugeSupported a b ell U f) (t : ℝ) :
    GaugeSupported a b ell U (t • f) := by
  intro n x hx hn
  exact hf n x hx (right_ne_zero_of_mul hn)

end

theorem directional (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (v : PressureStream.Lift S) :
    GaugeSupported a b ell U (fun n x => fderiv ℝ (f n) x v) :=
  fun n => fderiv_apply_supportedGauge hU hell (hf n) (fun _ => v)

theorem dr (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) :
    GaugeSupported a b ell U (o.dr f) := by
  have he := (hf.directional hU hell o.eR).add
    ((hf.directional hU hell o.vR).mul_left (fun n x => o.radialFrequency n * o.radialProfile x))
  convert! he using 1
  funext n x
  simp only [Operators.dr, graphDerivative, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem dz (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) :
    GaugeSupported a b ell U (o.dz f) :=
  (hf.directional hU hell o.eZ).mul_left (fun n _ => o.epsilon n)

theorem time (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) :
    GaugeSupported a b ell U (o.time f) :=
  ((hf.directional hU hell o.eT).mul_left (fun n _ => o.epsilon n)).neg.add
    ((hf.directional hU hell o.vT).mul_left (fun n _ => o.fastCoefficient n))

theorem radialDiv (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) (t : ℝ) :
    GaugeSupported a b ell U (o.radialDiv t f) :=
  (hf.dr hU hell o).add ((hf.mul_left o.invRadius).smul t)

theorem viscosity (hf : GaugeSupported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : Operators (PressureStream.Lift S)) (t : ℝ) :
    GaugeSupported a b ell U (o.viscosity t f) :=
  (((((hf.dr hU hell o).dr hU hell o).add ((hf.dr hU hell o).mul_left o.invRadius)).add
    ((hf.dz hU hell o).dz hU hell o)).sub
      (((hf.mul_left o.invRadius).mul_left o.invRadius).smul t)).mul_left (fun n _ => o.epsilon n)

end GaugeSupported

structure GaugeSupportedTriple (a b : ℝ) (ell : S → ℝ) (U : Set S)
    (m : Triple (PressureStream.Lift S)) : Prop where
  radial : GaugeSupported a b ell U m.radial
  angular : GaugeSupported a b ell U m.angular
  axial : GaugeSupported a b ell U m.axial

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem GaugeSupportedTriple.updated {a b : ℝ} {ell : S → ℝ} {U : Set S}
    {m h : Triple (PressureStream.Lift S)} (hm : GaugeSupportedTriple a b ell U m)
    (hh : GaugeSupportedTriple a b ell U h) : GaugeSupportedTriple a b ell U (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩

theorem gr_supportedGauge {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hell : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) (base m : Triple (PressureStream.Lift S))
    (W : Tensor (PressureStream.Lift S)) (hm : GaugeSupportedTriple a b ell U m)
    (hW : ∀ i j, GaugeSupported a b ell U (W i j)) :
    GaugeSupported a b ell U (MeanIncrementBounds.gr o base m W) := by
  have hrr : GaugeSupported a b ell U (radialRadial base m) :=
    ((hm.radial.mul_left base.radial).smul 2).add (hm.radial.mul_right m.radial)
  have hzr : GaugeSupported a b ell U (axialRadial base m) :=
    ((hm.axial.mul_left base.radial).add (hm.radial.mul_right base.axial)).add
      (hm.radial.mul_right m.axial)
  have htt : GaugeSupported a b ell U (radialAngular base m) :=
    ((hm.angular.mul_left base.angular).smul 2).add (hm.angular.mul_right m.angular)
  exact (((((hm.radial.time hU hell o).add ((hrr.add (hW 0 0)).radialDiv hU hell o 1)).add
    ((hzr.add (hW 2 0)).dz hU hell o)).sub ((htt.add (hW 1 1)).mul_left o.invRadius)).sub
      (hm.radial.viscosity hU hell o 1)).neg

/-- The containing fixed annulus supplies smoothness only. The precise
support conclusion retains the same moving physical edges. -/
theorem state_gr_moving_regular {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (ha : 0 < a) (hab : a < b)
    (c : Context LocalSignedRequest.Point) (u : State LocalSignedRequest.Point)
    (ho : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple a b (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported a b (qLength coord) U.carrier (u.covariance i j)) :
    SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.gr c) ∧
      GaugeSupported a b (qLength coord) U.carrier (u.gr c) := by
  obtain ⟨a₀, b₀, L, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have contain {f : ScalarField LocalSignedRequest.Point}
      (hf : GaugeSupported a b (qLength coord) U.carrier f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hf n x hx hn).1, (hf n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier u.mean :=
    ⟨⟨hm.radial, contain hms.radial⟩, ⟨hm.angular, contain hms.angular⟩, ⟨hm.axial, contain hms.axial⟩⟩
  have hWl (i j) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.covariance i j) :=
    ⟨hW i j, contain (hWs i j)⟩
  refine ⟨(LocalRankDefect.gr_localShell ha₀ U.isOpen hb hml ho u.covariance hWl).smooth, ?_⟩
  exact gr_supportedGauge U.isOpen
    (((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun p hp => U.time_pos p hp)).continuousOn)
    c.operators c.base u.mean u.covariance hms hWs


end MovingSupport


section MovingMeanPressure

open CorrectionState VariableGaugeMean LocalSignedRequest

variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

include hd hell

local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL

/-- The pressure difference is computed by the same variable-gauge integral.
Both radial-source regularity statements and its class follow from the
actual updated mean and unchanged covariance. -/
theorem reconstructedMeanStage_pressure_change_mem
    (c : Context Point) (u v : State Point) (inc : Triple Point)
    (hme : v.mean = updated u.mean inc) (hce : v.covariance = u.covariance)
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    {H κ : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (ho : OperatorBounds stageStrip c.operators κ)
    (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hi : IncrementBounds stageStrip H inc)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) inc)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier inc)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j)) :
    MeanClass stageStrip H ((reconstructState g c v).pressure - u.pressure) := by
  have huReg := state_gr_moving_regular U ha g.radial.inner_lt_outer c u hop hbase hm hms hW hWs
  have hvReg := state_gr_moving_regular U ha g.radial.inner_lt_outer c v hop hbase
    (by rw [hme]; exact smooth_updated hm him)
    (by rw [hme]; exact hms.updated his)
    (by simpa only [hce] using hW) (by simpa only [hce] using hWs)
  have hcov : ∀ i j, SmoothOn (stageStrip).domain (u.covariance i j) :=
    fun i j n => (hW i j n).mono (fun _ hx => hx.1)
  have hgr : MeanClass stageStrip H (v.gr c - u.gr c) := by
    simpa only [State.gr, hme, hce] using gr_change_mem ho hb hu.velocity hi hH u.covariance hcov hκ
  have hp := reconstructState_pressure_change_class U g ha hd hcL hcR ε L hε hεone hL hell
    c v u hvReg.1 huReg.1 hvReg.2 huReg.2 hgr
  simp only [hfixed] at hp
  exact hp

/-- Direct pressure bound for the literal temporal stage. No class of a
pressure source or pressure output is supplied as a hypothesis. -/
theorem gaugeTemporalStage_pressure_change_mem
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    {H κ : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (ho : OperatorBounds stageStrip c.operators κ)
    (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hi : IncrementBounds stageStrip H (temporalIncrementState g h index axial c u))
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (temporalIncrementState g h index axial c u))
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalIncrementState g h index axial c u))
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j)) :
    MeanClass stageStrip H (gaugeTemporalPressureChange g h index axial c u) := by
  let v := u.addIncrement (temporalIncrementState g h index axial c u) 0 0 0
    ⟨0, 0, temporalAliasState g h index c u⟩
  exact reconstructedMeanStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell c u v
    (temporalIncrementState g h index axial c u) rfl
    (by simp only [v, State.addIncrement, add_zero]; rfl)
    hfixed hH hκ ho hb hu hi hop hbase hm him hms his hW hWs

/-- The same integral update for the literal rank stage, with its full
centrifugal source change derived by the nonlinear mean identity. -/
theorem gaugeRankStage_pressure_change_mem
    (r : RankData PressureStream.Plane) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    {H κ : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10)
    (ho : OperatorBounds stageStrip c.operators κ)
    (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hi : IncrementBounds stageStrip H (rankIncrementState g r axial c u))
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (rankIncrementState g r axial c u))
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankIncrementState g r axial c u))
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j)) :
    MeanClass stageStrip H (gaugeRankPressureChange g r axial c u) := by
  let v := u.addIncrement (rankIncrementState g r axial c u) 0 0 0 ExcludedErrors.zero
  exact reconstructedMeanStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell c u v
    (rankIncrementState g r axial c u) rfl
    (by simp only [v, State.addIncrement, add_zero]; rfl)
    hfixed hH hκ ho hb hu hi hop hbase hm him hms his hW hWs

end MovingMeanPressure


section TemporalRegularity

open CorrectionState VariableGaugeMean LocalSignedRequest

variable {coord : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = qLength coord)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual c))

include ha hd hell hθ hz hpθ hpz hsz in
/-- Full local smoothness of the actual temporal stream components,
including the axis where the annular support makes the quotients zero. -/
theorem gaugeTemporalIncrement_smooth :
    SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (temporalIncrementState g h index axial c u) := by
  let pot := temporalPotential g h index c u
  have hf : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) pot := by
    intro n
    simpa only [pot, temporalPotential, hell] using
      streamPotential_q_contDiffOn U ha g.radial.inner_lt_outer hd (g.radial.frequency n)
        g.radial.radialDirection
        (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hz n) (hpz n))
        (temporalAtIndex_supportedGauge h n (index n) (hsz n))
  have hs : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier pot := by
    intro n
    simpa only [pot, temporalPotential, hell] using
      streamPotential_supportedGauge (M := g.radial.frequency n) ha g.radial.inner_lt_outer hd
        (qLength coord) g.radial.radialDirection U.isOpen
        (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs))
        (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hz n) (hpz n))
        (temporalAtIndex_supportedGauge h n (index n) (hsz n))
  obtain ⟨a, b, L, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hfShell : LocalRankDefect.LocalShell a b U.carrier pot :=
    ⟨hf, fun n x hx hn => ⟨(hleft _ hx).trans (hs n x hx hn).1,
      (hs n x hx hn).2.trans (hright _ hx)⟩⟩
  constructor
  · intro n
    exact (((contDiffOn_infty_iff_fderiv_of_isOpen (PhysicalMeanDomain.slowDomain_open U.isOpen)).mp
      (hf n)).2.clm_apply contDiffOn_const).neg
  · intro n
    exact temporalAtIndex_contDiffOn h n (index n) U.isOpen (hθ n) (hpθ n)
  · have hrad := hfShell.directional U.isOpen (1, 0)
    have htor := hfShell.directional U.isOpen (0, (0, g.radial.radialDirection))
    have hspeed : SmoothOn (LocalRankDefect.positiveDomain U.carrier)
        (fun n (x : Point) => PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n) x.1) := by
      intro n x hx
      exact ((PressureStream.physicalSpeed_smooth g.radial.exponent (g.radial.frequency n)
        hx.1.ne').comp x contDiffAt_fst).contDiffWithinAt
    have hprod := htor.coefficient_mul ha₀ U.isOpen hspeed
    have hgraph : SmoothOn (PhysicalMeanDomain.slowDomain U.carrier)
        (fun n => PressureStream.graphDr (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n))
          (0, g.radial.radialDirection) (pot n)) := by
      have he : (fun n => PressureStream.graphDr (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n))
          (0, g.radial.radialDirection) (pot n)) =
          (fun n x => fderiv ℝ (pot n) x (1, 0)) +
            (fun n (x : Point) => PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n) x.1) *
              (fun n x => fderiv ℝ (pot n) x (0, (0, g.radial.radialDirection))) := by
        funext n x
        change fderiv ℝ (pot n) x (1, _ • (0, g.radial.radialDirection)) = _
        rw [show (((1 : ℝ), PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n) x.1 •
            ((0 : PressureStream.Plane), g.radial.radialDirection)) : Point) =
            ((1, (0, (0 : PressureStream.Plane))) : Point) +
            PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n) x.1 •
              ((0, (0, g.radial.radialDirection)) : Point) by simp]
        simp only [map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.mul_apply]
        rfl
      rw [he]
      exact hrad.smooth.add hprod.smooth
    intro n
    exact (hgraph n).add (VariableGaugeMean.divideRadius_contDiffOn ha₀ U.isOpen (hf n) (hfShell.supported n))

end TemporalRegularity


section PeriodizedSignedConstruction

open CorrectionState VariableGaugeMean LocalSignedRequest

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I : Type}

/-- The primitive native data of one signed spatial label. Every copy
uses the same carrier, base, and graph directions. -/
structure PeriodizedSignedParameters (D I : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  base : LinearWaveBounds.WaveCoefficients (D × ℝ)
  directions : LinearWaveBounds.GraphDirections (D × ℝ)
  matrix : I → ℕ → D × ℝ → SignedWaveUpdate.Mat2
  target : I → ℕ → D × ℝ → SignedWaveUpdate.Vec2
  mask : I → ℕ → D × ℝ → ℝ
  fundamental : I → ℕ → D × ℝ → ProblemStatement.Space
  normalMotion : I → ℕ → D × ℝ → ProblemStatement.Space
  action : I → ℕ → D × ℝ → ProblemStatement.Space →L[ℝ] ProblemStatement.Space
  cutoff : I → ℕ → D × ℝ → ℝ
  angularFrequency : ℕ → ℤ
  column : Fin 2

namespace PeriodizedSignedParameters
variable (p : PeriodizedSignedParameters D I)

noncomputable def native (i : I) : SignedParameters D where
  base := p.base
  directions := p.directions
  matrix := p.matrix i
  target := p.target i
  mask := p.mask i
  fundamental := p.fundamental i
  normalMotion := p.normalMotion i
  action := p.action i
  cutoff := p.cutoff i
  angularFrequency := p.angularFrequency
  column := p.column

/-- The native fields are evaluated from the signed quotient and projected
homogeneous pressure before the one native cutoff is applied. -/
noncomputable def copyData (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    PeriodizedWaveBounds.CopyData (D × ℝ) I where
  background := p.base
  amplitude n i := ((p.native i).coefficients s request).amplitude n
  pressure n i := ((p.native i).coefficients s request).pressure n
  cutoff n i := p.cutoff i n
  source := fun _ _ => 0


noncomputable def exactBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.blockOfCoefficients
    ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions)
    p.angularFrequency

noncomputable def tangentBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.blockOfCoefficients (p.copyData s request).common p.angularFrequency

noncomputable def curlBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D := subBlock (p.exactBlock s request) (p.tangentBlock s request)

noncomputable def goodBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.coefficientBlock p.base.frequency (fun n x => p.base.phase n (x,0)) p.angularFrequency
    (fun n x => (p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s) p.directions n (x,0))
    (fun _ _ => 0)

noncomputable def gaussianBlock (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicBlock D :=
  SignedWaveUpdate.coefficientBlock p.base.frequency (fun n x => p.base.phase n (x,0)) p.angularFrequency
    (fun n x => (p.copyData s request).globalGaussian p.directions n (x,0)) (fun _ _ => 0)

theorem exact_tangent_carrier (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    SameCarrier (p.exactBlock s request) (p.tangentBlock s request) := ⟨rfl, rfl, rfl⟩

theorem exactBlock_split (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).oscillation =
      (p.tangentBlock s request).oscillation + (p.curlBlock s request).oscillation := by
  rw [curlBlock, subBlock_oscillation _ _ (p.exact_tangent_carrier s request)]
  abel

theorem exactBlock_band (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).BandLimited 1 := SignedWaveUpdate.coefficientBlock_band _ _ _ _ _

theorem tangentBlock_band (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.tangentBlock s request).BandLimited 1 := SignedWaveUpdate.coefficientBlock_band _ _ _ _ _

theorem gaussianBlock_band (s : StripData D) (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    (p.gaussianBlock s request).BandLimited 1 := SignedWaveUpdate.coefficientBlock_band _ _ _ _ _


end PeriodizedSignedParameters
end PeriodizedSignedConstruction

section ParticularConstruction

open CorrectionState VariableGaugeMean

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Primitive per-band data of the actual complex Volterra inverse. The
interval may vary with the physical clock. No solved field is stored. -/
structure ParticularParameters (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  tangent : ℤ → ℕ → CommonCoverSolve.TangentData P ProblemStatement.Space
  geometry : ℕ → CommonCoverSolve.Geometry
  length : ℕ → ℝ
  length_pos : ∀ n, 0 < length n
  cutoff : ℕ → TorusInverse.Plane → ℝ
  background : LinearWaveBounds.WaveCoefficients ((P × ℝ) × TorusInverse.Plane)
  directions : LinearWaveBounds.GraphDirections ((P × ℝ) × TorusInverse.Plane)

namespace ParticularParameters
variable (p : ParticularParameters P)

noncomputable def copyData (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (j : ℤ) :
    PeriodizedWaveBounds.CopyData ((P × ℝ) × TorusInverse.Plane) TorusInverse.Frequency where
  background := ParticularWaveAssembly.actualCarrier p.background b j
  amplitude n k := (ParticularWaveBounds.complexCopyCoefficients
    (ParticularWaveAssembly.actualCarrier p.background b j)
    (fun n => ParticularWaveAssembly.angleTangent (p.tangent j n))
    (ParticularWaveAssembly.sourceFamily c u b G A j) p.geometry (fun _ => k) p.length p.length_pos).amplitude n
  pressure n k := (ParticularWaveBounds.complexCopyCoefficients
    (ParticularWaveAssembly.actualCarrier p.background b j)
    (fun n => ParticularWaveAssembly.angleTangent (p.tangent j n))
    (ParticularWaveAssembly.sourceFamily c u b G A j) p.geometry (fun _ => k) p.length p.length_pos).pressure n
  cutoff n k x := p.cutoff n ((p.geometry n).coordinates k x.2)
  source := ParticularWaveAssembly.sourceFamily c u b G A j

noncomputable def nativeStrip (s : StripData (P × TorusInverse.Plane)) :
    StripData ((P × ℝ) × TorusInverse.Plane) :=
  ParticularWaveBounds.reindexStrip ParticularWaveAssembly.angleShuffle.symm (HarmonicWaveInteraction.productStrip s)

noncomputable def wave (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (j : ℤ) :
    LinearWaveBounds.WaveCoefficients ((P × ℝ) × TorusInverse.Plane) :=
  (p.copyData c u b G A j).commonCorrected (nativeStrip s) p.directions

noncomputable def updateBlock (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) : HarmonicBlock (P × TorusInverse.Plane) :=
  ParticularWaveAssembly.assembledBlock N b.frequency b.phase b.angularFrequency
    (fun j n x => (p.wave s c u b G A j).amplitude n (ParticularWaveAssembly.angleShuffle (x,0)))
    (fun j n x => (p.wave s c u b G A j).pressure n (ParticularWaveAssembly.angleShuffle (x,0)))

noncomputable def goodBlock (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) : HarmonicBlock (P × TorusInverse.Plane) :=
  ParticularWaveAssembly.assembledBlock N b.frequency b.phase b.angularFrequency
    (fun j n x => (p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n
      (ParticularWaveAssembly.angleShuffle (x,0))) (fun _ _ _ => 0)

noncomputable def gaussianBlock
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) : HarmonicBlock (P × TorusInverse.Plane) :=
  ParticularWaveAssembly.assembledBlock N b.frequency b.phase b.angularFrequency
    (fun j n x => (p.copyData c u b G A j).globalGaussian p.directions n
      (ParticularWaveAssembly.angleShuffle (x,0))) (fun _ _ _ => 0)

theorem updateBlock_band (s : StripData (P × TorusInverse.Plane))
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) :
    (p.updateBlock s c u b G A N).BandLimited N := ParticularWaveAssembly.assembledBlock_band _ _ _ _ _ _

theorem gaussianBlock_band
    (c : Context (P × TorusInverse.Plane)) (u : State (P × TorusInverse.Plane))
    (b : HarmonicBlock (P × TorusInverse.Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × TorusInverse.Plane)) (N : ℕ) :
    (p.gaussianBlock c u b G A N).BandLimited N := ParticularWaveAssembly.assembledBlock_band _ _ _ _ _ _


end ParticularParameters
end ParticularConstruction

end NavierStokes.CorrectionStep
