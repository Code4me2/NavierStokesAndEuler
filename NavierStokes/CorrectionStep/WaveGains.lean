import NavierStokes.CorrectionStep.CycleConstruction

/-!
# Exact field bookkeeping for one correction cycle: wave gains

Fourth part of `NavierStokes.CorrectionStep`.  It records the linear wave
theory of the constructed families (periodized signed and particular), the
supported wave gain, the cycle recurrence, the periodized curl identities, and
the resulting uniform and constructed wave gains and means.
-/

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds
open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section PeriodizedSignedLinear
open Set Filter WeightedClasses HarmonicCalculus CorrectionState
open scoped ContDiff Topology

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

namespace NativeAngularGeometry
variable {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
  {d : LinearWaveBounds.GraphDirections D} {C : ℕ → I → Set D}
  (g : NativeAngularGeometry a s d C)

include g


theorem common_pressure (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.common.pressure n) :=
  a.common_pressure_invariant d.angular (fun n i => g.cutoff i n)
    (fun n i => g.pressure i n) n

theorem corrected_amplitude (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular ((a.commonCorrected s d).amplitude n) :=
  a.commonCorrected_invariant s d d.angular (fun n i => g.cutoff i n)
    (fun n i => g.amplitude i n) g.radius g.radial_field
    (fun _ => CopyAngularInvariance.Invariant.const _) g.phase n

theorem good (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.globalGood s d n) :=
  a.globalGood_invariant s d (fun n i => g.cutoff i n) (fun n i => g.amplitude i n)
    (fun n i => g.pressure i n) g.radius g.radial_base g.frequency_base g.axial_base
    g.radial_field (fun _ => CopyAngularInvariance.Invariant.const _) g.phase n

theorem gaussian (hf : ∀ n, CopyAngularInvariance.Invariant d.angular (a.source n)) (n : ℕ) :
    CopyAngularInvariance.Invariant d.angular (a.globalGaussian d n) :=
  a.globalGaussian_invariant d d.angular (fun n i => g.cutoff i n)
    (fun n i => g.amplitude i n) hf n
end NativeAngularGeometry

namespace PeriodizedSignedParameters
variable {p : PeriodizedSignedParameters D I} {s : StripData D}
  {P : ℕ → D → ℝ} {κ β : ℝ} {h : p.NativeControl s P κ}
  {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}
  (d : NativeDynamics h request) (i₀ : I)

include i₀ in
theorem NativeDynamics.phase_eq (hθ : p.directions.angular = (0,1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (n : ℕ) (x : D) (θ : ℝ) :
    p.base.frequency n * p.base.phase n (x,θ) =
      p.base.frequency n * p.base.phase n (x,0) + (p.angularFrequency n : ℝ) * θ := by
  rw [CopyAngularInvariance.affinePhase_eq_zeroSlice
    (Φ := p.base.phase n) (m := d.slope n)
    (by simpa only [hθ] using (d.angular i₀).phase n) x θ,
    mul_add, ← mul_assoc, hkp]

include i₀ in
theorem NativeDynamics.exact_represents (hθ : p.directions.angular = (0,1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ)) :
    let z := (p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions
    (p.exactBlock s request).oscillation =
      (fun n x i => (vectorMode (p.base.frequency n) (p.base.phase n) (z.amplitude n) x i).re) ∧
    (p.exactBlock s request).oscillatoryPressure =
      (fun n x => (mode (p.base.frequency n) (p.base.phase n) (z.pressure n) x).re) := by
  apply SignedWaveUpdate.blockOfCoefficients_represents
  · intro n x θ
    exact CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [hθ] using (d.angularGeometry i₀).corrected_amplitude n) x θ
  · intro n x θ
    exact CopyAngularInvariance.invariant_eq_zeroSlice
      (by
        have hp := (d.angularGeometry i₀).common_pressure n
        simp only [hθ] at hp
        exact hp) x θ
  · exact d.phase_eq i₀ hθ hkp

include i₀ in
theorem NativeDynamics.good_represents (hθ : p.directions.angular = (0,1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ)) :
    (p.goodBlock s request).oscillation = fun n x i =>
      ((p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s)
        p.directions n x i * carrier (p.base.frequency n) (p.base.phase n) x).re := by
  let z : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
    {p.base with amplitude := ((p.copyData s request).globalGood
      (HarmonicWaveInteraction.productStrip s) p.directions), pressure := 0}
  exact (SignedWaveUpdate.blockOfCoefficients_represents z p.angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [hθ] using (d.angularGeometry i₀).good n) x θ)
    (fun _ _ _ => rfl) (d.phase_eq i₀ hθ hkp)).1

include i₀ in
theorem NativeDynamics.gaussian_represents (hθ : p.directions.angular = (0,1))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ)) :
    (p.gaussianBlock s request).oscillation = fun n x i =>
      ((p.copyData s request).globalGaussian p.directions n x i *
        carrier (p.base.frequency n) (p.base.phase n) x).re := by
  let z : LinearWaveBounds.WaveCoefficients (D × ℝ) :=
    {p.base with amplitude := (p.copyData s request).globalGaussian p.directions, pressure := 0}
  exact (SignedWaveUpdate.blockOfCoefficients_represents z p.angularFrequency
    (fun n x θ => CopyAngularInvariance.invariant_eq_zeroSlice
      (by simpa only [hθ] using ((d.angularGeometry i₀).gaussian
        (fun _ => CopyAngularInvariance.Invariant.const _) n)) x θ)
    (fun _ _ _ => rfl) (d.phase_eq i₀ hθ hkp)).1

theorem frame_common (p : PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) {c : Context D}
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base) :
    WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions
      ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions) :=
  ⟨hm.epsilon, hm.radius, hm.radial, hm.angular, hm.axial, hm.time,
    hm.radialBase, hm.angularBase, hm.axialBase⟩

theorem exactBlock_zero (p : PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    HarmonicWaveInteraction.ZeroMode (p.exactBlock s request) :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1

theorem exactBlock_pressure_zero (p : PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) :
    ∀ n, (p.exactBlock s request).pressure n 0 = 0 :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).2

include i₀ in
/-- The periodized signed update satisfies the actual context linear
operator, with the computed Gaussian term retained. -/
theorem NativeDynamics.context_linear_identity (hκ : κ ≤ 1 / 2)
    (hR : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x i))
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (c : Context D) (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (a : HarmonicBlock D) (hcarrier : SameCarrier a (p.exactBlock s request))
    (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c a (p.exactBlock s request) n x =
      (p.goodBlock s request).oscillation n x + (p.gaussianBlock s request).oscillation n x := by
  let z := (p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions
  have hb := h.global_bounds hκ request hR
  have hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain s.domain) :=
    HarmonicResidual.liftDirection_smooth (hrad n)
  have hz : ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain s.domain) := contDiffOn_const
  have hphase := (d.angular i₀).phase_smooth n
  rw [productStrip_domain] at hphase
  have hv (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => z.amplitude n y i)
      (HarmonicResidual.liftDomain s.domain) := by
    simpa only [productStrip_domain] using (CurlClassBounds.class_component hb.2.1 i).smooth n
  have hp : ContDiffOn ℝ ∞ (z.pressure n) (HarmonicResidual.liftDomain s.domain) := by
    have hp := hb.2.2.1.smooth n
    simp only [productStrip_domain] at hp
    exact hp
  have hvrep : (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)).oscillation n =
      fun y i => (vectorMode (z.frequency n) (z.phase n) (z.amplitude n) y i).re := by
    rw [withCarrier_of_same hcarrier]
    exact congrFun (d.exact_represents i₀ hm.angular hkp).1 n
  have hprep : (HarmonicWaveInteraction.withCarrier a (p.exactBlock s request)).oscillatoryPressure n =
      fun y => (mode (z.frequency n) (z.phase n) (z.pressure n) y).re := by
    rw [withCarrier_of_same hcarrier]
    exact congrFun (d.exact_represents i₀ hm.angular hkp).2 n
  rw [linearBlockField_eq_modeResidual s.isOpen_domain c a (p.exactBlock s request)
    (HarmonicWaveInteraction.productStrip s) p.directions z (p.frame_common s request hm)
    n hB hr hz hphase hv hp hvrep hprep ⟨hx, trivial⟩]
  rw [d.good_represents i₀ hm.angular hkp, d.gaussian_represents i₀ hm.angular hkp]
  funext i
  have he := congrArg Complex.re (congrFun (d.common_equation hκ hR n hx) i)
  simpa only [add_mul, Complex.add_re, Pi.add_apply] using he


end PeriodizedSignedParameters

end PeriodizedSignedLinear

section ParticularLinear
open Set WeightedClasses HarmonicCalculus
open ParticularWaveBounds LinearWaveBounds
variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem harmonicResidual_reindex (e : D ≃ₗᵢ[ℝ] E) (a : WaveCoefficients E)
    (s : StripData E) (d : GraphDirections E) (n : ℕ) (x : D) :
    (reindexCoefficients e a).harmonicResidual (reindexStrip e s) (reindexDirections e d) n x =
      a.harmonicResidual s d n (e x) := by
  have ht : LinearWaveResidual.timeDirection ((reindexStrip e s).epsilon n)
      ((reindexDirections e d).fastField n) (fun _ => (reindexDirections e d).slow) =
      reindexVector e (LinearWaveResidual.timeDirection (s.epsilon n)
        (d.fastField n) (fun _ => d.slow)) := by
    funext y
    simp only [LinearWaveResidual.timeDirection, GraphDirections.fastField,
      reindexDirections, reindexStrip, reindexVector, map_sub, map_smul]
  unfold WaveCoefficients.harmonicResidual
  rw [reindex_radialField, reindex_axialField, ht]
  exact StateReindex.linearResidual_field_pull e (s.epsilon n) (a.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow))
    (LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n))
    (vectorMode (a.frequency n) (a.phase n) (a.amplitude n))
    (mode (a.frequency n) (a.phase n) (a.pressure n)) x

open CorrectionState TorusInverse CommonCoverSolve ParticularWaveAssembly CopyAngularInvariance
open scoped ContDiff BigOperators

namespace ParticularParameters
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {p : ParticularParameters Q} {s : StripData (Q × Plane)}
  {c : Context (Q × Plane)} {u : State (Q × Plane)} {b : HarmonicBlock (Q × Plane)}
  {G A : HarmonicResidual.BlockCoefficients (Q × Plane)} {j : ℤ}
  {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
  {h : p.NativeControl s c u b G A j W α κ}

theorem NativeDynamics.frequency_ne (d : NativeDynamics h) (n : ℕ) : b.frequency n ≠ 0 := by
  intro hz
  exact d.frequency_nonzero n (by rw [hz, mul_zero])

theorem NativeDynamics.good_invariant (d : NativeDynamics h) (n : ℕ) :
    Invariant p.directions.angular ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n) :=
  d.angularGeometry.good n

theorem NativeDynamics.gaussian_invariant (d : NativeDynamics h) (n : ℕ) :
    Invariant p.directions.angular ((p.copyData c u b G A j).globalGaussian p.directions n) := by
  apply d.angularGeometry.gaussian
  intro m
  rw [d.background.angular]
  exact angleLift_invariant (residualSource c u b G A j m)

theorem NativeDynamics.section_equation (d : NativeDynamics h) (hκ : κ ≤ 1 / 2)
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) (i : Fin 3) :
    (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) i +
      residualSource c u b G A j n x.1 i *
        HarmonicFields.character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2) =
      ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n (angleShuffle (x.1,0)) i +
        (p.copyData c u b G A j).globalGaussian p.directions n (angleShuffle (x.1,0)) i) *
        HarmonicFields.character j (b.frequency n * b.phase n x.1 + (b.angularFrequency n : ℝ) * x.2) := by
  have hg := d.good_invariant n
  have he := d.gaussian_invariant n
  rw [d.background.angular] at hg he
  have hgs := invariant_angleShuffle hg x.1 x.2
  have hes := invariant_angleShuffle he x.1 x.2
  have hh := congrFun (d.common_equation hκ n (x := angleShuffle x) hx) i
  change (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) i +
    residualSource c u b G A j n x.1 i * carrier ((actualCarrier p.background b j).frequency n)
      ((actualCarrier p.background b j).phase n) (angleShuffle x) =
    ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n (angleShuffle x) i +
      (p.copyData c u b G A j).globalGaussian p.directions n (angleShuffle x) i) *
      carrier ((actualCarrier p.background b j).frequency n)
        ((actualCarrier p.background b j).phase n) (angleShuffle x) at hh
  rw [actualCarrier_character p.background b j d.frequency_ne n x, hgs, hes] at hh
  exact hh

theorem NativeDynamics.wave_smooth (d : NativeDynamics h) (hκ : κ ≤ 1 / 2) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => vectorMode ((p.wave s c u b G A j).frequency n)
      ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).amplitude n) (angleShuffle x) i)
      (HarmonicResidual.liftDomain s.domain) := by
  have hf := HarmonicCalculus.contDiffOn_mode ((j : ℝ) * b.frequency n) (d.background.phase_smooth n)
    ((CurlClassBounds.class_component (h.global_bounds hκ).2.1 i).smooth n)
  exact hf.comp (angleShuffle (P := Q)).contDiff.contDiffOn (fun _ hx => hx.1)

theorem NativeDynamics.pressure_smooth (d : NativeDynamics h) (hκ : κ ≤ 1 / 2) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun x => mode ((p.wave s c u b G A j).frequency n)
      ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).pressure n) (angleShuffle x))
      (HarmonicResidual.liftDomain s.domain) := by
  have hf := HarmonicCalculus.contDiffOn_mode ((j : ℝ) * b.frequency n) (d.background.phase_smooth n)
    ((h.global_bounds hκ).2.2.1.smooth n)
  exact hf.comp (angleShuffle (P := Q)).contDiff.contDiffOn (fun _ hx => hx.1)

theorem angleStrip_nativeStrip (s : StripData (Q × Plane)) :
    reindexStrip angleShuffle (nativeStrip s) = HarmonicWaveInteraction.productStrip s := by
  cases s
  rfl

theorem frame_wave (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (j : ℤ)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background)) :
    WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions)
      (reindexCoefficients angleShuffle (p.wave s c u b G A j)) :=
  ⟨hm.epsilon, hm.radius, hm.radial, hm.angular, hm.axial, hm.time,
    hm.radialBase, hm.angularBase, hm.axialBase⟩

theorem native_context_residual (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (j : ℤ)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) :
    (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) =
      LinearWaveResidual.linearResidual (c.operators.epsilon n)
        (fun y : (Q × Plane) × ℝ => c.operators.radius y.1) (radialDirection c n) angularDirection
        (axialDirection c n) (timeDirection c n) (complexBase c n)
        (fun y => vectorMode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
          ((p.wave s c u b G A j).amplitude n) (angleShuffle y))
        (fun y => mode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
          ((p.wave s c u b G A j).pressure n) (angleShuffle y)) x := by
  rw [← harmonicResidual_reindex angleShuffle (p.wave s c u b G A j) (nativeStrip s) p.directions,
    angleStrip_nativeStrip, (p.frame_wave s c u b G A j hm).harmonicResidual]
  rfl

variable (p : ParticularParameters Q) (s : StripData (Q × Plane))
  (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
  (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (N : ℕ)
  (C : ∀ j ∈ modes N, p.NativeControl s c u b G A j W α κ)
  (dyn : ∀ j hj, NativeDynamics (C j hj))

include dyn in
theorem update_represents :
    (p.updateBlock s c u b G A N).oscillation =
      (fun n x i => ∑ j ∈ modes N, (vectorMode ((p.wave s c u b G A j).frequency n)
        ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).amplitude n) (angleShuffle x) i).re) ∧
    (p.updateBlock s c u b G A N).oscillatoryPressure =
      (fun n x => ∑ j ∈ modes N, (mode ((p.wave s c u b G A j).frequency n)
        ((p.wave s c u b G A j).phase n) ((p.wave s c u b G A j).pressure n) (angleShuffle x)).re) := by
  constructor
  · funext n x i
    rw [updateBlock, assembledBlock_value]
    apply Finset.sum_congr rfl
    intro j hj
    have hinv := (dyn j hj).angularGeometry.corrected_amplitude n
    rw [(dyn j hj).background.angular] at hinv
    have hi : (p.wave s c u b G A j).amplitude n (angleShuffle x) =
        (p.wave s c u b G A j).amplitude n (angleShuffle (x.1,0)) :=
      invariant_angleShuffle hinv x.1 x.2
    change Complex.re (_ * _) = ((p.wave s c u b G A j).amplitude n (angleShuffle x) i *
      carrier ((actualCarrier p.background b j).frequency n) ((actualCarrier p.background b j).phase n)
        (angleShuffle x)).re
    rw [actualCarrier_character p.background b j (dyn j hj).frequency_ne n x, hi]
  · funext n x
    rw [updateBlock, assembledBlock_pressure_value]
    apply Finset.sum_congr rfl
    intro j hj
    have hinv := (dyn j hj).angularGeometry.common_pressure n
    rw [(dyn j hj).background.angular] at hinv
    have hi := invariant_angleShuffle hinv x.1 x.2
    change Complex.re (_ * _) = ((p.copyData c u b G A j).common.pressure n (angleShuffle x) *
      carrier ((actualCarrier p.background b j).frequency n) ((actualCarrier p.background b j).phase n)
        (angleShuffle x)).re
    rw [actualCarrier_character p.background b j (dyn j hj).frequency_ne n x, hi]
    rfl

include dyn in
theorem cancellation_sum (hκ : κ ≤ 1 / 2)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    (fun i => ∑ j ∈ modes N,
      ((p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) i).re) +
      (HarmonicResidual.residualBlock c u b G A).oscillation n x =
        (p.goodBlock s c u b G A N).oscillation n x + (p.gaussianBlock c u b G A N).oscillation n x := by
  apply finite_cancellation c u b G A N hN
    (fun j n x => (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x))
    (fun j n x => (p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n (angleShuffle (x,0)))
    (fun j n x => (p.copyData c u b G A j).globalGaussian p.directions n (angleShuffle (x,0))) n x
  intro j hj i
  exact (dyn j hj).section_equation hκ n x hx i

include dyn in
theorem context_linear_sum (hκ : κ ≤ 1 / 2)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c b (p.updateBlock s c u b G A N) n x =
      fun i => ∑ j ∈ modes N,
        ((p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n (angleShuffle x) i).re := by
  have hu := p.update_represents s c u b G A N C dyn
  have hv (j : ℤ) (hj : j ∈ modes N) (i : Fin 3) := (dyn j hj).wave_smooth hκ n i
  have hp (j : ℤ) (hj : j ∈ modes N) := (dyn j hj).pressure_smooth hκ n
  have hvs (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (p.updateBlock s c u b G A N).oscillation n y i) (HarmonicResidual.liftDomain s.domain) := by
    rw [hu.1]
    exact ContDiffOn.sum (fun j hj => Complex.reCLM.contDiff.comp_contDiffOn (hv j hj i))
  have hps : ContDiffOn ℝ ∞ ((p.updateBlock s c u b G A N).oscillatoryPressure n)
      (HarmonicResidual.liftDomain s.domain) := by
    rw [hu.2]
    exact ContDiffOn.sum (fun j hj => Complex.reCLM.contDiff.comp_contDiffOn (hp j hj))
  have hcarrier : SameCarrier b (p.updateBlock s c u b G A N) := ⟨rfl,rfl,rfl⟩
  have hr : ContDiffOn ℝ ∞ (radialDirection c n) (HarmonicResidual.liftDomain s.domain) :=
    HarmonicResidual.liftDirection_smooth (hrad n)
  rw [linearBlockField_eq_real s.isOpen_domain c b (p.updateBlock s c u b G A N) n hr
    contDiffOn_const hB (by simpa only [withCarrier_of_same hcarrier] using hvs)
    (by simpa only [withCarrier_of_same hcarrier] using hps) ⟨hx,trivial⟩,
    withCarrier_of_same hcarrier, hu.1, hu.2]
  have he := real_linearResidual_sum (Vθ := angularDirection) (modes N) (HarmonicResidual.liftDomain_open s.isOpen_domain)
    (c.operators.epsilon n) (fun y : (Q × Plane) × ℝ => c.operators.radius y.1) (timeDirection c n)
    hr contDiffOn_const (show ContDiffOn ℝ ∞ (axialDirection c n) (HarmonicResidual.liftDomain s.domain)
      from contDiffOn_const) (contextRealBase c n)
    (fun j y => vectorMode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
      ((p.wave s c u b G A j).amplitude n) (angleShuffle y))
    (fun j y => mode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
      ((p.wave s c u b G A j).pressure n) (angleShuffle y)) hv hp
    (fun i => ((contextRealBase_smooth hB n i).contDiffAt
      ((HarmonicResidual.liftDomain_open s.isOpen_domain).mem_nhds ⟨hx,trivial⟩)).differentiableAt (by simp))
    ⟨hx,trivial⟩
  rw [← complexBase_eq_realLift] at he
  rw [he]
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  rw [p.native_context_residual s c u b G A j hm]

include dyn in
theorem context_linear_cancellation (hκ : κ ≤ 1 / 2)
    (hN : (HarmonicResidual.residualBlock c u b G A).BandLimited N)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    linearBlockField c b (p.updateBlock s c u b G A N) n x +
      (HarmonicResidual.residualBlock c u b G A).oscillation n x =
        (p.goodBlock s c u b G A N).oscillation n x + (p.gaussianBlock c u b G A N).oscillation n x := by
  rw [p.context_linear_sum s c u b G A N C dyn hκ hB hrad hm n x hx]
  exact p.cancellation_sum s c u b G A N C dyn hκ hN n x hx


end ParticularParameters

end ParticularLinear

section SupportedWaveGain
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState
open scoped ContDiff Topology
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


end SupportedWaveGain

section ActualRecurrence
open Set CorrectionState WeightedClasses
open scoped BigOperators

abbrev AxisymmetricAlias := ℕ → CyclePoint → Fin 3 → ℝ

noncomputable def coefficientField (b : HarmonicBlock CyclePoint)
    (a : HarmonicResidual.BlockCoefficients CyclePoint) : Oscillation CyclePoint :=
  fun n x i => (HarmonicFields.field (a n i) (b.frequency n) (b.phase n) (b.angularFrequency n) x).re

/-- The axisymmetric alias is kept separately from the spatial labels.
No slot support is imposed on a zero angular mode. -/
structure CycleRepresentation {ι : Type} (v : CycleCoefficients ι)
    (u : State CyclePoint) (axis : AxisymmetricAlias) : Prop where
  velocity : ∀ n x i, u.oscillation n x i = ∑ l ∈ v.labels n, (v.blocks l).oscillation n x i
  pressure : ∀ n x, u.oscillatoryPressure n x = ∑ l ∈ v.labels n, (v.blocks l).oscillatoryPressure n x
  gaussian : ∀ n x i, u.errors.gaussian n x i = ∑ l ∈ v.labels n, coefficientField (v.blocks l) (v.gaussian l) n x i
  aliasError : ∀ n x i, u.errors.aliasError n x i = axis n x.1 i

/-- A common integer bound for stored coefficient values, including errors. -/
structure CoefficientBands {ι : Type} (v : CycleCoefficients ι) : Prop where
  velocityPressure : ∀ l, (v.blocks l).BandLimited v.residualBand
  gaussian : ∀ l n i, HarmonicFields.BandLimited (v.gaussian l n i) v.residualBand

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

theorem particular_carrier (l : ι) : SameCarrier (v.blocks l) (p.particularBlock v c u l) :=
  ⟨rfl,rfl,rfl⟩

theorem particularGaussian_carrier (l : ι) : SameCarrier (v.blocks l) (p.particularGaussianBlock v c u l) :=
  ⟨rfl,rfl,rfl⟩

/-- The new nonzero harmonic data are literal sums of the old and
constructed coefficients. All new mean aliases remain in the separate field. -/
noncomputable def nextCoefficients : CycleCoefficients ι where
  labels := v.labels
  blocks := p.finalBlock v c u
  gaussian := fun l => v.gaussian l + (p.particularGaussianBlock v c u l).velocity +
    (p.signedGaussianBlock v c u l).velocity
  residualBand := 2 * max v.residualBand 1

noncomputable def nextAxisymmetricAlias (axis : AxisymmetricAlias) : AxisymmetricAlias :=
  fun n x i => axis n x i +
    VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) n (x,0) i +
    (VariableGaugeMean.pressureAliasState p.gauge c (p.afterRank v c u) n (x,0) i -
      VariableGaugeMean.pressureAliasState p.gauge c u n (x,0) i)

theorem finalBlock_oscillation
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) (l : ι) :
    (p.finalBlock v c u l).oscillation = (v.blocks l).oscillation +
      (p.particularBlock v c u l).oscillation + (p.signedBlock v c u l).oscillation := by
  have hs : SameCarrier (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  rw [finalBlock, addBlock_oscillation _ _ hs, addBlock_oscillation _ _ (p.particular_carrier v c u l)]

theorem finalBlock_pressure
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) (l : ι) :
    (p.finalBlock v c u l).oscillatoryPressure = (v.blocks l).oscillatoryPressure +
      (p.particularBlock v c u l).oscillatoryPressure + (p.signedBlock v c u l).oscillatoryPressure := by
  have hs : SameCarrier (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  rw [finalBlock, addBlock_pressure _ _ hs, addBlock_pressure _ _ (p.particular_carrier v c u l)]

theorem nextCoefficients_gaussian_field
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (l : ι) (n : ℕ) (x : CyclePoint × ℝ) (i : Fin 3) :
    coefficientField ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c u).gaussian l) n x i =
      coefficientField (v.blocks l) (v.gaussian l) n x i +
        (p.particularGaussianBlock v c u l).oscillation n x i +
        (p.signedGaussianBlock v c u l).oscillation n x i := by
  have hs : SameCarrier (v.blocks l) (p.signedGaussianBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  have hp := p.particularGaussian_carrier v c u l
  change (HarmonicFields.field (v.gaussian l n i +
      (p.particularGaussianBlock v c u l).velocity n i + (p.signedGaussianBlock v c u l).velocity n i)
      ((v.blocks l).frequency n) ((v.blocks l).phase n) ((v.blocks l).angularFrequency n) x).re = _
  rw [HarmonicResidual.field_add, HarmonicResidual.field_add, Complex.add_re, Complex.add_re]
  simp only [coefficientField, HarmonicBlock.oscillation, hp.frequency, hp.phase, hp.angular,
    hs.frequency, hs.phase, hs.angular]

theorem next_representation {axis : AxisymmetricAlias}
    (hrep : CycleRepresentation v u axis)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) :
    CycleRepresentation (p.nextCoefficients v c u) (p.next v c u)
      (p.nextAxisymmetricAlias v c u axis) := by
  constructor
  · intro n x i
    rw [p.next_oscillation]
    simp only [Pi.add_apply, hrep.velocity n x i, particularVelocity, signedVelocity,
      LabelSumBounds.fieldSum, nextCoefficients, p.finalBlock_oscillation v c u hc,
      Finset.sum_add_distrib]
  · intro n x
    rw [p.next_oscillatoryPressure]
    simp only [Pi.add_apply, hrep.pressure n x, particularPressure, signedPressure,
      nextCoefficients, p.finalBlock_pressure v c u hc, Finset.sum_add_distrib]
  · intro n x i
    rw [p.next_gaussian_error]
    simp only [Pi.add_apply, hrep.gaussian n x i, particularGaussian, signedGaussian,
      LabelSumBounds.fieldSum, p.nextCoefficients_gaussian_field v c u hc,
      show (p.nextCoefficients v c u).labels = v.labels from rfl, Finset.sum_add_distrib]
  · intro n x i
    rw [p.next_alias_error]
    simp only [Pi.add_apply, Pi.sub_apply, hrep.aliasError n x i, nextAxisymmetricAlias]
    simp only [VariableGaugeMean.temporalAliasState, VariableGaugeMean.pressureAliasState]

theorem next_coefficient_bands (h : CoefficientBands v) :
    CoefficientBands (p.nextCoefficients v c u) := by
  have hn : max v.residualBand 1 ≤ 2 * max v.residualBand 1 := by omega
  have hb l : (p.finalBlock v c u l).BandLimited (max v.residualBand 1) := by
    simpa only [max_self] using p.finalBlock_band v c u h.velocityPressure l
  have hg l n i : HarmonicFields.BandLimited
      ((p.nextCoefficients v c u).gaussian l n i) (max v.residualBand 1) := by
    exact (((h.gaussian l n i).mono (le_max_left _ _)).add
      (((p.particularGaussianBlock_band v c u l).1 n i).mono (le_max_left _ _))).add
      ((((p.signed l).gaussianBlock_band p.strip (p.signedRequest v c u)).1 n i).mono (le_max_right _ _))
  exact ⟨fun l => ⟨fun n i => ((hb l).1 n i).mono hn, fun n => ((hb l).2 n).mono hn⟩,
    fun l n i => (hg l n i).mono hn⟩

/-- The residual value bound of the next actual state is derived from
stored coefficient bands, independently of a norm estimate. -/
theorem next_residual_band (h : CoefficientBands v) (l : ι) :
    (HarmonicResidual.residualBlock c (p.next v c u)
      ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c u).gaussian l)
      0).BandLimited
      (p.nextCoefficients v c u).residualBand := by
  have hb : (p.finalBlock v c u l).BandLimited (max v.residualBand 1) := by
    simpa only [max_self] using p.finalBlock_band v c u h.velocityPressure l
  have hg n i : HarmonicFields.BandLimited
      ((p.nextCoefficients v c u).gaussian l n i) (max v.residualBand 1) := by
    exact (((h.gaussian l n i).mono (le_max_left _ _)).add
      (((p.particularGaussianBlock_band v c u l).1 n i).mono (le_max_left _ _))).add
      ((((p.signed l).gaussianBlock_band p.strip (p.signedRequest v c u)).1 n i).mono (le_max_right _ _))
  have he := HarmonicResidual.residualBlock_band c (p.next v c u) (p.finalBlock v c u l)
    ((p.nextCoefficients v c u).gaussian l) 0 hb hg (fun _ _ => HarmonicResidual.band_zero _)
  have hn : max (max v.residualBand 1 + max v.residualBand 1) (max v.residualBand 1) =
      2 * max v.residualBand 1 := by omega
  simp only [hn] at he
  exact he

end CycleParameters

/-- The represented state and its literal coefficient data evolve together. -/
structure CycleState (ι : Type) where
  state : State CyclePoint
  coefficients : CycleCoefficients ι
  axisymmetricAlias : AxisymmetricAlias

namespace CycleState
variable {ι : Type}

noncomputable def step (p : CycleParameters ι) (c : Context CyclePoint) (u : CycleState ι) : CycleState ι where
  state := p.next u.coefficients c u.state
  coefficients := p.nextCoefficients u.coefficients c u.state
  axisymmetricAlias := p.nextAxisymmetricAlias u.coefficients c u.state u.axisymmetricAlias

noncomputable def iterate (p : ℕ → CycleParameters ι) (c : Context CyclePoint)
    (seed : CycleState ι) : ℕ → CycleState ι
  | 0 => seed
  | n + 1 => (iterate p c seed n).step (p n) c



theorem iterate_representation (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed : CycleState ι)
    (hseed : CycleRepresentation seed.coefficients seed.state seed.axisymmetricAlias)
    (hc : ∀ n l, let v := iterate p c seed n
      SameCarrier (v.coefficients.blocks l) ((p n).signedBlock v.coefficients c v.state l)) :
    ∀ n, let v := iterate p c seed n
      CycleRepresentation v.coefficients v.state v.axisymmetricAlias := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    exact (p n).next_representation (iterate p c seed n).coefficients c (iterate p c seed n).state ih (hc n)



end CycleState

end ActualRecurrence

section PeriodizedCurl
open Set Filter WeightedClasses HarmonicCalculus CorrectionState
open scoped ContDiff Topology InnerProductSpace

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem cylindricalDivergence_reindex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ) (Vr Vθ Vz : E → E) (a : E → ComplexVector) (x : D) :
    cylindricalDivergence (fun y => R (e y)) (StateReindex.vector e Vr)
      (StateReindex.vector e Vθ) (StateReindex.vector e Vz) (fun y => a (e y)) x =
      cylindricalDivergence R Vr Vθ Vz a (e x) := by
  simp only [cylindricalDivergence, StateReindex.along_pull_component]

namespace PeriodizedSignedParameters
variable {p : PeriodizedSignedParameters D I} {s : StripData D}
  {P : ℕ → D → ℝ} {κ β : ℝ} (h : p.NativeControl s P κ)
  (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)

theorem NativeControl.amplitude_cover (n : ℕ) (i : I) (x : D × ℝ)
    (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain) (hi : x ∈ h.cells.carrier n i) :
    x ∈ h.phasePatch n i ∨ ((p.copyData s request).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  rcases h.phase_cover n i x hx hi with hC | hcut | hmask
  · exact Or.inl hC
  · exact Or.inr ((p.copyData s request).localized_zero_germs hcut).1
  · exact Or.inr (localized_zero_of_mask request hmask).1

variable {h request}

theorem NativeDynamics.rawCurlData (d : NativeDynamics h request)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (G : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n x⟫_ℝ = 0) :
    LocalizedCurlRealization.RawData (p.copyData s request) (HarmonicWaveInteraction.productStrip s)
      p.directions h.phasePatch := by
  apply LocalizedCurlRealization.RawData.of_localClasses
    (fun n i => LocalizedCurlRealization.geometry_restrict (G n)
      ((HarmonicWaveInteraction.productStrip s).isOpen_domain.inter (d.open_patch n i)) inter_subset_left)
    (fun n i => ((d.angular i).phase_smooth n).mono inter_subset_left)
    (LocalizedWaveBounds.LocalClass.of_localJets
      (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (h.envelope_nonneg n x.1 hx)) (h.raw_jets request hR).1)
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    d.frequency_nonzero
  · intro n i x hx hzero
    change p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x = 0 at hzero
    have hh := h.normal_lower n i x hx.1 hx.2
    rw [hzero, norm_zero] at hh
    exact (not_le_of_gt h.lower_pos) hh
  · intro n i x hx
    exact LocalizedCurlRealization.signed_coefficients_tangent_at p.base
      (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i)
      (p.normalMotion i) (p.action i) p.column n (ht n i x hx.1 hx.2)

theorem NativeDynamics.full_divergence_zero (d : NativeDynamics h request) (i₀ : I)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (G : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n x⟫_ℝ = 0)
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (c : Context D) (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base)
    (n : ℕ) (x : D × ℝ) (hx : x.1 ∈ s.domain) :
    cylindricalDivergence (fun q => c.operators.radius q.1) (radialDirection c n)
      angularDirection (axialDirection c n) (fun q i => ((p.exactBlock s request).oscillation n q i : ℂ)) x = 0 := by
  have rd := d.rawCurlData hR G ht
  have hd := rd.common_divergence_zero h.cells h.cutoff_support (h.amplitude_cover request) n hx
  change cylindricalDivergence (p.base.radius n) _ _ _ _ x = 0 at hd
  have hs := rd.common_velocity_smooth h.cells h.cutoff_support (h.amplitude_cover request) n
  have hv i := ((contDiffOn_pi.mp hs i).contDiffAt
    ((HarmonicWaveInteraction.productStrip s).isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have he := ParticularWaveAssembly.divergence_map L (p.base.radius n) (p.directions.radialField n)
    (fun _ => p.directions.angular) (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n) hv
  rw [hd] at he
  have hθ : angularDirection (D := D) = fun _ => p.directions.angular := by rw [hm.angular]; rfl
  rw [(d.exact_represents i₀ hm.angular hkp).1, ← hm.radius, ← hm.radial, ← hm.axial, hθ]
  simp only [L, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    map_zero] at he
  exact he

theorem NativeDynamics.modeSolenoidal (d : NativeDynamics h request) (i₀ : I) (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (G : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      (p.base.radius n) (p.directions.radialField n) (fun _ => p.directions.angular)
      (p.directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
      ⟪p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x, p.fundamental i n x⟫_ℝ = 0)
    (hkp : ∀ n, p.base.frequency n * d.slope n = (p.angularFrequency n : ℝ))
    (hkpne : ∀ n, p.angularFrequency n ≠ 0)
    (c : Context D) (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) p.directions p.base) :
    HarmonicWaveInteraction.ModeSolenoidal s c (p.exactBlock s request) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full c (p.exactBlock s request)
  · intro n
    exact ((d.angular i₀).phase_smooth n).comp (SignedWaveUpdate.zeroSection (D := D)).contDiff.contDiffOn
      (fun _ hx => hx)
  · exact hkpne
  · exact HarmonicWaveInteraction.waveBounds_smooth (h.block_bounds hκ request hR).2.1 (p.exactBlock_zero s request)
  · exact d.full_divergence_zero i₀ hR G ht hkp c hm
end PeriodizedSignedParameters

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds LinearWaveBounds

namespace ParticularParameters
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {p : ParticularParameters Q} {s : StripData (Q × Plane)}
  {c : Context (Q × Plane)} {u : State (Q × Plane)} {b : HarmonicBlock (Q × Plane)}
  {G A : HarmonicResidual.BlockCoefficients (Q × Plane)} {j : ℤ}
  {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
  (h : p.NativeControl s c u b G A j W α κ)

theorem NativeControl.amplitude_cover (n : ℕ) (i : Frequency) (x : (Q × ℝ) × Plane)
    (hx : x ∈ (nativeStrip s).domain) (hi : x ∈ h.cells.carrier n i) :
    x ∈ h.phasePatch n i ∨ ((p.copyData c u b G A j).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0 :=
  (h.phase_cover n i x hx hi).imp_right (fun hz => (localized_zero_of_source_path hz).1)

variable {h}

theorem NativeDynamics.rawCurlData (d : NativeDynamics h) :
    LocalizedCurlRealization.RawData (p.copyData c u b G A j) (nativeStrip s)
      p.directions h.phasePatch := by
  apply LocalizedCurlRealization.RawData.of_localClasses
    (fun n i => LocalizedCurlRealization.geometry_restrict (d.background.cylindrical n)
      ((nativeStrip s).isOpen_domain.inter (d.open_patch n i)) inter_subset_left)
    (fun n _ => (d.background.phase_smooth n).mono inter_subset_left)
    (LocalizedWaveBounds.LocalClass.of_localJets
      (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (h.envelope_nonneg n x hx)) h.raw_jets.1)
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    d.frequency_nonzero
  · intro n i x hx hz
    have hh := h.normal_lower n i x hx.1 hx.2
    rw [← h.normal_match n i x hx.1 hx.2, hz, norm_zero] at hh
    exact (not_le_of_gt h.lower_pos) hh
  · intro n i x hx
    exact LocalizedCurlRealization.complexCopyCoefficients_tangent_at
      (p.copyData c u b G A j).background p.length_pos h.realControl h.imagControl n i hx.1 hx.2
      (h.normal_match n i x hx.1 hx.2)

theorem NativeDynamics.common_divergence_zero (d : NativeDynamics h) (n : ℕ)
    {x : (Q × ℝ) × Plane} (hx : x ∈ (nativeStrip s).domain) :
    cylindricalDivergence (p.background.radius n) (p.directions.radialField n)
      (fun _ => p.directions.angular) (p.directions.axialField (nativeStrip s) n)
      (vectorMode ((p.wave s c u b G A j).frequency n) ((p.wave s c u b G A j).phase n)
        ((p.wave s c u b G A j).amplitude n)) x = 0 :=
  d.rawCurlData.common_divergence_zero h.cells h.cutoff_support h.amplitude_cover n hx


theorem native_context_divergence (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane))
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (a : ((Q × ℝ) × Plane) → ComplexVector) (n : ℕ) (x : (Q × Plane) × ℝ) :
    cylindricalDivergence (fun y => c.operators.radius y.1) (radialDirection c n)
      angularDirection (axialDirection c n) (fun y => a (angleShuffle y)) x =
      cylindricalDivergence (p.background.radius n) (p.directions.radialField n)
        (fun _ => p.directions.angular) (p.directions.axialField (nativeStrip s) n) a (angleShuffle x) := by
  have hr : StateReindex.vector (angleShuffle (P := Q)) (p.directions.radialField n) =
      radialDirection c n :=
    (reindex_radialField (angleShuffle (P := Q)) p.directions n).symm.trans (hm.radial n)
  have hz : StateReindex.vector (angleShuffle (P := Q)) (p.directions.axialField (nativeStrip s) n) =
      axialDirection c n := by
    change reindexVector (angleShuffle (P := Q)) (p.directions.axialField (nativeStrip s) n) = _
    rw [← reindex_axialField (angleShuffle (P := Q)) p.directions (nativeStrip s) n, angleStrip_nativeStrip]
    exact hm.axial n
  have hθ : StateReindex.vector (angleShuffle (P := Q)) (fun _ => p.directions.angular) =
      angularDirection (D := Q × Plane) := by
    funext y
    exact hm.angular
  have hR : (fun y => p.background.radius n (angleShuffle y)) =
      (fun y : (Q × Plane) × ℝ => c.operators.radius y.1) := hm.radius n
  have he := cylindricalDivergence_reindex (angleShuffle (P := Q)) (p.background.radius n)
    (p.directions.radialField n) (fun _ => p.directions.angular)
    (p.directions.axialField (nativeStrip s) n) a x
  rw [hr, hz, hθ, hR] at he
  exact he


variable (p : ParticularParameters Q) (s : StripData (Q × Plane))
  (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
  (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (N : ℕ)
  (C : ∀ j ∈ modes N, p.NativeControl s c u b G A j W α κ)
  (dyn : ∀ j hj, NativeDynamics (C j hj))

include dyn in
theorem full_divergence_zero (hκ : κ ≤ 1 / 2)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (n : ℕ) (x : (Q × Plane) × ℝ) (hx : x.1 ∈ s.domain) :
    cylindricalDivergence (fun y => c.operators.radius y.1) (radialDirection c n)
      angularDirection (axialDirection c n)
      (fun y i => ((p.updateBlock s c u b G A N).oscillation n y i : ℂ)) x = 0 := by
  rw [(p.update_represents s c u b G A N C dyn).1]
  apply real_divergence_sum_zero (modes N)
  · intro j hj i
    exact (((dyn j hj).wave_smooth hκ n i).contDiffAt
      ((HarmonicResidual.liftDomain_open s.isOpen_domain).mem_nhds ⟨hx,trivial⟩)).differentiableAt (by simp)
  · intro j hj
    rw [p.native_context_divergence s c hm]
    exact (dyn j hj).common_divergence_zero n hx

include dyn in
theorem modeSolenoidal (hκ : κ ≤ 1 / 2)
    (hW : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x)
    (hm : WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle p.directions) (reindexCoefficients angleShuffle p.background))
    (hphase : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain)
    (hkp : ∀ n, b.angularFrequency n ≠ 0) :
    HarmonicWaveInteraction.ModeSolenoidal s c (p.updateBlock s c u b G A N) := by
  apply HarmonicWaveInteraction.modeSolenoidal_of_full c (p.updateBlock s c u b G A N) hphase hkp
  · exact HarmonicWaveInteraction.waveBounds_smooth (p.assembled_bounds s c u b G A N C hW hκ).1
      (assembledBlock_zero _ _ _ _ _ _).1
  · exact p.full_divergence_zero s c u b G A N C dyn hκ hm

end ParticularParameters

end PeriodizedCurl

section UniformCycleGains
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState
open LabelSumBounds UniformHarmonicInteraction
open scoped ContDiff Topology
variable {D ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Coefficient extraction preserves constants chosen before the spatial
label. The identity concerns the actual linear field and retained Gaussian. -/
theorem linearGoodBlock_cancel_uniform {s : StripData D} {P : ι → ℕ → D → ℝ} {γ : ℝ}
    (c : Context D) (a b source good : ι → HarmonicBlock D)
    (g : ι → HarmonicResidual.BlockCoefficients D)
    (hr : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hz : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).axial s.domain)
    (hB : SmoothTriple s.domain c.base)
    (hb : ∀ l n i, HarmonicResidual.SmoothCoefficients s.domain ((b l).velocity n i))
    (hp : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((b l).pressure n))
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hs : ∀ l n i, HarmonicFields.ConjugateSymmetric ((source l).velocity n i))
    (hg : ∀ l n i, HarmonicFields.ConjugateSymmetric ((good l).velocity n i))
    (hgood : UniformVelocity s P γ good)
    (hcancel : ∀ l n x, x ∈ s.domain → ∀ θ i, linearBlockField c (a l) (b l) n (x,θ) i +
      (HarmonicWaveInteraction.withCarrier (a l) (source l)).oscillation n (x,θ) i =
      (HarmonicWaveInteraction.withCarrier (a l) (good l)).oscillation n (x,θ) i +
      (HarmonicFields.field (g l n i) ((a l).frequency n) ((a l).phase n)
        ((a l).angularFrequency n) (x,θ)).re) :
    ∀ i j, j ≠ 0 → UniformWaveClass s P γ (fun l n x => (source l).velocity n i j x +
      (HarmonicWaveInteraction.linearGoodBlock c (a l) (b l) (g l)).velocity n i j x) := by
  intro i j hj
  apply (hgood i j hj).congr
  intro l n x hx
  exact (linearGoodBlock_cancel s.isOpen_domain c (a l) (b l) (source l) (good l) (g l) n
    (hr n) (hz n) (fun k => HarmonicMeanInteraction.tripleField_smooth hB n k)
    (hb l n) (hp l n) (hΦ l n) (hkp l n) (hs l n) (hg l n) hx j hj i
    (fun θ => hcancel l n x hx θ i)).symm

/-- The exact nonlinear update preserves the joint label/band estimate.
All three wave products and the support-local mean interaction are retained. -/
theorem waveStage_residual_uniform {s : StripData D} {P : ι → ℕ → D → ℝ}
    {κ α β H γ : ℝ} {C : ℕ → ι → Set D}
    (c : Context D) (ho : OperatorBounds s c.operators κ) (hκ : κ ≤ 1 / 2)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (hmean : v.mean = u.mean) (hm : IncrementBounds s H u.mean)
    (hbase : SmoothTriple s.domain c.base)
    (a b : ι → HarmonicBlock D) {M N : ℕ}
    (ha : UniformVelocity s P α a) (hb : UniformVelocity s P β b)
    (ha0 : ∀ l, HarmonicWaveInteraction.ZeroMode (a l))
    (hb0 : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hM : ∀ l, (a l).BandLimited M) (hN : ∀ l, (b l).BandLimited N)
    (hΦ : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hda : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (a l))
    (hdb : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (HarmonicWaveInteraction.withCarrier (a l) (b l)))
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (a l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s C (-(1/2)) (fun n l _ => (a l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s C (-(1/2)) (fun n l _ => ((a l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (b l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hpa : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((a l).pressure n))
    (hpb : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((b l).pressure n))
    (G g A₀ A₁ : ι → HarmonicResidual.BlockCoefficients D)
    (hA : ∀ l n i, HarmonicFields.BandLimited (A₁ l n i - A₀ l n i) 0)
    (hlinear : ∀ i j, j ≠ 0 → UniformWaveClass s P γ (fun l n x =>
      (HarmonicResidual.residualBlock c u (a l) (G l) (A₀ l)).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c (a l) (b l) (g l)).velocity n i j x))
    (hγm : γ ≤ β + H - 1/2) (hγc : γ ≤ α + β - κ) (hγs : γ ≤ 2*β - κ) :
    UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c v
      (HarmonicWaveInteraction.addBlock (a l) (b l)) (G l + g l) (A₁ l)) := by
  have hca l := block_waveBounds_all (a l) (waveBounds_each ha l) (ha0 l) (hP0 l)
  have hcb l := block_waveBounds_all (b l) (waveBounds_each hb l) (hb0 l) (hP0 l)
  intro i j hj
  have hnon := UniformHarmonicInteraction.interactionBlock_uniform c ho hκ hR hm ha hb ha0 hb0 hM hN
    hΦ hk hda hdb hNormal hFreq hAng hz hP0 hP1 hj i
  apply ((hlinear i j hj).add (hnon.mono_exponent (le_min hγm (le_min hγc hγs)))).congr
  intro l n x hx
  have hr : ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
    contDiffOn_const.add ((contDiffOn_const.mul (ho.radialProfile.smooth 0)).smul contDiffOn_const)
  have he := HarmonicWaveInteraction.residualBlock_wave_update_split s.isOpen_domain c u v hmean
    (a l) (b l) (G l) (g l) (A₀ l) (A₁ l) (hA l) n hr contDiffOn_const (hΦ l n) (hkp l n)
    (fun k => HarmonicMeanInteraction.tripleField_smooth hbase n k)
    (fun k => HarmonicMeanInteraction.tripleField_smooth hm.smooth n k)
    (fun k m => (hca l k m).smooth n) (fun k m => (hcb l k m).smooth n) (hpa l n) (hpb l n) hx j i
  change _ = _ at he
  linear_combination -he

/-- The unchanged oscillation retains a uniform residual estimate after
an actual mean increment; pressure recomputation and axisymmetric aliases
may change freely. -/
theorem meanStage_residual_uniform {s : StripData D} {P : ι → ℕ → D → ℝ}
    {κ α H γ : ℝ} {C : ℕ → ι → Set D}
    (c : Context D) (ho : OperatorBounds s c.operators κ) (hκ : κ ≤ 1/2)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u v : State D) (h : Triple D) (he : v.mean = updated u.mean h)
    (hbase : SmoothTriple s.domain c.base) (hm : SmoothTriple s.domain u.mean)
    (hh : IncrementBounds s H h) (b : ι → HarmonicBlock D) (hb : UniformVelocity s P α b)
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (b l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s C (-(1/2)) (fun n l _ => (b l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s C (-(1/2)) (fun n l _ => ((b l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (b l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (G A₀ A₁ : ι → HarmonicResidual.BlockCoefficients D)
    (hA : ∀ l n i, HarmonicFields.BandLimited (A₁ l n i - A₀ l n i) 0)
    (hold : UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A₀ l)))
    (hγ : γ ≤ α + H - 1/2) :
    UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c v (b l) (G l) (A₁ l)) := by
  intro i j hj
  have hdelta := LocalizedMeanInteraction.uniform_realMeanCross_class c ho hκ hR hh hb
    hNormal hFreq hAng hz hj i
  apply ((hold i j hj).add (hdelta.mono_exponent hγ)).congr
  intro l n x hx
  have hm' := (s.isOpen_domain.mem_nhds hx)
  have hd := HarmonicMeanInteraction.residualBlock_axisymmetric_alias_update c u v h he (b l)
    (G l) (A₀ l) (A₁ l) (hA l) n
    (fun k => ((HarmonicMeanInteraction.tripleField_smooth hbase n k).contDiffAt hm').differentiableAt (by simp))
    (fun k => ((HarmonicMeanInteraction.tripleField_smooth hm n k).contDiffAt hm').differentiableAt (by simp))
    (fun k => ((HarmonicMeanInteraction.tripleField_smooth hh.smooth n k).contDiffAt hm').differentiableAt (by simp))
    hj i
  change _ = _ at hd
  linear_combination -hd

end UniformCycleGains

section ConstructedWaveGains
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState
open HarmonicCalculus ParticularWaveAssembly ParticularWaveBounds
open scoped ContDiff Topology InnerProductSpace
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem meanIncrement_of_cumulative {s : StripData D} {m : Triple D}
    (h : MeanIncrementBounds.CumulativeBounds s m) : IncrementBounds s (9/10) m :=
  ⟨by convert! h.radial using 1; norm_num, h.angular, h.axial⟩

theorem pressureBounds_smooth {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {b : HarmonicBlock D} (h : b.PressureBounds s P α) (hz : ∀ n, b.pressure n 0 = 0)
    (n : ℕ) : HarmonicResidual.SmoothCoefficients s.domain (b.pressure n) := by
  intro j
  by_cases hj : j = 0
  · subst j
    rw [hz]
    exact contDiffOn_const
  · exact (h j hj).smooth n

theorem operator_radial_smooth {s : StripData D} {κ : ℝ} {c : Context D}
    (ho : OperatorBounds s c.operators κ) (n : ℕ) :
    ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain :=
  contDiffOn_const.add ((contDiffOn_const.mul (ho.radialProfile.smooth 0)).smul contDiffOn_const)

namespace ParticularParameters
open TorusInverse
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]


end ParticularParameters

namespace PeriodizedSignedParameters
variable {I : Type} {p : PeriodizedSignedParameters D I} {s : StripData D}
  {P : ℕ → D → ℝ} {B κ : ℝ} {h : p.NativeControl s P κ}
  {request : ℕ → D × ℝ → SignedWaveUpdate.Vec2}


end PeriodizedSignedParameters

end ConstructedWaveGains

section ConstructedWaveMeans
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest
open scoped ContDiff BigOperators Topology

section CovarianceAssembly
variable {D ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem assembledCovarianceIncrement_mem
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → LabelSumBounds.WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (a b : ι → HarmonicBlock D) (N : ℕ)
    (hNa : ∀ l, (a l).BandLimited N) (hNb : ∀ l, (b l).BandLimited N)
    (hcarrier : ∀ l, LabelSumBounds.SameCarrier (a l) (b l))
    (ha : UniformHarmonicInteraction.UniformVelocity s P α a)
    (hb : UniformHarmonicInteraction.UniformVelocity s P β b)
    (ha0 : ∀ l, HarmonicWaveInteraction.ZeroMode (a l))
    (hb0 : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hsu : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (a l).oscillation))
    (hsv : LabelSumBounds.SupportedOscillations sys label χ Y s.domain (fun l => (b l).oscillation))
    (u : State D)
    (hrep : u.oscillation = LabelSumBounds.fieldSum labels (fun l => (a l).oscillation)) :
    SignedMeanGain.TensorClass s (α + β)
      (SignedMeanGain.covarianceIncrement u.oscillation
        (LabelSumBounds.fieldSum labels (fun l => (b l).oscillation))) := by
  rw [hrep]
  exact fun i j => LabelSumBounds.harmonic_covariance_increment_sum_mem hαβ labels label hinj hlevel
    χ hχ Y a b N hNa hNb hcarrier
    (LabelSumBounds.uniform_coefficients_of_nonzero a ha ha0 hP0)
    (LabelSumBounds.uniform_coefficients_of_nonzero b hb hb0 hP0) hP0 hP1 hkp hsu hsv i j

end CovarianceAssembly

section WavePressureDebt
variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)
local notation "st" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL
local notation "ss" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL
variable (c : Context Point) (u : State Point) (w : Oscillation Point)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : GaugeDebtIncrement.RegularTriple U g.radial.inner g.radial.outer u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular U g.radial.inner g.radial.outer (u.covariance i j))
    (hX : ∀ i j, GaugeDebtIncrement.Regular U g.radial.inner g.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    {κ α : ℝ} (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL) c.operators κ)
    (hcX : SignedMeanGain.TensorClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL) α (SignedMeanGain.covarianceIncrement u.oscillation w))

include hd hell hop hbase hm hW hX ho hcX in
theorem gaugeWaveStage_pressure_from_covariance
    (hfixed : (reconstructState g c u).pressure = u.pressure) :
    MeanClass st (α-κ) (SignedMeanGain.pressureChange g c u w q gaussian) := by
  let v := SignedMeanGain.waveStage g c u w q gaussian
  have hmu := GaugeDebtIncrement.waveStage_mean_regular U g c u w q gaussian hm
  have hvW := GaugeDebtIncrement.waveStage_covariance_regular U g c u w q gaussian hW hX
  have hgu := hm.gr ha g.radial.inner_lt_outer hbase hop u.covariance hW
  have hgv := hmu.gr ha g.radial.inner_lt_outer hbase hop v.covariance hvW
  have hgr : MeanClass st (α-κ) (v.gr c - u.gr c) := by
    apply class_congr (SignedMeanGain.radialCovarianceChange_mem ho hcX)
    intro n x hx
    exact GaugeDebtIncrement.waveStage_gr_agree U ha g.radial.inner_lt_outer g c u w q gaussian
      hop hbase hm hW hX n hx.1
  have hp := reconstructState_pressure_change_class U g ha hd hcL hcR ε L hε hεone hL hell
    c v u hgv.smooth hgu.smooth hgv.supported hgu.supported hgr
  simp only [hfixed] at hp
  exact hp

include hd hell hop hbase hm hW hX ho hcX in
theorem gaugeWaveStage_mean_from_covariance
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (hb : BaseBounds st c.base) (hu : CorrectionState.CumulativeBounds st u)
    (hα : 9/10 ≤ α-κ) {β : ℝ} (hβ : β ≤ α-κ)
    (hθ : MeanClass st β (u.thetaResidual c))
    (hz : MeanClass st β (u.axialResidual c))
    (hdebt : ∀ i : Fin 3, UnweightedClass ss β (fun n x => debt c u n x i)) :
    let v := SignedMeanGain.waveStage g c u w q gaussian
    MeanClass st (α-κ) (SignedMeanGain.pressureChange g c u w q gaussian) ∧
    CorrectionState.CumulativeBounds st v ∧
    MeanClass st β (v.thetaResidual c) ∧
    MeanClass st β (v.axialResidual c) ∧
    (∀ i : Fin 3, UnweightedClass ss β (fun n x => debt c v n x i)) := by
  let v := SignedMeanGain.waveStage g c u w q gaussian
  have hp := gaugeWaveStage_pressure_from_covariance U g ha hd hcL hcR ε L hε hεone hL hell
    c u w q gaussian hop hbase hm hW hX ho hcX hfixed
  have hWs : ∀ i j, SmoothOn (st).domain (u.covariance i j) :=
    fun i j n => ((hW i j).smooth n).mono (fun _ hx => hx.1)
  have ht : MeanClass st (α-κ) (v.thetaResidual c - u.thetaResidual c) := by
    apply class_congr (SignedMeanGain.thetaCovarianceChange_mem ho hcX)
    exact SignedMeanGain.waveStage_theta_change (st).isOpen_domain g c u w q gaussian
      hb.smooth hu.velocity.smooth hWs (fun i j => (hcX i j).smooth)
  have hz' : MeanClass st (α-κ) (v.axialResidual c - u.axialResidual c) := by
    apply class_congr ((SignedMeanGain.axialCovarianceChange_mem ho hcX).add
      ((ho.dz hp).mono_exponent (by linarith)))
    exact SignedMeanGain.waveStage_axial_change (st).isOpen_domain g c u w q gaussian
      hb.smooth hu.velocity.smooth hWs (fun i j => (hcX i j).smooth) hu.pressure.smooth hp.smooth
  refine ⟨hp, gaugeWaveStage_cumulative g c u w q ⟨0,gaussian,0⟩ hu hp hα, ?_, ?_, ?_⟩
  · apply class_congr (hθ.add (ht.mono_exponent hβ))
    intro n x hx
    change v.thetaResidual c n x = u.thetaResidual c n x + (v.thetaResidual c n x - u.thetaResidual c n x)
    ring
  · apply class_congr (hz.add (hz'.mono_exponent hβ))
    intro n x hx
    change v.axialResidual c n x = u.axialResidual c n x + (v.axialResidual c n x - u.axialResidual c n x)
    ring
  · exact GaugeDebtIncrement.debt_mem_after_change ss c u v le_rfl hβ hdebt
      (GaugeDebtIncrement.waveStage_debt_change_mem U ha g.radial.inner_lt_outer hcL hcR
        ε L hε hεone hL g c u w q gaussian hop hbase hm hW hX ho hcX)

end WavePressureDebt

end ConstructedWaveMeans

section CycleSignedFamily
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState
open scoped ContDiff Topology BigOperators

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

noncomputable def beforeSignedBlock (l : ι) : HarmonicBlock CyclePoint :=
  addBlock (v.blocks l) (p.particularBlock v c u l)

noncomputable def signedTangent (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).tangentBlock p.strip (p.signedRequest v c u)

noncomputable def signedCurl (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).curlBlock p.strip (p.signedRequest v c u)

theorem beforeSignedBlock_represents {axis : AxisymmetricAlias}
    (hrep : CycleRepresentation v u axis) :
    (p.afterParticular v c u).oscillation =
      LabelSumBounds.fieldSum v.labels (fun l => (p.beforeSignedBlock v c u l).oscillation) := by
  funext n x i
  change u.oscillation n x i + p.particularVelocity v c u n x i = _
  rw [hrep.velocity n x i]
  simp only [beforeSignedBlock, addBlock_oscillation _ _ (p.particular_carrier v c u _),
    LabelSumBounds.fieldSum, particularVelocity, Pi.add_apply, Finset.sum_add_distrib]

theorem signedVelocity_split :
    p.signedVelocity v c u =
      LabelSumBounds.fieldSum v.labels (fun l => (p.signedTangent v c u l).oscillation) +
      LabelSumBounds.fieldSum v.labels (fun l => (p.signedCurl v c u l).oscillation) := by
  funext n x i
  simp only [signedVelocity, signedBlock, signedTangent, signedCurl,
    PeriodizedSignedParameters.exactBlock_split, LabelSumBounds.fieldSum,
    Pi.add_apply, Finset.sum_add_distrib]

private theorem block_band_mono {b : HarmonicBlock CyclePoint} {N M : ℕ}
    (h : b.BandLimited N) (hle : N ≤ M) : b.BandLimited M :=
  ⟨fun n i => (h.1 n i).mono hle, fun n => (h.2 n).mono hle⟩

/-- The family in the signed covariance identity is computed from the
current cycle, including its actual particular increment and signed curl. -/
noncomputable def signedFamily
    (primary : ι → HarmonicBlock CyclePoint) (P : ι → ℕ → CyclePoint → ℝ)
    {σ κ : ℝ} (hσ : 1/5 ≤ σ) (N : ℕ)
    (hprimary : ∀ l, (primary l).BandLimited N) (hband : CoefficientBands v)
    (hcp : ∀ l, SameCarrier (v.blocks l) (primary l))
    (hcs : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (17/25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (htangent : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ-κ)
      (fun l n x => (p.signedTangent v c u l).velocity n i j x))
    (hcurl : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1+σ-2*κ)
      (fun l n x => (p.signedCurl v c u l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ p.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ p.strip.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0) :
    LabelSumBounds.SignedFamily p.strip P (1/2) (17/25) (1/2+σ-κ) (1+σ-2*κ) where
  primary := primary
  old := p.beforeSignedBlock v c u
  tangent := p.signedTangent v c u
  curl := p.signedCurl v c u
  bandwidth := max (max N v.residualBand) 1
  primary_band l := block_band_mono (hprimary l) ((le_max_left _ _).trans (le_max_left _ _))
  old_band l := block_band_mono
    (show (p.beforeSignedBlock v c u l).BandLimited v.residualBand from by
      have hb := addBlock_band (hband.velocityPressure l) (p.particularBlock_band v c u l)
      simp only [max_self] at hb
      exact hb)
    ((le_max_right _ _).trans (le_max_left _ _))
  tangent_band l := block_band_mono ((p.signed l).tangentBlock_band _ _) (le_max_right _ _)
  curl_band l := block_band_mono
    (show (p.signedCurl v c u l).BandLimited 1 from by
      have hb := subBlock_band ((p.signed l).exactBlock_band p.strip (p.signedRequest v c u))
        ((p.signed l).tangentBlock_band p.strip (p.signedRequest v c u))
      simp only [max_self] at hb
      exact hb) (le_max_right _ _)
  primary_carrier l := ⟨(hcp l).frequency, (hcp l).phase, (hcp l).angular⟩
  tangent_carrier l := ⟨(hcs l).frequency, (hcs l).phase, (hcs l).angular⟩
  curl_carrier l := ⟨(hcs l).frequency, (hcs l).phase, (hcs l).angular⟩
  old_bounds i j := (hold i j).add ((hpart i j).mono_exponent (by linarith))
  difference_bounds i j := by
    apply ((hdiff i j).add ((hpart i j).mono_exponent (by linarith))).congr
    intro l n x hx
    change (v.blocks l).velocity n i j x - (primary l).velocity n i j x +
      (p.particularBlock v c u l).velocity n i j x =
      (v.blocks l).velocity n i j x + (p.particularBlock v c u l).velocity n i j x -
        (primary l).velocity n i j x
    ring
  tangent_bounds := htangent
  curl_bounds := hcurl
  envelope_nonneg := hP0
  envelope_le_one := hP1
  angular_ne_zero := hkp

end CycleParameters

end CycleSignedFamily

end NavierStokes.CorrectionStep
