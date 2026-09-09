import NavierStokes.ActualParticularStageControls
import NavierStokes.PhysicalResidualNaturality
import NavierStokes.ActualInitialCoherence
import NavierStokes.ParticularWaveBounds

/-!
# Native reference data from the actual common-cover state

The current state at the reference band still uses that band's common cover.
The reference Volterra geometry, on the other hand, uses the native cover.
This file changes the free auxiliary coordinate before forming the reference
source.  The change acts on the entire current residual, including its
Gaussian and alias inputs.
-/

noncomputable section

namespace NavierStokes.ActualReferenceRebase

open Set Function Filter WeightedClasses CorrectionState HarmonicFields HarmonicCalculus
open CommonCoverSolve TorusInverse PhysicalParticularWave
open scoped ContDiff Topology BigOperators ComplexConjugate


/-! ## Pullback of the actual state through an invertible linear map -/

section Pullback

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def pullField (e : D ≃L[ℝ] E) (f : MeanIncrementBounds.Field E) :
    MeanIncrementBounds.Field D := fun n x => f n (e x)

noncomputable def pullTriple (e : D ≃L[ℝ] E) (v : MeanIncrementBounds.Triple E) :
    MeanIncrementBounds.Triple D :=
  ⟨pullField e v.radial, pullField e v.angular, pullField e v.axial⟩

noncomputable def pullOperators (e : D ≃L[ℝ] E) (o : MeanIncrementBounds.Operators E) :
    MeanIncrementBounds.Operators D where
  epsilon := o.epsilon
  radialFrequency := o.radialFrequency
  fastCoefficient := o.fastCoefficient
  radius x := o.radius (e x)
  radialProfile x := o.radialProfile (e x)
  eR := e.symm o.eR
  eZ := e.symm o.eZ
  eT := e.symm o.eT
  vR := e.symm o.vR
  vT := e.symm o.vT

noncomputable def pullContext (e : D ≃L[ℝ] E) (c : Context E) : Context D where
  operators := pullOperators e c.operators
  base := pullTriple e c.base
  virtualTheta := pullField e c.virtualTheta
  virtualAxial := pullField e c.virtualAxial

noncomputable def pullOscillation (e : D ≃L[ℝ] E) (u : Oscillation E) : Oscillation D :=
  fun n x => u n (e x.1, x.2)

noncomputable def pullErrors (e : D ≃L[ℝ] E) (u : ExcludedErrors E) : ExcludedErrors D :=
  ⟨pullOscillation e u.base, pullOscillation e u.gaussian, pullOscillation e u.aliasError⟩

noncomputable def pullState (e : D ≃L[ℝ] E) (u : State E) : State D where
  mean := pullTriple e u.mean
  pressure := pullField e u.pressure
  oscillation := pullOscillation e u.oscillation
  oscillatoryPressure n x := u.oscillatoryPressure n (e x.1, x.2)
  errors := pullErrors e u.errors

noncomputable def pullCoefficients (e : D ≃L[ℝ] E) (a : Coefficients E) : Coefficients D :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (fun f : E → ℂ => fun x => f (e x)) rfl a.coeff)


theorem pullCoefficients_support (e : D ≃L[ℝ] E) (a : Coefficients E) :
    (pullCoefficients e a).support = a.support := by
  ext j
  simp only [Finsupp.mem_support_iff]
  apply not_congr
  constructor
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact congrFun h x
  · intro h
    funext x
    exact congrFun h (e x)


noncomputable def pullBlock (e : D ≃L[ℝ] E) (b : HarmonicBlock E) : HarmonicBlock D where
  velocity n i := pullCoefficients e (b.velocity n i)
  pressure n := pullCoefficients e (b.pressure n)
  frequency := b.frequency
  phase n x := b.phase n (e x)
  angularFrequency := b.angularFrequency

noncomputable def pullBlockCoefficients (e : D ≃L[ℝ] E)
    (a : HarmonicResidual.BlockCoefficients E) : HarmonicResidual.BlockCoefficients D :=
  fun n i => pullCoefficients e (a n i)



noncomputable def pullFrame (e : D ≃L[ℝ] E) (g : HarmonicResidual.Frame E) :
    HarmonicResidual.Frame D where
  radius x := g.radius (e x)
  radial x := e.symm (g.radial (e x))
  axial x := e.symm (g.axial (e x))
  time x := e.symm (g.time (e x))
  viscosity := g.viscosity




noncomputable def pullStrip (e : D ≃L[ℝ] E) (s : StripData E) : StripData D where
  domain := e ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage e.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta x := s.delta (e x)
  delta_pos x hx := s.delta_pos (e x) hx
  zeta x := s.zeta (e x)
  zeta_smooth := s.zeta_smooth.comp e.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg x hx := s.zeta_nonneg (e x) hx

noncomputable def pullWave (e : D ≃L[ℝ] E) (a : LinearWaveBounds.WaveCoefficients E) :
    LinearWaveBounds.WaveCoefficients D where
  radius n x := a.radius n (e x)
  radialBase n x := a.radialBase n (e x)
  frequencyBase n x := a.frequencyBase n (e x)
  axialBase n x := a.axialBase n (e x)
  phase n x := a.phase n (e x)
  amplitude n x := a.amplitude n (e x)
  pressure n x := a.pressure n (e x)
  frequency := a.frequency

noncomputable def pullDirections (e : D ≃L[ℝ] E) (d : LinearWaveBounds.GraphDirections E) :
    LinearWaveBounds.GraphDirections D where
  radial := e.symm d.radial
  auxiliary := e.symm d.auxiliary
  axial := e.symm d.axial
  angular := e.symm d.angular
  slow := e.symm d.slow
  fast := e.symm d.fast
  radialScale := d.radialScale
  fastScale := d.fastScale
  radialProfile x := d.radialProfile (e x)



end Pullback

/-! ## A separate, genuine native-reference assembly -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def inverseCover (k : ℕ) : (P × Plane) ≃L[ℝ] (P × Plane) :=
  (ContinuousLinearEquiv.refl ℝ P).prodCongr (coverPower k).symm



/-- All fields, all directions and the complete source are expressed in the
native fast coordinate.  This assembly is only a reference view; the target
solver keeps its original common-cover data. -/
noncomputable def rebaseAssembly (D : ParticularWaveAssembly.AssemblyData P) (k : ℕ) :
    ParticularWaveAssembly.AssemblyData P where
  reference := D.reference
  charts := ⟨fun _ => id, fun _ => 0, fun _ => 1⟩
  context := pullContext (inverseCover k) D.context
  state := pullState (inverseCover k) D.state
  carrierBlock := pullBlock (inverseCover k) D.carrierBlock
  gaussianInput := pullBlockCoefficients (inverseCover k) D.gaussianInput
  aliasInput := pullBlockCoefficients (inverseCover k) D.aliasInput
  background := pullWave (inverseCover k) D.background
  copy := D.copy
  strip := pullStrip (inverseCover k) D.strip
  directions := pullDirections (inverseCover k) D.directions



/-! ## Binding to the one actual initializer choice and current cycle state -/

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}








/-! The native reference has its own actual frame and phase. -/

@[simp] theorem associatedToLift_symm_apply (z : PhysicalResidualNaturality.Lift) :
    PhysicalResidualNaturality.associatedToLift.symm z =
      ((z.1, (z.2.1.2, z.2.1.1)), z.2.2) := rfl

@[simp] theorem cycleAssoc_apply (z : CorrectionStep.CyclePoint) :
    CorrectionStep.cycleAssoc z = ((z.1, z.2.1), z.2.2) := rfl

@[simp] theorem cycleAssoc_symm_apply (z : PhysicalResidualNaturality.Associated) :
    CorrectionStep.cycleAssoc.symm z = (z.1.1, (z.1.2, z.2)) := rfl

theorem inverseCover_associatedFrame (h Q : ℝ) (i k : ℕ) :
    pullFrame (inverseCover k) (PhysicalResidualNaturality.associatedFrame h Q i) =
      PhysicalResidualNaturality.associatedFrame h Q (i+k) := by
  unfold pullFrame PhysicalResidualNaturality.associatedFrame StateReindex.frame
    StateReindex.vector ParticularWaveBounds.reindexVector PhysicalResidualNaturality.commonFrame
  congr 1
  · funext x
    change ((1, (0, 0)), coverPower k
      ((ChartScales.Lambda ^ i * Q ^ (ChartScales.radialExponent h / 2) *
        GraphCalculus.radialSpeed (ChartScales.radialExponent h) x.1.1) •
          PhysicalGraphBounds.radialDirection)) = _
    rw [map_smul, coverPower_apply, PhysicalGraphBounds.cover_pow_radialDirection, smul_smul]
    congr 2
    simp only [ PhysicalResidualBridge.commonGraph,
      PhysicalResidualNaturality.associatedToLift_apply]
    rw [pow_add]
    ring
  · funext x
    change ((0, (0, Q ^ h)), coverPower k 0) = _
    rw [map_zero]
    rfl
  · funext x
    change ((0, (-(Q ^ h), 0)), coverPower k
      ((ChartScales.Tg ^ i * Q ^ (1+h)) • PhysicalGraphBounds.timeDirection)) = _
    rw [map_smul, coverPower_apply, PhysicalGraphBounds.cover_pow_timeDirection, smul_smul]
    congr 2
    simp only [PhysicalResidualBridge.commonGraph]
    rw [pow_add]
    ring

theorem associatedContext_frame (B n : ℕ) :
    HarmonicResidual.contextFrame (ActualParticularStageControls.associatedContext (B := B)) n =
      PhysicalResidualNaturality.associatedFrame h (ChartScales.Q n) (CommonWindow.index h n) := by
  rw [ActualParticularStageControls.associatedContext, StateReindex.contextFrame_pull]
  unfold StateReindex.frame StateReindex.vector ParticularWaveBounds.reindexVector
    PhysicalResidualNaturality.associatedFrame PhysicalResidualNaturality.commonFrame
  congr 1
  · funext x
    simp [HarmonicResidual.contextFrame, commonContext, CommonBaseContext.context,
      CommonBaseContext.operators, CorrectionState.graphOperators, CommonBaseContext.reconstruction,
      CommonBaseContext.radialFrequency, PhysicalResidualBridge.ScaledGraph.radial,
      PhysicalResidualBridge.commonGraph, GraphCalculus.radialSpeed, RadialPullback.radialJacobian, PhysicalGraphBounds.radialDirection, TorusInverse.vector, StateReindex.vector, ParticularWaveBounds.reindexVector,
      PhysicalResidualNaturality.associatedToLift_apply]
    rfl
  · funext x
    simp [HarmonicResidual.contextFrame, commonContext, CommonBaseContext.context,
      CommonBaseContext.operators, CorrectionState.graphOperators, ChartScales.epsilon,
      PhysicalResidualBridge.ScaledGraph.axial, PhysicalResidualBridge.commonGraph, StateReindex.vector, ParticularWaveBounds.reindexVector]
  · funext x
    simp [HarmonicResidual.contextFrame, commonContext, CommonBaseContext.context,
      CommonBaseContext.operators, CorrectionState.graphOperators, CommonBaseContext.fastCoefficient,
      PhysicalResidualBridge.ScaledGraph.temporal, PhysicalResidualBridge.commonGraph, StateReindex.vector, ParticularWaveBounds.reindexVector,
      PhysicalGraphBounds.timeDirection, TorusInverse.vector, ChartScales.epsilon]




theorem ratioPower_self {Q : ℝ} (hQ : 0 < Q) (a : ℝ) : ratioPower Q Q a = 1 :=
  div_self (Real.rpow_pos_of_pos hQ a).ne'



/-! ## Dependence of a copy solve on one complete parameter fiber -/

section FiberLocality

open ParticularWaveBounds

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem real_copySolve_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q,Y) = g (q,Y)) (copy : Frequency) (Y : Plane) :
    (realData t f).linearData.copySolve G hab copy (q,Y) =
      (realData t g).linearData.copySolve G hab copy (q,Y) := by
  apply CopySolveCompatibility.anchoredSolve_eq_of_sameInputs
  refine ⟨fun _ => rfl, ?_⟩
  intro z Z
  change t.linearData.forcingMap (q,z) (realPart (f (q,Z))) =
    t.linearData.forcingMap (q,z) (realPart (g (q,Z)))
  rw [hf Z]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem imag_copySolve_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q,Y) = g (q,Y)) (copy : Frequency) (Y : Plane) :
    (imagData t f).linearData.copySolve G hab copy (q,Y) =
      (imagData t g).linearData.copySolve G hab copy (q,Y) := by
  apply CopySolveCompatibility.anchoredSolve_eq_of_sameInputs
  refine ⟨fun _ => rfl, ?_⟩
  intro z Z
  change t.linearData.forcingMap (q,z) (imagPart (f (q,Z))) =
    t.linearData.forcingMap (q,z) (imagPart (g (q,Z)))
  rw [hf Z]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyVelocity_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q,Y) = g (q,Y)) (copy : Frequency) (Y : Plane) :
    complexCopyVelocity t f G hab copy (q,Y) = complexCopyVelocity t g G hab copy (q,Y) := by
  simp only [complexCopyVelocity, copyVelocity, real_copySolve_source_congr t f g G hab q hf,
    imag_copySolve_source_congr t f g G hab q hf]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem copyPressure_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (q : Q) (hf : ∀ Y, f (q,Y) = g (q,Y)) (copy : Frequency) (K : ℝ) (Y : Plane) :
    complexCopyPressure t f G hab copy K (q,Y) = complexCopyPressure t g G hab copy K (q,Y) := by
  simp only [complexCopyPressure, copyPressure, copyPressureReal,
    real_copySolve_source_congr t f g G hab q hf,
    imag_copySolve_source_congr t f g G hab q hf]
  simp only [realData, imagData, hf Y]

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonVelocity_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (cutoff : Plane → ℝ) (q : Q) (hf : ∀ Y, f (q,Y) = g (q,Y)) (Y : Plane) :
    ParticularWaveBounds.commonVelocity t f G hab cutoff (q,Y) =
      ParticularWaveBounds.commonVelocity t g G hab cutoff (q,Y) := by
  apply tsum_congr
  intro copy
  exact congrArg (fun v => cutoff (G.coordinates copy Y) • v)
    (copyVelocity_source_congr t f g G hab q hf copy Y)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem commonPressure_source_congr (t : TangentData Q ProblemStatement.Space)
    (f g : Q × Plane → ComplexVector) (G : Geometry) {a b : ℝ} (hab : a ≤ b)
    (cutoff : Plane → ℝ) (K : ℝ) (q : Q) (hf : ∀ Y, f (q,Y) = g (q,Y)) (Y : Plane) :
    ParticularWaveBounds.commonPressure t f G hab cutoff K (q,Y) =
      ParticularWaveBounds.commonPressure t g G hab cutoff K (q,Y) := by
  apply tsum_congr
  intro copy
  exact congrArg (fun v => cutoff (G.coordinates copy Y) • v)
    (copyPressure_source_congr t f g G hab q hf copy K Y)

end FiberLocality

/-! ## Actual common-band comparison, without truncated reverse gaps -/



theorem associatedChart_stateChart (n m k : ℕ) (z : PhysicalResidualNaturality.Associated) :
    CorrectionStep.cycleAssoc.symm
      (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n) (ChartScales.Q_pos m) k z) =
      GaugeStateCoherence.bandChartEquiv h n m k (CorrectionStep.cycleAssoc.symm z) := by
  simp only [PhysicalResidualNaturality.associatedChart_apply, cycleAssoc_symm_apply,
    GaugeStateCoherence.bandChartEquiv_apply, GaugeStateCoherence.bandSlowEquiv_apply,
    MeanChartCompatibility.coverMap_eq_coverPower, GaugeStateCoherence.bandScale_eq_ratioPower,
    parameterChange, ratioPower, Real.rpow_one,
    Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]


theorem assembly_source
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    (z : PhysicalResidualNaturality.Associated) :
    ParticularWaveAssembly.residualSource (ActualParticularStageControls.assembly x l).context
      (ActualParticularStageControls.assembly x l).state (ActualParticularStageControls.assembly x l).carrierBlock
      (ActualParticularStageControls.assembly x l).gaussianInput (ActualParticularStageControls.assembly x l).aliasInput
      j n z = ParticularWaveAssembly.residualSource (commonContext B) x.state
        (x.coefficients.blocks l) (x.coefficients.gaussian l) 0
        j n (CorrectionStep.cycleAssoc.symm z) := by
  funext i
  exact congrArg (fun b => b.velocity n i j z)
    (StateReindex.residualBlock_pull CorrectionStep.cycleAssoc.symm (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) 0)


theorem state_sourceWeight (n m : ℕ) :
    GaugeStateCoherence.bandVelocityScale h n m * GaugeStateCoherence.bandVelocityScale h n m *
      GaugeStateCoherence.bandScale n m = sourceWeight h (ChartScales.Q n) (ChartScales.Q m) := by
  simpa only [GaugeStateCoherence.bandVelocityScale_eq_ratioPower,
    GaugeStateCoherence.bandScale_eq_ratioPower, velocityWeight] using
      PhysicalResidualNaturality.weight_source (ChartScales.Q_pos n) (ChartScales.Q_pos m) h


/-! The reference operator identities hold on the entire free lift. -/

noncomputable def angleEmbed (v : PhysicalResidualNaturality.Associated) : WaveSpace :=
  ((v.1, 0), v.2)

theorem associatedDirections_radial (B n : ℕ) (z : WaveSpace) :
    (ActualParticularStageControls.directions (B := B)).radialField n z =
      angleEmbed ((HarmonicResidual.contextFrame
        (ActualParticularStageControls.associatedContext (B := B)) n).radial (z.1.1,z.2)) := by
  simp only [ActualParticularStageControls.directions, ParticularWaveBounds.reindex_radialField,
    PrimaryResidualClass.directions_radial, ActualParticularStageControls.associatedContext,
    StateReindex.contextFrame_pull, ParticularWaveBounds.reindexVector,
    HarmonicResidual.liftDirection, StateReindex.frame, StateReindex.vector]
  rfl

theorem associatedDirections_axial (B n : ℕ) (z : WaveSpace) :
    (ActualParticularStageControls.directions (B := B)).axialField
      (CorrectionStep.ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip) n z =
      angleEmbed ((HarmonicResidual.contextFrame
        (ActualParticularStageControls.associatedContext (B := B)) n).axial (z.1.1,z.2)) := by
  change (ChartScales.Q n ^ h) •
      (ActualParticularStageControls.nativeToFull.symm ((commonContext B).operators.eZ,0)) = _
  rw [← LinearIsometryEquiv.map_smul]
  simp only [Prod.smul_mk, smul_zero]
  rfl





/-! ## Reverse index order and the original recurrence interface -/




abbrev StateComparison (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (V : Set Plane) (n m k : ℕ) : Prop :=
  PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain V)
    (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
    (GaugeStateCoherence.bandScale n m) x.state x.state n m

abbrev BlockComparison (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (V : Set Plane) (n m k : ℕ) : Prop :=
  PhysicalResidualNaturality.BlockFieldsOn (PhysicalMeanDomain.slowDomain V)
    (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
    (GaugeStateCoherence.bandScale n m) (x.coefficients.blocks l) (x.coefficients.blocks l)
    (x.coefficients.gaussian l) 0
    (x.coefficients.gaussian l) 0 n m


/-! ## Regularity and support are transported, not postulated anew -/



/-! ## The unchanged target solve uses this native reference -/



/-- The literal current-source common coefficient in the actual stage. -/
noncomputable def actualCoefficients
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) : LinearWaveBounds.WaveCoefficients WaveSpace :=
  ((ActualParticularStageControls.parameters x l).copyData
    (ActualParticularStageControls.assembly x l).context (ActualParticularStageControls.assembly x l).state
    (ActualParticularStageControls.assembly x l).carrierBlock
    (ActualParticularStageControls.assembly x l).gaussianInput
    (ActualParticularStageControls.assembly x l).aliasInput j).common







/-! The full carrier uses the same rebase, including the angular integer. -/

theorem carrier_phase_rebase {K Kr J a theta phi psi : ℝ}
    (hK : K ≠ 0) (hKr : Kr ≠ 0) (hJ : J ≠ 0) (hphi : K * phi = Kr * psi) :
    (J * Kr) / (J * K) * (psi + a / Kr * theta) = phi + a / K * theta := by
  have he : (Kr / K) * psi = phi := by
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff hK).2 (by simpa only [mul_comm] using hphi.symm)
  rw [mul_div_mul_left _ _ hJ]
  calc
    _ = (Kr/K)*psi + ((Kr/K)*(a/Kr))*theta := by ring
    _ = phi + (a/K)*theta := by rw [he]; congr 2 ; field_simp




/-! Precisely the inherited lattice is retained. -/




end NavierStokes.ActualReferenceRebase
