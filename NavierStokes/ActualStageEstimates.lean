import NavierStokes.ActualPhysicalStageBounds
import NavierStokes.ActualCycleResidualBounds
import NavierStokes.ActualCyclePreservation
import NavierStokes.ActualIntermediateDebtBounds
import NavierStokes.MixedCandidateAssembly

/-!
# Stage estimates for the fixed actual iteration

The native step data and the actual physical field representations are
assembled into the finite-stage obligations of the mixed diagonal theorem.
No estimate of the output physical residual is an input.
-/

noncomputable section

namespace NavierStokes.ActualStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators


/-! ## Source indices do not change physical copy fields -/

/-- Add an unused tag to native source indices. The actual copies, their
carriers, and their physical fields are unchanged. -/
noncomputable def taggedSource {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {I K J T : Type*} (tag : T) (W : PhysicalStageBounds.WaveData h D I K J) :
    PhysicalStageBounds.WaveData h D (T × I) K J where
  lowerRadius := W.lowerRadius
  upperRadius := W.upperRadius
  nativeWidth := W.nativeWidth
  slowBound := W.slowBound
  frequencyBound := W.frequencyBound
  alpha := W.alpha
  shift := W.shift
  harmonics := W.harmonics
  gapBound := W.gapBound
  lower_pos := W.lower_pos
  width_nonneg := W.width_nonneg
  slow_nonneg := W.slow_nonneg
  frequency_one_le := W.frequency_one_le
  strip := W.strip
  weight i := W.weight i.2
  source i := W.source i.2
  source_bounds := {
    uniform := W.source_bounds.uniform.reindex Prod.snd
    flat_geometry := W.source_bounds.flat_geometry
    weight_le := by
      obtain ⟨c, hc, hb⟩ := W.source_bounds.weight_le
      exact ⟨c, hc, fun i => hb i.2⟩
    epsilon_eq := W.source_bounds.epsilon_eq
    slow_le := W.source_bounds.slow_le }
  copies := W.copies
  cells := W.cells
  chart i := {
    sourceIndex k L := (tag, (W.chart i).sourceIndex k L)
    map := (W.chart i).map
    domain := (W.chart i).domain
    open_domain := (W.chart i).open_domain
    smooth := (W.chart i).smooth
    positive_jets := (W.chart i).positive_jets
    amplitude_eq := (W.chart i).amplitude_eq
    contains := (W.chart i).contains }
  chart_maps := W.chart_maps
  carrier := W.carrier
  support := W.support
  smooth := W.smooth
  frequencies := W.frequencies

@[simp] theorem taggedSource_vector {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {I K T : Type*} (tag : T) (W : PhysicalStageBounds.WaveData h D I K (Fin 3)) :
    (taggedSource tag W).vector = W.vector := rfl

@[simp] theorem taggedSource_pressure {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {I K T : Type*} (tag : T) (W : PhysicalStageBounds.WaveData h D I K Unit) :
    (taggedSource tag W).pressure = W.pressure := rfl

/-! ## One fixed native iteration -/

noncomputable def StepData (B N0 j : ℕ)
    (H : ActualCyclePreservation.Invariant (ActualIterationLedger.sigma j)
      (ActualCyclePreservation.state B N0 j)) : Type :=
  CorrectionAnalyticStep.StepData ActualInitialization.geometry h (CommonWindow.index h)
    ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (ActualCycleParameters.swap B N0 l))
    ActualSignedStageControls.parameters rankData (commonContext B)
    (ActualCyclePreservation.state B N0 j) ActualInitialization.tangentBlock
    ActualInitialization.envelope ActualCoreSupport.refinedCarrier
    (ActualCyclePreservation.staticData B) H (ActualIterationLedger.sigma_admissible j)

/-- All data refer to the same fixed parameters and actual initial state.
The step record contains native wave constructions; it is not a physical
stage-bound or residual-bound oracle. -/
structure RunData (B N0 : ℕ) where
  invariant : ∀ j, ActualCyclePreservation.Invariant (ActualIterationLedger.sigma j)
    (ActualCyclePreservation.state B N0 j)
  step : ∀ j, StepData B N0 j (invariant j)
  particular : ∀ j, ActualParticularMeanGain.Inputs (ActualCyclePreservation.state B N0 j)
    (ActualIterationLedger.sigma j)

theorem RunData.result {B N0 : ℕ} (R : RunData B N0) (j : ℕ) :
    CorrectionAnalyticStep.StepResult ActualInitialization.geometry h (CommonWindow.index h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (ActualCycleParameters.swap B N0 l))
      ActualSignedStageControls.parameters rankData (commonContext B)
      (ActualCyclePreservation.state B N0 j) ActualInitialization.tangentBlock
      ActualInitialization.envelope ActualCoreSupport.refinedCarrier
      (σ := ActualIterationLedger.sigma j) (κ := ChartScales.kappa) :=
  CorrectionAnalyticStep.step _ _ _ _ _ _ _ _ _ _ _ _
    (ActualCyclePreservation.staticData B) (R.invariant j) (ActualIterationLedger.sigma_admissible j)
    ActualCyclePreservation.kappa_small (R.step j)

theorem RunData.rank_class {B N0 : ℕ} (R : RunData B N0) (j : ℕ) :
    WeightedClasses.UnweightedClass ActualInitialization.slowStrip
      (1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa)
      (CorrectionState.debt (commonContext B)
        (ActualIntermediateDebtBounds.postTemporal (ActualCyclePreservation.state B N0 j))) :=
  ActualIntermediateDebtBounds.afterTemporal_debt_from_stepData
    (ActualCyclePreservation.staticData B) (R.invariant j) (ActualIterationLedger.sigma_admissible j)
    (R.particular j) (R.step j)

theorem nativeMean_eq_ledger (j : ℕ) :
    1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa =
      ActualIterationLedger.meanNative ChartScales.kappa (j + 1) := by
  simp only [ActualIterationLedger.meanNative, ActualIterationLedger.inputSigma_succ,
    ExponentLedger.meanUpdateExponent, ExponentLedger.meanExponent]

theorem nativePotential_eq_ledger (j : ℕ) :
    1 / 2 + ActualIterationLedger.sigma j - ChartScales.kappa =
      ActualIterationLedger.waveNative ChartScales.kappa (j + 1) := by
  simp only [ActualIterationLedger.waveNative, ActualIterationLedger.inputSigma_succ,
    ExponentLedger.waveExponent]

theorem nativePressure_eq_ledger (j : ℕ) :
    1 + ActualIterationLedger.sigma j - ChartScales.kappa =
      ActualIterationLedger.wavePressureNative ChartScales.kappa (j + 1) := by
  simp only [ActualIterationLedger.wavePressureNative, ← nativePotential_eq_ledger]
  ring

variable {B N0 N : ℕ}

noncomputable def temporalInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  actualCycleTemporalInput M j hN (R.result j).afterSignedAxial

noncomputable def rankInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  actualCycleRankInput M j hN (R.rank_class j)

noncomputable def angularInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (CoordinateAlgebra.A h) :=
  actualCycleAngularInput M j hN (R.result j).temporal (R.result j).rank

noncomputable def pressureInput (R : RunData B N0)
    (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
      (fun _ => ActualCycleParameters.fixedParameters B N0))
    (hN : 4 ≤ N) (j : ℕ) : MeanInput h (2 * CoordinateAlgebra.A h) :=
  actualCyclePressureInput M j hN (R.result j).pressure

/-! ## Actual wave records and their native exponents -/

structure WaveInputs (DP : Type) [NormedAddCommGroup DP] [NormedSpace ℝ DP]
    (IP KP : Type*) (DS : Type) [NormedAddCommGroup DS] [NormedSpace ℝ DS] (IS KS : Type*) where
  particularPotential : ℕ → PhysicalStageBounds.WaveData h DP (Fin 3 × IP) KP (Fin 3)
  signedPotential : ℕ → PhysicalStageBounds.WaveData h DS (Fin 3 × IS) KS (Fin 3)
  particularPressure : ℕ → PhysicalStageBounds.WaveData h DP IP KP Unit
  signedPressure : ℕ → PhysicalStageBounds.WaveData h DS IS KS Unit
  particularPotential_exponent : ∀ j, 1/2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (particularPotential j).alpha
  signedPotential_exponent : ∀ j, 1/2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (signedPotential j).alpha
  particularPressure_exponent : ∀ j, 1 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (particularPressure j).alpha
  signedPressure_exponent : ∀ j, 1 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (signedPressure j).alpha
  particularPotential_shift : ∀ j, (particularPotential j).shift = -h
  signedPotential_shift : ∀ j, (signedPotential j).shift = -h
  particularPressure_shift : ∀ j, (particularPressure j).shift = -(2 * CoordinateAlgebra.A h)
  signedPressure_shift : ∀ j, (signedPressure j).shift = -(2 * CoordinateAlgebra.A h)

section CycleInputs

variable {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (R : RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : WaveInputs DP IP KP DS IS KS)

noncomputable def cycleInputs : CycleInputs h DP (Fin 3 × IP) KP DS (Fin 3 × IS) KS where
  particularPotential := W.particularPotential
  signedPotential := W.signedPotential
  particularPressure j := taggedSource (0 : Fin 3) (W.particularPressure j)
  signedPressure j := taggedSource (0 : Fin 3) (W.signedPressure j)
  temporal := temporalInput R M hN
  rank := rankInput R M hN
  angular := angularInput R M hN
  pressure := pressureInput R M hN





theorem cycleInputs_validScale {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    (cycleInputs R M hN W).ValidScale qbig :=
  ⟨fun _ => hq, fun _ => hq, fun _ => hq, fun _ => hq⟩

end CycleInputs

/-! ## The actual finite-stage estimate record -/

/-- The initialized background loss is fixed before the number of
correction stages is chosen. -/
noncomputable def backgroundLoss (waveAlpha waveShift : ℝ) : ℕ → ℝ :=
  MixedFiniteBackground.initialBackgroundLoss
    (InitializedPhysicalBackground.initialLoss h waveAlpha waveShift
      (1 - ChartScales.kappa) (9 / 10))
    (PhysicalStageBounds.potentialLoss h h 0) (PhysicalStageBounds.directLoss h 0)

end NavierStokes.ActualStageEstimates
