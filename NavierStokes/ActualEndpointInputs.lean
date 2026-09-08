import NavierStokes.OffplaneJetExtensions
import NavierStokes.MixedCandidateAssembly
import NavierStokes.ActualMeanStageData
import NavierStokes.TailGaugePotential
import NavierStokes.SlowBaseEndpoint
import NavierStokes.ActualStageEstimates

/-!
# Endpoint inputs for the actual raw candidate stages

Positive stages use their already proved raw estimates.  Stage zero uses
the actual initial mean families and the existing extensions of the same
base potential and pressure.  No output extension is an input below.
-/

noncomputable section

namespace NavierStokes.ActualEndpointInputs

open Set Function Filter ProblemStatement
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

universe u

/-- The three off-plane endpoint obligations of `candidate_of_finite_stages`.
This is an output package; the construction below does not assume its fields. -/
structure EndpointInputs (h qbig : ℝ) (A V : ℕ → VelocityField) (P : ℕ → PressureField) : Prop where
  potential : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (A j) x)
  direct : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (V j) x)
  pressure : ∀ x : Space, x 2 ≠ 0 → EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig →
    ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (P j) x)

section InitialModels

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The exact base and bounded finite initial potential correction. -/
noncomputable def initialPotentialModel (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3)) : VelocityField :=
  ActualPhysicalStageBounds.initialPotential certificate modulation upper B WA
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)

noncomputable def initialDirectModel (B N0 N : ℕ) : VelocityField :=
  (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField

/-- The pressure of the same summed base and the actual finite initial
wave and mean-pressure correction. -/
noncomputable def initialPressureModel (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit) : PressureField :=
  fun w => FinalSlowBase.pressure certificate modulation upper B w +
    ActualPhysicalStageBounds.initialPressureIncrement WP
      (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN) w






end InitialModels

section RawFamilies

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}




end RawFamilies

section ActualRun

variable {B N0 N : ℕ}
  {DP DS DA0 DP0 : Type}
  [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {IP KP IS KS IA0 KA0 IP0 KP0 : Type*}


end ActualRun

end NavierStokes.ActualEndpointInputs
