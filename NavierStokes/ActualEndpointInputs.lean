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

theorem initialPotentialModel_eq (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3)) (w : SpaceTime) :
    initialPotentialModel B N0 N hN WA w =
      TailGaugePotential.finalPotential certificate modulation upper B w +
        (WA.vector w + (ActualMeanPhysicalData.initialStreamFamily B N0 N).angularField w) := by
  change _ + (WA.vector w + (ActualMeanPhysicalData.initialTemporalFamily B N0 N).angularField w +
    (ActualMeanPhysicalData.initialRankFamily B N0 N).angularField w) = _
  rw [ActualMeanPhysicalData.initialStream_angularField]
  simp only [Pi.add_apply]
  abel

theorem initialPressureModel_eq (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit) (w : SpaceTime) :
    initialPressureModel B N0 N hN WP w =
      FinalSlowBase.pressure certificate modulation upper B w +
        (WP.pressure w + (ActualMeanPhysicalData.initialPressureFamily B N0 N).field w) := rfl

theorem initialPotentialModel_extension (B N0 N : ℕ) (hN : 4 ≤ N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialPotentialModel B N0 N hN WA) x) := by
  have hx0 : x ≠ 0 := by intro he; exact hx (by simp [he])
  have hb := TailGaugePotential.finalPotential_awayExtensions certificate modulation upper B x hx0
  have hi := OffplaneJetExtensions.initialIncrement_extension WA
    (ActualPhysicalStageBounds.actualInitialTemporalInput B N0 N hN)
    (ActualPhysicalStageBounds.actualInitialRankInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half (hq.trans (ChartScales.Q_le_one N)) hq hq hx hqx
  exact OffplaneJetExtensions.extension_add hb hi

theorem initialDirectModel_extension (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialDirectModel B N0 N) x) :=
  OffplaneJetExtensions.mean_angular_extension
    (ActualPhysicalStageBounds.actualInitialAngularInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half (hq.trans (ChartScales.Q_le_one N)) hq hx hqx

theorem initialPressureModel_extension (B N0 N : ℕ) (hN : 4 ≤ N)
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) {x : Space} (hx : x 2 ≠ 0)
    (hqx : EndpointCoordinates.endpointRoot (2 * h) (x 2) < qbig) :
    Nonempty (JointResidualLimits.OneSidedExtension (initialPressureModel B N0 N hN WP) x) := by
  have hb : Nonempty (JointResidualLimits.OneSidedExtension
      (FinalSlowBase.pressure certificate modulation upper B) x) :=
    ⟨SlowBaseEndpoint.finalPressureNonzeroAxial certificate modulation upper B hx⟩
  have hi := OffplaneJetExtensions.initialPressureIncrement_extension WP
    (ActualPhysicalStageBounds.actualInitialPressureInput B N0 N hN)
    outgoing.data.h_pos outgoing.data.h_lt_half (hq.trans (ChartScales.Q_le_one N)) hq hx hqx
  exact OffplaneJetExtensions.extension_add hb hi

end InitialModels

section RawFamilies

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The physical bounds and exact initial representations supply all
three endpoint inputs, including index zero.  No extension or endpoint
limit is assumed for any raw stage. -/
theorem endpointInputs_of_representations (B N0 N : ℕ) (hN : 4 ≤ N)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    (WA : PhysicalStageBounds.WaveData h DA IA KA (Fin 3))
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    {A V : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : MixedCandidateAssembly.StageEstimates h qbig A V P)
    (hA : EqOn (A 0) (initialPotentialModel B N0 N hN WA) (CutStageEstimates.physicalSublevel h qbig))
    (hV : EqOn (V 0) (initialDirectModel B N0 N) (CutStageEstimates.physicalSublevel h qbig))
    (hP : EqOn (P 0) (initialPressureModel B N0 N hN WP) (CutStageEstimates.physicalSublevel h qbig)) :
    EndpointInputs h qbig A V P := by
  have hq1 := hq.trans (ChartScales.Q_le_one N)
  constructor
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos outgoing.data.h_lt_half
          hA hx hqx (initialPotentialModel_extension B N0 N hN WA hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half hq1
          E.potential_bound (Nat.succ_le_succ (Nat.zero_le j)) (E.potential_smooth (j + 1)) hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos outgoing.data.h_lt_half
          hV hx hqx (initialDirectModel_extension B N0 N hN hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half hq1
          E.direct_bound (Nat.succ_le_succ (Nat.zero_le j)) (E.direct_smooth (j + 1)) hx hqx
  · intro x hx hqx j
    cases j with
    | zero =>
        exact OffplaneJetExtensions.extension_of_eqOn_sublevel outgoing.data.h_pos outgoing.data.h_lt_half
          hP hx hqx (initialPressureModel_extension B N0 N hN WP hq hx hqx)
    | succ j =>
        exact OffplaneJetExtensions.rawStage_extension outgoing.data.h_pos outgoing.data.h_lt_half hq1
          E.pressure_bound (Nat.succ_le_succ (Nat.zero_le j)) (E.pressure_smooth (j + 1)) hx hqx



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
