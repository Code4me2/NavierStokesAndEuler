import Research.UnforcedRestart.Round5.RadialPrimitive

/-! Exterior reduction of the literal selected diagonal sums. Stage zero's
scale cutoff is retained: this theorem does not replace it by a constant. -/
noncomputable section
namespace UnforcedRestart.Round5.SelectedExterior
open NavierStokes NavierStokes.ProblemStatement Set Filter
open UnforcedRestart.Round3.WitnessFeasibility
open scoped Topology

abbrev domain : Set SpaceTime := ActualExteriorPrefix.exteriorDomain
  (ActualCandidateConstruction.residualBand budget threshold)

def cutBasePotential : VelocityField := fun w =>
  SmoothCutoffs.scaledCutoff (selected.schedule 0 : ℝ) (PhysicalWaveSum.physicalQ h w) •
    TailGaugePotential.finalPotential CorrectionInitialization.ActualPrimary.certificate
      CorrectionInitialization.ActualPrimary.modulation CorrectionInitialization.ActualPrimary.upper budget w

def cutBasePressure : PressureField := fun w =>
  SmoothCutoffs.scaledCutoff (selected.schedule 0 : ℝ) (PhysicalWaveSum.physicalQ h w) •
    FinalSlowBase.pressure CorrectionInitialization.ActualPrimary.certificate
      CorrectionInitialization.ActualPrimary.modulation CorrectionInitialization.ActualPrimary.upper budget w

/-- All positive stages vanish by their actual exterior support identity. -/
theorem selected_potential_eqOn : EqOn (potentialSum selected.schedule) cutBasePotential domain := by
  intro w hw
  unfold potentialSum SolenoidalDiagonal.potentialSum
  rw [tsum_eq_single 0]
  · simp only [SolenoidalDiagonal.cutStage, cutBasePotential,
      (ActualCandidateAssembly.exteriorStages budget threshold geometry).potential_zero hw]
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [SolenoidalDiagonal.cutStage,
      (ActualCandidateAssembly.exteriorStages budget threshold geometry).potential_succ k hw,
      Pi.zero_apply, smul_zero]

/-- Includes the zeroth direct stage; no diagonal scale comparison is needed. -/
theorem selected_direct_eqOn : EqOn (directSum selected.schedule) 0 domain := by
  intro w hw
  unfold directSum SolenoidalDiagonal.potentialSum
  have hz : ∀ j, SolenoidalDiagonal.cutStage (fun j => (selected.schedule j : ℝ))
      (PhysicalWaveSum.physicalQ h)
      (ActualCandidateAssembly.directStages budget threshold geometry) j w = 0 := by
    intro j
    simp only [SolenoidalDiagonal.cutStage,
      (ActualCandidateAssembly.exteriorStages budget threshold geometry).direct_zero j hw,
      Pi.zero_apply, smul_zero]
  simp only [hz, tsum_zero, Pi.zero_apply]

theorem selected_pressure_eqOn : EqOn (pressureSum selected.schedule) cutBasePressure domain := by
  intro w hw
  unfold pressureSum SolenoidalDiagonal.potentialSum
  rw [tsum_eq_single 0]
  · simp only [SolenoidalDiagonal.cutStage, cutBasePressure,
      (ActualCandidateAssembly.exteriorStages budget threshold geometry).pressure_zero hw]
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [SolenoidalDiagonal.cutStage,
      (ActualCandidateAssembly.exteriorStages budget threshold geometry).pressure_succ k hw,
      Pi.zero_apply, smul_zero]

/-- A common ambient neighborhood justifies differentiating all three identities.
This is at an interior exterior point, not yet an incoming terminal neighborhood. -/
theorem selected_exterior_germs {w : SpaceTime} (hw : w ∈ domain) :
    (potentialSum selected.schedule =ᶠ[𝓝 w] cutBasePotential) ∧
    (directSum selected.schedule =ᶠ[𝓝 w] 0) ∧
    (pressureSum selected.schedule =ᶠ[𝓝 w] cutBasePressure) :=
  ⟨ActualExteriorPrefix.eqOn_exterior_germ selected_potential_eqOn hw,
    ActualExteriorPrefix.eqOn_exterior_germ selected_direct_eqOn hw,
    ActualExteriorPrefix.eqOn_exterior_germ selected_pressure_eqOn hw⟩

#print axioms selected_potential_eqOn
#print axioms selected_direct_eqOn
#print axioms selected_pressure_eqOn
#print axioms selected_exterior_germs
end UnforcedRestart.Round5.SelectedExterior
