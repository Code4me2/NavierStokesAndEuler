import NavierStokes.ActualCandidateAssembly

/-! One coherent closed selection, not a numerical evaluator or a force-removal theorem. -/
noncomputable section
namespace UnforcedRestart.Round3.WitnessFeasibility
open NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff

abbrev budget := ActualCandidateConstruction.selectedBudget
abbrev threshold := ActualCandidateConstruction.selectedThreshold
abbrev geometry := ActualCandidateConstruction.selectedThreshold_geometry
abbrev h := CorrectionInitialization.ActualPrimary.h

def potentialSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.potentialStages budget threshold geometry)
def directSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.directStages budget threshold geometry)
def pressureSum (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    (ActualCandidateAssembly.pressureStages budget threshold geometry)
def velocity (a : ℕ → ℕ) : VelocityField :=
  TimeLocalization.activatedVelocity
    (MixedPeriodicAssembly.periodicVelocity (potentialSum a) (directSum a))
def pressure (a : ℕ → ℕ) : PressureField :=
  TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure (pressureSum a))

structure Data where
  schedule : ℕ → ℕ
  selectedSchedule : MixedCandidateWitness.SelectedSchedule h
    (ActualCandidateConstruction.qbig budget threshold)
    (ActualCandidateAssembly.potentialStages budget threshold geometry)
    (ActualCandidateAssembly.directStages budget threshold geometry)
    (ActualCandidateAssembly.pressureStages budget threshold geometry) schedule
  ea : JointResidualLimits.AwayExtensions (potentialSum schedule)
  eb : JointResidualLimits.AwayExtensions (directSum schedule)
  ep : JointResidualLimits.AwayExtensions (pressureSum schedule)
  forcing : VelocityField
  candidate : CandidateProperties (velocity schedule) (pressure schedule) forcing
  smooth : ContDiff ℝ ∞ forcing
  jets : ∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n forcing (1, x) =
    MixedPeriodicAssembly.boundaryLimits (potentialSum schedule) (directSum schedule)
      (pressureSum schedule) ea eb ep x n

theorem data_nonempty : Nonempty Data := by
  obtain ⟨a, ha, ea, eb, ep, f, hc, hs, _, _, _, hj, _⟩ :=
    ActualCandidateAssembly.selected_witness
  exact ⟨⟨a, ha, ea, eb, ep, f, hc, hs, hj⟩⟩

/-- All consumers must project this record, not make separate choices. -/
def selected : Data := Classical.choice data_nonempty

theorem terminal_origin_jets (n : ℕ) :
    iteratedFDeriv ℝ n selected.forcing (1, 0) = 0 := by
  rw [selected.jets, MixedPeriodicAssembly.boundaryLimits_zero]

#print axioms potentialSum
#print axioms directSum
#print axioms pressureSum
#print axioms velocity
#print axioms pressure
#print axioms data_nonempty
#print axioms selected
#print axioms terminal_origin_jets
end UnforcedRestart.Round3.WitnessFeasibility
