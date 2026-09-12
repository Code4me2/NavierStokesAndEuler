import Research.UnforcedRestart.Round4.Integration.FinalAudit

noncomputable section
namespace UnforcedRestart.Round4.Integration
open NavierStokes.PeriodicIntegration Set MeasureTheory

/-- Initial mean of the actual selected force, by the closed-interval bridge. -/
theorem selected_force_initial_mean_zero (i : Fin 3) :
    (∫ y : Coords, Round3.WitnessFeasibility.selected.forcing (0, toSpace y) i
      ∂(volume.restrict (Icc 0 1))) = 0 := by
  exact selected_force_cell_mean_zero 0 (by constructor <;> norm_num) i

/-- Terminal mean; this does not assert terminal velocity regularity. -/
theorem selected_force_terminal_mean_zero (i : Fin 3) :
    (∫ y : Coords, Round3.WitnessFeasibility.selected.forcing (1, toSpace y) i
      ∂(volume.restrict (Icc 0 1))) = 0 := by
  exact selected_force_cell_mean_zero 1 (by constructor <;> norm_num) i

#print axioms selected_force_initial_mean_zero
#print axioms selected_force_terminal_mean_zero
end UnforcedRestart.Round4.Integration
