import Research.UnforcedRestart.Round4.Integration.Assembly

noncomputable section
open NavierStokes NavierStokes.ProblemStatement MeasureTheory
open UnforcedRestart.Round3

/-- Closed-interval acceptance with only time membership and a component index. -/
theorem selected_force_mean_acceptance (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin 3) :
    (∫ y : PeriodicIntegration.Coords,
      WitnessFeasibility.selected.forcing (t, PeriodicIntegration.toSpace y) i
      ∂(volume.restrict (Set.Icc 0 1))) = 0 :=
  UnforcedRestart.Round4.Integration.selected_force_cell_mean_zero t ht i

#print selected_force_mean_acceptance
#print UnforcedRestart.Round4.Integration.selected_force_cell_mean_zero
#print axioms selected_force_mean_acceptance
