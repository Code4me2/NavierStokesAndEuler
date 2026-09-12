import Research.UnforcedRestart.Round4.Integration.Main
import Research.UnforcedRestart.Round4.PeriodizationTransport.Residual

/-! Deliberately fail-closed end-to-end acceptance test. Not an accepted theorem
source: the named final producer has not been implemented. No assumptions about
mean cancellation or velocity regularity at the terminal time are permitted. -/
noncomputable section
open NavierStokes NavierStokes.ProblemStatement MeasureTheory
open UnforcedRestart.Round3

example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin 3) :
    (∫ y : PeriodicIntegration.Coords,
      WitnessFeasibility.selected.forcing (t, PeriodicIntegration.toSpace y) i
      ∂(volume.restrict (Set.Icc 0 1))) = 0 :=
  UnforcedRestart.Round4.Integration.selected_force_cell_mean_zero t ht i
