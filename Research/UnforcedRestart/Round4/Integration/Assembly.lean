import Research.UnforcedRestart.Round4.Integration.Main
import Research.UnforcedRestart.Round4.PressureIntegral.Components
import Research.UnforcedRestart.Round4.LaplacianIntegral.Regularity
import Research.UnforcedRestart.Round4.PeriodizationTransport.Cell

noncomputable section
namespace UnforcedRestart.Round4.Integration
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Set MeasureTheory

/-- Actual selected periodic force, not a renamed compact integral. -/
theorem selected_force_cell_mean_zero_interior {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    PeriodizationTransport.selectedCellMean t i = 0 := by
  rw [PeriodizationTransport.selected_cell_integral_transport ht i]
  exact selected_compact_residual_integral_zero ht i

/-- Both endpoints follow from continuity of the force mean and interior density.
No terminal velocity regularity is used. -/
theorem selected_force_cell_mean_zero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin 3) :
    (∫ y : Coords, Round3.WitnessFeasibility.selected.forcing (t, toSpace y) i
      ∂(volume.restrict (Icc 0 1))) = 0 := by
  change PeriodizationTransport.selectedCellMean t i = 0
  have hc := (PeriodizationTransport.selectedCellMean_continuousOn i t ht).mono
    (show Ioo (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 from Ioo_subset_Icc_self)
  apply hc.eq_const_of_mem_closure
  · simpa only [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] using ht
  · intro s hs
    exact selected_force_cell_mean_zero_interior hs i

#print axioms selected_force_cell_mean_zero_interior
#print axioms selected_force_cell_mean_zero
end UnforcedRestart.Round4.Integration
