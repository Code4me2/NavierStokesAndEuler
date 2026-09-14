import Research.UnforcedRestart.Round3.MeanTopology.Main
import Research.UnforcedRestart.Round3.WitnessFeasibility.Certificates

noncomputable section
namespace UnforcedRestart.Round4.PeriodizationTransport
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Round3 Set MeasureTheory Filter
open scoped ContDiff Topology

/-- Coordinate identity with the correct, different normed-space types. -/
theorem toSpace_measurePreserving :
    MeasurePreserving toSpace (volume : Measure Coords) (volume : Measure Space) :=
  PiLp.volume_preserving_toLp (Fin 3)

theorem wholeSpace_integral_coordinates (g : Space → ℝ) :
    (∫ y : Coords, g (toSpace y)) = ∫ x : Space, g x :=
  toSpace_measurePreserving.integral_comp toSpace.toHomeomorph.measurableEmbedding g

/-- The actual residual uses activated fields even before the activation plateau. -/
def compactResidual : VelocityField := fun z =>
  navierStokesResidual MeanTopology.compactVelocity
    (TimeLocalization.activatedPressure (SpatialLocalization.cutPressure
      (WitnessFeasibility.pressureSum WitnessFeasibility.selected.schedule))) z.1 z.2

theorem selected_force_inner {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space)
    (hx : x ∈ PeriodicLocalization.innerCube (1 / 4)) :
    WitnessFeasibility.selected.forcing (t, x) = compactResidual (t, x) := by
  rw [WitnessFeasibility.selected_force_eq_residual ht]
  change navierStokesResidual _ _ t x = navierStokesResidual _ _ t x
  apply ResidualRegularity.residual_congr (MeanTopology.compactVelocity_agreement (z := (t, x)) hx)
  exact MixedPeriodicAssembly.activated_periodicPressure_eventuallyEq_cut _ (t, x) hx

theorem selected_force_representative {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    WitnessFeasibility.selected.forcing (t, x) =
      compactResidual (t, MixedPeriodicAssembly.representative x) := by
  rw [← MixedPeriodicAssembly.eq_representative
    WitnessFeasibility.selected.candidate.force_periodic ht.1.le x]
  exact selected_force_inner ht _ (MixedPeriodicAssembly.representative_mem_innerCube x)

/-- This is the genuine cell functional in explicit coordinates, not a
whole-space compact integral renamed as a cell integral. -/
def selectedCellMean (t : ℝ) (i : Fin 3) : ℝ :=
  ∫ y : Coords, WitnessFeasibility.selected.forcing (t, toSpace y) i
    ∂(volume.restrict (Icc 0 1))

theorem selectedCellMean_eq (t : ℝ) (i : Fin 3) : selectedCellMean t i =
    cubeIntegral (fun x => WitnessFeasibility.selected.forcing (t, x) i) := rfl

theorem selectedCellMean_continuousOn (i : Fin 3) :
    ContinuousOn (fun t => selectedCellMean t i) (Icc (0 : ℝ) 1) := by
  exact cubeIntegral_continuousOn_Icc
    (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      WitnessFeasibility.selected.smooth.continuous).continuousOn)

#print axioms toSpace_measurePreserving
#print axioms wholeSpace_integral_coordinates
#print axioms compactResidual
#print axioms selected_force_inner
#print axioms selected_force_representative
#print axioms selectedCellMean
#print axioms selectedCellMean_eq
#print axioms selectedCellMean_continuousOn
end UnforcedRestart.Round4.PeriodizationTransport
