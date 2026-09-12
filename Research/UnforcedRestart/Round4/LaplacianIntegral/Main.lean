import Research.UnforcedRestart.Round3.SelectedBridge.Main

noncomputable section
namespace UnforcedRestart.Round4.LaplacianIntegral
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open NavierStokes.SolutionDifference NavierStokesR3.CompactEnergy
open Round3 Round3.MeanTopology Set MeasureTheory
open scoped ContDiff BigOperators

def secondPartial (t : ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  spatialPartial j (fun y => spatialPartial j (fun z => compactVelocity (t, z)) y i) x

theorem secondPartial_smooth {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i j : Fin 3) :
    ContDiff ℝ ∞ (secondPartial t i j) :=
  spatial_partial_contDiff (component_contDiff
    (spatial_partial_contDiff (compactVelocity_smooth_slice ht) j) i) j

theorem secondPartial_compact (t : ℝ) (i j : Fin 3) :
    HasCompactSupport (secondPartial t i j) :=
  compact_partial (compact_component (compact_partial (compactVelocity_compact_support t) j) i) j

theorem secondPartial_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i j : Fin 3) :
    Integrable (secondPartial t i j) :=
  (secondPartial_smooth ht i j).continuous.integrable_of_hasCompactSupport (secondPartial_compact t i j)

theorem secondPartial_integral_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i j : Fin 3) :
    (∫ x : Space, secondPartial t i j x) = 0 :=
  integral_partial_eq_zero (component_contDiff
    (spatial_partial_contDiff (compactVelocity_smooth_slice ht) j) i)
    (compact_component (compact_partial (compactVelocity_compact_support t) j) i) j

theorem laplacian_component {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) (i : Fin 3) :
    spatialLaplacian compactVelocity t x i = ∑ j : Fin 3, secondPartial t i j x := by
  change (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (∑ j : Fin 3,
    fderiv ℝ (fun y => spatialDerivative compactVelocity t y (coordinateVector j))
      x (coordinateVector j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (fderiv_component (spatial_partial_contDiff (compactVelocity_smooth_slice ht) j)
    i x (coordinateVector j)).symm

theorem laplacian_component_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    Integrable (fun x => spatialLaplacian compactVelocity t x i) := by
  simp_rw [laplacian_component ht]
  exact integrable_finsetSum _ (fun j _ => secondPartial_integrable ht i j)

theorem selected_compact_laplacian_integral_zero {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ x : Space, spatialLaplacian compactVelocity t x i) = 0 := by
  simp_rw [laplacian_component ht]
  rw [integral_finsetSum _ (fun j _ => secondPartial_integrable ht i j)]
  simp [secondPartial_integral_zero ht]

#print axioms secondPartial
#print axioms secondPartial_smooth
#print axioms secondPartial_compact
#print axioms secondPartial_integrable
#print axioms secondPartial_integral_zero
#print axioms laplacian_component
#print axioms laplacian_component_integrable
#print axioms selected_compact_laplacian_integral_zero
end UnforcedRestart.Round4.LaplacianIntegral
