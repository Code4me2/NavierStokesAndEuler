import Research.UnforcedRestart.Round4.LaplacianIntegral.Main

noncomputable section
namespace UnforcedRestart.Round4.LaplacianIntegral
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.SolutionDifference NavierStokesR3.CompactEnergy
open Round3 Round3.MeanTopology Set MeasureTheory
open scoped ContDiff BigOperators

/-- The actual operator vanishes off the fixed cylinder, at every time;
this uses a spatial-time zero germ, not terminal smoothness. -/
theorem laplacian_zero_outside (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) :
    spatialLaplacian compactVelocity t x = 0 := by
  rw [ResidualRegularity.spatialLaplacian_congr
    (compactVelocity_zero_germ (z := (t, x)) hx)]
  simp [spatialLaplacian, spatialDerivative]

theorem laplacian_support (t : ℝ) :
    tsupport (spatialLaplacian compactVelocity t) ⊆ SpatialLocalization.supportCylinder := by
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra hn
  exact hx (laplacian_zero_outside t hn)

theorem laplacian_compact (t : ℝ) :
    HasCompactSupport (spatialLaplacian compactVelocity t) :=
  SpatialLocalization.isCompact_supportCylinder.of_isClosed_subset
    (isClosed_tsupport _) (laplacian_support t)

theorem laplacian_component_smooth {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialLaplacian compactVelocity t x i) := by
  simp_rw [laplacian_component ht]
  exact ContDiff.sum (fun j _ => secondPartial_smooth ht i j)

theorem velocity_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun x => compactVelocity (t, x)) :=
  (compactVelocity_smooth_slice ht).continuous.integrable_of_hasCompactSupport
    (compactVelocity_compact_support t)

theorem velocity_component_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    Integrable (fun x => compactVelocity (t, x) i) :=
  (component_contDiff (compactVelocity_smooth_slice ht) i).continuous.integrable_of_hasCompactSupport
    (compact_component (compactVelocity_compact_support t) i)

#print axioms laplacian_zero_outside
#print axioms laplacian_support
#print axioms laplacian_compact
#print axioms laplacian_component_smooth
#print axioms velocity_integrable
#print axioms velocity_component_integrable
end UnforcedRestart.Round4.LaplacianIntegral
