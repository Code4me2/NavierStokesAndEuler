import Research.UnforcedRestart.Round4.PressureIntegral.Main

noncomputable section
namespace UnforcedRestart.Round4.PressureIntegral
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Set MeasureTheory
open scoped ContDiff

/-- The analytic assumptions needed for scalar derivative cancellation, with integrability
returned explicitly rather than inferred from a totalized integral. -/
theorem compact_scalar_partial_contract {q : Space → ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (i : Fin 3) :
    ContDiff ℝ ∞ (spatialPartial i q) ∧
    HasCompactSupport (spatialPartial i q) ∧
    Integrable (spatialPartial i q) ∧ (∫ x, spatialPartial i q x) = 0 := by
  have hs := SolutionDifference.spatial_partial_contDiff hq i
  have hk := NavierStokesR3.CompactEnergy.compact_partial hc i
  exact ⟨hs, hk, hs.continuous.integrable_of_hasCompactSupport hk,
    NavierStokesR3.CompactEnergy.integral_partial_eq_zero hq hc i⟩

theorem pressure_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun x => compactPressure (t, x)) :=
  (smooth_slice ht).continuous.integrable_of_hasCompactSupport (compact_support t)

/-- This differentiates the entire activated cut pressure, not just its uncut factor. -/
theorem selected_gradient_component_contract {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => pressureGradient compactPressure t x i) ∧
    HasCompactSupport (fun x => pressureGradient compactPressure t x i) ∧
    Integrable (fun x => pressureGradient compactPressure t x i) ∧
    (∫ x : Space, pressureGradient compactPressure t x i) = 0 := by
  simp_rw [gradient_component]
  exact compact_scalar_partial_contract (smooth_slice ht) (compact_support t) i

/-- Exact full-cutoff derivative interface; the spatial cutoff stays inside the derivative. -/
theorem gradient_full_cutoff (t : ℝ) (x : Space) (i : Fin 3) :
    pressureGradient compactPressure t x i = spatialPartial i
      (fun y => SmoothCutoffs.timeSwitch t *
        (SpatialLocalization.spatialCutoff y *
          Round3.WitnessFeasibility.pressureSum
            Round3.WitnessFeasibility.selected.schedule (t, y))) x := by
  rw [gradient_component]
  rfl

#print axioms gradient_full_cutoff
#print axioms compact_scalar_partial_contract
#print axioms pressure_integrable
#print axioms selected_gradient_component_contract
end UnforcedRestart.Round4.PressureIntegral
