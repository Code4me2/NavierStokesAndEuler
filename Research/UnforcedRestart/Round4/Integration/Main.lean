import Research.UnforcedRestart.Round4.PressureIntegral.Main
import Research.UnforcedRestart.Round4.LaplacianIntegral.Main
import Research.UnforcedRestart.Round4.PeriodizationTransport.Main

noncomputable section
namespace UnforcedRestart.Round4.Integration
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Round3 Round3.MeanTopology Set Filter MeasureTheory
open scoped ContDiff Topology

private theorem compact_of_zero_outside {f : Space → Space}
    (hf : ∀ x, x ∉ SpatialLocalization.supportCylinder → f x = 0) : HasCompactSupport f := by
  apply SpatialLocalization.isCompact_supportCylinder.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra hn
  exact hx (hf x hn)

theorem velocity_smoothOn :
    ContDiffOn ℝ ∞ compactVelocity (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
  fun z hz => (SelectedBridge.compactVelocity_smoothAt hz.1 z.2).contDiffWithinAt

theorem temporal_smooth_slice {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (temporalDerivative compactVelocity t) := by
  have hs := ResidualRegularity.contDiffOn_temporalDerivative
    (isOpen_Ioo.prod isOpen_univ) velocity_smoothOn
  rw [contDiff_iff_contDiffAt]
  intro x
  have hx : ContDiffAt ℝ ∞ (fun z : SpaceTime => temporalDerivative compactVelocity z.1 z.2) (t, x) :=
    hs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  exact hx.comp x (show ContDiffAt ℝ ∞ (fun y : Space => (t, y)) x from
    contDiffAt_const.prodMk contDiffAt_id)

theorem temporal_compact (t : ℝ) : HasCompactSupport (temporalDerivative compactVelocity t) := by
  apply compact_of_zero_outside
  intro x hx
  rw [ResidualRegularity.temporalDerivative_congr (compactVelocity_zero_germ (z := (t, x)) hx)]
  simp [temporalDerivative]

theorem temporal_component_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    Integrable (fun x => temporalDerivative compactVelocity t x i) :=
  (SolutionDifference.component_contDiff (temporal_smooth_slice ht) i).continuous.integrable_of_hasCompactSupport
    (NavierStokesR3.CompactEnergy.compact_component (temporal_compact t) i)

theorem advection_component_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    Integrable (fun x => advection compactVelocity t x i) := by
  have hv := compactVelocity_smooth_slice ht
  have hs : ContDiff ℝ ∞ (advection compactVelocity t) :=
    (hv.fderiv_right infty_add_one_le_infty).clm_apply hv
  have hc : HasCompactSupport (advection compactVelocity t) := by
    apply compact_of_zero_outside
    intro x hx
    simp [advection, compactVelocity_zero_outside t hx]
  exact (SolutionDifference.component_contDiff hs i).continuous.integrable_of_hasCompactSupport
    (NavierStokesR3.CompactEnergy.compact_component hc i)

theorem advection_component_integral_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ x : Space, advection compactVelocity t x i) = 0 := by
  have h := selected_compact_transport_zero ht i
  simp only [SolutionDifference.fderiv_component (compactVelocity_smooth_slice ht)] at h
  exact h

theorem selected_compact_residual_integrable {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    Integrable (fun x => PeriodizationTransport.compactResidual (t, x) i) := by
  change Integrable (fun x =>
    (temporalDerivative compactVelocity t x + advection compactVelocity t x -
      spatialLaplacian compactVelocity t x + pressureGradient PressureIntegral.compactPressure t x) i)
  simp only [PiLp.add_apply, PiLp.sub_apply]
  exact (((temporal_component_integrable ht i).add (advection_component_integrable ht i)).sub
    (LaplacianIntegral.laplacian_component_integrable ht i)).add
      (PressureIntegral.gradient_component_integrable ht i)

/-- Complete whole-space cancellation of the same activated compact residual.
This is not yet a statement about the genuine periodic cell. -/
theorem selected_compact_residual_integral_zero {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ x : Space, PeriodizationTransport.compactResidual (t, x) i) = 0 := by
  change (∫ x : Space,
    (temporalDerivative compactVelocity t x + advection compactVelocity t x -
      spatialLaplacian compactVelocity t x + pressureGradient PressureIntegral.compactPressure t x) i) = 0
  simp only [PiLp.add_apply, PiLp.sub_apply]
  have h1 := integral_add (((temporal_component_integrable ht i).add (advection_component_integrable ht i)).sub
      (LaplacianIntegral.laplacian_component_integrable ht i))
      (PressureIntegral.gradient_component_integrable ht i)
  have h2 := integral_sub ((temporal_component_integrable ht i).add (advection_component_integrable ht i))
      (LaplacianIntegral.laplacian_component_integrable ht i)
  have h3 := integral_add (temporal_component_integrable ht i) (advection_component_integrable ht i)
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  rw [h1, h2, h3, SelectedBridge.selected_compact_temporal_integral_zero ht i,
    advection_component_integral_zero ht i,
    LaplacianIntegral.selected_compact_laplacian_integral_zero ht i,
    PressureIntegral.selected_compact_pressure_integral_zero ht i]
  norm_num

#print axioms velocity_smoothOn
#print axioms temporal_smooth_slice
#print axioms temporal_compact
#print axioms temporal_component_integrable
#print axioms advection_component_integrable
#print axioms advection_component_integral_zero
#print axioms selected_compact_residual_integrable
#print axioms selected_compact_residual_integral_zero
end UnforcedRestart.Round4.Integration
