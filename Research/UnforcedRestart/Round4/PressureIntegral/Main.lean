import Research.UnforcedRestart.Round3.MeanTopology.Main

noncomputable section
namespace UnforcedRestart.Round4.PressureIntegral
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Round3 Set Filter MeasureTheory
open scoped ContDiff Topology

def compactPressure : PressureField :=
  TimeLocalization.activatedPressure (SpatialLocalization.cutPressure
    (WitnessFeasibility.pressureSum WitnessFeasibility.selected.schedule))

theorem zero_outside (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) : compactPressure (t, x) = 0 := by
  simp [compactPressure, TimeLocalization.activatedPressure,
    MixedPeriodicAssembly.cutPressure_zero_outside _ t hx]

theorem zero_germ {z : SpaceTime} (hz : z.2 ∉ SpatialLocalization.supportCylinder) :
    compactPressure =ᶠ[𝓝 z] (fun _ => 0) := by
  have hn : ∀ᶠ w : SpaceTime in 𝓝 z, w.2 ∉ SpatialLocalization.supportCylinder :=
    (SpatialLocalization.isClosed_supportCylinder.isOpen_compl.preimage
      continuous_snd).mem_nhds hz
  filter_upwards [hn] with w hw
  exact zero_outside w.1 hw

theorem agreement {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    WitnessFeasibility.pressure WitnessFeasibility.selected.schedule =ᶠ[𝓝 z]
      compactPressure :=
  MixedPeriodicAssembly.activated_periodicPressure_eventuallyEq_cut _ z hz

theorem smoothAt {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    ContDiffAt ℝ ∞ compactPressure (t, x) := by
  by_cases hx : x ∈ SpatialLocalization.supportCylinder
  · have hi : x ∈ PeriodicLocalization.innerCube (1 / 4) := by
      intro i
      have hb := SpatialLocalization.supportCylinder_coordinate_bound hx i
      change |x i| < 1 - 1 / 4
      linarith
    exact (smooth_at_interior WitnessFeasibility.selected.candidate.pressure_smooth ht x).congr_of_eventuallyEq
      (agreement (z := (t, x)) hi).symm
  · exact contDiffAt_const.congr_of_eventuallyEq (zero_germ (z := (t, x)) hx)

theorem smooth_slice {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x => compactPressure (t, x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (smoothAt ht x).comp x (contDiffAt_const.prodMk contDiffAt_id)

theorem compact_support (t : ℝ) : HasCompactSupport (fun x => compactPressure (t, x)) := by
  apply SpatialLocalization.isCompact_supportCylinder.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra hn
  exact hx (zero_outside t hn)

theorem gradient_component (t : ℝ) (x : Space) (i : Fin 3) :
    pressureGradient compactPressure t x i = spatialPartial i (fun y => compactPressure (t, y)) x := by
  change (EuclideanSpace.proj i) (∑ j : Fin 3,
    (spatialPartial j (fun y => compactPressure (t, y)) x) • coordinateVector j) = _
  simp [map_sum, coordinateVector]

theorem gradient_component_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    Integrable (fun x => pressureGradient compactPressure t x i) := by
  simp_rw [gradient_component]
  exact (SolutionDifference.spatial_partial_contDiff (smooth_slice ht) i).continuous.integrable_of_hasCompactSupport
    (NavierStokesR3.CompactEnergy.compact_partial (compact_support t) i)

theorem selected_compact_pressure_integral_zero {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ x : Space, pressureGradient compactPressure t x i) = 0 := by
  simp_rw [gradient_component]
  exact NavierStokesR3.CompactEnergy.integral_partial_eq_zero (smooth_slice ht) (compact_support t) i

#print axioms compactPressure
#print axioms zero_outside
#print axioms zero_germ
#print axioms agreement
#print axioms smoothAt
#print axioms smooth_slice
#print axioms compact_support
#print axioms gradient_component
#print axioms gradient_component_integrable
#print axioms selected_compact_pressure_integral_zero
end UnforcedRestart.Round4.PressureIntegral
