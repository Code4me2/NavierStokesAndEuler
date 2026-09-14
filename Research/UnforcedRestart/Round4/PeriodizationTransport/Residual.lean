import Research.UnforcedRestart.Round4.PeriodizationTransport.Main

noncomputable section
namespace UnforcedRestart.Round4.PeriodizationTransport
open NavierStokes NavierStokes.ProblemStatement
open Round3 Set Filter
open scoped Topology

theorem compactResidual_zero_outside (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) : compactResidual (t, x) = 0 := by
  apply ResidualRegularity.residual_eq_zero_of_eventually_zero
    (MeanTopology.compactVelocity_zero_germ (z := (t, x)) hx)
  have hn : ∀ᶠ z : SpaceTime in 𝓝 (t, x), z.2 ∉ SpatialLocalization.supportCylinder :=
    (SpatialLocalization.isClosed_supportCylinder.isOpen_compl.preimage continuous_snd).mem_nhds hx
  filter_upwards [hn] with z hz
  simp [TimeLocalization.activatedPressure, MixedPeriodicAssembly.cutPressure_zero_outside _ z.1 hz]

theorem compactResidual_supported : PeriodicLocalization.SupportedInCube (1 / 4) compactResidual :=
  MixedPeriodicAssembly.supportedInCube_of_zero_outside (fun t _ hx => compactResidual_zero_outside t hx)

/-- Exact actual selected force, not a separately selected compact forcing witness. -/
theorem selected_force_eq_periodize {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    WitnessFeasibility.selected.forcing (t, x) = PeriodicLocalization.periodize compactResidual (t, x) := by
  rw [selected_force_representative ht,
    ← MixedPeriodicAssembly.eq_representative
      (PeriodicLocalization.unitSpatialPeriodsOn_periodize compactResidual (univ : Set ℝ)) (mem_univ t) x,
    PeriodicLocalization.periodize_eq_on_innerCube compactResidual_supported
      (MixedPeriodicAssembly.representative_mem_innerCube x)]

#print axioms compactResidual_zero_outside
#print axioms compactResidual_supported
#print axioms selected_force_eq_periodize
end UnforcedRestart.Round4.PeriodizationTransport
