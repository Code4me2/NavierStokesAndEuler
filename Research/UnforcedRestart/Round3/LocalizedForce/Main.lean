import NavierStokes.MixedPeriodicAssembly

/-! Support certificates for the literal mixed cut residual, uniform in the selected fields.
No regularity of the unextended velocity at terminal time is assumed. -/
noncomputable section
namespace UnforcedRestart.Round3.LocalizedForce
open NavierStokes NavierStokes.ProblemStatement Set Filter
open scoped Topology

theorem cutResidual_zero_outside (A v : VelocityField) (p : PressureField)
    (t : ℝ) {x : Space} (hx : x ∉ SpatialLocalization.supportCylinder) :
    MixedPeriodicAssembly.cutResidual A v p (t, x) = 0 := by
  have hn : ∀ᶠ z : SpaceTime in 𝓝 (t, x),
      z.2 ∉ SpatialLocalization.supportCylinder :=
    (continuous_snd.continuousAt : ContinuousAt (fun z : SpaceTime => z.2) (t, x)).preimage_mem_nhds
      (SpatialLocalization.isClosed_supportCylinder.isOpen_compl.mem_nhds hx)
  apply ResidualRegularity.residual_eq_zero_of_eventually_zero
  · filter_upwards [hn] with z hz
    exact MixedPeriodicAssembly.cutVelocity_zero_outside A v z.1 hz
  · filter_upwards [hn] with z hz
    exact MixedPeriodicAssembly.cutPressure_zero_outside p z.1 hz

theorem cutResidual_eventually_zero_outside (A v : VelocityField) (p : PressureField)
    (t : ℝ) {x : Space} (hx : x ∉ SpatialLocalization.supportCylinder) :
    MixedPeriodicAssembly.cutResidual A v p =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
  have hn : ∀ᶠ z : SpaceTime in 𝓝 (t, x),
      z.2 ∉ SpatialLocalization.supportCylinder :=
    (continuous_snd.continuousAt : ContinuousAt (fun z : SpaceTime => z.2) (t, x)).preimage_mem_nhds
      (SpatialLocalization.isClosed_supportCylinder.isOpen_compl.mem_nhds hx)
  filter_upwards [hn] with z hz
  exact cutResidual_zero_outside A v p z.1 hz

theorem terminal_boundary_jets_zero_outside (A v : VelocityField) (p : PressureField)
    (ea : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (x : Space)
    (hx : MixedPeriodicAssembly.representative x ∉ SpatialLocalization.supportCylinder)
    (n : ℕ) : MixedPeriodicAssembly.boundaryLimits A v p ea ev ep x n = 0 := by
  classical
  let y := MixedPeriodicAssembly.representative x
  let e := MixedPeriodicAssembly.cutResidual_awayExtensions ea ev ep
  change JointResidualLimits.boundaryLimits (MixedPeriodicAssembly.cutResidual A v p) e y n = 0
  by_cases hy : y = 0
  · rw [hy]
    exact JointResidualLimits.boundaryLimits_zero (MixedPeriodicAssembly.cutResidual A v p) e n
  · let E := Classical.choice (e y hy)
    have he := SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
      (cutResidual_eventually_zero_outside A v p 1 hx) n
    have hz : Tendsto (iteratedFDeriv ℝ n (MixedPeriodicAssembly.cutResidual A v p))
        (𝓝[SpacetimeEndpoint.openPast 1] (1, y)) (𝓝 0) := by
      have hconst : Tendsto (fun _ : SpaceTime =>
          (0 : (SpaceTime [×n]→L[ℝ] Space)))
          (𝓝[SpacetimeEndpoint.openPast 1] (1, y)) (𝓝 0) := tendsto_const_nhds
      apply hconst.congr'
      simpa [y, Pi.zero_def] using (he.filter_mono nhdsWithin_le_nhds).symm
    have := JointResidualLimits.past_filter_neBot y
    have hlim := tendsto_nhds_unique (E.jet_tendsto n) hz
    simpa only [JointResidualLimits.boundaryLimits, dite_eq_right hy, ftaylorSeries] using hlim

#print axioms cutResidual_zero_outside
#print axioms cutResidual_eventually_zero_outside
#print axioms terminal_boundary_jets_zero_outside
end UnforcedRestart.Round3.LocalizedForce
