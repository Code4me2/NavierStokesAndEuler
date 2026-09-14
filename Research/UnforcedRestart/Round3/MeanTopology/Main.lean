import Research.UnforcedRestart.Round3.WitnessFeasibility.Main
import NavierStokes.R3.CompactEnergy

/-! Compact-first mean cancellation. No terminal velocity is used. -/
noncomputable section
namespace UnforcedRestart.Round3.MeanTopology
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

/-- A compact smooth incompressible field has zero total momentum, by testing
its divergence against a coordinate function, not a compact potential. -/
theorem compact_component_integral_zero {v : Space → Space}
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hd : ∀ x, (∑ j : Fin 3, spatialPartial j v x j) = 0) (i : Fin 3) :
    (∫ x, v x i) = 0 := by
  have h := NavierStokesR3.CompactEnergy.integral_fderiv_apply
    (EuclideanSpace.proj i).contDiff hv hc
  have he (x : Space) : fderiv ℝ (fun y : Space => y i) x = EuclideanSpace.proj i :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.fderiv
  change (∫ x, fderiv ℝ (fun y : Space => y i) x (v x)) = _ at h
  simpa only [he, EuclideanSpace.coe_proj, hd, mul_zero, integral_zero, neg_zero] using h

/-- This is the compact velocity from the SAME selected schedule, not the
separately existential compact-force component of the witness. -/
def compactVelocity : VelocityField :=
  TimeLocalization.activatedVelocity
    (MixedPeriodicAssembly.cutVelocity
      (WitnessFeasibility.potentialSum WitnessFeasibility.selected.schedule)
      (WitnessFeasibility.directSum WitnessFeasibility.selected.schedule))

theorem compactVelocity_zero_outside (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) : compactVelocity (t, x) = 0 :=
  MixedPeriodicAssembly.activated_cutVelocity_zero_outside _ _ t hx

theorem compactVelocity_zero_germ {z : SpaceTime}
    (hz : z.2 ∉ SpatialLocalization.supportCylinder) :
    compactVelocity =ᶠ[𝓝 z] (fun _ => 0) := by
  have hn : ∀ᶠ w : SpaceTime in 𝓝 z, w.2 ∉ SpatialLocalization.supportCylinder :=
    (SpatialLocalization.isClosed_supportCylinder.isOpen_compl.preimage
      continuous_snd).mem_nhds hz
  filter_upwards [hn] with w hw
  exact compactVelocity_zero_outside w.1 hw

theorem compactVelocity_agreement {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    WitnessFeasibility.velocity WitnessFeasibility.selected.schedule =ᶠ[𝓝 z]
      compactVelocity :=
  MixedPeriodicAssembly.activated_periodicVelocity_eventuallyEq_cut _ _ z hz

theorem compactVelocity_smooth_slice {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x => compactVelocity (t, x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hs : ContDiffAt ℝ ∞ compactVelocity (t, x) := by
    by_cases hx : x ∈ SpatialLocalization.supportCylinder
    · have hi : x ∈ PeriodicLocalization.innerCube (1 / 4) := by
        intro i
        have hb := SpatialLocalization.supportCylinder_coordinate_bound hx i
        change |x i| < 1 - 1 / 4
        linarith
      exact (smooth_at_interior WitnessFeasibility.selected.candidate.velocity_smooth ht x).congr_of_eventuallyEq
        (compactVelocity_agreement (z := (t, x)) hi).symm
    · exact contDiffAt_const.congr_of_eventuallyEq (compactVelocity_zero_germ (z := (t, x)) hx)
  exact hs.comp x (contDiffAt_const.prodMk contDiffAt_id)

theorem compactVelocity_divergence_free {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (x : Space) : spatialDivergence compactVelocity t x = 0 := by
  by_cases hx : x ∈ SpatialLocalization.supportCylinder
  · have hi : x ∈ PeriodicLocalization.innerCube (1 / 4) := by
      intro i
      have hb := SpatialLocalization.supportCylinder_coordinate_bound hx i
      change |x i| < 1 - 1 / 4
      linarith
    rw [← MixedPeriodicAssembly.spatialDivergence_congr (compactVelocity_agreement (z := (t, x)) hi)]
    exact WitnessFeasibility.selected.candidate.divergence_free t ht x
  · rw [MixedPeriodicAssembly.spatialDivergence_congr (compactVelocity_zero_germ (z := (t, x)) hx)]
    simp [spatialDivergence, spatialDerivative]

theorem compactVelocity_compact_support (t : ℝ) :
    HasCompactSupport (fun x => compactVelocity (t, x)) := by
  apply SpatialLocalization.isCompact_supportCylinder.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ SpatialLocalization.isClosed_supportCylinder
  intro x hx
  by_contra hn
  exact hx (compactVelocity_zero_outside t hn)

/-- Checked actual-candidate total compact momentum, for every interior time.
This does not yet identify a periodic cell integral of the selected force. -/
theorem selected_compact_momentum_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (i : Fin 3) : (∫ x, compactVelocity (t, x) i) = 0 := by
  apply compact_component_integral_zero (compactVelocity_smooth_slice ht)
    (compactVelocity_compact_support t)
  exact compactVelocity_divergence_free ⟨ht.1.le, ht.2⟩

/-- The actual compact nonlinear transport has zero component integral. -/
theorem selected_compact_transport_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (i : Fin 3) :
    (∫ x, fderiv ℝ (fun y => compactVelocity (t, y) i) x
      (compactVelocity (t, x))) = 0 := by
  have hv := compactVelocity_smooth_slice ht
  have h := NavierStokesR3.CompactEnergy.integral_fderiv_apply
    (NavierStokes.SolutionDifference.component_contDiff hv i) hv
    (compactVelocity_compact_support t)
  have hd (x : Space) :
      (∑ j : Fin 3, spatialPartial j (fun y => compactVelocity (t, y)) x j) = 0 :=
    compactVelocity_divergence_free ⟨ht.1.le, ht.2⟩ x
  simpa only [hd, mul_zero, integral_zero, neg_zero] using h

/-- Closed-slab continuity of the selected force's actual vector cell mean.
In particular a slab ending at one needs no terminal velocity regularity. -/
theorem selected_force_mean_continuousOn (a b : ℝ) :
    ContinuousOn (fun t => cubeIntegral (fun x => WitnessFeasibility.selected.forcing (t, x)))
      (Icc a b) :=
  cubeIntegral_continuousOn_Icc WitnessFeasibility.selected.smooth.continuous.continuousOn

/-- Necessary harmonic test for a periodic potential, using actual coordinate
partials and the library's unit-volume cube measure. Sufficiency is not claimed. -/
theorem periodic_potential_component_mean_zero {φ : Space → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hp : UnitPeriods φ) (i : Fin 3) :
    cubeIntegral (fun x => fderiv ℝ φ x (coordinateVector i)) = 0 :=
  cubeIntegral_partial_eq_zero hφ hp i

#print axioms compact_component_integral_zero
#print axioms compactVelocity
#print axioms compactVelocity_zero_outside
#print axioms compactVelocity_zero_germ
#print axioms compactVelocity_agreement
#print axioms compactVelocity_smooth_slice
#print axioms compactVelocity_divergence_free
#print axioms compactVelocity_compact_support
#print axioms selected_compact_momentum_zero
#print axioms selected_compact_transport_zero
#print axioms selected_force_mean_continuousOn
#print axioms periodic_potential_component_mean_zero
end UnforcedRestart.Round3.MeanTopology
