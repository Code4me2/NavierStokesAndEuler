import NavierStokes.TimeLocalization
import NavierStokes.ComparatorBridge
import NavierStokes.PeriodicLocalization

noncomputable section
namespace UnforcedRestart.PeriodicRestartData
open NavierStokes NavierStokes.ProblemStatement Set
open scoped ContDiff

/-- The genuine Comparator datum contract, without any zero-datum requirement. -/
theorem snapshot_admissible {u : VelocityField} {t₀ : ℝ}
    (ht : t₀ ∈ Ico (0 : ℝ) 1)
    (hs : ContDiffOn ℝ ∞ u preSingularDomain)
    (hd : ∀ x : Space, spatialDivergence u t₀ x = 0)
    (hp : UnitSpatialPeriodsOn (Ico 0 1) u) :
    Comparator.InitialVelocityConditionPeriodic (fun x : Space => u (t₀, x)) := by
  refine ⟨⟨?_, TimeLocalization.spatial_smooth_including_initial u hs t₀ ht⟩, ?_⟩
  · intro x
    rw [← ComparatorBridge.divergence_eq]
    exact hd x
  · exact hp t₀ ht

/-- Every interior snapshot of a repository candidate is admissible periodic data. -/
theorem candidate_snapshot {u f : VelocityField} {p : PressureField}
    (hc : CandidateProperties u p f) {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1) :
    Comparator.InitialVelocityConditionPeriodic (fun x : Space => u (t₀, x)) :=
  snapshot_admissible ⟨h0.le, h1⟩ hc.velocity_smooth
    (hc.divergence_free t₀ ⟨h0.le, h1⟩) hc.velocity_periodic

/-- Pressure is a smooth periodic scalar slice, not an initial velocity datum. -/
theorem candidate_pressure_snapshot {u f : VelocityField} {p : PressureField}
    (hc : CandidateProperties u p f) {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1) :
    ContDiff ℝ ∞ (fun x : Space => p (t₀, x)) ∧
      Comparator.IsOnePeriodic (fun x : Space => p (t₀, x)) :=
  ⟨TimeLocalization.spatial_smooth_including_initial p hc.pressure_smooth
      t₀ ⟨h0.le, h1⟩, hc.pressure_periodic t₀ ⟨h0.le, h1⟩⟩

/-- Taking a snapshot commutes with the actual spatial lattice sum.
No convergence or PDE superposition claim is needed for this identity. -/
theorem periodize_snapshot {V : Type*} [NormedAddCommGroup V]
    (g : SpaceTime → V) (t₀ : ℝ) (x : Space) :
    PeriodicLocalization.periodize g (t₀, x) =
      ∑' n : PeriodicLocalization.Lattice, g (t₀, x - PeriodicLocalization.lattice n) := rfl

/-- A time-dependent spatially constant gauge preserves pressure periodicity. -/
theorem pressure_gauge_periodic {p : PressureField} {I : Set ℝ}
    (hp : UnitSpatialPeriodsOn I p) (c : ℝ → ℝ) :
    UnitSpatialPeriodsOn I (fun z => p z + c z.1) := by
  intro t ht x i
  change p (t, x + coordinateVector i) + c t = p (t, x) + c t
  rw [hp t ht x i]

end UnforcedRestart.PeriodicRestartData

#print axioms UnforcedRestart.PeriodicRestartData.snapshot_admissible
#print axioms UnforcedRestart.PeriodicRestartData.candidate_snapshot
#print axioms UnforcedRestart.PeriodicRestartData.candidate_pressure_snapshot
#print axioms UnforcedRestart.PeriodicRestartData.periodize_snapshot
#print axioms UnforcedRestart.PeriodicRestartData.pressure_gauge_periodic
