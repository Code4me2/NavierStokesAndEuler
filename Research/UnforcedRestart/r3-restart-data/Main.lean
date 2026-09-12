import NavierStokes.R3CompactCandidate
import NavierStokes.TimeLocalization
import NavierStokes.ActualCandidateAssembly

noncomputable section

namespace UnforcedRestart.R3RestartData

open Set Function NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff Topology

/-- Spatial smoothness includes time zero, but excludes the singular time. -/
theorem snapshot_smooth {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x : Space => u (t, x)) :=
  TimeLocalization.spatial_smooth_including_initial u h.velocity_smooth t ht

theorem snapshot_divergence {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ∀ x : Space, Comparator.divergence (fun y => u (t, y)) x = 0 := by
  intro x
  rw [← ComparatorBridge.divergence_eq]
  exact h.divergence_free t ht x

/-- One compact set supports every spatial jet at every presingular slice. -/
theorem fixed_jet_support {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) :
    ∃ K : Set Space, IsCompact K ∧ ∀ t ∈ Ico (0 : ℝ) 1, ∀ m : ℕ,
      tsupport (iteratedFDeriv ℝ m (fun x : Space => u (t, x))) ⊆ K := by
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  refine ⟨K, hK, ?_⟩
  intro t ht m
  apply (tsupport_iteratedFDeriv_subset m).trans
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (hs t ht x hn)

/-- Full Frechet jets, with every real decay exponent (not just integers). -/
theorem compact_smooth_decay {a : Space → Space} (ha : ContDiff ℝ ∞ a)
    {S : Set Space} (hS : IsCompact S)
    (hs : ∀ m : ℕ, tsupport (iteratedFDeriv ℝ m a) ⊆ S)
    (m : ℕ) (k : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖iteratedFDeriv ℝ m a x‖ ≤ C / (1 + ‖x‖) ^ k := by
  have hj : Continuous (iteratedFDeriv ℝ m a) :=
    ha.continuous_iteratedFDeriv (by simp)
  have hw : Continuous (fun x : Space => (1 + ‖x‖) ^ k) := by
    apply (continuous_const.add continuous_norm).rpow_const
    intro x
    left
    change 1 + ‖x‖ ≠ 0
    exact ne_of_gt (by positivity)
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hj.norm.mul hw).continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hp : 0 < (1 + ‖x‖) ^ k := Real.rpow_pos_of_pos (by positivity) k
  by_cases hx : x ∈ S
  · apply (le_div_iff₀ hp).mpr
    exact (le_abs_self _).trans ((hM x hx).trans (le_max_left _ _))
  · have hz : iteratedFDeriv ℝ m a x = 0 := by
      by_contra hn
      exact hx (hs m (subset_closure hn))
    rw [hz, norm_zero]
    exact le_of_lt (div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hp)

/-- Admissibility in the real delivered whole-space initial-data predicate. -/
theorem snapshot_admissible {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    Comparator.InitialVelocityConditionDecay (fun x : Space => u (t, x)) := by
  refine ⟨⟨snapshot_divergence h ht, snapshot_smooth h ht⟩, ?_⟩
  obtain ⟨K, hK, hs⟩ := fixed_jet_support h
  intro m k
  obtain ⟨C, _, hC⟩ := compact_smooth_decay (snapshot_smooth h ht) hK (hs t ht) m k
  exact ⟨C, hC⟩

theorem snapshot_compactSupport {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    HasCompactSupport (fun x : Space => u (t, x)) := by
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (hs t ht x hn)

/-- Finite kinetic energy at each slice, with whole-space Lebesgue volume. -/
theorem snapshot_energy_integrable {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    MeasureTheory.Integrable (fun x : Space => ‖u (t, x)‖ * ‖u (t, x)‖) := by
  have hc := (snapshot_smooth h ht).continuous.norm
  exact (hc.mul hc).integrable_of_hasCompactSupport
    (snapshot_compactSupport h ht).norm.mul_right

/-- Closed assembly supplies a genuine compact candidate with admissible snapshots.
No unforced continuation or terminal force removal is asserted. -/
theorem actual_candidate_restart_data :
    ∃ (u : VelocityField) (p : PressureField) (f : VelocityField),
      R3CompactCandidate.Properties u p f ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        Comparator.InitialVelocityConditionDecay (fun x : Space => u (t, x)) ∧
        MeasureTheory.Integrable (fun x : Space => ‖u (t, x)‖ * ‖u (t, x)‖) := by
  obtain ⟨a, _, ea, eb, ep, f, _, _, _, _, _, _, fc, hc⟩ :=
    ActualCandidateAssembly.selected_witness
  refine ⟨_, _, fc, hc, ?_⟩
  intro t ht0 ht1
  exact ⟨snapshot_admissible hc ⟨ht0.le, ht1⟩,
    snapshot_energy_integrable hc ⟨ht0.le, ht1⟩⟩

#print axioms actual_candidate_restart_data
#print axioms snapshot_smooth
#print axioms snapshot_divergence
#print axioms fixed_jet_support
#print axioms compact_smooth_decay
#print axioms snapshot_admissible
#print axioms snapshot_compactSupport
#print axioms snapshot_energy_integrable

end UnforcedRestart.R3RestartData
