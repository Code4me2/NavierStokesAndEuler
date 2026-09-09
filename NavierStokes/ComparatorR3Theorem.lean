import NavierStokes.R3FiniteEnergyComparison
import NavierStokes.R3ActualCandidate

/-!
# The constructed compact candidate implies option (C)

The whole-space deliverable is the same three-step chain as the periodic one
(`ComparatorTheorem`), with the compact set and the uniqueness theorem changed:

1. **A reference solution with unbounded speed at time one.**
   `R3CompactCandidate.selected_compact_candidate` gives `(u, p, f)` with
   `R3CompactCandidate.Properties u p f`: the same witness before
   periodization, compactly supported in space.
2. **Identification.** A hypothetical global comparator solution rescales to a
   global finite-energy viscosity-one solution
   (`ComparatorBridge.normalized_solution_Rn`), which by whole-space
   uniqueness agrees with `u` below time one
   (`ComparatorBridge.compact_candidate_agree_on_overlap`).
3. **Contradiction by compactness.** It is continuous on `[0,1] × K` for the
   candidate's support `K`, off which `u` vanishes
   (`R3CompactCandidate.Properties.not_global_agreement`, through the shared
   `SpeedUnboundedAtOne.false_of_agree`).

Steps 2 and 3 are `ComparatorBridge.compact_candidate_excludes_global_solution`.
The comparator's decay bounds come from `CompactSpatialForceDecay.forceConditionDecay`.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff

/-- Any witness of the compact candidate conditions implies option (C), for
every positive viscosity, with all comparator hypotheses discharged. -/
theorem option_C_of_candidate
    {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : R3CompactCandidate.Properties u p f) (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨K, hK, hs⟩ := h.force_support
  refine ⟨fun _ => 0, toComparator (rescaledForce ν f), zero_initial_condition_decay,
    CompactSpatialForceDecay.forceConditionDecay hK
      (rescale_smooth h.force_smooth (ν ^ 2) hν.le)
      (CompactSpatialForceDecay.rescale_supported hs (ν ^ 2) hν.le)
      (rescale_support h.force_time_support (ν ^ 2) hν), ?_⟩
  rintro ⟨v, q, hv⟩
  exact compact_candidate_excludes_global_solution h (normalized_solution_Rn hν hv)

/-- Option (C) with exactly the comparator's quantifiers. -/
theorem navier_stokes_breakdown_R3 (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionDecay u₀ ∧ Comparator.ForceConditionDecay f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  obtain ⟨u, p, f, h⟩ := R3CompactCandidate.selected_compact_candidate
  exact option_C_of_candidate h ν hν

end NavierStokes.ComparatorBridge
