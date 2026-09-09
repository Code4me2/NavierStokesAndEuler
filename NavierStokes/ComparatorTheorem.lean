import NavierStokes.ComparatorBridge
import NavierStokes.MaximalLifespan
import NavierStokes.PeriodicForceDecay
import NavierStokes.ActualCandidateAssembly

/-!
# The constructed candidate implies option (D)

The periodic deliverable is a three-step chain, and this module is its top:

1. **A reference solution with unbounded speed at time one.**
   `ActualCandidateAssembly.selected_candidate` gives `(u, p, f)` with
   `CandidateProperties u p f`: a smooth periodic viscosity-one solution on
   `[0,1)` with zero datum, force smooth and vanishing after a finite time, and
   `SpeedUnboundedAtOne u`.
2. **Identification.** A hypothetical global comparator solution for viscosity
   `ν` with datum `0` and force `fν x t = ν² • f (ν t, x)` rescales to a global
   viscosity-one solution (`ComparatorBridge.normalized_solution`), which by
   periodic uniqueness agrees with `u` below time one
   (`MaximalLifespan.candidate_agree_on_overlap`).
3. **Contradiction by compactness.** It is continuous on `[0,1] × cube`, so
   `u` would be bounded before time one
   (`MaximalLifespan.candidate_no_solution_after_one`, through the shared
   `SpeedUnboundedAtOne.false_of_agree`).

Steps 2 and 3 are `MaximalLifespan.candidate_excludes_global_solution`. The
comparator's force-decay bounds come from `PeriodicForceDecay.forceConditionPeriodic`.
The whole-space deliverable (`ComparatorR3Theorem`) has the same three steps
with whole-space uniqueness and the candidate's support in place of the cube.
No result here uses any of the comparator's unproved statements.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement
open scoped ContDiff

/-- Any witness of the candidate contract implies option (D), for every
positive viscosity, with all comparator hypotheses discharged. -/
theorem option_D_of_candidate {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) := by
  refine ⟨fun _ => 0, toComparator (rescaledForce ν f), zero_initial_condition,
    PeriodicForceDecay.forceConditionPeriodic
      (rescale_smooth h.force_smooth (ν ^ 2) hν.le)
      (rescale_periodic h.force_periodic (ν ^ 2) hν.le)
      (rescale_support h.force_time_support (ν ^ 2) hν), ?_⟩
  rintro ⟨v, q, hv⟩
  exact MaximalLifespan.candidate_excludes_global_solution h (normalized_solution hν hv)

/-- Option (D), with exactly the comparator's quantifiers, from the project's
closed candidate construction. -/
theorem navier_stokes_breakdown_periodic (ν : ℝ) (hν : ν > 0) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) := by
  obtain ⟨u, p, f, h⟩ := ActualCandidateAssembly.selected_candidate
  exact option_D_of_candidate h ν hν

end NavierStokes.ComparatorBridge
