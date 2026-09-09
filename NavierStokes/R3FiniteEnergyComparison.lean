import NavierStokes.R3.WholeSpaceUniqueness
import NavierStokes.R3CompactCandidate
import NavierStokes.ComparatorR3Bridge

/-!
# The whole-space exclusion: no global solution extends the compact candidate

This is the (C) branch of the delivered argument, steps two and three of the
three-step chain described in `NavierStokes/ComparatorR3Theorem.lean`:

* identification — a global finite-energy solution with the candidate's force
  and zero datum agrees with the compact candidate on every `[0,t]`, `t < 1`
  (`NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`, ported
  from the verified `ℝ³` development; the competitor retains exactly the
  smoothness and finite-energy conditions of the comparator, the candidate's
  compact support supplies the reference bounds);
* contradiction — `R3CompactCandidate.Properties.not_global_agreement`.

`compact_candidate_excludes_global_solution` is the composite consumed by the
adapter; it has the same signature as the periodic exclusion
`MaximalLifespan.candidate_excludes_global_solution`.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem GlobalSolutionRn.uniformFiniteEnergy {f v : VelocityField} {q : PressureField}
    (h : GlobalSolutionRn f v q) (T : ℝ) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
  intro t ht
  constructor
  · simpa only [NavierStokesR3.ProblemStatement.SquareIntegrableAtTime, norm_norm] using!
      (memLp_two_iff_integrable_sq_norm (h.integrable t ht.1).1).mp (h.integrable t ht.1)
  · change (1 / 2 : ℝ) * (∫ x : Space, ‖v (t, x)‖ ^ 2) ≤ max 0 (E / 2)
    have hb := (hE t ht.1).le
    have hm := le_max_right 0 (E / 2)
    linarith

/-- Step two of the whole-space argument: identification below time one, by
whole-space uniqueness on each closed interval `[0, t]`. -/
theorem compact_candidate_agree_on_overlap
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) (hv : GlobalSolutionRn f v q) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x) := by
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  intro t ht x
  by_cases ht0 : t = 0
  · subst t
    rw [h.zero_initial_velocity, hv.zero_initial_velocity]
  have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hI : Icc 0 t ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right ht.2
  have hu' := h.toSolution.mono hI
  have hv' := hv.toSolution.mono (Icc_subset_Ici_self : Icc (0 : ℝ) t ⊆ Ici 0)
  have hsupport : ∀ r ∈ Icc (0 : ℝ) t, tsupport (fun y => u (r, y)) ⊆ K := by
    intro r hr
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (hs r (hI hr) y hyK)
  exact NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc hpos
    hu'.velocity_smooth hv'.velocity_smooth hu'.pressure_smooth hv'.pressure_smooth
    hK hsupport (hv.uniformFiniteEnergy t)
    (fun r hr => hu'.divergence_free r ⟨hr.1.le, hr.2.le⟩)
    (fun r hr => hv'.divergence_free r ⟨hr.1.le, hr.2.le⟩)
    (fun r hr y => (hu'.navier_stokes r ⟨hr.1.le, hr.2.le⟩ hr.1 y).trans
      (hv'.navier_stokes r ⟨hr.1.le, hr.2.le⟩ hr.1 y).symm)
    (fun y => (h.zero_initial_velocity y).trans (hv.zero_initial_velocity y).symm)
    t ⟨ht.1, le_rfl⟩ x

/-- The whole-space exclusion, option (C): a compact candidate with unbounded
speed excludes every global smooth solution having the comparator's
finite-energy bound. -/
theorem compact_candidate_excludes_global_solution
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) (hv : GlobalSolutionRn f v q) : False :=
  h.not_global_agreement hv.velocity_smooth (compact_candidate_agree_on_overlap h hv)

end NavierStokes.ComparatorBridge
