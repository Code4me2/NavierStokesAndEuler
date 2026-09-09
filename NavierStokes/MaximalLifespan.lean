import NavierStokes.PeriodicUniqueness

/-!
# The periodic exclusion: no global solution extends the candidate

This is the (D) branch of the delivered argument, steps two and three of the
three-step chain described in `NavierStokes/ComparatorTheorem.lean`:

* identification — a classical periodic solution with the candidate's force
  and zero datum agrees with the candidate below time one
  (`candidate_agree_on_overlap`, from `PeriodicUniqueness.classical_uniqueness_on_Icc`);
* contradiction — a solution living past time one is continuous on
  `[0,1] × cube`, and periodicity reduces every value of the candidate to the
  cube, so `SpeedUnboundedAtOne` fails
  (`candidate_no_solution_after_one`, via `SpeedUnboundedAtOne.false_of_agree`).

`candidate_excludes_global_solution` is the composite consumed by the adapter;
it has the same signature as the whole-space exclusion
`ComparatorBridge.compact_candidate_excludes_global_solution`. The manuscript's
corollaries about maximality of the lifespan live in
`NavierStokes/CandidateConsequences.lean`, off this path. No general
Navier--Stokes existence theorem is assumed and pressure gauges are never
identified.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace NavierStokes.MaximalLifespan

open ProblemStatement PeriodicIntegration SolutionDifference

/-- A classical periodic solution of the viscosity-one equation with zero
datum on the finite positive lifespan `[0, T)`. Pressures are retained as
witnesses but are never required to agree with a different gauge. -/
structure ClassicalSolution (f : VelocityField) (T : ℝ) (u : VelocityField)
    (p : PressureField) : Prop extends Solution (Ico 0 T) f u p where
  lifespan_pos : 0 < T
  velocity_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) p

noncomputable def VelocityAgreesOn (T : ℝ) (u v : VelocityField) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)

theorem ClassicalSolution.restrict {f : VelocityField} {S T : ℝ} {u : VelocityField}
    {p : PressureField} (h : ClassicalSolution f T u p) (hS : 0 < S) (hST : S ≤ T) :
    ClassicalSolution f S u p where
  toSolution := h.toSolution.mono (Ico_subset_Ico_right hST)
  lifespan_pos := hS
  velocity_periodic := fun t ht => h.velocity_periodic t (Ico_subset_Ico_right hST ht)
  pressure_periodic := fun t ht => h.pressure_periodic t (Ico_subset_Ico_right hST ht)

/-- Any two classical solutions agree on their common interval. This is
derived by restriction to each compact subinterval and the proved energy
uniqueness theorem. Only velocity equality is asserted. -/
theorem ClassicalSolution.agree_on_overlap {f : VelocityField} {T S : ℝ}
    {u v : VelocityField} {p q : PressureField}
    (hu : ClassicalSolution f T u p) (hv : ClassicalSolution f S v q) :
    VelocityAgreesOn (min T S) u v := by
  intro t ht x
  have hT : Icc 0 t ⊆ Ico (0 : ℝ) T := Icc_subset_Ico_right (lt_min_iff.mp ht.2).1
  have hS : Icc 0 t ⊆ Ico (0 : ℝ) S := Icc_subset_Ico_right (lt_min_iff.mp ht.2).2
  have hu' := hu.toSolution.mono hT
  have hv' := hv.toSolution.mono hS
  refine PeriodicUniqueness.classical_uniqueness_on_Icc hu'.velocity_smooth hv'.velocity_smooth
    hu'.pressure_smooth hv'.pressure_smooth
    (fun r hr => hu.velocity_periodic r (hT hr)) (fun r hr => hv.velocity_periodic r (hS hr))
    (fun r hr => hu.pressure_periodic r (hT hr)) (fun r hr => hv.pressure_periodic r (hS hr))
    (fun r hr => hu'.divergence_free r ⟨hr.1.le, hr.2.le⟩)
    (fun r hr => hv'.divergence_free r ⟨hr.1.le, hr.2.le⟩)
    (fun r hr => hu'.navier_stokes r ⟨hr.1.le, hr.2.le⟩ hr.1)
    (fun r hr => hv'.navier_stokes r ⟨hr.1.le, hr.2.le⟩ hr.1)
    (fun y => (hu.zero_initial_velocity y).trans (hv.zero_initial_velocity y).symm)
    t ⟨ht.1, le_rfl⟩ x

theorem candidate_is_classical_solution {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ClassicalSolution f 1 u p :=
  ⟨h.toSolution, zero_lt_one, h.velocity_periodic, h.pressure_periodic⟩

/-- Step two of the periodic argument: identification below time one. -/
theorem candidate_agree_on_overlap {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f T v q) :
    VelocityAgreesOn (min T 1) v u :=
  hv.agree_on_overlap (candidate_is_classical_solution h)

/-- Step three of the periodic argument: no classical solution for the same
force and datum can have lifespan larger than one. It would be continuous on
`[0,1] × cube`, and by periodicity every value of the candidate is attained on
the cube, contradicting `SpeedUnboundedAtOne`. -/
theorem candidate_no_solution_after_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f) (hT : 1 < T)
    (hv : ClassicalSolution f T v q) : False := by
  have hagree := candidate_agree_on_overlap h hv
  refine h.speed_unbounded.false_of_agree PeriodicUniqueness.isCompact_cubeImage
    (hv.velocity_smooth.continuousOn.mono
      (prod_mono (Icc_subset_Ico_right hT) (subset_univ _))) ?_ ?_
  · intro t ht x _
    exact (hagree t ⟨ht.1, lt_min (ht.2.trans hT) ht.2⟩ x).symm
  · intro t ht x
    right
    obtain ⟨y, hy, hyx⟩ := PeriodicUniqueness.exists_cubeImage_representative
      (f := fun z : Space => u (t, z)) (fun i z => h.velocity_periodic t ht z i) x
    exact ⟨y, hy, hyx.symm⟩

theorem candidate_all_lifespans_le_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f T v q) : T ≤ 1 := by
  by_contra hnot
  exact candidate_no_solution_after_one h (lt_of_not_ge hnot) hv

/-- A global periodic solution restricts to a classical solution of every
positive lifespan. -/
theorem _root_.NavierStokes.ProblemStatement.GlobalSolutionOne.toClassicalSolution
    {f v : VelocityField} {q : PressureField} (hv : GlobalSolutionOne f v q)
    {T : ℝ} (hT : 0 < T) : ClassicalSolution f T v q where
  toSolution := hv.toSolution.mono Ico_subset_Ici_self
  lifespan_pos := hT
  velocity_periodic := fun t ht => hv.velocity_periodic t ht.1
  pressure_periodic := fun t ht => hv.pressure_periodic t ht.1

/-- The periodic exclusion, option (D): the candidate excludes every global
smooth periodic viscosity-one solution with its force and zero datum, because
such a solution would restrict to a forbidden lifespan greater than one. -/
theorem candidate_excludes_global_solution {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) (hv : GlobalSolutionOne f v q) :
    False :=
  candidate_no_solution_after_one h one_lt_two (hv.toClassicalSolution two_pos)

end NavierStokes.MaximalLifespan
