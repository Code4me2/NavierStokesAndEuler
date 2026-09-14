import NavierStokes.MaximalLifespan

/-!
Diagnostic reductions for the local-theory audit. No existence theorem for
nonzero data, continuation theorem, or stability estimate is asserted.
-/

namespace UnforcedRestart.LocalTheoryObstruction

open Set NavierStokes.ProblemStatement NavierStokes.MaximalLifespan
open scoped ContDiff

/-- Restricting the time set in `Solution` never removes its zero-datum field.
In particular this structure cannot encode a nonzero snapshot restart. -/
theorem nonzero_snapshot_not_solution
    {u f : VelocityField} {p : PressureField} {I : Set ℝ} {t₀ : ℝ}
    (ha : ∃ x : Space, u (t₀, x) ≠ 0) :
    ¬ Solution I f (fun z => u (t₀ + z.1, z.2)) p := by
  intro h
  obtain ⟨x, hx⟩ := ha
  exact hx (by simpa only [add_zero] using h.zero_initial_velocity x)

/-- Keeping both physical fields fixed keeps the force fixed at every point
where both residual equations hold. No uniqueness theorem is involved. -/
theorem unchanged_fields_force_rigidity
    {u f g : VelocityField} {p : PressureField} {t : ℝ} {x : Space}
    (hf : navierStokesResidual u p t x = f (t, x))
    (hg : navierStokesResidual u p t x = g (t, x)) :
    f (t, x) = g (t, x) := hf.symm.trans hg

/-- A periodic, zero-datum, viscosity-one solution with zero force is zero
on its lifespan. This uses the actual repository energy uniqueness theorem.
It does not apply to a nonzero restart datum. -/
theorem zero_datum_unforced_periodic_is_zero
    {T : ℝ} {u : VelocityField} {p : PressureField}
    (hu : ClassicalSolution (fun _ => 0) T u p) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = 0 := by
  have hz : ClassicalSolution (fun _ => 0) T (fun _ => 0) (fun _ => 0) := {
    velocity_smooth := contDiffOn_const
    pressure_smooth := contDiffOn_const
    zero_initial_velocity := fun _ => rfl
    divergence_free := fun _ _ _ => by simp [spatialDivergence, spatialDerivative]
    navier_stokes := fun t _ _ x => zero_residual t x
    lifespan_pos := hu.lifespan_pos
    velocity_periodic := fun _ _ _ _ => rfl
    pressure_periodic := fun _ _ _ _ => rfl
  }
  simpa only [min_self, VelocityAgreesOn] using hu.agree_on_overlap hz

#print axioms UnforcedRestart.LocalTheoryObstruction.nonzero_snapshot_not_solution
#print axioms UnforcedRestart.LocalTheoryObstruction.unchanged_fields_force_rigidity
#print axioms UnforcedRestart.LocalTheoryObstruction.zero_datum_unforced_periodic_is_zero

end UnforcedRestart.LocalTheoryObstruction
