import NavierStokes.ComparatorBridge

/-!
# The finite-energy add-on for the whole-space comparator

The whole-space competitor keeps the comparator's square integrability and
uniform kinetic energy bound; nothing periodic or compactly supported is
assumed of it. The normalization itself is `ComparatorBridge.normalized_solution_core`.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem zero_initial_condition_decay :
    Comparator.InitialVelocityConditionDecay (fun _ : Space => (0 : Space)) := by
  refine ⟨⟨fun x => Comparator.divergence_const 0 x, contDiff_const⟩, ?_⟩
  intro m K
  exact ⟨0, by simp⟩

/-- A global whole-space viscosity-one solution with zero datum and the
comparator's finite-energy bound: what a hypothetical comparator solution for
option (C) becomes after coordinate swap and viscosity normalization. -/
structure GlobalSolutionRn (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop
    extends Solution (Ici 0) f v p where
  integrable : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Space => ‖v (t, x)‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v (t, x)‖ ^ 2) < E

/-- The finite-energy add-on: a hypothetical solution of the whole-space
comparator statement normalizes to a `GlobalSolutionRn`. -/
theorem normalized_solution_Rn {ν : ℝ} (hν : 0 < ν) {f : VelocityField}
    {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : Comparator.NavierStokesExistenceAndSmoothnessRn ν (fun _ => 0)
      (toComparator (rescaledForce ν f)) v p) :
    GlobalSolutionRn f (rescale ν⁻¹ ν⁻¹ (fromComparator v))
      (rescale (ν⁻¹ ^ 2) ν⁻¹ (fromComparator p)) := by
  have hc : 0 < ν⁻¹ := inv_pos.mpr hν
  refine ⟨normalized_solution_core hν h.toNavierStokesExistenceAndSmoothness, ?_, ?_⟩
  · intro t ht
    simpa only [rescale, fromComparator, norm_smul] using
      (h.integrable (ν⁻¹ * t) (mul_nonneg hc.le ht)).const_mul ‖ν⁻¹‖
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨ν⁻¹ ^ 2 * E, ?_⟩
    intro t ht
    simp only [rescale, fromComparator, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc, mul_pow, integral_const_mul]
    exact mul_lt_mul_of_pos_left (hE (ν⁻¹ * t) (mul_nonneg hc.le ht)) (sq_pos_of_pos hc)

end NavierStokes.ComparatorBridge
