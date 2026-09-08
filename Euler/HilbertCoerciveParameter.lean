import Euler.TransverseVariationalOperator

/-!
# Parameter regularity of the genuinely constructed coercive inverse

The positive lower-bound certificate may vary with the parameter and need not
be differentiable. The inverse itself is the actual operator inverse, so its
regularity depends only on the operator coefficients.
-/

noncomputable section

open scoped ContDiff

namespace EulerHilbertCoerciveParameter

open ContinuousLinearMap InnerProductSpace EulerCoerciveProjection EulerInverseRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Changing the coercivity certificate does not affect parameter regularity
of the actual inverse operator. -/
theorem contDiff_coerciveInverse_variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hA : ∀ x v, c x * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    {n : ℕ∞ω} (hreg : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => coerciveInverse (A x) (c x) (hc x) (hA x)) := by
  have hfun : (fun x => coerciveInverse (A x) (c x) (hc x) (hA x)) =
      fun x => (A x).inverse := by
    funext x
    exact coerciveInverse_eq_mapInverse (A x) (c x) (hc x) (hA x)
  rw [hfun, contDiff_iff_contDiffAt]
  intro x
  have he : (coerciveEquiv (A x) (c x) (hc x) (hA x) : E →L[ℝ] E) = A x := by
    ext v
    exact coerciveEquiv_apply (A x) (c x) (hc x) (hA x) v
  have hinv : ContDiffAt ℝ n ContinuousLinearMap.inverse (A x) := by
    rw [← he]
    exact contDiffAt_map_inverse (coerciveEquiv (A x) (c x) (hc x) (hA x))
  exact hinv.comp x hreg.contDiffAt


/-- Actual forcing-to-solution regularity for a parameterized coercive solve. -/
theorem contDiff_coerciveSolution_variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hA : ∀ x v, c x * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    (f : P → E) {n : ℕ∞ω} (hreg : ContDiff ℝ n A) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => coerciveInverse (A x) (c x) (hc x) (hA x) (f x)) :=
  (contDiff_coerciveInverse_variable A c hc hA hreg).clm_apply hf

end EulerHilbertCoerciveParameter
