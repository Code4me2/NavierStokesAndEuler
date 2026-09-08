import Euler.HilbertCoerciveParameter
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual all-order estimates for a coercive inverse

At a parameter value `x`, freeze the inverse of `A x` and write
`u y = (A x)⁻¹ (f y - (A y - A x) (u y))`. The coefficient difference
vanishes at `x`, so differentiating gives a triangular estimate with no
highest-order solution term on the right. The factorial estimate below is
therefore derived from genuine derivatives of the constructed inverse.
-/

noncomputable section

open scoped ContDiff

namespace EulerHilbertCoerciveGevrey

open ContinuousLinearMap Finset InnerProductSpace EulerGevrey
  EulerCoerciveProjection EulerHilbertCoerciveParameter

section Normed

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Freezing the coefficient gives the actual triangular derivative bound. -/
theorem derivative_recurrence
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y) (x : P)
    (I : E →L[ℝ] E) (hI : ∀ v, I (A x v) = v) (n : ℕ) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ ‖I‖ *
      (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
        (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) A x‖ *
          ‖iteratedFDeriv ℝ (n-(j+1)) u x‖) := by
  let B : P → E →L[ℝ] E := fun y => A y - A x
  have hB : ContDiff ℝ ∞ B := hA.sub contDiff_const
  have hBu : ContDiff ℝ ∞ (fun y => B y (u y)) := hB.clm_apply hu
  have hfreeze : u = I ∘ (fun y => f y - B y (u y)) := by
    funext y
    dsimp [B]
    rw [sub_apply, ← heq y, sub_sub_cancel]
    exact (hI (u y)).symm
  have hzero : ‖iteratedFDeriv ℝ 0 B x‖ = 0 := by
    rw [norm_iteratedFDeriv_zero]
    simp [B]
  have hpositive (j : ℕ) :
      iteratedFDeriv ℝ (j+1) B x = iteratedFDeriv ℝ (j+1) A x := by
    change iteratedFDeriv ℝ (j+1) (A - fun _ => A x) x = _
    rw [iteratedFDeriv_sub_apply (hA.contDiffAt.of_le (by simp)) contDiffAt_const]
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
  have hprod := norm_iteratedFDeriv_clm_apply hB hu x (n := n) (by simp)
  rw [sum_range_succ'] at hprod
  simp only [hzero, mul_zero, zero_mul, add_zero, hpositive] at hprod
  have hsub : ‖iteratedFDeriv ℝ n (fun y => f y - B y (u y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n (fun y => B y (u y)) x‖ := by
    change ‖iteratedFDeriv ℝ n (f - fun y => B y (u y)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp))
      (hBu.contDiffAt.of_le (by simp))]
    exact norm_sub_le _ _
  have hbound := I.norm_iteratedFDeriv_comp_left (x := x)
    ((hf.sub hBu).contDiffAt) (n := n) (by simp)
  rw [← hfreeze] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (hsub.trans (add_le_add (le_refl ‖iteratedFDeriv ℝ n f x‖) hprod)) (norm_nonneg I))

end Normed

section Hilbert

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]




end Hilbert

end EulerHilbertCoerciveGevrey
