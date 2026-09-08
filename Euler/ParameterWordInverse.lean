import Euler.ParameterWordProduct
import Euler.BoundedInverseGevrey

/-!
# A genuine inverse recurrence for the unchanged word sums

Freeze the actual left inverse at a parameter value. The coefficient
difference vanishes there, so the direct word-product estimate removes the
top unknown term. The same factorial radius is used for input and output.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Freezing the actual inverse yields the sharp recurrence for actual ordered word sums. -/
theorem inverse_word_recurrence (directions : ι → P)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y) (x : P)
    (I : E →L[ℝ] E) (hI : ∀ v, I (A x v) = v) (n : ℕ) :
    wordSum directions u n x ≤ ‖I‖ *
      (wordSum directions f n x + ∑ j ∈ range n,
        (n.choose (j+1) : ℝ) * wordSum directions A (j+1) x *
          wordSum directions u (n-(j+1)) x) := by
  let B : P → E →L[ℝ] E := A-fun _ => A x
  have hB : ContDiff ℝ ∞ B := hA.sub contDiff_const
  have hBu : ContDiff ℝ ∞ (fun y => B y (u y)) := hB.clm_apply hu
  have hfreeze : u = I ∘ (f-fun y => B y (u y)) := by
    funext y
    dsimp [B]
    rw [sub_apply, ← heq y, sub_sub_cancel]
    exact (hI (u y)).symm
  have hzero : wordSum directions B 0 x = 0 := by
    rw [wordSum_zero]
    simp only [B, Pi.sub_apply, sub_self, norm_zero]
  have hpos (j : ℕ) : wordSum directions B (j+1) x = wordSum directions A (j+1) x :=
    wordSum_sub_const_succ directions A hA (A x) j x
  have hprod := wordSum_clm_apply_le directions B u hB hu n x
  unfold leibnizConvolution at hprod
  rw [sum_range_succ'] at hprod
  simp only [hzero, mul_zero, zero_mul, add_zero, hpos] at hprod
  have hbound := wordSum_comp_clm_le directions I (f-fun y => B y (u y)) (hf.sub hBu) n x
  rw [← hfreeze] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    ((wordSum_sub_le directions f (fun y => B y (u y)) hf hBu n x).trans
      (add_le_add le_rfl hprod)) (norm_nonneg I))


end EulerParameterWordGevrey
