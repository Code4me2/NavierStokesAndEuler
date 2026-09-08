import Euler.ParameterSobolevCoefficient

/-! Exact parameter restriction and injective subalphabet bounds for genuine derivative words. -/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P Q E ι κ : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ]



omit [Fintype ι] in
/-- A linear parameter map transports the actual directions exactly. -/
theorem wordDerivative_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (f : Q → E) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f ∘ A) w x = wordDerivative (A ∘ directions) f w (A x) := by
  have h := congrArg (fun D : P[×n]→L[ℝ] E => D (fun j => directions (w j)))
    (A.iteratedFDeriv_comp_right hf x (i := n) (by simp))
  exact h

theorem wordSum_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (f : Q → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    wordSum directions (f ∘ A) n x = wordSum (A ∘ directions) f n (A x) := by
  unfold wordSum
  exact sum_congr rfl (fun w _ => congrArg norm (wordDerivative_comp_right directions A f hf w x))

/-- Restricting parameters does not change a fixed block when the directions are transported. -/
theorem block_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (q : ℕ) (f : Q → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block directions q (f ∘ A) n x = block (A ∘ directions) q f n (A x) := by
  rw [block_eq_sum_levels _ q _ (hf.comp A.contDiff),block_eq_sum_levels _ q _ hf]
  exact sum_congr rfl (fun k _ => wordSum_comp_right directions A f hf (n+k) x)

end EulerParameterWordGevrey
