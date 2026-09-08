import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Scalar flatness and fixed power losses

This file isolates the scalar asymptotic argument used in Lemmas 11.2--11.5
of the candidate manuscript. It proves neither the asserted bounds for physical
jets nor the existence, compatibility, or smooth extension of those jets.

All powers here have natural exponents. Constants and neighborhoods may depend
on the requested power, as they do in a flatness statement.
-/

open Filter Topology

namespace NavierStokes.Flatness

variable {α : Type*} {l : Filter α} {q f g : α → ℝ}

/-- Along `l`, `f` is eventually bounded by a constant times every natural
power of the absolute value of the scale `q`. -/
def PowerFlat (l : Filter α) (q f : α → ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, |f x| ≤ C * |q x| ^ n

/-- An exact scalar estimate: `n + loss` powers of smallness absorb `loss`
powers in a nonzero denominator. No assumption that the scale is small is
needed for this algebraic step. -/
theorem fixed_power_loss_bound {x scale C : ℝ} {n loss : ℕ}
    (hscale : scale ≠ 0) (hx : |x| ≤ C * |scale| ^ (n + loss)) :
    |x / scale ^ loss| ≤ C * |scale| ^ n := by
  rw [abs_div, abs_pow]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hscale) loss)).2
  simpa only [pow_add, mul_assoc] using hx

/-- Arbitrary power decay persists after any fixed inverse-power loss. -/
theorem PowerFlat.div_pow (hf : PowerFlat l q f)
    (hq : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) :
    PowerFlat l q (fun x => f x / q x ^ loss) := by
  intro n
  obtain ⟨C, hC, hbound⟩ := hf (n + loss)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hbound] with x hx hfx
  exact fixed_power_loss_bound hx hfx

/-- Flat estimates are stable under finite addition. -/
theorem PowerFlat.add (hf : PowerFlat l q f) (hg : PowerFlat l q g) :
    PowerFlat l q (fun x => f x + g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf n
  obtain ⟨D, hD, hgb⟩ := hg n
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [hfb, hgb] with x hfx hgx
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * |q x| ^ n + D * |q x| ^ n := add_le_add hfx hgx
    _ = (C + D) * |q x| ^ n := (add_mul _ _ _).symm

/-- Flat estimates are stable under multiplication. Only boundedness of the
second factor, the `n = 0` case of its flatness, is used. -/
theorem PowerFlat.mul (hf : PowerFlat l q f) (hg : PowerFlat l q g) :
    PowerFlat l q (fun x => f x * g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf n
  obtain ⟨D, hD, hgb⟩ := hg 0
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  filter_upwards [hfb, hgb] with x hfx hgx
  have hgx' : |g x| ≤ D := by simpa only [pow_zero, mul_one] using hgx
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C * |q x| ^ n) * D :=
      mul_le_mul hfx hgx' (abs_nonneg _) (mul_nonneg hC (pow_nonneg (abs_nonneg _) _))
    _ = (C * D) * |q x| ^ n := by ring





end NavierStokes.Flatness
