import Euler.PacketMomentumExpansion

/-! Bounds for the surviving grades of the actual finite packet residual. -/

noncomputable section

namespace EulerPacketTailBound

open Finset

theorem sum_geometric_le_two (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (N : ℕ) :
    (∑ i ∈ range N, q^i) ≤ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ']
      simp only [pow_succ, pow_zero]
      rw [← sum_mul]
      have h := mul_le_mul_of_nonneg_right ih hq
      linarith

theorem sum_geometric_Ico_le (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (a b : ℕ) :
    (∑ i ∈ Ico a b, q^i) ≤ 2*q^a := by
  rw [sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (sum_geometric_le_two q hq hqhalf (b-a))
    (pow_nonneg hq a)).trans_eq (mul_comm _ _)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



end EulerPacketTailBound
