import Euler.PacketTimePathGluing
import Euler.ParameterSobolevLinear

/-! Matching time paths glue without any external-word or fixed-Sobolev loss. -/

noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerTimeIntervalGlue EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

@[simp] theorem glueOperator_apply (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) :
    glueOperator S τ hτ0 hτS u = gluePath S τ hτ0 hτS u := rfl

theorem gluePath_left (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) (t : Icc (0 : ℝ) τ) :
    gluePath S τ hτ0 hτS u ⟨t, t.property.1, t.property.2.trans hτS⟩=u.val.1 t := by
  change glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t = _
  rw [glue_left τ _ _ t t.property.2, projIcc_of_mem hτ0 t.property]




variable [Fintype ι]


/-- Fixed H6 is the specialization q=6; no tensor-to-word conversion occurs. -/
theorem glue_block_bound (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (q : ℕ) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => gluePath S τ hτ0 hτS (f y)) n x ≤
      block directions q f n x := by
  have h := block_comp_clm_le directions q (glueOperator S τ hτ0 hτS) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right
    (glueOperator_norm_le_one S τ hτ0 hτS) (block_nonneg directions q f n x)).trans_eq (one_mul _))

end EulerPacketTimePathGluing
