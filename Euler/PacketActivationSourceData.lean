import Euler.PacketActivationRay
import Euler.TransversePacketHistoryData

/-! The source deformation can be equipped with the actual activation
normal.  The new reference plane is the literal orthogonal complement,
and the history hypotheses are inherited without any new analytic input. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerPacketMovingFrame

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]






theorem Data.activationRayScale_bounds (D : Data U) (t₀ : Icc (0 : ℝ) D.T) (n : Space)
    (hn : ‖n‖=1) :
    0 < activationRayScale (D.deformationEquiv t₀ 0) n ∧
      activationRayScale (D.deformationEquiv t₀ 0) n ≤ D.inverseBound ∧
      (activationRayScale (D.deformationEquiv t₀ 0) n)⁻¹ ≤ D.frameBound := by
  have hn0 : n ≠ 0 := by intro hz; rw [hz,norm_zero] at hn; norm_num at hn
  let F := D.deformationEquiv t₀ 0
  have hpos : 0 < ‖F.toContinuousLinearMap.adjoint n‖ :=
    norm_pos_iff.mpr (forward_adjoint_ne_zero F hn0)
  have hlo : 1 ≤ D.inverseBound*‖F.toContinuousLinearMap.adjoint n‖ := by
    calc
      1 = ‖F.symm.toContinuousLinearMap.adjoint (F.toContinuousLinearMap.adjoint n)‖ := by
        rw [inverse_adjoint_forward_adjoint,hn]
      _ ≤ ‖F.symm.toContinuousLinearMap.adjoint‖*‖F.toContinuousLinearMap.adjoint n‖ :=
        F.symm.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ D.inverseBound*‖F.toContinuousLinearMap.adjoint n‖ := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_right (D.inverse_norm t₀ 0) (norm_nonneg _)
  have hhi : ‖F.toContinuousLinearMap.adjoint n‖ ≤ D.frameBound := by
    calc
      _ ≤ ‖F.toContinuousLinearMap.adjoint‖*‖n‖ := F.toContinuousLinearMap.adjoint.le_opNorm n
      _ = ‖D.F.field t₀ 0‖ := by rw [LinearIsometryEquiv.norm_map,hn,mul_one]; rfl
      _ ≤ D.frameBound := D.frame_norm t₀ 0
  refine ⟨activationRayScale_pos F hn0,?_,?_⟩
  · simpa only [activationRayScale,one_div] using (div_le_iff₀ hpos).mpr hlo
  · simpa only [activationRayScale,inv_inv] using hhi

end EulerTransversePacketProvider
