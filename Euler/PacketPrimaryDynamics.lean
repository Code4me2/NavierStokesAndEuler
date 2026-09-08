import Euler.PacketPrimaryFactorization
import Euler.PacketPrimaryScaling
import Euler.FixedEndpointClassical
import Euler.TransversePacketTimeData

/-! Tangency, the physical tangent ODE, and nonvanishing of the actual
canonical primary. Nonvanishing follows from the prescribed nonzero
terminal displacement, rather than from an assumption on the solved velocity. -/

noncomputable section

namespace EulerLinearDuhamel.Evolution

open Set ContinuousLinearMap EulerVolterraConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ} {hT : 0 ≤ T} {G : C(Icc (0 : ℝ) T,E →L[ℝ] E)}

/-- A zero of a genuine homogeneous solution propagates in either time direction. -/
theorem homogeneous_zero_at (U : Evolution T hT G) (f : ℝ → E)
    (hf : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt f (G t (f t)) (Icc (0 : ℝ) T) t)
    (s t : Icc (0 : ℝ) T) (hs : f s = 0) : f t = 0 := by
  let q : ℝ → E := fun r => extendPath T hT U.backward r (f r)
  have hq : ∀ r ∈ Icc (0 : ℝ) T, HasDerivWithinAt q 0 (Icc (0 : ℝ) T) r := by
    intro r hr
    have hd := (U.backward_derivative ⟨r,hr⟩).clm_apply (hf ⟨r,hr⟩)
    convert! hd using 1
    · simp only [neg_apply,comp_apply,extendPath,projIcc_of_mem hT hr]
      abel
  have he : q t = q s := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hq
      (fun r hr => by simp) (convex_Icc (0 : ℝ) T) s.property t.property
    simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using h
  have hqs : q s = 0 := by simp only [q,hs,map_zero]
  have ht : U.backward t (f t) = 0 := by
    simpa only [q,extendPath,projIcc_of_mem hT t.property] using he.trans hqs
  have h := congrArg (U.forward t) ht
  change ((U.forward t).comp (U.backward t)) (f t) = U.forward t 0 at h
  simpa only [U.forward_backward,id_apply,map_zero] using h

end EulerLinearDuhamel.Evolution

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerVolterraConvolution
  EulerTransverseEndpointCoordinates EulerFixedEndpointClassical

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- A nonzero terminal coordinate forces the actual physical history
velocity to be nonzero at some time. -/
theorem labelVelocity_exists_ne_zero (x : Space) (ξ : U) (hξ : ξ ≠ 0) :
    ∃ t : Icc (0 : ℝ) T, D.labelVelocity x ξ t ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hv : ∀ t : Icc (0 : ℝ) T, D.labelCoordinate x ξ t = 0 := by
    intro t
    have h := D.labelFrame_lower x t (D.labelCoordinate x ξ t)
    change D.lower*‖D.labelCoordinate x ξ t‖^2 ≤ ‖D.labelVelocity x ξ t‖^2 at h
    rw [hn t,norm_zero,zero_pow (by decide : 2 ≠ 0)] at h
    have hs : ‖D.labelCoordinate x ξ t‖^2 ≤ 0 := nonpos_of_mul_nonpos_right h D.lower_pos
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (D.labelCoordinate x ξ t)])
  let z := EulerFixedEndpointClassical.displacement T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
    (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
    D.potential D.potential_nonneg (D.labelHessian_upper x) D.small ξ
  have hd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T D.time_pos.le z) 0 (Icc (0 : ℝ) T) t := by
    intro t ht
    have h := EulerFixedEndpointClassical.displacement_hasDerivWithinAt T D.time_pos.le (D.labelFrame x)
      (D.labelFrameDerivative x) (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x)
      (D.labelFrame_derivative x) D.potential D.potential_nonneg (D.labelHessian_upper x) D.small
      (D.labelFrameSecond x) D.time_pos (D.labelFrame_second_derivative x) (D.labelFrame_equation x)
      ξ ⟨t,ht⟩
    change HasDerivWithinAt (extendPath T D.time_pos.le z) (D.labelCoordinate x ξ ⟨t,ht⟩)
      (Icc (0 : ℝ) T) t at h
    rwa [hv] at h
  have he : extendPath T D.time_pos.le z T = extendPath T D.time_pos.le z 0 := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
      (fun r hr => by simp) (convex_Icc (0 : ℝ) T)
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,D.time_pos.le⟩)
      (show T ∈ Icc (0 : ℝ) T from ⟨D.time_pos.le,le_rfl⟩)
    simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using h
  have hz0 : extendPath T D.time_pos.le z 0 = 0 := by
    rw [extendPath,projIcc_of_mem D.time_pos.le (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,D.time_pos.le⟩)]
    exact EulerFixedEndpointClassical.displacement_initial T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
      (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
      D.potential D.potential_nonneg (D.labelHessian_upper x) D.small ξ
  have hzT : extendPath T D.time_pos.le z T = ξ := by
    rw [extendPath,projIcc_of_mem D.time_pos.le (show T ∈ Icc (0 : ℝ) T from ⟨D.time_pos.le,le_rfl⟩)]
    exact EulerFixedEndpointClassical.displacement_terminal T D.time_pos.le (D.labelFrame x) (D.labelFrameDerivative x)
      (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
      D.potential D.potential_nonneg (D.labelHessian_upper x) D.small D.time_pos ξ
  exact hξ (hzT.symm.trans (he.trans hz0))

end EulerCylinderDirichlet.Coefficients

namespace EulerPacketPrimaryFactorization

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketTerminalDatum EulerTransversePacketPrimary EulerSpatialCutoffs
  EulerLinearDuhamel EulerVolterraConvolution

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

omit [CompleteSpace U] in
theorem canonicalNormal_equation (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => D.normal.field (D.clamp s) x)
      (-(D.M.field t x).adjoint (D.normal.field t x)) (Icc (0 : ℝ) D.T) t := by
  simpa only [extendPath,Data.clamp,projIcc_of_mem D.T_pos.le t.property,
    Data.normalDerivative_apply] using D.normal_hasDerivWithinAt t t.property x









end EulerPacketPrimaryFactorization
