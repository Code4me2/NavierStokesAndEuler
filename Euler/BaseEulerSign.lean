import Euler.BaseEulerGuards
import Euler.ParentPacketStrainEvolution

/-! The first pressure numerator stays positive for the actual evolving
normal and the actual homogeneous transverse velocity. Initial plateau
data are the only geometric inputs; all time equations are constructed. -/

noncomputable section

namespace EulerBaseEulerGuards

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransverseFrameCoordinates
  EulerPacketFirstPressureSign EulerTimeIntervalRestriction

variable {G : Parent} (L : LabelData G)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S)

omit [CompleteSpace U] in
theorem source_normal_initial (x : Space) :
    (G.transverseData m hm R S hS).normal.field G.zeroTime x=m := by
  change (G.inverse.field G.zeroTime x).adjoint m=m
  have hi : G.inverse.field G.zeroTime x=ContinuousLinearMap.id ℝ Space := by
    exact ContinuousLinearMap.ext (G.inverse_initial x)
  rw [hi,adjoint_id,id_apply]

omit [CompleteSpace U] in
theorem source_frame_initial (ξ : U) (x : Space) :
    (G.transverseData m hm R S hS).frame.field G.zeroTime x ξ=(R ξ : Space) := by
  change G.frame.field G.zeroTime x (R ξ : Space)=_
  rw [G.frame_initial,id_apply]

theorem source_numerator_pos (ξ : U) (hξ : ‖ξ‖=1) (x : Space)
    (h0 : ⟪m,G.initialStrain.field x (R ξ : Space)⟫_ℝ=1)
    (hshort : coefficientCost L.K*G.T ≤ 1/2)
    (hsmall : firstSignRate (coefficientCost L.K) (coefficientCost L.K)*G.T ≤ 1/2)
    (t : Icc (0 : ℝ) G.T) :
    1/2 ≤ ⟪(G.transverseData m hm R S hS).normal.field t x,
      G.strain.field t x (EulerPacketForwardFactorization.uncutVelocity
        (G.transverseData m hm R S hS) ξ t x)⟫_ℝ := by
  apply uncut_numerator_pos (G.transverseData m hm R S hS) ξ x
    (fun s => G.curvature.field s x) (coefficientCost L.K) (coefficientCost L.K)
    (coefficientCost_nonneg L.K) (coefficientCost_nonneg L.K)
    (fun s => strain_norm L s x) (fun s => curvature_norm L s x)
    (fun s => G.strain_within s x) _ _ _ hshort hsmall t
  · change ‖(G.transverseData m hm R S hS).normal.field G.zeroTime x‖=1
    rw [source_normal_initial m hm R S hS]
    exact hm
  · change ‖(G.transverseData m hm R S hS).frame.field G.zeroTime x ξ‖=1
    rw [source_frame_initial m hm R S hS]
    exact (R.norm_map ξ).trans hξ
  · change ⟪(G.transverseData m hm R S hS).normal.field G.zeroTime x,
      G.strain.field G.zeroTime x ((G.transverseData m hm R S hS).frame.field G.zeroTime x ξ)⟫_ℝ=1
    rw [source_normal_initial m hm R S hS,source_frame_initial m hm R S hS]
    rw [G.strain_apply,comp_apply,G.inverse_initial]
    exact h0


end EulerBaseEulerGuards
