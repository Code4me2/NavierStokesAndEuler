import Euler.TransversePacketPrimaryHistory
import Euler.TransversePacketPiolaData
import Euler.PacketFrameCoefficients
import Euler.PacketPhysicalEulerTransform

/-! The actual compact primary has exactly the source rank-one shear at
zero phase throughout its history interval, including the activation time.
No derivative of the finite-dimensional history is postulated. -/

noncomputable section

namespace EulerPacketPrimaryShear

open Set Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerGraphPullback EulerPacketNormalizedPrimary
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPeriodicProfile
open scoped ContDiff

theorem zero_slice_hasFDerivAt (A : Space × ℝ → Space) (x a : Space)
    (hA : DifferentiableAt ℝ A (x,0)) (hzero : ∀ y, A (y,0)=0)
    (ha : HasDerivAt (fun θ : ℝ => A (x,θ)) a 0) :
    HasFDerivAt A ((toSpanSingleton ℝ a).comp (snd ℝ Space ℝ)) (x,0) := by
  have hs := hA.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (0 : ℝ) x))
  have he : (fun y => A (y,0)) = fun _ : Space => (0 : Space) := funext hzero
  change HasFDerivAt (fun y => A (y,0)) ((fderiv ℝ A (x,0)).comp (inl ℝ Space ℝ)) x at hs
  rw [he] at hs
  have hspace : ∀ v : Space, fderiv ℝ A (x,0) (v,0)=0 := by
    intro v
    have h := congrArg (fun L : Space →L[ℝ] Space => L v)
      (hs.unique (hasFDerivAt_const (0 : Space) x))
    exact h
  have ht := hA.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
  have hangle : fderiv ℝ A (x,0) (0,1)=a := ht.unique ha
  have hd : fderiv ℝ A (x,0) = (toSpanSingleton ℝ a).comp (snd ℝ Space ℝ) := by
    apply ContinuousLinearMap.ext
    rintro ⟨v,s⟩
    have hp : (v,s) = (v,(0 : ℝ))+s•((0 : Space),(1 : ℝ)) := by simp
    rw [hp,map_add,map_smul,hspace,hangle]
    simp
  exact hd ▸ hA.hasFDerivAt

theorem zero_phase_graph_hasFDerivAt (A : Space × ℝ → Space) (a m : Space)
    (hA : DifferentiableAt ℝ A (0,0)) (hzero : ∀ y, A (y,0)=0)
    (ha : HasDerivAt (fun θ : ℝ => A (0,θ)) a 0) (c k : ℝ) :
    HasFDerivAt (fun y => c • A (y,k*⟪m,y⟫_ℝ)) ((c*k) • rankOne ℝ a m) 0 := by
  have hp : HasFDerivAt A ((toSpanSingleton ℝ a).comp (snd ℝ Space ℝ)) (graphMap k m 0) := by
    rw [map_zero]
    change HasFDerivAt A ((toSpanSingleton ℝ a).comp (snd ℝ Space ℝ)) (0,0)
    exact zero_slice_hasFDerivAt A 0 a hA hzero ha
  have h := (hp.comp 0 (graphMap k m).hasFDerivAt).const_smul c
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,toSpanSingleton_apply,coe_snd',graphMap_apply,
    rankOne_apply,smul_smul]
  congr 1
  ring

theorem rankOne_normalized (c : ℝ) (v m : Space) (hv : v ≠ 0) (hm : m ≠ 0) :
    c • rankOne ℝ v m =
      (c*(‖m‖*‖v‖)) • rankOne ℝ (unit v) (unit m) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,rankOne_apply,unit,real_inner_smul_left,smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hv,norm_ne_zero_iff.mpr hm]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)





end EulerPacketPrimaryShear
