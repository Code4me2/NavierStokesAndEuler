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
