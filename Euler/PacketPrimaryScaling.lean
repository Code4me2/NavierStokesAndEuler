import Euler.PacketPrimaryFactorization
import Euler.TransversePacketPrimaryHistory
import Euler.TransversePacketPiolaData
import Euler.PacketFrameCoefficients
import Euler.PacketPhysicalEulerTransform
import Euler.TransversePacketPrimaryHomogeneity
import Euler.PacketCylinderFieldAlgebra

/-! The amplitude in the literal terminal datum gives exactly the
amplitude multiplying the physical primary wave.

Merged in from the former module `Euler.PacketPrimaryShearIdentity`: `rankOne_normalized`.
-/

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
end

noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerTransversePacketProvider EulerSpatialCutoffs

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

omit [CompleteSpace U] in
theorem terminal_smul (δ : ℝ) (hδ : 0 < δ) (ξ : U) (a : ℝ) :
    terminal δ hδ (a • ξ) = a • terminal δ hδ ξ := by
  apply Lp.ext
  filter_upwards [terminal_ae δ hδ (a • ξ),
    Lp.coeFn_smul a (terminal δ hδ ξ),terminal_ae δ hδ ξ] with x hz hs hy
  rw [hz,hs,Pi.smul_apply,hy]
  simp only [field,smul_smul]
  congr 1
  ring

theorem initialData_value_smul (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (a : ℝ) :
    (initialData D δ hδ (a • ξ) hs).value = a • (initialData D δ hδ ξ hs).value := by
  exact Subtype.ext (terminal_smul δ hδ ξ a)

end EulerPacketTerminalDatum

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerCylinderSmoothOrbit EulerPacketCylinderField
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPacketPrimaryFactorization
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

theorem vector_terminal_smul (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,θ)) =
      a • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)) := by
  let G := vectorField τ hτ hτT B (initialData D δ hδ ξ hs)
  let H := vectorField τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
  have hp : H.path = (G.smul a).path :=
    velocityPath_eq_smul τ hτ hτT B _ _ a (initialData_value_smul D δ hδ ξ hs a)
  have he := congrFun (pointField_eq_of_slice_eq period H.path (G.smul a).path
    H.orbit (G.smul a).orbit t t (congrArg (fun p => p t) hp)) (x,(θ : AddCircle period))
  exact (H.raw_eq t x θ).trans (he.trans ((G.smul a).raw_eq t x θ).symm)



end EulerPacketPrimaryShear
