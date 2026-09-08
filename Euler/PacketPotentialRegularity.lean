import Euler.PacketPotentialMultiplier
import Euler.PacketPiolaPair
import Euler.AnglePrimitiveSpatialRegularity

/-! Spatial smoothness of the source vector potential, derived from its literal integral. -/

noncomputable section

namespace EulerPacketPiola

open EulerSmoothLimit EulerPacketCrossProduct EulerPacketAngularPotential
  EulerAngleMeanZeroPrimitive EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerMeanBoundary Set MeasureTheory InnerProductSpace
open scoped ContDiff

def curlLinear : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun := curlMatrix
  map_add' := curlMatrix_add
  map_smul' := curlMatrix_smul

def curlOperator : (Space →L[ℝ] Space) →L[ℝ] Space := curlLinear.toContinuousLinearMap

@[simp] theorem curlOperator_apply (A : Space →L[ℝ] Space) : curlOperator A = curlMatrix A := rfl

theorem coveringPotential_contDiff (P : ℝ) (hP : 0 ≤ P)
    (m : Space → Space) (A : LiftTangent → Space)
    (hm : ContDiff ℝ ∞ m) (hnz : ∀ y, m y ≠ 0) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (coveringPotential P m A) := by
  exact primitive_joint_contDiff P hP
    (fun z : LiftTangent => potentialMultiplier (m z.1) (A z))
    (((potentialMultiplier_contDiff m hm hnz).comp contDiff_fst).clm_apply hA)



end EulerPacketPiola
