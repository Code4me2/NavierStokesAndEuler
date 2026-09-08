import Euler.PacketInitializedExactLifted
import Euler.PacketForwardInitializedResidualEquation
import Euler.PacketForwardInitializedCorrectionChoice
import Euler.PacketForwardInitializedCorrectionParity

/-! Source budgets and the actual zero-history initialized residual construct exact
corrected lifted packets at every sufficiently large frequency. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerAllOrderDriftCorrection
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerCylinderReflection
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def forwardInitializedExactPacket (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk)) :
    ExactLiftedPacket period D.T_pos
      (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k hk) Q :=
  exactPacketOfResidual period Q
    (forwardInitializedApproximationResidual M D hTime δ hδ ξ hs α Cagree N hN k hk)



end EulerPacketTerminalDatum
