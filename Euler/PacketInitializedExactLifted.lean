import Euler.PacketInitializedResidualEquation
import Euler.PacketInitializedAllOrderBudget
import Euler.PacketPrimaryCommonRadius
import Euler.PacketCommonRadius
import Euler.PacketJoinedCoefficientBudgets
import Euler.PacketInitializedCorrectionParity

/-! Source budgets and the actual initialized residual construct exact
corrected lifted packets at every sufficiently large frequency. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerGevreyMetricEstimate
  EulerCorrectionOperators EulerSobolevCoefficientPressure EulerVolterraConvolution
  EulerCorrectionAssembly EulerCylinderReflection EulerCorrectionResidualCancellation

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} (hT : 0 < T) (A : Data P T)

/-- The output fields and all their properties are conclusions of the
constructed correction and the verified approximate residual. -/
structure ExactLiftedPacket (B : Budget P hT A) where
  velocity : FieldTower P T
  pressure : FieldTower P T
  zero_initial_correction : ∀ q,
    velocity.realization q ⟨0,le_rfl,hT.le⟩-A.approximation.realization q ⟨0,le_rfl,hT.le⟩=0
  divergence : ∀ t, velocity.field t ∈ divergenceFreeSpace P A.κ A.direction
  gradient : ∀ t, pressure.field t ∈ gradientSpace P A.κ A.direction
  energy : ∀ (n : ℕ) t,
    energyNorm P n (by omega : n+6 ≤ (n+6)+1) (B.radius t) (B.metric.operatorPath P t)
        (velocity.realization ((n+6)+1) t-A.approximation.realization ((n+6)+1) t) ≤
      2*(B.spatial (n+6) (by omega)).full.residual*Real.exp (3*B.growthCoefficient*t.val) ∧
    energyNorm P n (by omega : n+6 ≤ (n+6)+1) (B.radius t) (B.metric.operatorPath P t)
        (velocity.realization ((n+6)+1) t-A.approximation.realization ((n+6)+1) t) ≤ B.delta/2
  equation : ∀ (q : ℕ) (hq : 6 ≤ q) t (ht : t ∈ Ioo 0 T),
    HasDerivAt (extendPath T hT.le (velocity.realization q))
      (-nonlinearity P (A.atOrder P q) hq ⟨t,ht.1.le,ht.2.le⟩
        (velocity.realization (q+1) ⟨t,ht.1.le,ht.2.le⟩)-
        coefficientSobolevOperator P (A.metric.jet q ⟨t,ht.1.le,ht.2.le⟩)
          (pressure.realization q ⟨t,ht.1.le,ht.2.le⟩)) t

variable {hT A}

def exactPacketOfResidual (B : Budget P hT A) (R : ApproximationResidual P hT A) :
    ExactLiftedPacket P hT A B where
  velocity := B.correctedFieldTower P
  pressure := B.correctedPressureTower P R
  zero_initial_correction q := by rw [B.correctedFieldTower_initial P q,sub_self]
  divergence := B.correctedFieldTower_divergence P
  gradient := B.correctedPressureTower_gradient P R
  energy := B.correctedFieldTower_error_energy P
  equation := B.correctedFieldTower_hasDerivAt P R

theorem exactPacketOfResidual_velocity_odd (B : Budget P hT A)
    (R : ApproximationResidual P hT A) (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    -reflection P ((exactPacketOfResidual P B R).velocity.field t) =
      (exactPacketOfResidual P B R).velocity.field t := by
  change -reflection P (A.approximation.field t+B.commonPath P t) =
    A.approximation.field t+B.commonPath P t
  rw [map_add,neg_add,E.approximation,B.commonPath_odd P E]

end EulerAllOrderDriftCorrection

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerAllOrderDriftCorrection
  EulerPacketCorrectionScalar EulerPacketSourceFrequency EulerCylinderReflection
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedExactPacket (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)) :
    ExactLiftedPacket period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk) Q :=
  exactPacketOfResidual period Q
    (initializedApproximationResidual M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk)



end EulerPacketTerminalDatum
