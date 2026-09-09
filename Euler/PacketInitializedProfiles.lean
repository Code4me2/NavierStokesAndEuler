import Euler.PacketTerminalPrimaryFields
import Euler.PacketPrimaryGradeBounds
import Euler.PacketJoinedUniformProfiles

/-! Uniform recursive packet bounds with the literal primary initialization discharged.

Merged in from the former module `Euler.PacketTerminalPrimaryBudget`: `joinedTerminalPrimary_budget`.
-/

/-! The literal compact terminal wave initializes the mean-time packet budget. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (hR : wordRadius (Fin 4) δ ≤ L.R)
  (W : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6 δ*‖ξ‖))

include hδ1 hα hR W

theorem joinedTerminalPrimary_budget (S : Scales (Icc (0 : ℝ) M.T))
    (hgrowth : timeProfileChange S.growth hTime=α • L.fullProfile) :
    ProfileBudget (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) S L.R 1 := by
  have hg : (S.changeTime hTime).growth=α • L.fullProfile :=
    (S.growth_changeTime hTime).trans hgrowth
  have hD := primary_profile_budget H NB δ hδ hδ1 ξ hs α hα hR W
    (joinedSourceOperators period M D τ hτ hτT B) rfl (S.changeTime hTime) hg
  have hM := hD.changeTime hTime.symm M.T_pos.le
  simpa only [Scales.changeTime_roundtrip, joinedTerminalPrimaryWitness, joinedTerminalPrimary] using hM

end EulerPacketTerminalDatum
end

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile EulerParameterWordGevrey

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedProfiles : ℕ → Profile :=
  joinedSourceProfiles period M D τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))

def initializedProfileWitness (p : ℕ) :
    ProfileRegularity period M.T M.T_pos.le D.support (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α p) :=
  joinedSourceProfileWitness period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) p

variable
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6 δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initialized_profile_budgets (p : ℕ) (hp : 1 ≤ p) :
    ProfileBudget (initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α p) S L.R p :=
  joinedSource_profile_budgets period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα hgrowth
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    rfl (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) p hp

end EulerPacketTerminalDatum
