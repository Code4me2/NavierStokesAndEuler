import Euler.PacketGeometryControlledGrowth
import Euler.PacketParentPhysicalBudgets

/-! The actual activation geometry supplies H3 in the complete joined
packet budget.  Source label bounds and the original curvature hypotheses
remain inputs; no propagator estimate or chosen growth profile is assumed. -/

noncomputable section

namespace EulerPacketSourceGeometry.Guards

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketCofactor EulerPacketPiola EulerPacketParentLabelBounds EulerPacketSourcePropagator
  EulerTransversePacketProvider EulerGevrey EulerVolterraConvolution EulerTimeIntervalRestriction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (J : Guards hτ hτT P H)
  (hball : (1/2 : ℝ) ≤ J.radius)

def sourceGrowthProfile : C(Icc (0 : ℝ) (D.T-τ),ℝ) :=
  (J.halfBall_controlledGrowth hball).choose

theorem sourceGrowthProfile_positive (t : Icc (0 : ℝ) (D.T-τ)) :
    0 < J.sourceGrowthProfile hball t := (J.halfBall_controlledGrowth hball).choose_spec.1 t

theorem sourceGrowthProfile_initial :
    J.sourceGrowthProfile hball ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩=1 :=
  (J.halfBall_controlledGrowth hball).choose_spec.2.1

theorem sourceGrowthProfile_propagator :
    PhysicalGrowth (D.tail τ hτ.le hτT) EulerPacketParentPhysicalBudgets.halfBall
      (J.sourceGrowthProfile hball) (560*P.horizon^10/P.epsilon) :=
  (J.halfBall_controlledGrowth hball).choose_spec.2.2.1

theorem sourceGrowthProfile_amplitude (t : Icc (0 : ℝ) (D.T-τ)) :
    J.primaryAmplitude hball*J.sourceGrowthProfile hball t ≤
      8*Real.exp 6*J.δ*J.hchild/P.rayScale hτ hτT :=
  (J.halfBall_controlledGrowth hball).choose_spec.2.2.2 t



end EulerPacketSourceGeometry.Guards
