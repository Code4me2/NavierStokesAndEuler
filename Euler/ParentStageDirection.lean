import Euler.ParentFrameReframe
import Euler.ParentPacketJoinedInput
import Euler.PacketForwardGeometryData

/-! The source direction at a stage is constructed from the actual
parent deformation and older frame. Both branch-specific normal-choice
identities are conclusions, and the reference plane is literal. -/

noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖=1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R S hS) τ)

def crossDirection : Space := cross (unit (P.m τ)) (unit (P.v τ))

theorem crossDirection_unit (hτT : τ ≤ A.T) : ‖P.crossDirection‖=1 := by
  exact (frame_orthonormal (unit (P.m τ)) (unit (P.v τ))
    (unit_inner_self (P.ray_nonzero τ ⟨le_rfl,hτT⟩))
    (unit_inner_self (P.velocity_nonzero τ ⟨le_rfl,hτT⟩))
    (unit_inner_zero (P.tangent τ ⟨le_rfl,hτT⟩))).norm_eq_one 2

theorem crossDirection_ne_zero (hτT : τ ≤ A.T) : P.crossDirection ≠ 0 := by
  intro hz
  have h := P.crossDirection_unit hτT
  rw [hz,norm_zero] at h
  norm_num at h

variable (hτ : 0 < τ) (hτT : τ < A.T)

def activationNormal : Space :=
  activationDirection ((A.transverseData m hm R S hS).deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
    P.crossDirection

theorem activationNormal_unit : ‖P.activationNormal hτ hτT‖=1 :=
  activationDirection_unit _ (P.crossDirection_ne_zero hτT.le)

def activationData : Data (referencePlane (P.activationNormal hτ hτT)) :=
  A.transverseData (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT))) S hS

def activationFrame : ParentFrame (P.activationData hτ hτT) τ :=
  P.reframe (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT)))

theorem activation_normal_choice :
    (P.activationData hτ hτT).m₀=
      activationDirection ((P.activationData hτ hτT).deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
        (cross (unit ((P.activationFrame hτ hτT).m τ))
          (unit ((P.activationFrame hτ hτT).v τ))) := rfl

theorem activation_parameters :
    (P.activationFrame hτ hτT).a=P.a ∧ (P.activationFrame hτ hτT).sigma=P.sigma ∧
      (P.activationFrame hτ hτT).shear=P.shear ∧ (P.activationFrame hτ hτT).epsilon=P.epsilon ∧
      (P.activationFrame hτ hτT).horizon=P.horizon ∧ (P.activationFrame hτ hτT).G=P.G ∧
      (P.activationFrame hτ hτT).error=P.error := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩



def activationHistory (H : LowBounds A) :
    HistoryData ((P.activationData hτ hτT).initial τ hτ hτT.le) :=
  A.historyOn H (P.activationNormal hτ hτT) (P.activationNormal_unit hτ hτT)
    (LinearIsometryEquiv.refl ℝ (referencePlane (P.activationNormal hτ hτT))) S hS τ hτ hτT


end EulerPacketSourceGeometry.ParentFrame

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖=1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {S : Set Space} {hS : IsCompact S}
  (P : ParentFrame (A.transverseData m hm R S hS) 0)

def forwardData : Data (referencePlane P.crossDirection) :=
  A.transverseData P.crossDirection (P.crossDirection_unit A.T_pos.le)
    (LinearIsometryEquiv.refl ℝ (referencePlane P.crossDirection)) S hS

def forwardFrame : ParentFrame P.forwardData 0 :=
  P.reframe P.crossDirection (P.crossDirection_unit A.T_pos.le)
    (LinearIsometryEquiv.refl ℝ (referencePlane P.crossDirection))

theorem forward_normal_choice : P.forwardData.m₀=
    cross (unit (P.forwardFrame.m 0)) (unit (P.forwardFrame.v 0)) := rfl



theorem forward_parameters :
    P.forwardFrame.a=P.a ∧ P.forwardFrame.sigma=P.sigma ∧
      P.forwardFrame.shear=P.shear ∧ P.forwardFrame.epsilon=P.epsilon ∧
      P.forwardFrame.horizon=P.horizon ∧ P.forwardFrame.G=P.G ∧ P.forwardFrame.error=P.error :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end EulerPacketSourceGeometry.ParentFrame
