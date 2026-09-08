import Euler.PacketActivationInitial
import Euler.PacketActivationSourceData

/-! A fully constructed normal and terminal coordinate for a positive
activation time.  The initial matching statements concern the actual
source history and its continuation, with no normal-choice premise. -/

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseActivationSelection
  EulerTransverseFrameCoordinates EulerPacketMovingFrame EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerPacketPrimaryFactorization

theorem activation_cross_ne_zero (m v : Space) (hm : m ≠ 0) (hv : v ≠ 0)
    (hmv : ⟪m,v⟫_ℝ=0) : cross (unit m) (unit v) ≠ 0 := by
  have h := (frame_orthonormal (unit m) (unit v)
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)).norm_eq_one 2
  change ‖cross (unit m) (unit v)‖=1 at h
  intro hz
  rw [hz,norm_zero] at h
  norm_num at h

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

def activatedData (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0)
    (hmv : ⟪m τ,v τ⟫_ℝ=0) :
    Data (referencePlane (activationDirection (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ))))) :=
  D.activation ⟨τ,hτ.le,hτT.le⟩ (cross (unit (m τ)) (unit (v τ)))
    (activation_cross_ne_zero _ _ hm hv hmv)



end EulerPacketActivationHistory
