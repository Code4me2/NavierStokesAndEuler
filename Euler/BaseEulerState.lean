import Euler.BaseEulerSobolev
import Euler.BaseEulerSign

/-! The initial induction state is completely constructed from the
compact β-family. A single positive time and a single label constant
work for the family, with actual low-order guards and pressure sign. -/

noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerBaseEulerGuards EulerTransverseFrameCoordinates

def initialTime : ℝ := guardTime solutionTime solutionLabelConstant

theorem initialTime_pos : 0 < initialTime :=
  guardTime_pos _ _ solutionTime_pos

theorem initialTime_le : initialTime ≤ solutionTime := guardTime_le _ _

theorem initialTime_le_one : initialTime ≤ 1 := guardTime_le_one _ _

def initialCoefficientCost : ℝ := coefficientCost solutionLabelConstant

theorem initialCoefficientCost_nonneg : 0 ≤ initialCoefficientCost := coefficientCost_nonneg _

theorem initialTime_small :
    initialCoefficientCost*initialTime ≤ 1/4 ∧
      EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost initialCoefficientCost*initialTime ≤ 1/4 :=
  guardTime_small _ _

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)

def initialParent : Parent :=
  (solutionParent β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

def initialLabelData : LabelData (initialParent β hβ ell hell hell1) :=
  (solutionLabelData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


def initialEvolution : Evolution (initialParent β hβ ell hell hell1) :=
  (solutionEvolution β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

def initialSobolevData : SobolevData (initialEvolution β hβ ell hell hell1) :=
  (solutionSobolevData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

theorem initialOddData : OddData (initialParent β hβ ell hell hell1) :=
  (solutionOddData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

def initialLowBounds : LowBounds (initialParent β hβ ell hell hell1) :=
  lowBounds (solutionLabelData β hβ ell hell hell1)




theorem initial_velocity (x : Space) :
    (initialParent β hβ ell hell hell1).velocity.field ⟨0,le_rfl,initialTime_pos.le⟩ x=
      velocity (linear β) x :=
  solution_initial_velocity β hβ ell hell hell1 x


theorem solution_initialStrain (x : Space) (hx : ‖ell • x‖ < 1) :
    (solutionParent β hβ ell hell hell1).initialStrain.field x=linear β := by
  rw [Parent.initialStrain_apply,Parent.first_apply]
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      (solutionParent β hβ ell hell hell1).zeroTime : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_fderiv_plateau _ (linear_trace β) (ell • x) hx

theorem initialStrain_plateau (x : Space) (hx : ‖ell • x‖ < 1) :
    (initialParent β hβ ell hell hell1).initialStrain.field x=linear β := by
  change ((solutionParent β hβ ell hell hell1).restrictTime initialTime initialTime_pos
    initialTime_le).initialStrain.field x=linear β
  erw [Parent.restrictTime_initialStrain]
  exact solution_initialStrain β hβ ell hell hell1 x hx

theorem initial_strain_bound (t : Icc (0 : ℝ) initialTime) (x : Space) :
    ‖(initialParent β hβ ell hell hell1).strain.field t x‖ ≤ initialCoefficientCost :=
  strain_norm (initialLabelData β hβ ell hell hell1) t x

theorem initial_curvature_bound (t : Icc (0 : ℝ) initialTime) (x : Space) :
    ‖(initialParent β hβ ell hell hell1).curvature.field t x‖ ≤ initialCoefficientCost :=
  curvature_norm (initialLabelData β hβ ell hell hell1) t x


variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (R : U ≃ₗᵢ[ℝ] referencePlane (EuclideanSpace.single 0 1 : Space))
  (ξ : U) (hξ : (R ξ : Space)=EuclideanSpace.single 1 1)
  (S : Set Space) (hS : IsCompact S)



end EulerBaseDatum
