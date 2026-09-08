import Euler.BaseStaticEuler
import Euler.BaseEulerUniform

/-! A single positive time and a single label bound work for every
compact base datum with |β|≤1. The parent, inverse and Euler evolution
below are the actual constructed objects. -/

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames

private local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def solutionTime : ℝ :=
  EulerStaticEuler.baseTime 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)

theorem solutionTime_pos : 0 < solutionTime :=
  EulerStaticEuler.baseTime_pos 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)

def solutionLabelConstant : ℝ :=
  EulerStaticEuler.baseLabelConstant 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)

def solutionParent : Parent :=
  EulerStaticEuler.baseParent 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1

def solutionLabelData : LabelData (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseLabelData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1


def solutionEvolution : Evolution (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseEvolution 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1



theorem solutionOddData : OddData (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseOddData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1 (velocity_odd (linear β))

theorem solution_initial_velocity (x : Space) :
    (solutionParent β hβ ell hell hell1).velocity.field ⟨0,le_rfl,solutionTime_pos.le⟩ x=
      velocity (linear β) x :=
  EulerStaticEuler.baseParent_initial_velocity 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1 x




omit β hβ ell hell hell1 in
theorem solutionLabelConstant_one : 1 ≤ solutionLabelConstant :=
  (solutionLabelData 0 (by norm_num) 1 zero_lt_one le_rfl).K_one

end EulerBaseDatum
