import Euler.ParentEulerState
import Euler.ParentPacketParity

/-! The physical velocity and pressure force inherit the genuine
particle symmetry, so their values vanish at the fixed origin. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit

variable {A : Parent} (E : Evolution A) (O : OddData A)

include O





theorem strain_origin (t : Icc (0 : ℝ) A.T) :
    A.strain.field t 0=fderiv ℝ (fun y => E.velocity (t,y)) 0 := by
  rw [E.strain_eq,smul_zero,O.position_zero]


end EulerParentPacketFrames.Evolution
