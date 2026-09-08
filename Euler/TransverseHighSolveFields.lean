import Euler.TransversePacketCorrectorOperator

/-! Actual cylinder witnesses for the total high-solve operator and its literal corrector. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
  EulerCylinderSmoothOrbit EulerLpCylinderPaths

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField)

def highSolveDerivative : VectorField := by
  classical
  exact if h : Nonempty (Forcing P D raw) then (Classical.choice h).vectorDerivative I else 0

def highSolveCorrectorDerivative : VectorField := by
  classical
  exact if h : Nonempty (Forcing P D raw) then (Classical.choice h).correctorDerivative I else 0

variable (h : Nonempty (Forcing P D raw))












end EulerTransversePacketProvider
