import Euler.CorrectionAssemblyReconstruction
import Euler.InviscidSobolevEvolution
import Euler.SobolevPointMultiplication

/-! Genuine pointwise time differentiation of the generically assembled correction. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerVolterraConvolution EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation EulerSobolevPointMultiplication EulerSobolevCoefficientPressure
  EulerQuadraticSourceLimit EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The canonical pointwise nonlinear raw source of the actual common correction. -/
def FiniteFamily.pointRawSource (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (F.rawSourcePath period 6 le_rfl t))

/-- The canonical actual time derivative, defined by bounded evaluation of the genuine continuous Sobolev source. -/
def FiniteFamily.pointTimeDerivative (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (((A.atOrder period 6).coefficients period le_rfl).apply t (F.solution 6 le_rfl t)))


/-- The pointwise time derivative is the literal raw-source and signed-pressure expression. -/
theorem FiniteFamily.pointTimeDerivative_eq_pressure (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointTimeDerivative period t x = -F.pointRawSource period t x -
      (A.metric.coefficient t).coefficient x (F.pointPressure period t x) := by
  unfold FiniteFamily.pointTimeDerivative
  rw [EulerInviscidSobolevEvolution.CorrectionData.source_sobolev]
  simp only [map_sub, map_neg]
  rw [pointEvaluation_coefficient period (by omega : 3 ≤ 6) ((A.atOrder period 6).metric.coefficient t)
    ((A.atOrder period 6).metric.jet t)]
  rfl



end EulerCorrectionAssembly
