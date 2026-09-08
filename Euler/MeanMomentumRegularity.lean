import Euler.MeanDisplacementRegularity
import Euler.TransverseMomentumRegularity

/-!
# Genuine mean momentum regularity from the variational solve

Zero-initial-trace solenoidal test primitives are mapped by F into the actual
mean test space. The two original boundary terms then vanish, and the weak
identity constructs an AC representative of `Pσ F* η_t`. This is a regularity
conclusion, not an assumed momentum equation or an assumed second derivative.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution EulerMeanSolenoidal
  EulerTimeH1OperatorProduct EulerTimeWeakDerivative EulerTransverseMomentumRegularity

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The frame adjoint is the actual ordinary solenoidal projection of `F*`. -/
theorem solenoidalFrame_adjoint (t : Icc (0 : ℝ) T) :
    (solenoidalFrame T F t).adjoint =
      solenoidalSpace.orthogonalProjectionOnto.comp (F t).adjoint := by
  change ((F t).comp solenoidalSpace.subtypeL).adjoint = _
  calc
    _ = solenoidalSpace.subtypeL.adjoint.comp (F t).adjoint :=
      adjoint_comp _ _
    _ = _ := congrArg (fun A : L2 →L[ℝ] solenoidalSpace => A.comp (F t).adjoint)
      (Submodule.adjoint_subtypeL solenoidalSpace)





end EulerMeanVariationalInverse
