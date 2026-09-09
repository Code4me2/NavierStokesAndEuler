import Euler.SmoothFlowAcceleration
import Euler.SmoothFlowJacobian
import Euler.SmoothPathTimeJets
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Genuine joint time-space regularity of the constructed flow and its
inverse. Interior C² uses only the actual first time derivative of the
velocity coefficient, together with its existing smooth spatial jets. -/

noncomputable section


open scoped ContDiff Topology

namespace EulerSmoothBanachFlow

open Set Filter EulerVolterraConvolution EulerContinuousTimeIntegral
  EulerContinuousPathCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)

theorem accelerationFamily_contDiff : ContDiff ℝ ∞ (accelerationFamily T hT A A₁) := by
  have hp := pathFamily_contDiff T hT A
  exact (A₁.superposition_contDiff.comp hp).add
    (contDiff_apply _ _ (A.derivative.superposition_contDiff.comp hp)
      (velocityFamily_contDiff T hT A))





omit [FiniteDimensional ℝ E] in
def timeLiftEquiv (J : E ≃L[ℝ] E) (v : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ ℝ E).prod
      (((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ E)) +
        J.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E)))
    ((ContinuousLinearMap.fst ℝ ℝ E).prod
      (J.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.snd ℝ ℝ E) -
          (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ E))))
    (by intro p; ext <;> simp)
    (by intro p; ext <;> simp)





end EulerSmoothBanachFlow
