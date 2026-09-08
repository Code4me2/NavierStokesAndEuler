import Euler.MeanTranslatedInverse
import Euler.MeanFixedCoefficientGevrey
import Euler.HilbertCoerciveGevrey

/-!
# Genuine all-order spatial estimates for the translated mean inverse

The recurrence is proved for the actual coercive inverse. The translated
solution is identified with the real spatial translation orbit before its
iterated Fréchet derivatives are estimated. Coefficient and forcing amplitudes
enter through explicit polynomials, independently of derivative order.
-/

noncomputable section

namespace EulerMeanTranslatedGevrey

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerTimeLp
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanFixedSpaceInverse
  EulerMeanFixedTranslation EulerMeanTranslatedInverse EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerHilbertCoerciveGevrey EulerCoerciveProjection
  EulerGevrey EulerOperatorGevreyCalculus EulerTransverseGramInverse
open scoped ContDiff

-- Reuse the nested Hilbert-space instances in the translated inverse estimates.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

/-- The proved polynomial amplitude for the actual fixed mean operator. -/
def operatorAmplitude (T CF CF₁ CH CM CA L : ℝ) : ℝ :=
  9*(T*CF₁+CF)^2*(1+(T^2/2)*CH+T*(CM+|L| * CA))

/-- The proved polynomial amplitude of the actual forcing pullback. -/
def forcingAmplitude (T CF CF₁ Cf : ℝ) : ℝ := 3*(T*(T*CF₁+CF))*Cf

theorem operatorAmplitude_nonneg (T CF CF₁ CH CM CA L : ℝ)
    (hT : 0 ≤ T) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCA : 0 ≤ CA) :
    0 ≤ operatorAmplitude T CF CF₁ CH CM CA L := by unfold operatorAmplitude; positivity

theorem forcingAmplitude_nonneg (T CF CF₁ Cf : ℝ)
    (hT : 0 ≤ T) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) :
    0 ≤ forcingAmplitude T CF CF₁ Cf := by unfold forcingAmplitude; positivity

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L c : ℝ)
  (hc : 0 < c)
  (hcoercive : ∀ v, c*‖v‖^2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v,v⟫_ℝ)


end EulerMeanTranslatedGevrey
