import Euler.MeanGramTranslation
import Euler.MeanFixedCoefficientGevrey
import Euler.TimeLpAccelerationForcing

/-!
# Genuine spatial estimates for mean acceleration

The coordinate acceleration is recovered through the actual coercive Gram
inverse. Covariance identifies its parameterized solve with spatial
translation of the original field. Consequently the estimates below concern
the real spatial orbit, with no assumed derivatives of the inverse.
-/

noncomputable section

namespace EulerMeanAccelerationGevrey

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanVariationalInverse EulerMeanGramTranslation EulerTimeLp EulerVolterraConvolution
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey EulerTimeLpGramInverse
  EulerTimeLpGramGevrey EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) := inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (v : TimeLp T solenoidalSpace) (f : TimeLp T L2)

/-- The actual acceleration orbit is the actual translated Gram solve. -/
theorem meanAcceleration_orbit_eq :
    (fun a : Space => timeSolenoidalTranslation T a (meanAcceleration T hT F F₁ c hc hLower v f)) =
    fun a : Space => gramSolver T hT (solenoidalFrame T (translatePath T a F)) c hc
      (translatedFrame_lower T F c hLower a)
      (EulerTimeLpAccelerationForcing.forcing T hT
        (fun b => solenoidalFrame T (translatePath T b F))
        (fun b => solenoidalFrame T (translatePath T b F₁))
        (fun b => timeTranslation T b f) (fun b => timeSolenoidalTranslation T b v) a) :=
  funext (fun a => (meanAcceleration_translate T hT a F F₁ c hc hLower v f).symm)

/-- Actual spatial smoothness passes from the solved coordinate velocity to
the acceleration through the proved Gram inverse. -/
theorem meanAcceleration_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a v))
    (hf : ContDiff ℝ n (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ n (fun a : Space =>
      timeSolenoidalTranslation T a (meanAcceleration T hT F F₁ c hc hLower v f)) := by
  let Q := fun a : Space => solenoidalFrame T (translatePath T a F)
  let Q₁ := fun a : Space => solenoidalFrame T (translatePath T a F₁)
  have hQ : ContDiff ℝ n Q := contDiff_solenoidalFrame T (fun a => translatePath T a F) hF
  have hQ₁ : ContDiff ℝ n Q₁ := contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁
  have hg := EulerTimeLpAccelerationForcing.forcing_contDiff T hT Q Q₁
    (fun a => timeTranslation T a f) (fun a => timeSolenoidalTranslation T a v) hQ hQ₁ hf hv
  have hs := gramSolution_contDiff T hT Q c hc (translatedFrame_lower T F c hLower)
    (EulerTimeLpAccelerationForcing.forcing T hT Q Q₁
      (fun a => timeTranslation T a f) (fun a => timeSolenoidalTranslation T a v)) hQ hg
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ n g)
    (meanAcceleration_orbit_eq T hT F F₁ c hc hLower v f)) hs


end EulerMeanAccelerationGevrey
