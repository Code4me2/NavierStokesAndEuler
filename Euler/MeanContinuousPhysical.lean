import Euler.MeanContinuousAcceleration
import Euler.MeanPhysicalTranslation

/-!
# Uniform-time spatial calculus for the actual physical mean derivative

Multiplication by the actual mean frame commutes with spatial translation.
The continuous physical derivative is the sum of the two actual frame
products, so its smoothness and bounds follow without a new regularity
assumption on the solution.
-/

noncomputable section

namespace EulerMeanContinuousPhysical

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousTimeIntegral EulerContinuousPathCalculus EulerGevrey
open scoped ContDiff

private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2) := inferInstance

variable (T : ℝ) (F : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2))
  (v : C(Icc (0 : ℝ) T,solenoidalSpace))

/-- The actual continuous frame product has the exact translated product orbit. -/
theorem framePathApply_orbit_eq :
    (fun a : Space => pathTranslation T a (multiplier (solenoidalFrame T F) v)) =
      fun a : Space => multiplier (solenoidalFrame T (translatePath T a F))
        (coordinatePathTranslation T a v) := by
  funext a
  apply ContinuousMap.ext
  intro t
  exact (EulerMeanPointwiseGramTranslation.frame_translation a (F t) (v t)).symm

theorem framePathApply_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a v)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a (multiplier (solenoidalFrame T F) v)) :=
  Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => ContDiff ℝ n g)
    (framePathApply_orbit_eq T F v))
    (contDiff_apply (fun a => solenoidalFrame T (translatePath T a F))
      (fun a => coordinatePathTranslation T a v)
      (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF) hv)


end EulerMeanContinuousPhysical

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath
  EulerMeanContinuousPhysical EulerMeanContinuousAcceleration EulerContinuousTimeIntegral
  EulerOperatorGevreyCalculus EulerTimeLp EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (fC : C(Icc (0 : ℝ) T,L2))

/-- The original continuous physical derivative is exactly its two frame products. -/
theorem classicalPhysicalDerivative_eq_products :
    s.classicalPhysicalDerivative c hc hLower fC =
      multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath +
      multiplier (solenoidalFrame T F) (s.classicalAcceleration c hc hLower fC) := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The actual continuous coordinate acceleration has a smooth spatial orbit. -/
theorem classicalAcceleration_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (hf : ContDiff ℝ n (fun a : Space => pathTranslation T a fC)) :
    ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a (s.classicalAcceleration c hc hLower fC)) :=
  meanAccelerationPath_translation_contDiff T F F₁ c hc hLower s.coordinateVelocityPath fC hF hF₁ hv hf

/-- The actual continuous B_t has a smooth spatial orbit, derived from the constructed acceleration. -/
theorem classicalPhysicalDerivative_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (hf : ContDiff ℝ n (fun a : Space => pathTranslation T a fC)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a (s.classicalPhysicalDerivative c hc hLower fC)) := by
  have he : (fun a : Space => pathTranslation T a (s.classicalPhysicalDerivative c hc hLower fC)) =
      fun a : Space =>
        pathTranslation T a (multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath) +
        pathTranslation T a (multiplier (solenoidalFrame T F) (s.classicalAcceleration c hc hLower fC)) := by
    funext a
    exact (congrArg (pathTranslation T a) (s.classicalPhysicalDerivative_eq_products c hc hLower fC)).trans
      ((pathTranslation T a).map_add _ _)
  exact Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => ContDiff ℝ n g) he)
    ((framePathApply_translation_contDiff T F₁ s.coordinateVelocityPath hF₁ hv).add
      (framePathApply_translation_contDiff T F (s.classicalAcceleration c hc hLower fC) hF
        (s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hv hf)))


end EulerMeanVariationalInverse.StrongMeanEvolution
