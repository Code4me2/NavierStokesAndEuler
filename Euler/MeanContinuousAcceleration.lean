import Euler.MeanPointwiseGramTranslation
import Euler.MeanCoordinatePath
import Euler.MeanFixedCoefficientGevrey
import Euler.ContinuousAccelerationGevrey

/-!
# Actual spatial orbits of continuous mean acceleration

The ordinary solenoidal Gram inverse commutes with simultaneous translation
of its data. This identifies the parameterized continuous solve with the
genuine spatial orbit of the acceleration, including endpoint times.
-/

noncomputable section

namespace EulerMeanContinuousAcceleration

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath EulerMeanGramTranslation
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousGramAcceleration EulerContinuousAccelerationGevrey
  EulerTimeLpGramGevrey EulerGevrey
open scoped ContDiff

private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2) := inferInstance

variable (T : ℝ) (F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (v : C(Icc (0 : ℝ) T,solenoidalSpace)) (f : C(Icc (0 : ℝ) T,L2))

/-- The continuous mean acceleration constructed at each actual time. -/
def meanAccelerationPath : C(Icc (0 : ℝ) T,solenoidalSpace) :=
  accelerationPath T (solenoidalFrame T F) (solenoidalFrame T F₁) c hc hLower v f

/-- The genuine spatial orbit equals the actual solve with translated data. -/
theorem meanAccelerationPath_orbit_eq :
    (fun a : Space => coordinatePathTranslation T a (meanAccelerationPath T F F₁ c hc hLower v f)) =
      fun a : Space => accelerationPath T (solenoidalFrame T (translatePath T a F))
        (solenoidalFrame T (translatePath T a F₁)) c hc (translatedFrame_lower T F c hLower a)
        (coordinatePathTranslation T a v) (pathTranslation T a f) := by
  funext a
  apply ContinuousMap.ext
  intro t
  exact (EulerMeanPointwiseGramTranslation.acceleration_translation a (F t) (F₁ t)
    c hc (hLower t) (v t) (f t)).symm

/-- Smooth coefficient and data orbits give the actual continuous acceleration orbit. -/
theorem meanAccelerationPath_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a v))
    (hf : ContDiff ℝ n (fun a : Space => pathTranslation T a f)) :
    ContDiff ℝ n (fun a : Space =>
      coordinatePathTranslation T a (meanAccelerationPath T F F₁ c hc hLower v f)) := by
  have hs := acceleration_contDiff T
    (fun a : Space => solenoidalFrame T (translatePath T a F))
    (fun a : Space => solenoidalFrame T (translatePath T a F₁))
    c hc (translatedFrame_lower T F c hLower)
    (fun a : Space => coordinatePathTranslation T a v) (fun a : Space => pathTranslation T a f)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁) hv hf
  exact Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => ContDiff ℝ n g)
    (meanAccelerationPath_orbit_eq T F F₁ c hc hLower v f)) hs


end EulerMeanContinuousAcceleration
