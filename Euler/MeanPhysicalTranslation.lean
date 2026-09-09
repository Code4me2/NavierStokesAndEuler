import Euler.MeanOperatorTranslation
import Euler.MeanStrongEstimates
import Euler.MeanFixedCoefficientGevrey

/-!
# Spatial orbit estimates for the actual physical mean fields

Frame multiplication preserves genuine translation regularity and factorial
bounds. These identities apply to the physical velocity, its actual time
derivative, and the pressure residual constructed by the strong mean solve.
-/

noncomputable section

namespace EulerMeanPhysicalTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanVariationalInverse EulerTimeLp EulerVolterraConvolution
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey EulerOperatorGevreyCalculus EulerGevrey
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

/-- The actual spatial orbit of a frame product. -/
theorem frameApply_orbit_eq (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (v : TimeLp T solenoidalSpace) :
    (fun a : Space => timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) v)) =
      fun a : Space => timeMultiplier T hT (solenoidalFrame T (translatePath T a F))
        (timeSolenoidalTranslation T a v) :=
  funext (fun a => (frameMultiplier_translate T hT a F v).symm)

/-- Genuine spatial regularity survives multiplication by the actual frame. -/
theorem frameApply_translation_contDiff (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (v : TimeLp T solenoidalSpace) {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a v)) :
    ContDiff ℝ n (fun a : Space =>
      timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) v)) := by
  have hQ := contDiff_solenoidalFrame T (fun a : Space => translatePath T a F) hF
  have hp := (contDiff_timeMultiplier T hT
    (fun a : Space => solenoidalFrame T (translatePath T a F)) hQ).clm_apply hv
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T L2 => ContDiff ℝ n g)
    (frameApply_orbit_eq T hT F v)) hp


end EulerMeanPhysicalTranslation

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanPhysicalTranslation
  EulerTimeLp EulerVolterraConvolution EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

theorem velocityDerivative_orbit_eq :
    (fun a : Space => timeTranslation T a s.velocityDerivative) =
      fun a : Space => timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp) +
        timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) s.acceleration) :=
  funext (fun a => (timeTranslation T a).map_add _ _)


/-- The physical velocity has the genuine spatial regularity of the coordinate velocity. -/
theorem velocityField_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.velocityLp)) :
    ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityField) :=
  frameApply_translation_contDiff T hT F s.velocityLp hF hv

/-- This is spatial regularity of the actual time derivative B_t. -/
theorem velocityDerivative_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.acceleration)) :
    ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityDerivative) :=
  Eq.mpr (congrArg (fun g : Space → TimeLp T L2 => ContDiff ℝ n g) s.velocityDerivative_orbit_eq)
    ((frameApply_translation_contDiff T hT F₁ s.velocityLp hF₁ hv).add
      (frameApply_translation_contDiff T hT F s.acceleration hF ha))




end EulerMeanVariationalInverse.StrongMeanEvolution
