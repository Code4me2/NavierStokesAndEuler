import Euler.MeanStrongEstimates
import Euler.ContinuousGramAcceleration
import Euler.TimeH1ContinuousDerivative
import Euler.TimeH1Reconstruction

/-!
# Continuous acceleration and classical time derivatives for the mean inverse

With a continuous representative of the prescribed forcing, the actual
strong equation constructs continuous coordinate acceleration and physical
time derivative. The original AC paths have these derivatives at every
interior time, and within the interval at both endpoints.
-/

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerMeanSolenoidal EulerVolterraConvolution EulerTransverseGramInverse
  EulerTimeH1FieldProduct EulerTimeH1ContinuousDerivative EulerTimeH1Reconstruction
  EulerContinuousGramAcceleration

-- Fix the Hilbert-space instances before forming continuous operator paths.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The original coordinate velocity is continuous on the closed time interval. -/
def coordinateVelocityPath : C(Icc (0 : ℝ) T, solenoidalSpace) :=
  ⟨fun t => s.velocity t, by
    have hc : ContinuousOn s.velocity (Icc (0 : ℝ) T) := by
      simpa only [uIcc_of_le hT] using s.velocity_ac.continuousOn
    exact hc.domRestrict⟩

@[simp] theorem coordinateVelocityPath_apply (t : Icc (0 : ℝ) T) :
    s.coordinateVelocityPath t = s.velocity t := rfl

/-- This is a continuous representative of the actual L² coordinate velocity. -/
theorem coordinateVelocityPath_ae :
    (s.velocityLp : ℝ → solenoidalSpace) =ᵐ[timeMeasure T] extendPath T hT s.coordinateVelocityPath := by
  filter_upwards [s.velocity_ae, ae_restrict_mem measurableSet_Icc] with t hv ht
  change s.velocityLp t = s.velocity (projIcc 0 T hT t)
  rw [projIcc_of_mem hT ht]
  exact hv


/-- The already proved projected equation is the ordinary solenoidal Gram equation. -/
theorem gram_equation_ae :
    ∀ᵐ t ∂timeMeasure T,
      gram (extendPath T hT (solenoidalFrame T F) t) (s.acceleration t) =
      (solenoidalFrame T F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • solenoidalFrame T F₁ (projIcc 0 T hT t) (s.velocityLp t)) := by
  filter_upwards [s.equation, s.velocity_ae] with t ht hv
  have hh := congrArg (fun v : solenoidalSpace =>
    solenoidalProjection ((F (projIcc 0 T hT t)).adjoint
      (f t-(2 : ℝ) • F₁ (projIcc 0 T hT t) (v : L2)))) hv
  exact gram_equation_of_ordinary (F (projIcc 0 T hT t)) (F₁ (projIcc 0 T hT t))
    (f t) (s.acceleration t) (s.velocityLp t) (ht.trans hh.symm)

variable (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (fC : C(Icc (0 : ℝ) T, L2))

/-- Continuous coordinate acceleration constructed by the actual Gram inverse. -/
def classicalAcceleration : C(Icc (0 : ℝ) T, solenoidalSpace) :=
  accelerationPath T (solenoidalFrame T F) (solenoidalFrame T F₁) c hc hLower
    s.coordinateVelocityPath fC


/-- The L² acceleration is genuinely represented by this continuous path. -/
theorem classicalAcceleration_ae
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC) :
    (s.acceleration : ℝ → solenoidalSpace) =ᵐ[timeMeasure T]
      extendPath T hT (s.classicalAcceleration c hc hLower fC) :=
  accelerationPath_ae T (solenoidalFrame T F) (solenoidalFrame T F₁) c hc hLower hT
    s.velocityLp s.acceleration f s.coordinateVelocityPath fC s.coordinateVelocityPath_ae hf s.gram_equation_ae

/-- Coordinate velocity has the classical acceleration at every time within the interval. -/
theorem velocity_hasDerivWithinAt
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt s.velocity (s.classicalAcceleration c hc hLower fC t) (Icc (0 : ℝ) T) t :=
  hasDerivWithinAt_of_continuous_representative T hT s.acceleration
    (s.classicalAcceleration c hc hLower fC) (s.classicalAcceleration_ae c hc hLower fC hf)
    s.velocity s.velocity_ac s.velocity_derivative t

/-- The physical derivative path is the actual continuous product-rule expression. -/
def classicalPhysicalDerivative : C(Icc (0 : ℝ) T, L2) :=
  ⟨fun t => F₁ t (s.coordinateVelocityPath t : L2) +
      F t (s.classicalAcceleration c hc hLower fC t : L2),
    (F₁.continuous.clm_apply (solenoidalSpace.subtypeL.continuous.comp s.coordinateVelocityPath.continuous)).add
      (F.continuous.clm_apply (solenoidalSpace.subtypeL.continuous.comp
        (s.classicalAcceleration c hc hLower fC).continuous))⟩

/-- This continuous path is the already constructed physical derivative B_t. -/
theorem classicalPhysicalDerivative_ae
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC) :
    (s.velocityDerivative : ℝ → L2) =ᵐ[timeMeasure T]
      extendPath T hT (s.classicalPhysicalDerivative c hc hLower fC) := by
  filter_upwards [fieldProductDerivative_ae T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
      s.velocityLp s.acceleration, s.coordinateVelocityPath_ae,
    s.classicalAcceleration_ae c hc hLower fC hf] with t ht hv ha
  exact ht.trans (congrArg₂ (fun v a : solenoidalSpace =>
    F₁ (projIcc 0 T hT t) (v : L2)+F (projIcc 0 T hT t) (a : L2)) hv ha)

/-- The original physical mean velocity now has a classical time derivative
at every time, including the endpoint derivatives within the interval. -/
theorem physical_hasDerivWithinAt
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt s.physicalPath (s.classicalPhysicalDerivative c hc hLower fC t)
      (Icc (0 : ℝ) T) t := by
  have hp := s.physical_h1 hF
  exact hasDerivWithinAt_of_continuous_representative T hT s.velocityDerivative
    (s.classicalPhysicalDerivative c hc hLower fC) (s.classicalPhysicalDerivative_ae c hc hLower fC hf)
    s.physicalPath hp.1 hp.2.2 t


end EulerMeanVariationalInverse.StrongMeanEvolution
