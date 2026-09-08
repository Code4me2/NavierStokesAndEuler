import Euler.MeanContinuousPhysical
import Euler.MeanPathTimeDerivative

/-!
# Classical spatial representatives of the actual mean time evolution

The actual continuous velocity and continuous time derivative have smooth
spatial translation orbits. The bounded time-integral identity commutes
with those spatial derivatives, giving genuine jointly continuous spatial
representatives and their pointwise classical time derivative.
-/

noncomputable section

namespace EulerMeanClassicalSpatialTime

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeContinuousTranslation EulerMeanSmoothRepresentative EulerVolterraConvolution
open scoped ContDiff


end EulerMeanClassicalSpatialTime

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanClassicalSpatialTime EulerVolterraConvolution EulerTimeLp
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (fC : C(Icc (0 : ℝ) T,L2))

/-- The reconstructed velocity path has its actual continuous derivative
at every time, including within-interval endpoint derivatives. -/
theorem continuousVelocity_hasDerivWithinAt (hTpos : 0 < T)
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT s.continuousVelocity)
      (s.classicalPhysicalDerivative c hc hLower fC t) (Icc (0 : ℝ) T) t := by
  apply (s.physical_hasDerivWithinAt c hc hLower fC hf hFTime t).congr_of_mem _ t.property
  intro r hr
  change s.continuousVelocity (projIcc 0 T hT r) = s.physicalPath r
  rw [projIcc_of_mem hT hr]
  exact s.continuousVelocity_eq_physicalPath hTpos hFTime ⟨r, hr⟩


end EulerMeanVariationalInverse.StrongMeanEvolution
