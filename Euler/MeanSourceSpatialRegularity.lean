import Euler.MeanSourceGevrey
import Euler.MeanSourceStrongInverse
import Euler.MeanAccelerationGevrey
import Euler.MeanPhysicalTranslation
import Euler.MeanContinuousVelocity
import Euler.MeanSmoothRepresentative

/-!
# Spatial regularity of the actual source mean inverse

Every strong realization of the constructed source solver has the same fixed
coordinate velocity. Its spatial regularity is therefore supplied by the
actual variational inverse, then passed through the proved Gram inverse and
physical frame. No spatial regularity of the unknown fields is assumed.
-/

noncomputable section

namespace EulerMeanSourceSpatialRegularity

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanSourceFixedInverse EulerMeanSourceGevrey
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanGramTranslation EulerMeanAccelerationGevrey EulerTimeLp EulerVolterraConvolution
open scoped NNReal ContDiff

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1*Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v,v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2)+Be*T+boundaryLocalizationC2*Bc*r^3*T ≤ 1/2)
  (f : TimeLp T L2)
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall f) f)

include hInv hF hRight

/-- The actual strong velocity is the constructed fixed-coordinate source solve. -/
theorem velocity_eq_sourceCoordinates :
    s.velocityLp = sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
      hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f := by
  have hs := StrongMeanEvolution.velocityLp_eq_meanBackward T hT FInv
    (operatorPath T F.field) (operatorPath T F₁.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall f)
    f s hInv hF hRight
  exact hs.trans (sourceCoordinateSolver_eq_mean T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall hRight f).symm

/-- Actual coordinate-velocity spatial regularity follows from the source assumptions. -/
theorem velocity_translation_contDiff
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp) := by
  have heq := velocity_eq_sourceCoordinates T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s
  have horbit : (fun a : Space => timeSolenoidalTranslation T a s.velocityLp) =
      fun a : Space => timeSolenoidalTranslation T a
        (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
          hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f) :=
    funext (fun a => congrArg (timeSolenoidalTranslation T a) heq)
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ ∞ g) horbit)
    (sourceCoordinateSolver_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
      hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f hf)






end EulerMeanSourceSpatialRegularity
