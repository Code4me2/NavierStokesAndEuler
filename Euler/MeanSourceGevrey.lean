import Euler.MeanSourceFixedInverse
import Euler.MeanTranslatedGevrey
import Euler.MeanScaledBoundaryGevrey

/-!
# The actual source mean coordinate inverse has Gevrey spatial bounds

The spatial lower bound, operator smoothness, cutoff derivatives, fixed-space
transport, and inverse recurrence are all supplied by proved constructions.
The remaining quantitative inputs are literal spatial derivatives of the given
matrix coefficients and the actual translation derivatives of the forcing.
-/

noncomputable section

namespace EulerMeanSourceGevrey

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanSourceFixedInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTranslatedGevrey
  EulerTimeLp EulerCoerciveProjection EulerGevrey EulerOperatorGevreyCalculus
open scoped NNReal ContDiff

/-- True spatial coefficient bounds become bounds for the conjugated operator path. -/
theorem translatedPath_bound (T : ℝ)
    (F : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b (operatorPath T F.field)) a‖ ≤ C*majorant R 0 n := by
  simpa only [translatePath_operatorPath] using
    norm_iteratedFDeriv_operatorPathTranslation_le T F n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hbound n) a

/-- The initial matrix multiplier has the same literal spatial derivative bounds. -/
theorem translatedMultiplier_bound
    (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b (multiplier M0.field)) a‖ ≤ C*majorant R 0 n := by
  simpa only [translateOperator_multiplier] using
    norm_iteratedFDeriv_multiplierTranslation_le M0 n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hbound n) a

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1*Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v,v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2)+Be*T+boundaryLocalizationC2*Bc*r^3*T ≤ 1/2)


end EulerMeanSourceGevrey
