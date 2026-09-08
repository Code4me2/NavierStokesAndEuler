import Euler.CylinderDirichletRegularity
import Euler.CylinderActionWords
import Euler.LpCylinderPathBounds
import Euler.TransverseFixedSobolev

/-!
# Genuine fixed-Sobolev bounds for the cylinder history inverse

The actual mixed translation orbit has identical fixed-base word norms at
every translation. Thus the forcing needs a bound only at zero. Coefficient
jets lift to L² operator paths with constant one, and the true fixed-space
inverse adds one shift while preserving the external radius.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerMeanCoefficients EulerTransverseFixedSobolev
  EulerParameterWordGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

private local instance : NormedAddCommGroup (CylinderL2 P U) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E) := inferInstance

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameOrbit_bound (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => (D.shifted b.1).frame P) a‖ ≤ C :=
  mixedOperatorPath_bound P D.Q hQ n C hb a

omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivativeOrbit_bound (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => (D.shifted b.1).frameDerivative P) a‖ ≤ C :=
  mixedOperatorPath_bound P D.Q₁ hQ₁ n C hb a

omit [CompleteSpace U] [CompleteSpace E] in
theorem hessianOrbit_bound (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => (D.shifted b.1).hessian P) a‖ ≤ C :=
  mixedOperatorPath_bound P D.H hH n C hb a

variable {ι : Type*} [Fintype ι]
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C₁*majorant Rc 0 n)
  (hbH : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ CH*majorant Rc 0 n)
  (hR : 2*blockCost ι q T Rc C₀ C₁ CH D.lower Cf*(sobolevCoefficientRadius ι Rc+1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR



end EulerCylinderDirichlet.Coefficients
