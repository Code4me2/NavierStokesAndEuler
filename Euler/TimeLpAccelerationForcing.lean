import Euler.TimeLpGramGevrey
import Euler.TimeLpCoefficientGevrey

/-!
# The actual forcing in the projected acceleration equation

Both the mean and transverse strong equations use `Q* (f - 2 Q₁ v)`.
This module gives its genuine parameter regularity and factorial estimate,
with the explicit amplitude needed by the actual Gram inverse.
-/

noncomputable section

open scoped ContDiff

namespace EulerTimeLpAccelerationForcing

open Set ContinuousLinearMap EulerTimeLp EulerVolterraConvolution
  EulerTransverseGramInverse EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey
  EulerOperatorGevreyCalculus EulerGevrey

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The literal right side of the projected strong acceleration equation. -/
def forcing (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (f : P → TimeLp T E) (v : P → TimeLp T U) (x : P) : TimeLp T U :=
  (timeMultiplier T hT (Q x)).adjoint
    (f x - (2 : ℝ) • timeMultiplier T hT (Q₁ x) (v x))

/-- The actual strong forcing is smoothly parameterized whenever its inputs are. -/
theorem forcing_contDiff (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (f : P → TimeLp T E) (v : P → TimeLp T U) {n : ℕ∞ω}
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (forcing T hT Q Q₁ f v) :=
  ((realAdjoint (U := TimeLp T U) (E := TimeLp T E)).contDiff.comp
    (contDiff_timeMultiplier T hT Q hQ)).clm_apply
    (hf.sub (((contDiff_timeMultiplier T hT Q₁ hQ₁).clm_apply hv).const_smul (2 : ℝ)))


end EulerTimeLpAccelerationForcing
