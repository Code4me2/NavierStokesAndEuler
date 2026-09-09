import Euler.ContinuousGramPath
import Euler.BoundedInverseGevrey
import Euler.TimeLpGramGevrey

/-!
# Uniform-time factorial bounds for the actual Gram inverse

The inverse is a genuinely smooth continuous operator path. Applying the
frozen-coefficient recurrence in the uniform norm gives actual inverse-path
and solution estimates, without a Hilbert structure on the path space.
-/

noncomputable section

namespace EulerContinuousGramGevrey

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerContinuousGramPath EulerTransverseGramInverse
  EulerTransverseGramPath EulerTransverseStrongEstimates EulerOperatorGevreyCalculus
  EulerTimeLpGramGevrey EulerGevrey
open scoped ContDiff

private theorem cost_bounds (c C D : ℝ) (hc : 0 < c) (hD : 0 ≤ D) :
    1 ≤ gramCost c C D ∧ c⁻¹*(3*C^2) ≤ gramCost c C D ∧ c⁻¹*D ≤ gramCost c C D := by
  have hi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  unfold gramCost
  constructor
  · have h : 0 ≤ c⁻¹*(3*C^2+D+1) := by positivity
    linarith
  constructor <;> nlinarith [sq_nonneg C]

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private local instance : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,U →L[ℝ] U) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ] U) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup
    (C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ] U)) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ
    (C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ] U)) := inferInstance



variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (T : ℝ) (Q : P → C(Icc (0 : ℝ) T,U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
  (hQ : ContDiff ℝ ∞ Q)
  (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C*majorant Rc 0 n)

include hQ hRc hC hbQ



end EulerContinuousGramGevrey
