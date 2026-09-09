import Euler.ContinuousPathComposition

/-!
# Actual continuous-time acceleration forcing

The expression `Q*(f-2 Q₁v)` is a genuine continuous path. Its smoothness and
factorial bound are proved in the uniform time norm and are shared by the
mean and transverse strong equations.
-/

noncomputable section


namespace EulerContinuousAccelerationForcing

open ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {K P U E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The literal continuous forcing in the projected acceleration equation. -/
def forcing (Q Q₁ : P → C(K,U →L[ℝ] E)) (f : P → C(K,E)) (v : P → C(K,U)) (x : P) : C(K,U) :=
  multiplier (adjointMap (Q x)) (f x - (2 : ℝ) • multiplier (Q₁ x) (v x))

/-- Actual uniform-time regularity of the acceleration forcing. -/
theorem forcing_contDiff (Q Q₁ : P → C(K,U →L[ℝ] E)) (f : P → C(K,E)) (v : P → C(K,U))
    {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (hv : ContDiff ℝ n v) : ContDiff ℝ n (forcing Q Q₁ f v) :=
  contDiff_apply (fun x => adjointMap (Q x)) _ (contDiff_adjoint Q hQ)
    (hf.sub ((contDiff_apply Q₁ v hQ₁ hv).const_smul (2 : ℝ)))


end EulerContinuousAccelerationForcing
