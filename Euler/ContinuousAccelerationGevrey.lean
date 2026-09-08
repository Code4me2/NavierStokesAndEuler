import Euler.ContinuousGramAcceleration
import Euler.ContinuousGramGevrey
import Euler.ContinuousAccelerationForcing

/-!
# Uniform-time regularity of actual acceleration

The continuous acceleration is the already constructed Gram inverse applied
to its literal forcing. Smoothness and factorial estimates therefore apply
to the actual continuous path, including its endpoint values.
-/

noncomputable section

namespace EulerContinuousAccelerationGevrey

open Set ContinuousLinearMap EulerContinuousGramAcceleration
  EulerContinuousGramPath EulerContinuousGramGevrey EulerContinuousAccelerationForcing
  EulerOperatorGevreyCalculus EulerTimeLpGramGevrey EulerGevrey
open scoped ContDiff

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (Q Q₁ : P → C(Icc (0 : ℝ) T,U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
  (v : P → C(Icc (0 : ℝ) T,U)) (f : P → C(Icc (0 : ℝ) T,E))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The continuous acceleration is the genuine continuous Gram solve. -/
theorem acceleration_eq_solve :
    (fun x => accelerationPath T (Q x) (Q₁ x) c hc (hLower x) (v x) (f x)) =
      fun x => solve T (Q x) c hc (hLower x) (forcing Q Q₁ f v x) := by
  funext x
  apply ContinuousMap.ext
  intro t
  rfl

/-- Actual uniform-time acceleration depends smoothly on the actual coefficients and data. -/
theorem acceleration_contDiff {n : ℕ∞ω}
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hv : ContDiff ℝ n v) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => accelerationPath T (Q x) (Q₁ x) c hc (hLower x) (v x) (f x)) :=
  Eq.mpr (congrArg (fun g : P → C(Icc (0 : ℝ) T,U) => ContDiff ℝ n g)
    (acceleration_eq_solve T Q Q₁ c hc hLower v f))
    (solve_contDiff T c hc Q hLower (forcing Q Q₁ f v) hQ
      (forcing_contDiff Q Q₁ f v hQ hQ₁ hf hv))


end EulerContinuousAccelerationGevrey
