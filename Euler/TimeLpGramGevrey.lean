import Euler.TimeLpGramInverse
import Euler.HilbertCoerciveGevrey

/-!
# Uniform factorial estimates for the actual time Gram inverse

The lower frame bound and actual coefficient derivatives give the estimates
for the inverse appearing in the strong acceleration equation. No derivative
bounds on a pre-existing inverse are assumed.
-/

noncomputable section

open scoped ContDiff

namespace EulerTimeLpGramGevrey

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramInverse EulerHilbertCoerciveGevrey EulerHilbertCoerciveParameter
  EulerTransverseGramPath EulerGevrey

/-- A polynomial top constant for coefficient amplitude `3 C²` and forcing amplitude `D`. -/
def gramCost (c C D : ℝ) : ℝ := 1 + c⁻¹ * (3*C^2+D+1)

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Gram solve is the actual smoothly parameterized coercive solution. -/
theorem gramSolution_contDiff (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
    (f : P → TimeLp T U) {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => gramSolver T hT (Q x) c hc (hLower x) (f x)) :=
  contDiff_coerciveSolution_variable (fun x => gramOperator T hT (Q x)) (fun _ => c)
    (fun _ => hc) (fun x => gramOperator_coercive T hT (Q x) c (hLower x)) f
    (gramOperator_contDiff T hT Q hQ) hf



end EulerTimeLpGramGevrey
