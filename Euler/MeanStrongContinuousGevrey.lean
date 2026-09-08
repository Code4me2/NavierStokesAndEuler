import Euler.MeanContinuousPhysical
import Euler.MeanStrongGevrey

/-!
# Uniform-time factorial bounds for the strong mean solution

The proved H¹ reconstruction estimates the continuous coordinate velocity.
The actual continuous Gram inverse then controls acceleration and the
physical time derivative. All bounds concern genuine spatial derivatives.
-/

noncomputable section

namespace EulerMeanStrongContinuousGevrey

open EulerGevrey

/-- The fixed H¹ trace cost for unit velocity and acceleration jet amplitudes. -/
def coordinateTraceCost (T : ℝ) : ℝ := T⁻¹*Real.sqrt T+2*Real.sqrt T

theorem coordinateTraceCost_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ coordinateTraceCost T := by
  unfold coordinateTraceCost
  positivity

end EulerMeanStrongContinuousGevrey

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanContinuousAcceleration EulerMeanStrongGevrey
  EulerMeanStrongContinuousGevrey EulerOperatorGevreyCalculus EulerTimeLpGramGevrey
  EulerTimeLp EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (fC : C(Icc (0 : ℝ) T,L2))


end EulerMeanVariationalInverse.StrongMeanEvolution
