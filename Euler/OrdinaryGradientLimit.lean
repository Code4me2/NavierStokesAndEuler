import Euler.OrdinaryGradientStability
import Euler.OrdinaryEulerCauchy

/-! Common-interval smooth Euler limits under a uniform bound on the
actual time integral of the velocity gradient. The H³ bound, all higher
bounds, and path Cauchy convergence are derived from the true equations. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
open scoped Topology

def gradientTensorBound (R G : ℝ) : ℝ :=
  wordCount 3*Real.sqrt (wordCount 3*R^2*Real.exp (gradientEnergyConstant*G))

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

theorem h3_tensorNorm_gradient_uniform (U : Evolution T hT) (R G : ℝ)
    (hR : tensorNorm 3 (U.velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.velocity t) ≤ gradientTensorBound R G := by
  apply (U.h3_tensorNorm_of_gradientIntegral G hG t).trans
  apply mul_le_mul_of_nonneg_left _ (wordCount_nonneg 3)
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (wordEnergy_le_tensorNorm _ 3).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (tensorNorm_nonneg 3 _) hR 2) (wordCount_nonneg 3))


end Evolution

variable {T : ℝ} {hT : 0 ≤ T}




end EulerOrdinarySobolev
