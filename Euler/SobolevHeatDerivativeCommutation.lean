import Euler.SobolevLaplacian

/-! Exact heat commutation with the genuine Sobolev derivatives and Laplacian. -/

noncomputable section

namespace EulerSobolevLaplacian

open EulerCylinderSobolevSpace EulerSobolevHeat
open scoped NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Actual heat commutes with every strong coordinate derivative between consecutive Sobolev levels. -/
theorem derivative_heat {q : ℕ} (i : Fin 4) (v : ℝ≥0) (u : SobolevSpace period (q+1)) :
    derivativeOperator period q i (heatOperator period (q+1) v u) =
      heatOperator period q v (derivativeOperator period q i u) := by
  apply Subtype.ext
  funext w
  rfl


end EulerSobolevLaplacian
