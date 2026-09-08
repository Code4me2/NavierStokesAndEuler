import Euler.EulerCorrectionLocal

/-! Actual correction coefficient data restricted along continuous time maps. -/

noncomputable section

namespace EulerCorrectionOperators

open Set EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerSobolevCoefficientPressure
  EulerQuadraticSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Restrict the actual spatial coefficient and its jet along a continuous parameter map. -/
def CoefficientPath.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (A : CoefficientPath period q T) (f : C(U,T)) : CoefficientPath period q U where
  coefficient t := A.coefficient (f t)
  jet t := A.jet (f t)
  continuous := A.continuous.comp f.continuous

/-- Restrict every actual coefficient, background field, and residual along the same time map. -/
def CorrectionData.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U,T)) : CorrectionData period q U where
  κ := D.κ
  direction := D.direction
  scale_bound := D.scale_bound
  direction_bound := D.direction_bound
  metric := D.metric.comp period f
  coercivity := D.coercivity
  coercivity_pos := D.coercivity_pos
  metric_pos t := D.metric_pos (f t)
  linear := D.linear.comp period f
  quadratic i := (D.quadratic i).comp period f
  approximation := D.approximation.comp f
  residual := D.residual.comp f



end EulerCorrectionOperators
