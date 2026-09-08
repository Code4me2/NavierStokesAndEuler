import Euler.EulerCorrectionLocal
import Euler.MildEquationBridge

/-! The constructed local viscous Euler correction satisfies the actual differential equation and pressure constraint. -/

noncomputable section

namespace EulerCorrectionOperators

open MeasureTheory InnerProductSpace Set EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevTransport
  EulerSobolevCoefficientPressure EulerQuadraticSource EulerMildEquationBridge
  EulerSobolevHeatGenerator EulerDuhamelDifferentiation EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance equationSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance equationSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual non-pressure residual and nonlinear increment in equation (17). -/
def CorrectionData.rawSource {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q+1)) : SobolevSpace period q :=
  (D.coefficients period hq).forcing t + (D.coefficients period hq).linear t e +
    (D.coefficients period hq).quadratic t e e

/-- The correction pressure is the actual unique coercive gradient solution with the sign of equation (17). -/
def CorrectionData.pressure {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q+1)) : SobolevSpace period q :=
  -(pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity D.coercivity_pos
    (D.metric_pos t) (D.rawSource period hq t e))

/-- The actual pressure belongs to the closed lifted gradient space. -/
theorem CorrectionData.pressure_mem_gradient {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q+1)) :
    value period (D.pressure period hq t e) ∈ gradientSpace period D.κ D.direction := by
  change -value period (pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
    D.coercivity_pos (D.metric_pos t) _) ∈ _
  exact (gradientSpace period D.κ D.direction).neg_mem
    (pressureSobolev_mem_gradient period (D.metric.jet t) D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos t) _)

/-- The projected source equals the literal non-pressure source plus the actual coefficient-weighted pressure. -/
theorem CorrectionData.source_value {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q+1)) :
    value period ((D.coefficients period hq).apply t e) =
      -value period (D.rawSource period hq t e) -
        (D.metric.coefficient t).operator (value period (D.pressure period hq t e)) := by
  change -value period (projectedSourceOperator period (D.metric.jet t) D.κ D.direction D.coercivity
    D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)) = _
  rw [projectedSourceOperator_value]
  change -(value period (D.rawSource period hq t e) -
    (D.metric.coefficient t).operator ((D.metric.coefficient t).pressure D.κ D.direction D.coercivity D.coercivity_pos
      (D.metric_pos t) (value period (D.rawSource period hq t e)))) =
    -value period (D.rawSource period hq t e) - (D.metric.coefficient t).operator
      (-value period (pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)))
  rw [map_neg, pressureSobolevOperator_value]
  abel


end EulerCorrectionOperators
