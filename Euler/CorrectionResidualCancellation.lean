import Euler.InviscidSobolevEvolution

/-! Adding the actual correction removes a genuine approximate-solution residual. -/

noncomputable section

namespace EulerCorrectionResidualCancellation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerQuadraticSource EulerVolterraConvolution
  EulerInviscidSobolevEvolution EulerSobolevCoefficientPressure
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev group structure for exact residual cancellation. -/
local instance residualSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- The inherited real Sobolev module structure for exact residual cancellation. -/
local instance residualSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual linear coefficient plus the full transport-and-algebraic quadratic nonlinearity. -/
def nonlinearity {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u : SobolevSpace period (q+1)) : SobolevSpace period q :=
  coefficientSobolevOperator period (D.linear.jet t) (truncateOperator period q u) +
    (D.coefficients period hq).quadratic t u u

/-- The actual raw correction source is exactly the prescribed residual plus the full nonlinear increment about the prescribed approximation. -/
theorem rawSource_eq_residual_increment {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q+1)) :
    D.rawSource period hq t e = D.residual t +
      nonlinearity period D hq t (D.approximation t+e) -
      nonlinearity period D hq t (D.approximation t) := by
  let B := (D.coefficients period hq).quadratic t
  let A := (coefficientSobolevOperator period (D.linear.jet t)).comp (truncateOperator period q)
  change D.residual t + linearize B A (D.approximation t) e + B e e =
    D.residual t + (A (D.approximation t+e) + B (D.approximation t+e) (D.approximation t+e)) -
      (A (D.approximation t) + B (D.approximation t) (D.approximation t))
  simp only [linearize_apply,map_add,add_apply]
  abel

/-- The signed approximate and correction equations cancel the residual and add their actual pressures. -/
theorem residual_cancellation {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (e : SobolevSpace period (q+1)) (pa : SobolevSpace period q) :
    (D.residual t-nonlinearity period D hq t (D.approximation t)-
        coefficientSobolevOperator period (D.metric.jet t) pa) +
      (-D.rawSource period hq t e-
        coefficientSobolevOperator period (D.metric.jet t) (D.pressure period hq t e)) =
      -nonlinearity period D hq t (D.approximation t+e)-
        coefficientSobolevOperator period (D.metric.jet t) (pa+D.pressure period hq t e) := by
  rw [rawSource_eq_residual_increment period D hq t e,map_add]
  abel






end EulerCorrectionResidualCancellation
