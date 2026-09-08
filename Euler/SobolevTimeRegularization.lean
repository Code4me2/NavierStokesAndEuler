import Euler.TimeLpStrongOperators
import Euler.TimeLpMultiplier
import Euler.HeatRegularizedPaths

/-! Strong actual heat approximation and time-dependent operator commutators in Bochner Sobolev spaces. -/

noncomputable section

namespace EulerSobolevTimeRegularization

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerHeatRegularizedPaths EulerTimeLp
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine Sobolev heat regularizations converge strongly on every Bochner L² time field. -/
theorem heat_timeLp_tendsto (q : ℕ) (T : ℝ) (u : TimeLp T (SobolevSpace period q)) :
    Filter.Tendsto (fun n => (heatOperator period q (regularizerVariance n)).compLpL 2 (timeMeasure T) u)
      Filter.atTop (𝓝 u) := by
  apply strong_operator_timeLp_tendsto T (fun n => heatOperator period q (regularizerVariance n)) 1
  · intro n x
    simpa only [one_mul] using heatOperator_bound period (regularizerVariance n) x
  · intro x
    have h := (heatOperator_continuous period x).continuousAt.tendsto.comp regularizerVariance_tendsto
    simpa only [heatOperator_zero, Function.comp_def] using h



end EulerSobolevTimeRegularization
