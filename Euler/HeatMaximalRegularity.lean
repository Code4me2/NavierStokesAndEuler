import Euler.HeatMaximalCauchy
import Euler.RegularizedMildEquation
import Euler.TimeLpMap

/-! Genuine maximal spatial regularity of the actual viscous mild solution, proved by strong Cauchy limits. -/

noncomputable section

namespace EulerHeatMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevLaplacian EulerTimeLp EulerVolterraConvolution EulerRegularizedMildEquation
  EulerHeatMaximalCauchy EulerHeatMaximalEstimate
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual regularized mild solutions are strongly Cauchy in Bochner L² time with two derivatives. -/
theorem regularized_mild_cauchy (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) := by
  apply heat_H2_cauchy period T hT ν hν (fun n => regularizedState period T n u)
    (fun n => regularizedForcing period T n f)
    (regularizedState_first_time_derivative period T hT ν hν u₀ f u hsol)
  · exact (regularizedState_low_tendsto period T u).cauchySeq
  · exact (pathLp_tendsto T hT _ _ (regularizedForcing_value_tendsto period T f)).cauchySeq







end EulerHeatMaximalRegularity
