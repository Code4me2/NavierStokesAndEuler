import Euler.AllOrderCorrectionCoherence

/-! Concrete uniform Gevrey budgets for one coherent family of prescribed data. -/

noncomputable section

namespace EulerAllOrderCorrectionBudget

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerAllOrderCorrectionData EulerGevreyMetricEstimate EulerCorrectionLowerData
  EulerVolterraConvolution EulerInviscidSobolevEvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual all-order data budgets with common radius, error size and time interval; these are coefficient/background/residual inequalities, not solution or energy hypotheses. -/
structure Budget {T : ℝ} (hT : 0 < T) (A : Data period T) where
  /-- The common actual inverse metric and its genuine time derivative. -/
  metric : MetricBudget period T hT.le (A.atOrder period 1)
  /-- The common positive shrinking-radius path. -/
  radius : C(Icc (0 : ℝ) T,ℝ)
  /-- The common scalar growth coefficient. -/
  constant : ℝ
  /-- The common desired error size. -/
  delta : ℝ
  /-- The common initial radius. -/
  initialRadius : ℝ
  /-- Genuine coefficient, background and residual bounds at each finite construction cutoff. -/
  spatial : ∀ q (hq : 6 ≤ q), SpatialBudget period (hq.trans (by omega : q ≤ (q+1)+1))
    (A.atOrder period ((q+1)+1)) (q-4) radius
  /-- The fixed scalar dominates each proved nonlinear energy constant. -/
  constant_bound : ∀ q hq, combinedConstant period (spatial q hq)
    (A.metricBudget period hT.le metric (q+1)) ≤ constant
  /-- Strictly positive target error size. -/
  delta_pos : 0 < delta
  /-- The target error is at most one. -/
  delta_le_one : delta ≤ 1
  /-- Strictly positive initial radius. -/
  radius_pos : 0 < initialRadius
  /-- Every construction retains half the common initial radius. -/
  decay : ∀ q hq, 2*constant*((spatial q hq).B0+delta)*T ≤ initialRadius/2
  /-- The coefficient scale fits the common initial radius. -/
  scale : ∀ q hq, initialRadius*(spatial q hq).Rc ≤ 1
  /-- The actual residual budgets beat the genuine Gronwall factor. -/
  small : ∀ q hq, 2*(spatial q hq).residual*Real.exp (3*constant*T) ≤ delta/2
  /-- Every finite construction uses the same actual shrinking radius. -/
  radius_eq : ∀ q hq t, radius t=initialRadius-2*constant*((spatial q hq).B0+delta)*t.val
  /-- The prescribed approximate field is genuinely lifted divergence-free. -/
  divergence : ∀ t, A.approximation.field t ∈ divergenceFreeSpace period A.κ A.direction


end EulerAllOrderCorrectionBudget
