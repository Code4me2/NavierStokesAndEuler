import Euler.FiniteMetricEnergy

/-! Finite-word viscous energy for the actual lifted transport and projected-pressure equation. -/

noncomputable section

namespace EulerCylinderViscousEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerMetricHeatEnergy EulerFiniteMetricEnergy
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The exact coefficient left after absorbing half the variable-metric heat dissipation. -/
def heatEnergyConstant (K : SmoothCoefficient period) (c : ℝ) : ℝ :=
  2 * (K.firstBound : ℝ) ^ 2 / c ^ 2

/-- The actual transport metric correction for a bounded lifted velocity. -/
def transportEnergyConstant (K : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (B : ℝ≥0) : ℝ :=
  (1 / 2 : ℝ) * K.firstBound * ((|κ| + ‖m‖) * B)


end EulerCylinderViscousEnergy
