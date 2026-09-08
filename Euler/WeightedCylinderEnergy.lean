import Euler.WeightedRootLimit

/-! Actual Gevrey-weighted cylinder energy with signed radius derivative and no zero-norm differentiation. -/

noncomputable section

namespace EulerWeightedCylinderEnergy

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerSpatialSobolevInverse EulerCylinderSobolev EulerMetricEnergyEvolution
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy EulerWeightedRootLimit
  EulerPacketWeights EulerWeightedEnergy
open scoped ContDiff ENNReal NNReal Topology

section WeightedNorms

variable {α β H : Type*} [Fintype α] [Fintype β]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The finite external-word Gevrey sum of the source's base-word metric roots. -/
def weightedMetricSum (ρ : ℝ) (order : α → ℕ) (K : H →L[ℝ] H) (e : α → β → H) : ℝ :=
  ∑ i, weight ρ (order i) * familyMetricNorm K (e i)

/-- The same metric sum with the external derivative count, giving the radius-loss term. -/
def weightedMetricLoss (ρ : ℝ) (order : α → ℕ) (K : H →L[ℝ] H) (e : α → β → H) : ℝ :=
  ∑ i, (order i : ℝ) * weight ρ (order i) * familyMetricNorm K (e i)

/-- The actual finite weighted sum of base-word Hilbert forcing norms. -/
def weightedForcingSum (ρ : ℝ) (order : α → ℕ) (f : α → β → H) : ℝ :=
  ∑ i, weight ρ (order i) * familyNorm (f i)

end WeightedNorms

variable (period : ℝ) [Fact (0 < period)]

/-- The explicit common coefficient in the actual viscous metric-root estimate. -/
def viscousGrowthCoefficient (K : SmoothCoefficient period)
    (K' : LiftL2 period →L[ℝ] LiftL2 period) (κ : ℝ) (m : Vector3) (c ν : ℝ) (B : ℝ≥0) : ℝ :=
  (‖K'‖ + 2 * transportEnergyConstant period K κ m B +
    2 * ν * heatEnergyConstant period K c) / (2 * c ^ 2)


end EulerWeightedCylinderEnergy
