import Euler.GevreyForcingComponents
import Euler.GevreyPressureComplete

/-! The actual differentiated correction forcing and its cutoff-independent nonlinear bound. -/

noncomputable section

namespace EulerGevreyCorrectionForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy EulerBasePressureCommutator
  EulerGevreyBaseTransport EulerGevreyForcingComponents EulerWeightedForcingAlgebra
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerH6Nonlinear EulerBaseTransportL2

variable (period : ℝ) [Fact (0 < period)]

/-- The seven literal commutator/source terms after external and base differentiation of equation (17).
The two pressure arguments are the positive projected inverses; the PDE pressure has the opposite sign. -/
def correctionForcing {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N+6 ≤ s) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f p0 p1 : SobolevSpace period s) : ExternalWord N → BaseWord 6 → LiftL2 period :=
  -energyValues period 6 N hN f + -externalTransportForcing period hs N hN L hL u v +
    -baseTransportForcing period N hN L hL u v + externalPressureForcing period K N hN p0 +
    basePressureForcing period K0 N hN p0 + externalPressureForcing period K N hN p1 +
    basePressureForcing period K0 N hN p1

/-- The triangle inequality for seven actual forcing arrays has coefficient one. -/
theorem forcing_seven_le {α β H : Type*} [Fintype α] [Fintype β] [NormedAddCommGroup H]
    (ρ : ℝ) (hρ : 0 < ρ) (order : α → ℕ) (a b c d e f g : α → β → H) :
    weightedForcingSum ρ order (a+b+c+d+e+f+g) ≤ weightedForcingSum ρ order a + weightedForcingSum ρ order b +
      weightedForcingSum ρ order c + weightedForcingSum ρ order d + weightedForcingSum ρ order e +
      weightedForcingSum ρ order f + weightedForcingSum ρ order g := by
  have h1 := weightedForcingSum_add_le ρ hρ order a b
  have h2 := weightedForcingSum_add_le ρ hρ order (a+b) c
  have h3 := weightedForcingSum_add_le ρ hρ order (a+b+c) d
  have h4 := weightedForcingSum_add_le ρ hρ order (a+b+c+d) e
  have h5 := weightedForcingSum_add_le ρ hρ order (a+b+c+d+e) f
  have h6 := weightedForcingSum_add_le ρ hρ order (a+b+c+d+e+f) g
  linarith



end EulerGevreyCorrectionForcing
