import Euler.GevreyUniformConstants
import Euler.GevreyRestriction

/-! The actual nonlinear correction forcing with explicit constants independent of the derivative cutoff. -/

noncomputable section

namespace EulerGevreyCorrectionBound

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators EulerGevreyCorrectionForcing
  EulerBasePressureCommutator EulerBaseTransportL2 EulerH6Nonlinear EulerSobolevTransportCommutator
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerGevreyUniformConstants
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy EulerGevreyRestriction EulerGevreyOrderZero

variable (period : ℝ) [Fact (0 < period)]

/-- The coefficient multiplying the actual order-zero forcing. -/
def sourceConstant (B M : ℝ) : ℝ := 1+2*M*(3136*B+1)

/-- The coefficient for actual base transport and the lower-order nonlinear pressure commutator. -/
def transportConstant (B M : ℝ) : ℝ :=
  5461*baseTransportConstant period + 2688*B*(8*M*(5460*lowerProductConstant period 3))

/-- The coefficient for the actual external radius loss. -/
def lossConstant (M : ℝ) : ℝ := (4+32*M)*productConstant period 3

omit [Fact (0 < period)] in
theorem sourceConstant_nonneg {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) : 0 ≤ sourceConstant B M := by
  unfold sourceConstant
  positivity

theorem transportConstant_nonneg {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) : 0 ≤ transportConstant period B M := by
  unfold transportConstant
  exact add_nonneg (mul_nonneg (by norm_num) (baseTransportConstant_nonneg period))
    (mul_nonneg (mul_nonneg (by norm_num) hB)
      (mul_nonneg (mul_nonneg (by norm_num) hM) (mul_nonneg (by norm_num) (lowerProductConstant_nonneg period 3))))

theorem lossConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ lossConstant period M :=
  mul_nonneg (by linarith) (productConstant_nonneg period 3)


end EulerGevreyCorrectionBound
