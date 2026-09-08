import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact core and carrier scaling

Real-power identities and the integer-frequency estimate in Appendix A,
Proposition A.2 and Remark 8.6 of the candidate manuscript. These are scalar
scaling facts; they do not supply a Navier--Stokes solution or analytic estimates
for its profiles. The arbitrary envelope is kept in the carrier Reynolds product.
-/

noncomputable section

namespace NavierStokes.Scaling

/-- The core velocity scale, with the fixed profile coefficient omitted. -/
def coreVelocity (q h : ℝ) : ℝ := q ^ (-(1 / 2 + h))

/-- The radial length scale. -/
def radialLength (q : ℝ) : ℝ := q ^ (1 / 2 : ℝ)






theorem sqrt_viscosity {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Real.sqrt (Q ^ h) = Q ^ (h / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQ.le]
  congr 1
  ring




/-- The integer carrier frequency is the natural ceiling of `ε ^ (-1/2)`. -/
def carrierFrequency (ε : ℝ) : ℕ := ⌈ε ^ (-(1 / 2 : ℝ))⌉₊

theorem inverse_sqrt_power {ε : ℝ} (hε : 0 < ε) :
    ε ^ (-(1 / 2 : ℝ)) = (Real.sqrt ε)⁻¹ := by
  rw [Real.rpow_neg hε.le, Real.sqrt_eq_rpow]

/-- Integer rounding changes `k √ε` by at most `√ε`. -/
theorem carrier_frequency_sqrt_bounds {ε : ℝ} (hε : 0 < ε) :
    1 ≤ (carrierFrequency ε : ℝ) * Real.sqrt ε ∧
      (carrierFrequency ε : ℝ) * Real.sqrt ε ≤ 1 + Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hp : 0 ≤ ε ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hε _).le
  have hc : ε ^ (-(1 / 2 : ℝ)) * Real.sqrt ε = 1 := by
    rw [inverse_sqrt_power hε, inv_mul_cancel₀ hs.ne']
  constructor
  · have hl := mul_le_mul_of_nonneg_right
      (Nat.le_ceil (ε ^ (-(1 / 2 : ℝ)))) hs.le
    simpa only [carrierFrequency, hc] using hl
  · have hu := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hp).le hs.le
    calc
      (carrierFrequency ε : ℝ) * Real.sqrt ε ≤
          (ε ^ (-(1 / 2 : ℝ)) + 1) * Real.sqrt ε := hu
      _ = 1 + Real.sqrt ε := by rw [add_mul, hc, one_mul]

theorem carrier_frequency_pos {ε : ℝ} (hε : 0 < ε) :
    0 < (carrierFrequency ε : ℝ) := by
  have h := (carrier_frequency_sqrt_bounds hε).1
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  nlinarith

/-- The lower and upper viscosity bounds include the integer ceiling error. -/
theorem carrier_viscosity_bounds {ε : ℝ} (hε : 0 < ε) :
    1 ≤ ε * (carrierFrequency ε : ℝ) ^ 2 ∧
      ε * (carrierFrequency ε : ℝ) ^ 2 ≤ (1 + Real.sqrt ε) ^ 2 := by
  obtain ⟨hl, hu⟩ := carrier_frequency_sqrt_bounds hε
  have hk : 0 ≤ (carrierFrequency ε : ℝ) * Real.sqrt ε := by positivity
  have heq : ((carrierFrequency ε : ℝ) * Real.sqrt ε) ^ 2 =
      ε * (carrierFrequency ε : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hε.le]
    ring
  constructor
  · have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hk).mpr hl
    simpa only [one_pow, heq] using hsq
  · have hsq := (sq_le_sq₀ hk (by positivity : 0 ≤ 1 + Real.sqrt ε)).mpr hu
    simpa only [heq] using hsq

theorem one_add_sqrt_sq_le_four {ε : ℝ} (hε₁ : ε ≤ 1) :
    (1 + Real.sqrt ε) ^ 2 ≤ 4 := by
  have hs : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε₁
  have hs₀ := Real.sqrt_nonneg ε
  nlinarith

/-- The manuscript's complete inequality, for `0 < ε ≤ 1`. -/
theorem order_one_viscosity {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    1 ≤ ε * (carrierFrequency ε : ℝ) ^ 2 ∧
      ε * (carrierFrequency ε : ℝ) ^ 2 ≤ (1 + Real.sqrt ε) ^ 2 ∧
      (1 + Real.sqrt ε) ^ 2 ≤ 4 := by
  exact ⟨(carrier_viscosity_bounds hε).1, (carrier_viscosity_bounds hε).2,
    one_add_sqrt_sq_le_four hε₁⟩

theorem reciprocal_frequency_bounds {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    Real.sqrt ε / 2 ≤ 1 / (carrierFrequency ε : ℝ) ∧
      1 / (carrierFrequency ε : ℝ) ≤ Real.sqrt ε := by
  obtain ⟨hl, hu⟩ := carrier_frequency_sqrt_bounds hε
  have hk := carrier_frequency_pos hε
  have hs : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε₁
  constructor
  · apply (le_div_iff₀ hk).mpr
    nlinarith
  · apply (div_le_iff₀ hk).mpr
    nlinarith







end NavierStokes.Scaling
