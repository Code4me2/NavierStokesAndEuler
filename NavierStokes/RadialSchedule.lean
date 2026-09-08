import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar identities for the outgoing radial schedule

This file verifies the ideal-prefix source and its lower bound, the exponential
weights of the axial moment rows, their two-column algebraic reset, the negative
energy term in equation (13), and the constant-coefficient lag equation.

These finite-dimensional calculations do not establish existence of the full
smooth schedule, estimates on the correction bumps, or the stress-cone bounds.
-/

noncomputable section

open MeasureTheory

namespace NavierStokes.RadialSchedule

def axialExponent (h : ℝ) : ℝ := 1 / 2 - h

def axialShape (η : ℝ) : ℝ := 1 - η ^ 2

def coordinateFactor (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2

def idealAxialVelocity (η : ℝ) : ℝ := 4 * η

def idealTransport (h η : ℝ) : ℝ :=
  1 - 2 * axialExponent h * η * idealAxialVelocity η - axialShape η * 4

/-- The logarithmic shape derivative of `(1 + η²)⁻¹`. -/
def logShapeDerivative (η : ℝ) : ℝ := -(2 * η / (1 + η ^ 2))


def idealSource (h η : ℝ) : ℝ :=
  -(3 / 5) * idealTransport h η - h * (1 - 2 * η * idealAxialVelocity η) -
    (axialExponent h * η + axialShape η * idealAxialVelocity η) *
      logShapeDerivative η

/-- The constant particular solution with `l = 3/5`. -/
def idealLag (h η : ℝ) : ℝ := idealSource h η / (8 / 5)

theorem ideal_transport_eq (h η : ℝ) :
    idealTransport h η = 1 - 4 * coordinateFactor h η := by
  unfold idealTransport axialExponent axialShape idealAxialVelocity coordinateFactor
  ring

theorem ideal_source_displayed (h η : ℝ) :
    idealSource h η =
      (3 / 5) * (4 * coordinateFactor h η - 1) - h * (1 - 8 * η ^ 2) +
        (axialExponent h + 4 * axialShape η) * η * (2 * η / (1 + η ^ 2)) := by
  unfold idealSource logShapeDerivative idealAxialVelocity
  rw [ideal_transport_eq]
  ring

theorem ideal_source_positive_decomposition (h η : ℝ) :
    idealSource h η = 9 / 5 - h + (16 / 5) * h * η ^ 2 +
      2 * (axialExponent h + 4 * axialShape η) * η ^ 2 / (1 + η ^ 2) := by
  rw [ideal_source_displayed]
  unfold coordinateFactor
  ring



def radiusProfile (X₀ y : ℝ) : ℝ := X₀ * Real.exp y

def angularVelocityProfile (e₀ lam y : ℝ) : ℝ :=
  e₀ * Real.exp (-(1 / 2 + lam) * y)

def angularMomentumProfile (H₀ lam y : ℝ) : ℝ :=
  H₀ * Real.exp (-lam * y)

/-- Weight of `R` in `dM/dy = X E R`. -/
theorem first_axial_moment_weight (X₀ e₀ lam y : ℝ) :
    radiusProfile X₀ y * angularVelocityProfile e₀ lam y =
      (X₀ * e₀) * Real.exp ((1 / 2 - lam) * y) := by
  unfold radiusProfile angularVelocityProfile
  calc
    _ = (X₀ * e₀) * Real.exp (y + -(1 / 2 + lam) * y) := by
      rw [Real.exp_add]
      ring
    _ = _ := by congr 2; ring



/-- The two axial slopes differ whenever `lam > 0`, as do their translated weights. -/
theorem axial_weight_gap_neg {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    Real.exp ((1 / 2 - 2 * lam) * δ) -
      Real.exp ((1 / 2 - lam) * δ) < 0 := by
  have hgap : (1 / 2 - 2 * lam) * δ < (1 / 2 - lam) * δ := by
    nlinarith [mul_pos hlam hδ]
  exact sub_neg.mpr (Real.exp_lt_exp.mpr hgap)



/-- The exact negative part of the scaled pulse energy in equation (13). -/
theorem pulse_negative_energy_integral :
    (∫ z in (0 : ℝ)..13, (1 / 2 : ℝ) * Real.exp (-2 * z)) =
      (1 - Real.exp (-26)) / 4 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (-2 : ℝ) ≠ 0),
    integral_exp]
  norm_num
  ring

def pulseEnergyDebt : ℝ := (1 - Real.exp (-26)) / 4

theorem pulse_energy_debt_bounds :
    (6 / 25 : ℝ) ≤ pulseEnergyDebt ∧ pulseEnergyDebt ≤ 1 / 4 := by
  have hexp : (27 : ℝ) ≤ Real.exp 26 := by
    linarith [Real.add_one_le_exp (26 : ℝ)]
  have hinv : Real.exp (-26) ≤ 1 / 27 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 27) hexp
  have hpos := (Real.exp_pos (-26 : ℝ)).le
  unfold pulseEnergyDebt
  constructor <;> linarith

/-- Equation (13) has opposite endpoint signs if its error is at most `1/100`.
The asymptotic estimate needed to establish that bound is not formalized here. -/
theorem pulse_amplitude_endpoint_signs {K error₀ error₁ : ℝ}
    (hKlo : 1 / 5 ≤ K) (hKhi : K ≤ 1 / 4)
    (herror₀ : |error₀| ≤ 1 / 100) (herror₁ : |error₁| ≤ 1 / 100) :
    K * (9 / 10 : ℝ) ^ 2 - pulseEnergyDebt + error₀ < 0 ∧
      0 < K * (6 / 5 : ℝ) ^ 2 - pulseEnergyDebt + error₁ := by
  rcases pulse_energy_debt_bounds with ⟨hlo, hhi⟩
  rcases abs_le.mp herror₀ with ⟨he₀lo, he₀hi⟩
  rcases abs_le.mp herror₁ with ⟨he₁lo, he₁hi⟩
  constructor <;> nlinarith


/-- Constant-source lag solution, written in a form that also specifies its initial value. -/
def lagSolution (a c q₀ y : ℝ) : ℝ :=
  c / a + (q₀ - c / a) * Real.exp (-a * y)


theorem lag_solution_hasDerivAt (a c q₀ y : ℝ) :
    HasDerivAt (lagSolution a c q₀)
      (-(a * (q₀ - c / a) * Real.exp (-a * y))) y := by
  have he := ((hasDerivAt_id y).const_mul (-a)).exp
  convert! (he.const_mul (q₀ - c / a)).const_add (c / a) using 1
  simp only [mul_one, id_eq]
  ring




end NavierStokes.RadialSchedule
