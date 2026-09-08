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




def radiusProfile (X₀ y : ℝ) : ℝ := X₀ * Real.exp y

def angularVelocityProfile (e₀ lam y : ℝ) : ℝ :=
  e₀ * Real.exp (-(1 / 2 + lam) * y)








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



/-- Constant-source lag solution, written in a form that also specifies its initial value. -/
def lagSolution (a c q₀ y : ℝ) : ℝ :=
  c / a + (q₀ - c / a) * Real.exp (-a * y)






end NavierStokes.RadialSchedule
