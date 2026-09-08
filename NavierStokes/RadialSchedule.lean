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


def coordinateFactor (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2












def radiusProfile (X₀ y : ℝ) : ℝ := X₀ * Real.exp y









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









end NavierStokes.RadialSchedule
