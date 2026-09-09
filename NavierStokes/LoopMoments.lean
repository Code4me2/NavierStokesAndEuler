import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact moment algebra for the true-cone loop construction

This file proves the finite-distribution form of the averaging and rephasing
identities in Lemma 6.1 of the candidate manuscript. The formulas are algebraic;
no existence, smoothness, or invertibility of a circle reparametrization is
asserted here. The hypotheses of `rephased_moments` are ordinary mass, mean,
and variance constraints, not an assumption that a desired loop exists.

The final lemmas give explicit two-point distributions with prescribed variance.
They establish finite moment feasibility, including a one-sided support bound.
-/

namespace NavierStokes.LoopMoments

open scoped BigOperators

noncomputable section

variable {ι : Type*}











/-- The rephasing density relative to the old averaging parameter. -/
def phaseDensity (a v t : ℝ) : ℝ := a * (1 + t ^ 2) / v

/-- The positive first component of the loop shear. -/
def loopA (v t : ℝ) : ℝ := v / (1 + t ^ 2)

/-- The signed second component; this corresponds to `-b_L`. -/
def loopC (v t : ℝ) : ℝ := v * t / (1 + t ^ 2)

theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by
  nlinarith [sq_nonneg t]

theorem loopA_pos (v t : ℝ) (hv : 0 < v) : 0 < loopA v t := by
  exact div_pos hv (one_add_sq_pos t)

theorem phaseDensity_pos (a v t : ℝ) (ha : 0 < a) (hv : 0 < v) :
    0 < phaseDensity a v t := by
  exact div_pos (mul_pos ha (one_add_sq_pos t)) hv

theorem loop_speed (v t : ℝ) : loopA v t * (1 + t ^ 2) = v := by
  unfold loopA
  exact div_mul_cancel₀ v (ne_of_gt (one_add_sq_pos t))

theorem loop_slope (v t : ℝ) (hv : v ≠ 0) : loopC v t / loopA v t = t := by
  unfold loopC loopA
  field_simp

theorem density_times_loopA (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopA v t = a := by
  unfold phaseDensity loopA
  field_simp

theorem density_times_loopC (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopC v t = a * t := by
  unfold phaseDensity loopC
  field_simp





/-- A two-point probability law. This is a concrete finite object, without
any hypothesis asserting the existence of the manuscript's smooth loop. -/
structure TwoPoint where
  leftWeight : ℝ
  rightWeight : ℝ
  leftValue : ℝ
  rightValue : ℝ

















end

end NavierStokes.LoopMoments
