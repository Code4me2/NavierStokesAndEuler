import NavierStokes.SpatialCurl
import NavierStokes.ResidualStability
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NavierStokes.JetBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real oscillatory curl realization

The potential and curl below use actual Euclidean spatial derivatives. The
oscillatory carrier is kept separate from the stripped remainder coefficient.
-/

noncomputable section

namespace NavierStokes.OscillatoryCurl

open ProblemStatement Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace


/-- Cross product on the same Euclidean space as the PDE target, as a bounded
bilinear map. -/
def crossLinear : Space →L[ℝ] Space →L[ℝ] Space :=
  (EuclideanSpace.proj 1).smulRight ((EuclideanSpace.proj 2).smulRight (coordinateVector 0)) -
  (EuclideanSpace.proj 2).smulRight ((EuclideanSpace.proj 1).smulRight (coordinateVector 0)) +
  (EuclideanSpace.proj 2).smulRight ((EuclideanSpace.proj 0).smulRight (coordinateVector 1)) -
  (EuclideanSpace.proj 0).smulRight ((EuclideanSpace.proj 2).smulRight (coordinateVector 1)) +
  (EuclideanSpace.proj 0).smulRight ((EuclideanSpace.proj 1).smulRight (coordinateVector 2)) -
  (EuclideanSpace.proj 1).smulRight ((EuclideanSpace.proj 0).smulRight (coordinateVector 2))

def cross (u v : Space) : Space := crossLinear u v


theorem cross_apply (u v : Space) :
    cross u v =
      u 1 • (v 2 • coordinateVector 0) - u 2 • (v 1 • coordinateVector 0) +
      u 2 • (v 0 • coordinateVector 1) - u 0 • (v 2 • coordinateVector 1) +
      u 0 • (v 1 • coordinateVector 2) - u 1 • (v 0 • coordinateVector 2) := rfl

@[simp] theorem cross_zero (u v : Space) : (cross u v) 0 = u 1 * v 2 - u 2 * v 1 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_one (u v : Space) : (cross u v) 1 = u 2 * v 0 - u 0 * v 2 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_two (u v : Space) : (cross u v) 2 = u 0 * v 1 - u 1 * v 0 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_smul_left (c : ℝ) (u v : Space) :
    cross (c • u) v = c • cross u v := by simp [cross]

@[simp] theorem cross_smul_right (c : ℝ) (u v : Space) :
    cross u (c • v) = c • cross u v := by simp [cross]

@[simp] theorem cross_zero_right (u : Space) : cross u 0 = 0 := by simp [cross]

theorem inner_coordinates (u v : Space) :
    ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]





/-- The actual Euclidean gradient map applied to a scalar derivative. -/
def gradientLinear : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).smulRight (coordinateVector i)

@[simp] theorem gradientLinear_apply (L : Space →L[ℝ] ℝ) (i : Fin 3) :
    (gradientLinear L) i = L (coordinateVector i) := by
  fin_cases i <;> simp [gradientLinear, Fin.sum_univ_three, coordinateVector]

theorem curlLinear_smulRight (L : Space →L[ℝ] ℝ) (a : Space) :
    SpatialCurl.curlLinear (L.smulRight a) = cross (gradientLinear L) a := by
  ext i
  fin_cases i <;> simp






























end NavierStokes.OscillatoryCurl
