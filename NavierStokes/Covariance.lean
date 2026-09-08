import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two signed covariance slots

The finite-dimensional algebra underlying Lemma 8.7 and equation (29) of the
candidate manuscript. In the orthonormal `(N,K)` coordinates, the two normalized
columns are `(-a,-b)` and `(-a,b)`, with positive column scales. A target `(-m,t)`
lies strictly between them precisely when `|a*t| < b*m`.

The actual integrated columns in the manuscript include approximation errors.
This file does not identify those columns with the exact model, or prove the
Gaussian, parameter-derivative, or flat-edge estimates.
-/

noncomputable section

namespace NavierStokes.Covariance

open Matrix

/-- The two columns, with their individual positive size factors. -/
def signedMatrix (a b scaleMinus scalePlus : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-a * scaleMinus, -a * scalePlus;
     -b * scaleMinus,  b * scalePlus]

/-- The stress target in normal and transverse coordinates. -/
def target (m t : ℝ) : Fin 2 → ℝ := ![-m, t]

/-- Explicit squared amplitudes for the two signed slots. -/
def coefficients (a b scaleMinus scalePlus m t : ℝ) : Fin 2 → ℝ :=
  ![(b * m - a * t) / (2 * a * b * scaleMinus),
    (b * m + a * t) / (2 * a * b * scalePlus)]

theorem determinant_formula (a b scaleMinus scalePlus : ℝ) :
    (signedMatrix a b scaleMinus scalePlus).det =
      -(2 * a * b * scaleMinus * scalePlus) := by
  simp [signedMatrix, Matrix.det_fin_two]
  ring

theorem determinant_neg {a b scaleMinus scalePlus : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (signedMatrix a b scaleMinus scalePlus).det < 0 := by
  rw [determinant_formula]
  have : 0 < 2 * a * b * scaleMinus * scalePlus := by positivity
  linarith

theorem determinant_ne_zero {a b scaleMinus scalePlus : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (signedMatrix a b scaleMinus scalePlus).det ≠ 0 :=
  ne_of_lt (determinant_neg ha hb hMinus hPlus)

/-- The explicit coefficients solve the two covariance equations exactly. -/
theorem reconstruct {a b scaleMinus scalePlus : ℝ} (m t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hMinus : scaleMinus ≠ 0) (hPlus : scalePlus ≠ 0) :
    (signedMatrix a b scaleMinus scalePlus).mulVec
      (coefficients a b scaleMinus scalePlus m t) = target m t := by
  ext i
  fin_cases i <;>
    simp [signedMatrix, coefficients, target, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- Thus the explicit formula is the matrix inverse applied to the stress. -/
theorem inverse_formula {a b scaleMinus scalePlus : ℝ} (m t : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (signedMatrix a b scaleMinus scalePlus)⁻¹.mulVec (target m t) =
      coefficients a b scaleMinus scalePlus m t := by
  have hdet : IsUnit (signedMatrix a b scaleMinus scalePlus).det :=
    isUnit_iff_ne_zero.mpr (determinant_ne_zero ha hb hMinus hPlus)
  rw [← reconstruct m t (ne_of_gt ha) (ne_of_gt hb)
    (ne_of_gt hMinus) (ne_of_gt hPlus)]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem solution_unique {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (y : Fin 2 → ℝ)
    (hy : (signedMatrix a b scaleMinus scalePlus).mulVec y = target m t) :
    y = coefficients a b scaleMinus scalePlus m t := by
  have hdet : IsUnit (signedMatrix a b scaleMinus scalePlus).det :=
    isUnit_iff_ne_zero.mpr (determinant_ne_zero ha hb hMinus hPlus)
  calc
    y = (signedMatrix a b scaleMinus scalePlus)⁻¹.mulVec
        ((signedMatrix a b scaleMinus scalePlus).mulVec y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = (signedMatrix a b scaleMinus scalePlus)⁻¹.mulVec (target m t) := by rw [hy]
    _ = coefficients a b scaleMinus scalePlus m t :=
      inverse_formula m t ha hb hMinus hPlus

/-- A strict geometric cone condition makes both squared amplitudes positive. -/
theorem coefficients_pos {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    ∀ i, 0 < coefficients a b scaleMinus scalePlus m t i := by
  have hc := abs_lt.mp hcone
  intro i
  fin_cases i
  · change 0 < (b * m - a * t) / (2 * a * b * scaleMinus)
    exact div_pos (by linarith) (by positivity)
  · change 0 < (b * m + a * t) / (2 * a * b * scalePlus)
    exact div_pos (by linarith) (by positivity)


/-- The primary velocity amplitudes are positive square roots of the solve. -/
def amplitudes (a b scaleMinus scalePlus m t : ℝ) : Fin 2 → ℝ :=
  fun i => Real.sqrt (coefficients a b scaleMinus scalePlus m t i)

theorem amplitudes_pos {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    ∀ i, 0 < amplitudes a b scaleMinus scalePlus m t i := by
  intro i
  exact Real.sqrt_pos.mpr (coefficients_pos ha hb hMinus hPlus hcone i)

theorem amplitudes_sq {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    (fun i => (amplitudes a b scaleMinus scalePlus m t i) ^ 2) =
      coefficients a b scaleMinus scalePlus m t := by
  funext i
  exact Real.sq_sqrt (le_of_lt (coefficients_pos ha hb hMinus hPlus hcone i))



/-- Positive normal magnitude in the manuscript's signed directions. -/
def normalMagnitude (c u : ℝ) : ℝ := -c * Real.sqrt (1 + u ^ 2)

theorem normalMagnitude_pos {c u : ℝ} (hc : c < 0) : 0 < normalMagnitude c u := by
  unfold normalMagnitude
  exact mul_pos (neg_pos.mpr hc) (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg u]))

/-- The manuscript's strict ratio choice for `u_*` implies the exact cone test. -/
theorem cone_of_ratio {c u m t : ℝ} (hm : 0 < m)
    (hratio : |c * t / m| < u / Real.sqrt (1 + u ^ 2)) :
    |normalMagnitude c u * t| < u * m := by
  have hs : 0 < Real.sqrt (1 + u ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg u])
  have hr : |c * t| / m < u / Real.sqrt (1 + u ^ 2) := by
    simpa only [abs_div, abs_of_pos hm] using hratio
  have hcross : |c * t| * Real.sqrt (1 + u ^ 2) < u * m :=
    (div_lt_div_iff₀ hm hs).mp hr
  calc
    |normalMagnitude c u * t| = |c * t| * Real.sqrt (1 + u ^ 2) := by
      rw [show normalMagnitude c u * t = -(c * t) * Real.sqrt (1 + u ^ 2) by
        unfold normalMagnitude
        ring]
      rw [abs_mul, abs_neg, abs_of_pos hs]
    _ < u * m := hcross


end NavierStokes.Covariance
