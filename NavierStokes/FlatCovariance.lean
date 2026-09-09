import NavierStokes.FlatCutoff
import NavierStokes.SmoothCovariance
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Covariance amplitudes across an exponential-flat edge

The normalized matrix and target are actual smooth functions with an explicit
strict cone. Columns are then multiplied by `edge κᵢ`, and the target by
`edge σ`. Exact inverse and square-root identities exhibit a positive remaining
exponential whenever `κᵢ < σ`; in particular the squared-factor convention
`κᵢ = 2 λᵢ` is covered by `λᵢ < σ / 2`.

The coefficient quotients are proved smooth from these formulas. Their
smoothness across the singular matrix at the edge is not assumed.
-/

noncomputable section

namespace NavierStokes.FlatCovariance

open Matrix Set
open SmoothCovariance (Mat2 Vec2)
open FlatCutoff (edge)
open scoped ContDiff Topology

/-- Multiplication of column `j` by its scalar factor `c j`. -/
def columns (G : Mat2) (c : Vec2) : Mat2 := fun i j => c j * G i j

def scaledTarget (r : ℝ) (T : Vec2) : Vec2 := fun i => r * T i

/-- The actual edge-degenerate covariance matrix. -/
def edgeMatrix (κ : Vec2) (G : ℝ → Mat2) (x : ℝ) : Mat2 :=
  columns (G x) (fun j => edge (κ j) x)

def edgeTarget (σ : ℝ) (T : ℝ → Vec2) (x : ℝ) : Vec2 :=
  scaledTarget (edge σ x) (T x)

/-- The actual matrix-inverse solve, also defined at the zero edge. -/
def inverseCoefficients (σ : ℝ) (κ : Vec2) (G : ℝ → Mat2) (T : ℝ → Vec2)
    (x : ℝ) : Vec2 :=
  (edgeMatrix κ G x)⁻¹.mulVec (edgeTarget σ T x)

def primaryAmplitude (σ : ℝ) (κ : Vec2) (G : ℝ → Mat2) (T : ℝ → Vec2)
    (x : ℝ) : Vec2 :=
  fun i => Real.sqrt (inverseCoefficients σ κ G T x i)

/-- The signed covariance update divides by the fixed positive primary. -/
def signedAmplitude (σ τ : ℝ) (κ : Vec2) (G : ℝ → Mat2)
    (T R : ℝ → Vec2) (x : ℝ) : Vec2 :=
  fun i => inverseCoefficients τ κ G R x i / (2 * primaryAmplitude σ κ G T x i)





theorem determinant_columns (G : Mat2) (c : Vec2) :
    (columns G c).det = c 0 * c 1 * G.det := by
  simp only [Matrix.det_fin_two, columns]
  ring

theorem columns_det_ne_zero {G : Mat2} {c : Vec2}
    (hG : G.det ≠ 0) (hc : ∀ i, c i ≠ 0) : (columns G c).det ≠ 0 := by
  rw [determinant_columns]
  exact mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) hG

/-- Cramer's formula records the exact effect of individual column factors. -/
theorem weights_columns (G : Mat2) (c : Vec2) (T : Vec2) (r : ℝ)
    (hG : G.det ≠ 0) (hc : ∀ i, c i ≠ 0) (i : Fin 2) :
    SmoothCovariance.weights (columns G c) (scaledTarget r T) i =
      (r / c i) * SmoothCovariance.weights G T i := by
  have hc0 := hc 0
  have hc1 := hc 1
  fin_cases i <;>
    simp only [SmoothCovariance.weights, determinant_columns,
      SmoothCovariance.cramerNumerator, columns, scaledTarget,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] <;>
    field_simp

theorem edgeMatrix_det_ne_zero {κ : Vec2} {G : ℝ → Mat2} {x : ℝ}
    (hG : (G x).det ≠ 0) (hx : 0 < x) : (edgeMatrix κ G x).det ≠ 0 :=
  columns_det_ne_zero hG (fun i => ne_of_gt (FlatCutoff.edge_pos (κ i) hx))

theorem inverseCoefficients_of_nonpos (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) :
    inverseCoefficients σ κ G T x = 0 := by
  have ht : edgeTarget σ T x = 0 := by
    ext i
    simp [edgeTarget, scaledTarget, FlatCutoff.edge_of_nonpos σ hx]
  simp [inverseCoefficients, ht]

theorem primaryAmplitude_of_nonpos (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) (i : Fin 2) :
    primaryAmplitude σ κ G T x i = 0 := by
  simp [primaryAmplitude, inverseCoefficients_of_nonpos σ κ G T hx]


/-- Exact cancellation of the column exponential in the actual inverse.
This identity includes the edge and the full zero half-line. -/
theorem inverseCoefficients_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    inverseCoefficients σ κ G T x i =
      edge (σ - κ i) x * SmoothCovariance.weights (G x) (T x) i := by
  by_cases hx : x ≤ 0
  · simp [inverseCoefficients_of_nonpos σ κ G T hx,
      FlatCutoff.edge_of_nonpos (σ - κ i) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    have hs := SmoothCovariance.inverse_formula (edgeMatrix κ G x) (edgeTarget σ T x)
      (edgeMatrix_det_ne_zero hG hp)
    change ((edgeMatrix κ G x)⁻¹.mulVec (edgeTarget σ T x)) i = _
    rw [hs]
    dsimp only [edgeMatrix, edgeTarget]
    rw [weights_columns (G x) (fun j => edge (κ j) x) (T x) (edge σ x) hG
      (fun j => ne_of_gt (FlatCutoff.edge_pos (κ j) hp)) i]
    rw [congrFun (FlatCutoff.edge_div_edge σ (κ i)) x]





theorem inverseCoefficients_pos {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) (hx : 0 < x) (i : Fin 2) :
    0 < inverseCoefficients σ κ G T x i := by
  rw [inverseCoefficients_factor σ κ G T hcone.det_ne_zero i]
  exact mul_pos (FlatCutoff.edge_pos _ hx) (hcone.weights_pos i)

theorem primaryAmplitude_pos {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) (hx : 0 < x) (i : Fin 2) :
    0 < primaryAmplitude σ κ G T x i :=
  Real.sqrt_pos.mpr (inverseCoefficients_pos hcone hx i)

/-- The inverse still reconstructs its target at every real point, including
the zero half-line where the matrix itself is singular. -/
theorem inverse_reconstruct (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) :
    (edgeMatrix κ G x).mulVec (inverseCoefficients σ κ G T x) = edgeTarget σ T x := by
  by_cases hx : x ≤ 0
  · rw [inverseCoefficients_of_nonpos σ κ G T hx, Matrix.mulVec_zero]
    ext i
    simp [edgeTarget, scaledTarget, FlatCutoff.edge_of_nonpos σ hx]
  · have hp : 0 < x := lt_of_not_ge hx
    unfold inverseCoefficients
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (edgeMatrix_det_ne_zero hG hp)),
      Matrix.one_mulVec]


/-- Exact two-sided cross covariance of the primary and signed increment. -/
theorem signed_cross_reconstruct {σ τ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T R : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) :
    (edgeMatrix κ G x).mulVec
        (fun i => 2 * primaryAmplitude σ κ G T x i * signedAmplitude σ τ κ G T R x i) =
      edgeTarget τ R x := by
  have hcross :
      (fun i => 2 * primaryAmplitude σ κ G T x i * signedAmplitude σ τ κ G T R x i) =
        inverseCoefficients τ κ G R x := by
    funext i
    by_cases hx : x ≤ 0
    · simp [primaryAmplitude_of_nonpos σ κ G T hx,
        inverseCoefficients_of_nonpos τ κ G R hx]
    · have ha : primaryAmplitude σ κ G T x i ≠ 0 :=
        ne_of_gt (primaryAmplitude_pos hcone (lt_of_not_ge hx) i)
      unfold signedAmplitude
      field_simp
  rw [hcross]
  exact inverse_reconstruct τ κ G R hcone.det_ne_zero

section Smooth

variable {s : Set ℝ} {σ τ : ℝ} {κ : Vec2}
variable {G : ℝ → Mat2} {T R : ℝ → Vec2}












end Smooth



section GlobalFlatness

variable {σ τ : ℝ} {κ : Vec2} {G : ℝ → Mat2} {T R : ℝ → Vec2}





end GlobalFlatness

section ParameterFamilies

variable {E : Type*}





variable [NormedAddCommGroup E] [NormedSpace ℝ E]



end ParameterFamilies

end NavierStokes.FlatCovariance
