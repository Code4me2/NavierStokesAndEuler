import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Tangent projection and pressure cancellation

This file checks the algebra in manuscript Lemma 8.4, equation (27), and
Appendix A.3.  The vectors are in an arbitrary real inner-product space;
`Kt` denotes the value of the matrix `K` on `t`.  No assertion about the
existence, size, or differentiated estimates of a pulse is made here.
-/

namespace NavierStokes.TangentProjection

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped InnerProductSpace

/-- Orthogonal projection onto the hyperplane perpendicular to `n`, for `n ≠ 0`. -/
def tangentProj (n f : E) : E := f - (⟪n, f⟫_ℝ / ⟪n, n⟫_ℝ) • n

/-- The right-hand side of equation (27), with the viscous coefficient `δ`. -/
def projectedRhs (n n' t Kt f : E) (δ : ℝ) : E :=
  -Kt + ((⟪n, Kt⟫_ℝ - ⟪n', t⟫_ℝ) / ⟪n, n⟫_ℝ) • n - δ • t - tangentProj n f

/-- The real coefficient of the normal vector canceled by pressure. -/
def pressureCoefficient (n n' t Kt f : E) : ℝ :=
  (⟪n, Kt⟫_ℝ - ⟪n', t⟫_ℝ + ⟪n, f⟫_ℝ) / ⟪n, n⟫_ℝ

theorem tangentProj_normal {n : E} (hn : n ≠ 0) (f : E) :
    ⟪n, tangentProj n f⟫_ℝ = 0 := by
  have hn2 : ⟪n, n⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hn
  simp only [tangentProj, inner_sub_right, inner_smul_right]
  rw [div_mul_cancel₀ _ hn2, sub_self]

theorem tangentProj_of_tangent (n f : E) (hf : ⟪n, f⟫_ℝ = 0) :
    tangentProj n f = f := by
  simp [tangentProj, hf]


/-- The full normal identity includes the damping of an existing tangency defect. -/
theorem normal_projectedRhs {n : E} (hn : n ≠ 0) (n' t Kt f : E) (δ : ℝ) :
    ⟪n, projectedRhs n n' t Kt f δ⟫_ℝ = -⟪n', t⟫_ℝ - δ * ⟪n, t⟫_ℝ := by
  have hn2 : ⟪n, n⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hn
  simp only [projectedRhs, inner_sub_right, inner_add_right, inner_neg_right,
    inner_smul_right, tangentProj_normal hn, div_mul_cancel₀ _ hn2]
  ring

/-- In particular the projected vector field has the normal derivative required by tangency. -/
theorem normal_projectedRhs_of_tangent {n : E} (hn : n ≠ 0)
    (n' t Kt f : E) (δ : ℝ) (ht : ⟪n, t⟫_ℝ = 0) :
    ⟪n, projectedRhs n n' t Kt f δ⟫_ℝ = -⟪n', t⟫_ℝ := by
  rw [normal_projectedRhs hn, ht]
  ring

/-- Rearranging the projected equation leaves exactly this normal vector. -/
theorem projected_balance (n n' t Kt f : E) (δ : ℝ) :
    projectedRhs n n' t Kt f δ + Kt + δ • t + f =
      pressureCoefficient n n' t Kt f • n := by
  unfold projectedRhs tangentProj pressureCoefficient
  module

/-- A pressure force with the opposite normal coefficient cancels the residual exactly. -/
theorem pressure_cancellation (n n' t Kt f : E) (δ : ℝ) :
    projectedRhs n n' t Kt f δ + Kt + δ • t -
      pressureCoefficient n n' t Kt f • n = -f := by
  have h := projected_balance n n' t Kt f δ
  rw [← h]
  abel


/-- Along any differentiable solution of (27), the tangency defect solves `h' = -δ h`. -/
theorem tangency_defect_derivative {n t : ℝ → E} {n' : E} {x : ℝ}
    {Kt f : E} {δ : ℝ} (hn0 : n x ≠ 0)
    (hn : HasDerivAt n n' x)
    (ht : HasDerivAt t (projectedRhs (n x) n' (t x) Kt f δ) x) :
    HasDerivAt (fun y => ⟪n y, t y⟫_ℝ) (-δ * ⟪n x, t x⟫_ℝ) x := by
  convert! hn.inner ℝ ht using 1
  rw [normal_projectedRhs hn0]
  ring

/-- Integrating-factor proof of zero-data uniqueness for the scalar defect equation.
The primitive `D` is explicit, so no existence assumption is hidden in this statement. -/
theorem scalar_defect_zero (h δ D : ℝ → ℝ)
    (hD : ∀ x, HasDerivAt D (δ x) x)
    (hh : ∀ x, HasDerivAt h (-δ x * h x) x)
    (x₀ : ℝ) (hzero : h x₀ = 0) : ∀ x, h x = 0 := by
  have hp : ∀ x, HasDerivAt (fun y => Real.exp (D y) * h y) 0 x := by
    intro x
    convert! (hD x).exp.mul (hh x) using 1
    ring
  intro x
  have heq := is_const_of_deriv_eq_zero (fun y => (hp y).differentiableAt)
    (fun y => (hp y).deriv) x x₀
  have hz : Real.exp (D x) * h x = 0 := by
    simpa only [hzero, mul_zero] using heq
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)




/-- With `c = k j' ≠ 0`, the manuscript's pressure is `i A / c`.
Multiplication by the Fourier gradient `i c` yields `-A`, fixing the sign. -/
theorem complex_pressure_sign (A c : ℂ) (hc : c ≠ 0) :
    (Complex.I * c) * (Complex.I * A / c) = -A := by
  calc
    (Complex.I * c) * (Complex.I * A / c) =
        (Complex.I * Complex.I) * A * (c / c) := by ring
    _ = -A := by rw [Complex.I_mul_I, div_self hc]; ring

end

end NavierStokes.TangentProjection
