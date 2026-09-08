import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebra of the manuscript coordinates

This module checks the algebra in equations (3)--(5). It does not construct a
smooth inverse coordinate chart, a Navier--Stokes solution, or a singularity.
`q ^ b` below denotes the real power, while `η ^ 2` is a natural power.
-/

namespace NavierStokes.CoordinateAlgebra

noncomputable section

def A (h : ℝ) : ℝ := 1 / 2 + h
def D (h : ℝ) : ℝ := 1 / 2 - h
def d (η : ℝ) : ℝ := 1 - η ^ 2
def L (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2




/-- Eliminating `η` from `z = q^D η` gives the implicit formula for `τ`. -/
theorem forward_coordinate_identity {q : ℝ} (hq : 0 < q) (h η : ℝ) :
    q * d η = q - (q ^ D h * η) ^ 2 * q ^ (2 * h) := by
  have hp : (q ^ D h) ^ 2 * q ^ (2 * h) = q := by
    rw [← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq]
    have he : D h * (2 : ℕ) + 2 * h = (1 : ℝ) := by unfold D; ring
    rw [he, Real.rpow_one]
  calc
    q * d η = q - q * η ^ 2 := by unfold d; ring
    _ = q - ((q ^ D h) ^ 2 * q ^ (2 * h)) * η ^ 2 := by rw [hp]
    _ = _ := by ring

theorem D_pos {h : ℝ} (hh : h < 1 / 2) : 0 < D h := by
  unfold D
  linarith

theorem d_pos {η : ℝ} (hη : η ^ 2 < 1) : 0 < d η := by
  unfold d
  linarith

/-- The explicit smallness condition needed for the manuscript's `L > 0`. -/
theorem L_pos {h η : ℝ} (hh₀ : 0 ≤ h) (hh : h < 1 / 2)
    (hη : η ^ 2 ≤ 1) : 0 < L h η := by
  unfold L
  nlinarith [mul_nonneg hh₀ (sub_nonneg.mpr hη)]

/-- Determinant of the forward coordinate Jacobian for
`τ = q (1-η²)` and `z = q^D η`. The derivative of `q^D` is
written as `D * (q^D/q)` on the positive half-line. -/
theorem jacobian_det {q : ℝ} (hq : q ≠ 0) (h η : ℝ) :
    d η * q ^ D h - (-2 * q * η) * (D h * η * (q ^ D h / q)) =
      q ^ D h * L h η := by
  field_simp
  unfold d D L
  ring


/-- The inverse Jacobian acting on `(τ',z')`, first component. -/
def inverseQ (q h η τ' z' : ℝ) : ℝ :=
  (τ' + 2 * q * η * z' / q ^ D h) / L h η

/-- The inverse Jacobian acting on `(τ',z')`, second component. -/
def inverseEta (q h η τ' z' : ℝ) : ℝ :=
  (d η * z' / q ^ D h - D h * η * τ' / q) / L h η



theorem inverseQ_recover {q h η : ℝ} (hq : 0 < q) (hL : L h η ≠ 0)
    (q' η' : ℝ) :
    inverseQ q h η (d η * q' - 2 * q * η * η')
      (D h * η * (q ^ D h / q) * q' + q ^ D h * η') = q' := by
  have hpow : q ^ D h ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  unfold inverseQ
  field_simp
  unfold d D L
  ring

theorem inverseEta_recover {q h η : ℝ} (hq : 0 < q) (hL : L h η ≠ 0)
    (q' η' : ℝ) :
    inverseEta q h η (d η * q' - 2 * q * η * η')
      (D h * η * (q ^ D h / q) * q' + q ^ D h * η') = η' := by
  have hpow : q ^ D h ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  unfold inverseEta
  field_simp
  unfold d D L
  ring


def qTime (h η : ℝ) : ℝ := -1 / L h η
def etaTime (q h η : ℝ) : ℝ := D h * η / (q * L h η)
def xTime (q h η X : ℝ) : ℝ := X / (q * L h η)
def qAxial (q h η : ℝ) : ℝ := 2 * η * q / (q ^ D h * L h η)
def etaAxial (q h η : ℝ) : ℝ := d η / (q ^ D h * L h η)
def xAxial (q h η X : ℝ) : ℝ := -2 * η * X / (q ^ D h * L h η)



theorem qAxial_rpow {q : ℝ} (hq : 0 < q) (h η : ℝ) :
    qAxial q h η = 2 * η * q ^ (1 - D h) / L h η := by
  rw [Real.rpow_sub hq, Real.rpow_one]
  unfold qAxial
  ring



/-- The `T_b` coefficient in equation (4), at a profile jet `(F,FX,Fη)`. -/
def timeCoeff (b h η X F FX Fη : ℝ) : ℝ :=
  (-b * F + D h * η * Fη + X * FX) / L h η

/-- The `Z_b` coefficient in equation (4), at a profile jet `(F,FX,Fη)`. -/
def axialCoeff (b h η X F FX Fη : ℝ) : ℝ :=
  (2 * η * b * F + d η * Fη - 2 * η * X * FX) / L h η

/-- Product/chain-rule expression for the time derivative of `q^b F(X,η)`.
The theorem checks its exact coefficient and power of `q`; analytic
derivative hypotheses are separate from this algebraic identity. -/
theorem time_chain_coefficient {q : ℝ} (hq : 0 < q)
    (b h η X F FX Fη : ℝ) :
    b * q ^ (b - 1) * qTime h η * F +
        q ^ b * (FX * xTime q h η X + Fη * etaTime q h η) =
      q ^ (b - 1) * timeCoeff b h η X F FX Fη := by
  rw [Real.rpow_sub_one hq.ne']
  unfold qTime xTime etaTime timeCoeff
  ring

/-- Product/chain-rule expression for the axial derivative of `q^b F(X,η)`. -/
theorem axial_chain_coefficient {q : ℝ} (hq : 0 < q)
    (b h η X F FX Fη : ℝ) :
    b * q ^ (b - 1) * qAxial q h η * F +
        q ^ b * (FX * xAxial q h η X + Fη * etaAxial q h η) =
      q ^ (b - D h) * axialCoeff b h η X F FX Fη := by
  by_cases hL : L h η = 0
  · simp [qAxial, xAxial, etaAxial, axialCoeff, hL]
  have hpow : q ^ D h ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  rw [Real.rpow_sub_one hq.ne', Real.rpow_sub hq]
  unfold qAxial xAxial etaAxial axialCoeff
  field_simp [hq.ne', hpow, hL]; ring

/-- Algebra behind the incompressibility formula (5). The two hypotheses
are the primitive identities `(X Ubar)_X = U` and its `η` derivative. -/
theorem incompressibility_numerator
    (h η X U UX Uη Ubar UbarX Ubarη UbarηX : ℝ)
    (hU : Ubar + X * UbarX = U) (hUη : Ubarη + X * UbarηX = Uη) :
    2 * η * U - 2 * D h * η * Ubar - d η * Ubarη +
        X * (2 * η * UX - 2 * D h * η * UbarX - d η * UbarηX) =
      2 * A h * η * U - d η * Uη + 2 * η * X * UX := by
  calc
    _ = 2 * η * U - 2 * D h * η * (Ubar + X * UbarX) -
        d η * (Ubarη + X * UbarηX) + 2 * η * X * UX := by ring
    _ = _ := by rw [hU, hUη]; unfold A D; ring


end

end NavierStokes.CoordinateAlgebra
