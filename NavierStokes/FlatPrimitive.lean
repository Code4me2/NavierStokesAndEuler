import NavierStokes.FlatCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual primitives of exponential-flat edges

This file studies the integral of `exp (-c / u²) * u⁻ʲ * b u` from zero.
The integrand uses the smooth zero extension from `FlatCutoff`.

In particular, smoothness of the primitive is distinct from smoothness of its
quotient by an exponentially small factor. The statements below keep those
obligations separate.
-/

noncomputable section

open Filter Topology Set MeasureTheory Polynomial
open scoped ContDiff
open NavierStokes.FlatCutoff

namespace NavierStokes.FlatPrimitive

def integrand (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  (edge c x / x ^ j) * b x

def primitive (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, integrand c j b u

/-- The expected factor `exp(-c/x²) x^(3-j)`, written without truncated
natural subtraction and defined smoothly at zero. -/
def scale (c : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (edge c x / x ^ j) * x ^ 3


theorem integrand_continuous {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) : Continuous (integrand c j b) :=
  ((edge_div_pow_contDiff hc j : ContDiff ℝ ∞ _).continuous).mul hb

theorem primitive_hasDerivAt {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) (x : ℝ) :
    HasDerivAt (primitive c j b) (integrand c j b x) x := by
  have hf := integrand_continuous hc j hb
  exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt



@[simp] theorem primitive_zero (c : ℝ) (j : ℕ) (b : ℝ → ℝ) :
    primitive c j b 0 = 0 := by simp [primitive]

theorem primitive_of_nonpos (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : x ≤ 0) : primitive c j b x = 0 := by
  unfold primitive
  calc
    (∫ u in (0 : ℝ)..x, integrand c j b u) = ∫ _u in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : u ≤ 0 := (uIcc_of_ge hx ▸ hu).2
      simp [integrand, edge_of_nonpos c hu0]
    _ = 0 := intervalIntegral.integral_zero




theorem edge_hasDerivAt {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (edge c) (2 * c * edge c x / x ^ 3) x := by
  have h := polynomialEdge_hasDerivAt hc (1 : ℝ[X]) x
  rw [polynomialEdge_one] at h
  convert! h using 1
  simp [polynomialEdge, derivativePolynomial, div_eq_mul_inv, inv_pow]
  ring


@[simp] theorem scale_zero (c : ℝ) (j : ℕ) : scale c j 0 = 0 := by simp [scale]

theorem scale_hasDerivAt {c : ℝ} (hc : 0 < c) (j : ℕ) (x : ℝ) :
    HasDerivAt (scale c j)
      ((edge c x / x ^ j) * (2 * c + (3 - (j : ℝ)) * x ^ 2)) x := by
  unfold scale
  by_cases hx : x = 0
  · subst x
    have h := (((edge_div_pow_contDiff hc j : ContDiff ℝ ∞ _).differentiable
      (by simp) 0).hasDerivAt).fun_mul ((hasDerivAt_id (0 : ℝ)).fun_pow 3)
    simpa [scale] using h
  · have h := (((edge_hasDerivAt hc x).fun_div ((hasDerivAt_id x).fun_pow j)
      (pow_ne_zero j hx)).fun_mul ((hasDerivAt_id x).fun_pow 3))
    simp only [id_eq] at h
    convert! h using 1
    cases j with
    | zero => simp; field_simp
    | succ j =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, mul_one, pow_succ]
      field_simp; ring













end NavierStokes.FlatPrimitive
