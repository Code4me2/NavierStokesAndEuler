import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Foundations for the Euler construction

Elementary ingredients used everywhere later in the Euler development:

* `EulerGevrey` -- explicit numerical estimates for the factorial majorants
  behind the Gevrey bookkeeping (pure combinatorics on binomial coefficients).
* `EulerSmoothUniformLimit` -- smoothness of uniform limits of smooth families.
* `EulerPacketWeights` -- the geometric packet weights `weight ρ n` and their
  summation identities.
* `EulerCoerciveProjection` -- Lax-Milgram style solvability for coercive
  operators, on a complete space and on a closed subspace.
* `EulerInverseRegularity` -- regularity of the inverse produced by the previous
  namespace, including its projected variant.

This is part 1 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

/-!
Explicit numerical estimates for the factorial majorants used in the proposed
Euler construction. These lemmas prove combinatorial implications; they do not
assert the analytic estimates needed to apply the implications to Euler.
-/

namespace EulerGevrey

open Finset

/-- Every interior entry of the `n`th binomial row is at least `n`. -/
theorem le_choose_of_interior (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases hk1 : k = 1
      · simp [hk1]
      by_cases hkn' : k = n
      · subst k
        simp
      have hklt : k < n := by omega
      have hkp : 0 < k - 1 := by omega
      have hp := ih (k - 1) hkp (by omega)
      have hq := ih k hk hklt
      rw [Nat.choose_succ_left n k hk]
      omega

/-- The reciprocal binomial row has uniformly bounded sum, including order zero. -/
theorem sum_inv_choose_le_three (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) ≤ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hsum : ∑ k ∈ range n, (1 : ℝ) / ((n + 1).choose (k + 1) : ℝ)
          ≤ n * (1 / (n + 1) : ℝ) := by
        calc
          _ ≤ ∑ _k ∈ range n, (1 / (n + 1) : ℝ) := by
            apply sum_le_sum
            intro k hk
            apply one_div_le_one_div_of_le hn
            exact_mod_cast le_choose_of_interior (n + 1) (k + 1)
              (by omega) (by have := mem_range.mp hk; omega)
          _ = _ := by simp
      have hquot : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hn]
        linarith
      rw [sum_range_succ', sum_range_succ]
      norm_num only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one]
      linarith

/-- Adding nonnegative shifts to both lower factorial indices enlarges the binomial coefficient. -/
theorem choose_le_shifted (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    n.choose k ≤ (n + d₁ + d₂).choose (k + d₁) := by
  calc
    n.choose k = n.choose (n - k) := (Nat.choose_symm hkn).symm
    _ ≤ (n + d₁).choose (n - k) := Nat.choose_le_add n d₁ (n - k)
    _ = (n + d₁).choose (k + d₁) := by
      apply Nat.choose_symm_of_eq_add
      omega
    _ ≤ (n + d₁ + d₂).choose (k + d₁) :=
      Nat.choose_le_add (n + d₁) d₂ (k + d₁)

/-- The exact reciprocal-binomial comparison used in the shifted product estimate. -/
theorem choose_ratio_le_inv (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2
      ≤ 1 / (n.choose k : ℝ) := by
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hle : (n.choose k : ℝ) ≤ (n + d₁ + d₂).choose (k + d₁) := by
    exact_mod_cast choose_le_shifted n k d₁ d₂ hkn
  apply (div_le_div_iff₀ (sq_pos_of_pos (lt_of_lt_of_le hc hle)) hc).2
  nlinarith

/-- A term of the shifted factorial convolution gains the reciprocal binomial coefficient. -/
theorem shifted_factorial_kernel_le (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
        ((n - k + d₂).factorial : ℝ) ^ 2
      ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 / (n.choose k : ℝ) := by
  have hlarge : k + d₁ ≤ n + d₁ + d₂ := by omega
  have hsub : n + d₁ + d₂ - (k + d₁) = n - k + d₂ := by omega
  have hfac : ((n + d₁ + d₂).choose (k + d₁) : ℝ) *
      ((k + d₁).factorial : ℝ) * ((n - k + d₂).factorial : ℝ) =
      ((n + d₁ + d₂).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hlarge
    rw [hsub] at h
    exact_mod_cast h
  have hC : ((n + d₁ + d₂).choose (k + d₁) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hlarge
  calc
    _ = ((n + d₁ + d₂).factorial : ℝ) ^ 2 *
        ((n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2) := by
      rw [← hfac]
      field_simp
    _ ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 * (1 / (n.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left (choose_ratio_le_inv n k d₁ d₂ hkn) (sq_nonneg _)
    _ = _ := by ring

/-- The Gevrey-two factorial majorant with a nonnegative integer shift. -/
def majorant (R : ℝ) (d n : ℕ) : ℝ :=
  R ^ (n + d) * ((n + d).factorial : ℝ) ^ 2

theorem majorant_nonneg (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    0 ≤ majorant R d n := by
  unfold majorant
  positivity

/-- A single Leibniz term obeys the uniform shifted estimate. -/
theorem majorant_product_term (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
  have hexp : k + d₁ + (n - k + d₂) = n + d₁ + d₂ := by omega
  have hpow : R ^ (k + d₁) * R ^ (n - k + d₂) = R ^ (n + d₁ + d₂) := by
    rw [← pow_add, hexp]
  have h := mul_le_mul_of_nonneg_left (shifted_factorial_kernel_le n k d₁ d₂ hkn)
    (pow_nonneg hR (n + d₁ + d₂))
  unfold majorant
  simp only [← Nat.add_assoc]
  calc
    _ = (R ^ (k + d₁) * R ^ (n - k + d₂)) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by ring
    _ = R ^ (n + d₁ + d₂) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by rw [hpow]
    _ ≤ _ := by simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc] using h

/-- The product constant is exactly `3`, independently of order and both shifts. -/
theorem majorant_convolution (R : ℝ) (hR : 0 ≤ R) (n d₁ d₂ : ℕ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ 3 * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      exact majorant_product_term R hR n k d₁ d₂ (by have := mem_range.mp hk; omega)
    _ = majorant R (d₁ + d₂) n *
        ∑ k ∈ range (n + 1), (1 / (n.choose k : ℝ)) := by rw [mul_sum]
    _ ≤ majorant R (d₁ + d₂) n * 3 :=
      mul_le_mul_of_nonneg_left (sum_inv_choose_le_three n) (majorant_nonneg R hR _ _)
    _ = _ := by ring

/-- Discarding the reciprocal binomial gain is valid for each admissible split. -/
theorem majorant_product_term_le (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n := by
  have hc : (1 : ℝ) ≤ n.choose k := by
    exact_mod_cast Nat.choose_pos hkn
  have hi : (1 : ℝ) / (n.choose k : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hc
  exact (majorant_product_term R hR n k d₁ d₂ hkn).trans
    (mul_le_of_le_one_right (majorant_nonneg R hR _ _) hi)

/-- One spare factorial shift supplies a factor of at least `R`. -/
theorem majorant_shift_le (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    R * majorant R d n ≤ majorant R (d + 1) n := by
  have hf : (((n + d).factorial : ℕ) : ℝ) ≤ ((n + (d + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show n + d ≤ n + (d + 1) by omega)
  have hs : ((n + d).factorial : ℝ) ^ 2 ≤ ((n + (d + 1)).factorial : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (n + d).factorial by positivity]
  unfold majorant
  calc
    _ = R ^ (n + (d + 1)) * ((n + d).factorial : ℝ) ^ 2 := by
      rw [show n + (d + 1) = (n + d) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (pow_nonneg hR _)

/-- The geometric tail is bounded uniformly in the truncation length. -/
theorem geometric_tail_le_two_mul (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (n : ℕ) : ∑ k ∈ range n, q ^ (k + 1) ≤ 2 * q := by
  have hgeom : ∀ m : ℕ, ∑ k ∈ range m, q ^ k ≤ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [sum_range_succ']
        simp_rw [pow_succ]
        rw [← sum_mul]
        simp only [pow_zero]
        have hm := mul_le_mul_of_nonneg_right ih hq
        linarith
  simpa only [pow_succ, ← sum_mul] using mul_le_mul_of_nonneg_right (hgeom n) hq

/-- A coefficient of radius `Rc ≤ q R` has the geometric gain `q^k`. -/
theorem majorant_coefficient_term (R Rc q : ℝ)
    (hR : 0 ≤ R) (hRc : 0 ≤ Rc) (hq : 0 ≤ q) (hscale : Rc ≤ q * R)
    (n k d : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * Rc ^ k * (k.factorial : ℝ) ^ 2 * majorant R d (n - k)
      ≤ q ^ k * majorant R d n := by
  have hp : Rc ^ k ≤ (q * R) ^ k := pow_le_pow_left₀ hRc hscale k
  have hterm := majorant_product_term_le R hR n k 0 d hkn
  simp only [zero_add] at hterm
  have hscaled := mul_le_mul_of_nonneg_left hterm (pow_nonneg hq k)
  calc
    _ ≤ (n.choose k : ℝ) * (q * R) ^ k * (k.factorial : ℝ) ^ 2 *
        majorant R d (n - k) := by
      gcongr
      exact majorant_nonneg R hR d (n - k)
    _ = q ^ k * ((n.choose k : ℝ) * majorant R 0 k * majorant R d (n - k)) := by
      simp only [majorant, Nat.add_zero, mul_pow]
      ring
    _ ≤ _ := hscaled

/--
The triangular inverse rule with an explicit sufficient radius, uniform in the
derivative order and in the input shift. The recurrence sums the indices `1,…,n`
as `k + 1` for `k ∈ range n`. No sign assumption on `F` or `Z` is needed.
-/
theorem triangular_inverse_majorant (A Rc R : ℝ)
    (hA : 1 ≤ A) (hRc : 0 ≤ Rc) (hlarge : 2 * A * (Rc + 1) ≤ R)
    (d : ℕ) (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant R d n)
    (hZ : ∀ n, Z n ≤ A * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant R (d + 1) n := by
  have hA0 : 0 ≤ A := by linarith
  have hARc : 0 ≤ A * Rc := mul_nonneg hA0 hRc
  have hR : 0 < R := by nlinarith
  have hq0 : 0 ≤ Rc / R := div_nonneg hRc hR.le
  have hqhalf : Rc / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hR).2
    nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hRc]
  have hscale : Rc ≤ (Rc / R) * R := by rw [div_mul_cancel₀ _ hR.ne']
  have hbudget : A / R + 2 * A * (Rc / R) ≤ 1 := by
    calc
      _ = (A + 2 * A * Rc) / R := by ring
      _ ≤ 1 := (div_le_one hR).2 (by nlinarith)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hw : 0 ≤ majorant R (d + 1) n := majorant_nonneg R hR.le _ _
      have hshift : majorant R d n ≤ majorant R (d + 1) n / R := by
        apply (le_div_iff₀ hR).2
        simpa only [mul_comm] using majorant_shift_le R hR.le d n
      have hs : (∑ k ∈ range n,
          (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
            Z (n - (k + 1)))
          ≤ (2 * (Rc / R)) * majorant R (d + 1) n := by
        calc
          _ ≤ ∑ k ∈ range n, (Rc / R) ^ (k + 1) * majorant R (d + 1) n := by
            apply sum_le_sum
            intro k hk
            have hklt : k < n := mem_range.mp hk
            have hlow : n - (k + 1) < n := by omega
            have hc : 0 ≤ (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) *
                ((k + 1).factorial : ℝ) ^ 2 := by positivity
            exact (mul_le_mul_of_nonneg_left (ih _ hlow) hc).trans
              (majorant_coefficient_term R Rc (Rc / R) hR.le hRc hq0 hscale
                n (k + 1) (d + 1) (by omega))
          _ = (∑ k ∈ range n, (Rc / R) ^ (k + 1)) * majorant R (d + 1) n :=
            (sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (geometric_tail_le_two_mul (Rc / R) hq0 hqhalf n) hw
      calc
        Z n ≤ A * (F n + ∑ k ∈ range n,
            (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
              Z (n - (k + 1))) := hZ n
        _ ≤ A * (majorant R (d + 1) n / R +
            (2 * (Rc / R)) * majorant R (d + 1) n) :=
          mul_le_mul_of_nonneg_left (add_le_add ((hF n).trans hshift) hs) hA0
        _ = (A / R + 2 * A * (Rc / R)) * majorant R (d + 1) n := by ring
        _ ≤ majorant R (d + 1) n := mul_le_of_le_one_left hw hbudget


/-- The shifted product rule applies directly to arbitrary real sequences bounded in absolute value. -/
theorem sequence_product_majorant (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (d₁ d₂ : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ A * majorant R d₁ n)
    (hg : ∀ n, |g n| ≤ B * majorant R d₂ n) (n : ℕ) :
    |∑ k ∈ range (n + 1), (n.choose k : ℝ) * f k * g (n - k)|
      ≤ 3 * A * B * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1), |(n.choose k : ℝ) * f k * g (n - k)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), A * B *
        ((n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)) := by
      apply sum_le_sum
      intro k _hk
      have hfg : |f k| * |g (n - k)| ≤
          (A * majorant R d₁ k) * (B * majorant R d₂ (n - k)) :=
        mul_le_mul (hf k) (hg (n - k)) (abs_nonneg _)
          (mul_nonneg hA (majorant_nonneg R hR d₁ k))
      have hc : (0 : ℝ) ≤ n.choose k := by positivity
      have h := mul_le_mul_of_nonneg_left hfg hc
      simpa only [abs_mul, abs_of_nonneg hc, mul_assoc, mul_left_comm, mul_comm] using h
    _ = A * B * (∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)) := by rw [mul_sum]
    _ ≤ A * B * (3 * majorant R (d₁ + d₂) n) :=
      mul_le_mul_of_nonneg_left (majorant_convolution R hR n d₁ d₂) (mul_nonneg hA hB)
    _ = _ := by ring

end EulerGevrey

end

section

namespace EulerSmoothUniformLimit

open Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]

/-- An infinite compatible derivative tower is smooth at every level. -/
theorem contDiff_of_derivative_tower (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hJ : ∀ n x, HasFDerivAt (J n) (L n (J (n + 1) x)) x) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  have hfinite : ∀ k : ℕ, ∀ n, ContDiff ℝ k (J n) := by
    intro k
    induction k with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun x => (hJ n x).continuousAt))
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hJ n x).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (J n) = fun x => L n (J (n + 1) x) :=
        funext (fun x => (hJ n x).fderiv)
      rw [he]
      exact (L n).contDiff.comp (ih (n + 1))
  intro n
  exact contDiff_infty.mpr (fun k => hfinite k n)

/-- Uniform limits of a compatible smooth derivative tower are again smooth.
This is the completion step for Sobolev mollifications. -/
theorem contDiff_of_uniform_derivative_limits
    (f : ∀ n, ℕ → E → F n) (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hlim : ∀ n, TendstoUniformly (f n) (J n) atTop) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  apply contDiff_of_derivative_tower J L
  intro n x
  have hd := (L n).uniformContinuous.comp_tendstoUniformly (hlim (n + 1))
  exact hasFDerivAt_of_tendstoUniformly hd (hf n) (fun y => (hlim n).tendsto_at y) x

/-- Completeness constructs every limit in a uniformly Cauchy derivative tower;
the limit and all of its compatible derivatives are smooth. -/
theorem exists_smooth_limit_of_uniform_cauchy_tower [∀ n, CompleteSpace (F n)]
    (f : ∀ n, ℕ → E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hC : ∀ n, UniformCauchySeqOn (f n) atTop Set.univ) :
    ∃ J : ∀ n, E → F n,
      (∀ n, TendstoUniformly (f n) (J n) atTop) ∧ (∀ n, ContDiff ℝ ∞ (J n)) := by
  have hp : ∀ n x, ∃ v : F n, Tendsto (fun k => f n k x) atTop (nhds v) := by
    intro n x
    exact cauchy_map_iff_exists_tendsto.mp ((hC n).cauchy_map (Set.mem_univ x))
  choose J hJ using hp
  have hlim : ∀ n, TendstoUniformly (f n) (J n) atTop := by
    intro n
    rw [← tendstoUniformlyOn_univ]
    exact (hC n).tendstoUniformlyOn_of_tendsto (fun x _ => hJ n x)
  exact ⟨J, hlim, contDiff_of_uniform_derivative_limits f J L hf hlim⟩

end EulerSmoothUniformLimit

end

section

/-!
Exact weight identities used in the proposed packet's Gevrey estimates (18)--(19).
These lemmas do not assert the nonlinear PDE estimates or an Euler blowup theorem.
-/

namespace EulerPacketWeights

/-- Factorial weight at radius `ρ` for the Gevrey-two energy series. -/
noncomputable def weight (ρ : ℝ) (n : ℕ) : ℝ :=
  ρ ^ n / (n.factorial : ℝ) ^ 2

theorem weight_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : 0 < weight ρ n := by
  unfold weight
  positivity

theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

/-- The binomial gain that compensates a Gevrey-2 derivative in a non-top commutator. -/
theorem choose_add_lower (j l : ℕ) (hl : 1 ≤ l) :
    j + 1 ≤ (j + l).choose l := by
  rw [← Nat.choose_symm_add]
  have h := Nat.choose_le_choose j (Nat.add_le_add_left hl j)
  simpa only [Nat.choose_succ_self_right] using h

/-- Equation (18)'s source weight ratio, written without truncated natural subtraction. -/
theorem shifted_source_ratio (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) =
      1 / ((j + l + 1).choose l : ℝ) := by
  have hl₀ : l ≤ j + l := Nat.le_add_left l j
  have hl₁ : l ≤ j + l + 1 := hl₀.trans (Nat.le_add_right _ _)
  have hsub : j + l + 1 - l = j + 1 := by omega
  rw [Nat.cast_choose ℝ hl₀, Nat.cast_choose ℝ hl₁]
  simp only [Nat.add_sub_cancel_right, hsub]
  unfold weight
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, pow_one]
  field_simp [factorial_cast_ne_zero, hρ]

/-- Equation (19)'s external-commutator ratio. -/
theorem external_commutator_ratio (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) =
      ρ⁻¹ * ((j + 1 : ℕ) : ℝ) / ((j + l).choose l : ℝ) := by
  rw [Nat.cast_choose ℝ (Nat.le_add_left l j)]
  simp only [Nat.add_sub_cancel_right]
  unfold weight
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, pow_one]
  field_simp [factorial_cast_ne_zero, hρ]

/-- The source ratio in (18) is at most one, uniformly in the derivative indices. -/
theorem shifted_source_ratio_le_one (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) ≤ 1 := by
  rw [shifted_source_ratio ρ hρ j l]
  have hn : 0 < (j + l + 1).choose l :=
    Nat.choose_pos ((Nat.le_add_left l j).trans (Nat.le_add_right _ _))
  have hp : (0 : ℝ) < ((j + l + 1).choose l : ℝ) := by exact_mod_cast hn
  apply (div_le_one hp).2
  exact_mod_cast hn

/-- The non-top ratio in (19) is at most the inverse radius, with no order loss. -/
theorem external_commutator_ratio_le (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ)
    (hl : 1 ≤ l) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) ≤ ρ⁻¹ := by
  rw [external_commutator_ratio ρ hρ.ne' j l]
  have hp : (0 : ℝ) < ((j + l).choose l : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left l j)
  have hb : ((j + 1 : ℕ) : ℝ) ≤ ((j + l).choose l : ℝ) := by
    exact_mod_cast choose_add_lower j l hl
  exact (div_le_iff₀ hp).2 (mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hρ.le))

end EulerPacketWeights

end

section

/-!
The Hilbert-space inverse used for the packet pressure equation.
Invertibility is constructed from Lax--Milgram, not assumed.  The coercivity
hypothesis is an explicit quadratic inequality on the given bounded operator.
This does not assert the Fourier or Sobolev realization of the pressure space.
-/


namespace EulerCoerciveProjection

open InnerProductSpace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bounded bilinear form associated with an operator and the real inner product. -/
def operatorBilinear (T : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp T

lemma operatorBilinear_coercive (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    IsCoercive (operatorBilinear T) := by
  refine ⟨c, hc, fun x => ?_⟩
  change c * ‖x‖ * ‖x‖ ≤ ⟪T x, x⟫_ℝ
  simpa only [pow_two, mul_assoc] using hT x

section Complete

variable [CompleteSpace E]

/-- Lax--Milgram constructs an equivalence from the operator's coercivity. -/
def coerciveEquiv (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) : E ≃L[ℝ] E :=
  (operatorBilinear_coercive T c hc hT).continuousLinearEquivOfBilin

@[simp]
theorem coerciveEquiv_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (x : E) :
    coerciveEquiv T c hc hT x = T x := by
  apply ext_inner_right ℝ
  intro y
  exact (operatorBilinear_coercive T c hc hT).continuousLinearEquivOfBilin_apply x y

/-- The inverse operator constructed from the coercive Lax–Milgram equivalence. -/
def coerciveInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) : E →L[ℝ] E :=
  (coerciveEquiv T c hc hT).symm.toContinuousLinearMap

@[simp]
theorem operator_inverse_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (y : E) :
    T (coerciveInverse T c hc hT y) = y := by
  change T ((coerciveEquiv T c hc hT).symm y) = y
  rw [← coerciveEquiv_apply T c hc hT]
  exact (coerciveEquiv T c hc hT).apply_symm_apply y

@[simp]
theorem inverse_operator_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (x : E) :
    coerciveInverse T c hc hT (T x) = x := by
  change (coerciveEquiv T c hc hT).symm (T x) = x
  rw [← coerciveEquiv_apply T c hc hT]
  exact (coerciveEquiv T c hc hT).symm_apply_apply x

theorem coerciveInverse_apply_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (y : E) :
    ‖coerciveInverse T c hc hT y‖ ≤ c⁻¹ * ‖y‖ := by
  let x := coerciveInverse T c hc hT y
  change ‖x‖ ≤ c⁻¹ * ‖y‖
  by_cases hx : x = 0
  · simp only [hx, norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : c * ‖x‖ ≤ ‖y‖ := by
    apply (mul_le_mul_iff_left₀ hn).mp
    calc
      c * ‖x‖ * ‖x‖ = c * ‖x‖ ^ 2 := by ring
      _ ≤ ⟪T x, x⟫_ℝ := hT x
      _ = ⟪y, x⟫_ℝ := by rw [show T x = y from operator_inverse_apply T c hc hT y]
      _ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
  have := (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using this

theorem coerciveInverse_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    ‖coerciveInverse T c hc hT‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le)
  exact coerciveInverse_apply_norm_le T c hc hT

/-- The exact resolvent identity for the inverses constructed by Lax--Milgram. -/
theorem coerciveInverse_resolvent (T U : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ)
    (hU : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪U x, x⟫_ℝ) :
    coerciveInverse T c hc hT - coerciveInverse U d hd hU =
      (coerciveInverse T c hc hT).comp
        ((U - T).comp (coerciveInverse U d hd hU)) := by
  ext y
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, operator_inverse_apply]

theorem coerciveInverse_norm_sub_le (T U : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ)
    (hU : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪U x, x⟫_ℝ) :
    ‖coerciveInverse T c hc hT - coerciveInverse U d hd hU‖ ≤
      c⁻¹ * d⁻¹ * ‖U - T‖ := by
  rw [coerciveInverse_resolvent T U c d hc hd hT hU]
  calc
    ‖(coerciveInverse T c hc hT).comp
        ((U - T).comp (coerciveInverse U d hd hU))‖ ≤
        ‖coerciveInverse T c hc hT‖ *
          ‖(U - T).comp (coerciveInverse U d hd hU)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖coerciveInverse T c hc hT‖ *
        (‖U - T‖ * ‖coerciveInverse U d hd hU‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ c⁻¹ * (‖U - T‖ * d⁻¹) :=
      mul_le_mul (coerciveInverse_norm_le T c hc hT)
        (mul_le_mul_of_nonneg_left (coerciveInverse_norm_le U d hd hU) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.2 hc.le)
    _ = c⁻¹ * d⁻¹ * ‖U - T‖ := by ring

end Complete

section Subspace

variable (S : Submodule ℝ E) [CompleteSpace S]

/-- Orthogonal projection of the given ambient operator, restricted to the subspace. -/
def projectedOperator (G : E →L[ℝ] E) : S →L[ℝ] S :=
  S.orthogonalProjectionOnto.comp (G.comp S.subtypeL)

theorem projectedOperator_inner (G : E →L[ℝ] E) (x y : S) :
    ⟪projectedOperator S G x, y⟫_ℝ = ⟪G (x : E), (y : E)⟫_ℝ := by
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right y (G x)

theorem projectedOperator_coercive (G : E →L[ℝ] E) (c : ℝ)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (x : S) :
    c * ‖x‖ ^ 2 ≤ ⟪projectedOperator S G x, x⟫_ℝ := by
  rw [projectedOperator_inner]
  exact hG x

/-- The projected-pressure inverse, constructed by applying Lax--Milgram on `S`. -/
def projectedInverse (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) : S →L[ℝ] S :=
  coerciveInverse (projectedOperator S G) c hc (projectedOperator_coercive S G c hG)

@[simp]
theorem projectedOperator_inverse_apply (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : S) :
    projectedOperator S G (projectedInverse S G c hc hG f) = f :=
  operator_inverse_apply (projectedOperator S G) c hc (projectedOperator_coercive S G c hG) f


@[simp]
theorem projectedOperator_sub (G H : E →L[ℝ] E) :
    projectedOperator S (G - H) = projectedOperator S G - projectedOperator S H := by
  ext x
  simp [projectedOperator]



/-- Solves the projected equation with an ambient forcing vector. -/
def pressureSolver (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) : E →L[ℝ] S :=
  (projectedInverse S G c hc hG).comp S.orthogonalProjectionOnto

theorem pressureSolver_equation (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : E)) =
      S.orthogonalProjectionOnto f :=
  projectedOperator_inverse_apply S G c hc hG (S.orthogonalProjectionOnto f)

theorem pressureSolver_apply_norm_le (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    ‖pressureSolver S G c hc hG f‖ ≤ c⁻¹ * ‖f‖ := by
  calc
    ‖pressureSolver S G c hc hG f‖ ≤ c⁻¹ * ‖S.orthogonalProjectionOnto f‖ :=
      coerciveInverse_apply_norm_le (projectedOperator S G) c hc
        (projectedOperator_coercive S G c hG) (S.orthogonalProjectionOnto f)
    _ ≤ c⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (S.norm_orthogonalProjectionOnto_apply_le f)
        (inv_nonneg.2 hc.le)


end Subspace


end EulerCoerciveProjection

end

section

namespace EulerInverseRegularity

open EulerCoerciveProjection InnerProductSpace ContinuousLinearMap
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]












theorem coerciveInverse_eq_mapInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    coerciveInverse T c hc hT = T.inverse := by
  have he : (coerciveEquiv T c hc hT : E →L[ℝ] E) = T := by
    ext x
    exact coerciveEquiv_apply T c hc hT x
  calc
    coerciveInverse T c hc hT =
        (coerciveEquiv T c hc hT).symm.toContinuousLinearMap := rfl
    _ = (coerciveEquiv T c hc hT : E →L[ℝ] E).inverse :=
      (ContinuousLinearMap.inverse_equiv (coerciveEquiv T c hc hT)).symm
    _ = T.inverse := congrArg ContinuousLinearMap.inverse he

theorem coerciveInverse_eq_ringInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    coerciveInverse T c hc hT = Ring.inverse T := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact coerciveInverse_eq_mapInverse T c hc hT


/-- The time derivative of the constructed inverse is `-I T' I`. -/
theorem hasDerivAt_coerciveInverse (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ)
    (t : ℝ) (T₁ : E →L[ℝ] E) (hder : HasDerivAt T T₁ t) :
    HasDerivAt (fun s => coerciveInverse (T s) c hc (hT s))
      (-(coerciveInverse (T t) c hc (hT t)).comp
        (T₁.comp (coerciveInverse (T t) c hc (hT t)))) t := by
  let u : (E →L[ℝ] E)ˣ := (coerciveEquiv (T t) c hc (hT t)).toUnit
  have hu : (u : E →L[ℝ] E) = T t := by
    ext x
    exact coerciveEquiv_apply (T t) c hc (hT t) x
  have hui : (↑u⁻¹ : E →L[ℝ] E) = coerciveInverse (T t) c hc (hT t) := rfl
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  have hcomp := hi.comp_hasDerivAt t hder
  have hfun : (fun s => coerciveInverse (T s) c hc (hT s)) = Ring.inverse ∘ T := by
    funext s
    exact coerciveInverse_eq_ringInverse (T s) c hc (hT s)
  rw [hfun]
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcomp

theorem hasDerivAt_coerciveSolution (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ)
    (f : ℝ → E) (t : ℝ) (T₁ : E →L[ℝ] E) (f₁ : E)
    (hder : HasDerivAt T T₁ t) (hf : HasDerivAt f f₁ t) :
    HasDerivAt (fun s => coerciveInverse (T s) c hc (hT s) (f s))
      (coerciveInverse (T t) c hc (hT t)
        (f₁ - T₁ (coerciveInverse (T t) c hc (hT t) (f t)))) t := by
  convert (hasDerivAt_coerciveInverse T c hc hT t T₁ hder).clm_apply hf using 1
  simp only [neg_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

section Projected

variable (S : Submodule ℝ E) [CompleteSpace S]


omit [CompleteSpace E] in
theorem hasDerivAt_projectedOperator (G : ℝ → E →L[ℝ] E) (t : ℝ)
    (G₁ : E →L[ℝ] E) (hder : HasDerivAt G G₁ t) :
    HasDerivAt (fun s => projectedOperator S (G s)) (projectedOperator S G₁) t := by
  simpa only [zero_comp, comp_zero, zero_add, add_zero, projectedOperator, comp_assoc] using
    (hasDerivAt_const t S.orthogonalProjectionOnto).clm_comp
      (hder.clm_comp (hasDerivAt_const t S.subtypeL))



end Projected

end EulerInverseRegularity

end

end
