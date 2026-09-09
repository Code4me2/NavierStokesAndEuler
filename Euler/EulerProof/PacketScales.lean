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
import Euler.EulerProof.PacketFrames

/-!
# Scale sequences for the packet cascade

The numerical scale bookkeeping that chains the stages together:

* `EulerScale` -- the basic scale vocabulary and its limits.
* `EulerPacketScaleGeometry`, `EulerPacketBaseScales` -- geometry of the scale
  sequence and the base scales.
* `EulerPacketSourceScales`, `EulerPacketSourceTime` -- the source scales
  (`sourceTheta`, `sourceEpsilon`, the error terms) and the time widths
  (`sourceTimeWidth`, `sourceTimeRatio`) built from them.
* `EulerPacketUniformScaleSums`, `EulerPacketUniformLogBounds`,
  `EulerPacketUniformScaleChoice`, `EulerPacketFiniteScaleChoice`,
  `EulerPacketScaleActivation` -- uniform summability of the scales, the
  logarithmic bounds behind it, and the choice of scales (uniform, finite and
  activated) that the cascade uses.

This is part 8 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

/-!
Convergence estimates for the actual quadratic scale recurrence in (37).
The sequence is reindexed so that `x 0 = x_{J-1}` and
`x (n+1) = (J+n)^2 x n`; hence `J+n` is the stage index in the source.
-/

namespace EulerScale

open Filter
open scoped Topology

/-- Positivity propagates through the scale recurrence from any positive initial scale. -/
theorem quadratic_growth_pos (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, 0 < x n := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [hx]
      have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
      positivity

/-- The reciprocal of the stage index tends to zero. -/
theorem stage_inv_tendsto_zero (J : ℕ) :
    Tendsto (fun n : ℕ => (((J + n : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using
    ((tendsto_add_atTop_iff_nat J).2
      (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0)))

/-- Every fixed polynomial in the stage index divided by the scale is summable. -/
theorem polynomial_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) : Summable (fun n => ((J + n : ℕ) : ℝ) ^ A / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  have hlim : Tendsto
      (fun n : ℕ => (1 + (((J + n : ℕ) : ℝ))⁻¹) ^ A *
        ((((J + n : ℕ) : ℝ))⁻¹) ^ 2) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (stage_inv_tendsto_zero J)).pow A).mul
      ((stage_inv_tendsto_zero J).pow 2)
    simpa using h
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Eventually.of_forall fun n => ne_of_gt (div_pos (pow_pos (hjp n) _) (hxp n))
  · apply hlim.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (hjp (n + 1)).le _) (hxp (n + 1)).le),
      Real.norm_of_nonneg (div_nonneg (pow_nonneg (hjp n).le _) (hxp n).le), hx]
    have hj : (((J + (n + 1) : ℕ) : ℝ)) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hj]
    have hi : 1 + (((J + n : ℕ) : ℝ))⁻¹ =
        (((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ) := by
      field_simp [ne_of_gt (hjp n)]
    rw [hi, div_pow]
    field_simp [ne_of_gt (hjp n), ne_of_gt (hxp n)]

/-- A simple exponential majorization requiring no numerical approximations. -/
theorem exp_neg_le_reciprocal (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ 1 / t := by
  have he : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le ht he

/-- Every exponential decay in a scale divided by a fixed natural power is summable. -/
theorem exponential_decay_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) (b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hs := (polynomial_over_growth_summable J hJ x hx0 hx A).mul_left (1 / b)
  apply hs.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have ht : 0 < b * (x n / ((J + n : ℕ) : ℝ) ^ A) :=
    mul_pos hb (div_pos (hxp n) (pow_pos hj _))
  calc
    _ = Real.exp (-(b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by congr 1; ring
    _ ≤ 1 / (b * (x n / ((J + n : ℕ) : ℝ) ^ A)) := exp_neg_le_reciprocal _ ht
    _ = (1 / b) * (((J + n : ℕ) : ℝ) ^ A / x n) := by field_simp

/-- The same decay conclusion holds for every real power, including `7/2`. -/
theorem exponential_decay_real_power_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  apply (exponential_decay_summable J hJ x hx0 hx N b hb).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro n
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj
  have hpow : ((J + n : ℕ) : ℝ) ^ A ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hj hN.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (div_le_div_of_nonneg_left (hxp n).le (Real.rpow_pos_of_pos hjp A) hpow) (by linarith)

/-- The logarithm of the rapidly growing scale still has a quadratic polynomial bound. -/
theorem abs_log_growth_le (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, |Real.log (x n)| ≤ (|Real.log (x 0)| + 2) * ((J + n : ℕ) : ℝ) ^ 2 := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  intro n
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hJ2 : (1 : ℝ) ≤ (J : ℝ) ^ 2 := one_le_pow₀ hJr
      calc
        _ ≤ |Real.log (x 0)| + 2 := by linarith
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hJ2 (by positivity : 0 ≤ |Real.log (x 0)| + 2)
  | succ n ih =>
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj1
      have hlog : 0 ≤ Real.log ((J + n : ℕ) : ℝ) := Real.log_nonneg hj1
      have hlogle : Real.log ((J + n : ℕ) : ℝ) ≤ (J + n : ℕ) :=
        (Real.log_le_sub_one_of_pos hjp).trans (by linarith)
      have hjnext : (((J + (n + 1) : ℕ) : ℝ)) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hx, Real.log_mul (pow_ne_zero _ hjp.ne') (hxp n).ne', Real.log_pow]
      calc
        _ ≤ |(2 : ℝ) * Real.log ((J + n : ℕ) : ℝ)| + |Real.log (x n)| := abs_add_le _ _
        _ = 2 * Real.log ((J + n : ℕ) : ℝ) + |Real.log (x n)| := by rw [abs_of_nonneg (by positivity)]
        _ ≤ 2 * ((J + n : ℕ) : ℝ) +
            (|Real.log (x 0)| + 2) * ((J + n : ℕ) : ℝ) ^ 2 := by linarith
        _ ≤ _ := by
          rw [hjnext]
          nlinarith [abs_nonneg (Real.log (x 0)),
            mul_nonneg (abs_nonneg (Real.log (x 0))) hjp.le]

/-- Every polynomial weight times `|log x|/x` is summable. -/
theorem polynomial_log_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) : Summable (fun n => ((J + n : ℕ) : ℝ) ^ A * |Real.log (x n)| / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hs := (polynomial_over_growth_summable J hJ x hx0 hx (A + 2)).mul_left
    (|Real.log (x 0)| + 2)
  apply hs.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (hxp n).le)
  intro n
  have h := mul_le_mul_of_nonneg_left (abs_log_growth_le J hJ x hx0 hx n)
    (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)
  have hd := div_le_div_of_nonneg_right h (hxp n).le
  simpa only [pow_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hd


/-- The logarithm of the stage index is also harmless in every polynomially weighted scale sum. -/
theorem polynomial_stage_log_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) :
    Summable (fun n => ((J + n : ℕ) : ℝ) ^ A * Real.log ((J + n : ℕ) : ℝ) / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hj1 : ∀ n, (1 : ℝ) ≤ (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 1 ≤ J + n by omega)
  apply (polynomial_over_growth_summable J hJ x hx0 hx (A + 1)).of_nonneg_of_le
  · intro n
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (hj1 n))) (hxp n).le
  · intro n
    have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one (hj1 n)
    have hl : Real.log ((J + n : ℕ) : ℝ) ≤ (J + n : ℕ) :=
      (Real.log_le_sub_one_of_pos hjp).trans (by linarith)
    simpa only [pow_succ] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)) (hxp n).le





/-- A starting scale at least one stays at least one. -/
theorem quadratic_growth_one_le (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 1 ≤ x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, 1 ≤ x n := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [hx]
      have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) ih







/-- Exponential scale decay remains summable after a quantitatively vanishing relative error. -/
theorem perturbed_exponential_decay_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b : ℝ) (hb : 0 < b) (e : ℕ → ℝ)
    (he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0)) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) + e n)) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hb2 : 0 < b / 2 := by linarith
  apply (exponential_decay_real_power_summable J hJ x hx0 hx A (b / 2) hb2).of_norm_bounded_eventually_nat
  filter_upwards [he.eventually_le_const hb2] with n hn
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have hy : 0 < x n / ((J + n : ℕ) : ℝ) ^ A := div_pos (hxp n) (Real.rpow_pos_of_pos hj A)
  have herror := (div_le_iff₀ hy).mp hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  linarith


end EulerScale

end

section

open Set Filter
open scoped Topology

namespace EulerPacketScaleGeometry

open Real EulerScale

/-- The activation-time interval in (38) follows from the two frame
invariants in (24), with the numerical constants stated in the source. -/
theorem activation_time_bounds
    {a β H x X : ℝ} (ha : 1 / 2 ≤ a) (ha₂ : a ≤ 2)
    (hH : 0 < H) (hx : 0 < x) (hX : 0 ≤ X)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    (3 * X * x / sqrt H) / 6 ≤ X / sqrt (β * a * H) ∧
      X / sqrt (β * a * H) ≤ 2 * (3 * X * x / sqrt H) / 3 := by
  have ha₀ : 0 < a := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hroot : 0 < sqrt (β * a * H) := sqrt_pos.2 (by positivity)
  have hrootH : 0 < sqrt H := sqrt_pos.2 hH
  have hs := sq_sqrt (show 0 ≤ β * a * H by positivity)
  have hsH := sq_sqrt hH.le
  have hprodLow : 1 / 4 ≤ β * x ^ 2 * a := by
    have hh := mul_le_mul hβx ha (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by positivity : 0 ≤ β * x ^ 2)
    nlinarith only [hh]
  have hprodUp : β * x ^ 2 * a ≤ 4 := by
    have hh := mul_le_mul hβx₂ ha₂ ha₀.le (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh]
  have hlo : sqrt H ≤ 2 * x * sqrt (β * a * H) := by
    have hh := mul_le_mul_of_nonneg_right hprodLow hH.le
    have hhroot : 0 ≤ 2 * x * sqrt (β * a * H) := by positivity
    nlinarith only [hh, hs, hsH, hhroot, hrootH]
  have hup : x * sqrt (β * a * H) ≤ 2 * sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hprodUp hH.le
    have hhroot : 0 ≤ x * sqrt (β * a * H) := by positivity
    nlinarith only [hh, hs, hsH, hhroot, hrootH]
  constructor
  · have hid : 3 * X * x / sqrt H / 6 = X * x / (2 * sqrt H) := by ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity) hroot).2
    have hh := mul_le_mul_of_nonneg_left hup hX
    nlinarith only [hh]
  · have hid : 2 * (3 * X * x / sqrt H) / 3 = 2 * X * x / sqrt H := by ring
    rw [hid]
    apply (div_le_div_iff₀ hroot hrootH).2
    have hh := mul_le_mul_of_nonneg_left hlo hX
    nlinarith only [hh]




/-- The ratio of a stage to any fixed predecessor tends to one. -/
theorem stage_div_shifted_tendsto_one (J d : ℕ) (hJ : d < J) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) /
      ((J - d + n : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h := (stage_inv_tendsto_zero (J - d)).const_mul (d : ℝ)
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add h
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by
    exact_mod_cast (show 0 < J - d + n by omega)
  have hj : ((J + n : ℕ) : ℝ) = ((J - d + n : ℕ) : ℝ) + d := by
    exact_mod_cast (show J + n = (J - d + n) + d by omega)
  dsimp only
  rw [hj]
  field_simp

/-- A real power below a predecessor's natural power has vanishing
ratio; this includes the source's support exponent `7/2`. -/
theorem stage_rpow_div_shifted_power_tendsto_zero
    (J d B : ℕ) (hJ : d < J) (A : ℝ) (hAB : A < B) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ A /
      ((J - d + n : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  have hjtop : Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.add_comm] using tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat J)
  have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hAB)).comp hjtop
  have hh := ((stage_div_shifted_tendsto_one J d hJ).pow B).mul hp
  simp only [one_pow, mul_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by
    exact_mod_cast (show 0 < J + n by omega)
  have hprev : (0 : ℝ) < (J - d + n : ℕ) := by
    exact_mod_cast (show 0 < J - d + n by omega)
  dsimp only [Function.comp_def]
  rw [neg_sub, rpow_sub hj, rpow_natCast, div_pow]
  field_simp

/-- Polynomial logarithms are negligible relative to `x/j^A`, for every
nonnegative real exponent `A`. -/
theorem polynomial_log_relative_tendsto_zero
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A C p q : ℝ) (_hA : 0 ≤ A) :
    Tendsto (fun n => (C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)) /
      (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hjp (n : ℕ) : (0 : ℝ) < (J + n : ℕ) := by
    exact_mod_cast (show 0 < J + n by omega)
  have hpoly : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A / x n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (polynomial_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    · intro n
      exact div_nonneg (rpow_nonneg (hjp n).le A) (hxp n).le
    · intro n
      apply div_le_div_of_nonneg_right _ (hxp n).le
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hlogx : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * log (x n) / x n) atTop (𝓝 0) := by
    have hb := (polynomial_log_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    apply squeeze_zero_norm' _ hb
    apply Eventually.of_forall
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (rpow_nonneg (hjp n).le A),
      abs_of_pos (hxp n)]
    apply div_le_div_of_nonneg_right _ (hxp n).le
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hlogj : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * log ((J + n : ℕ) : ℝ) / x n)
      atTop (𝓝 0) := by
    have hb := (polynomial_stage_log_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · intro n
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      exact div_nonneg (mul_nonneg (rpow_nonneg (hjp n).le A) (log_nonneg hj1)) (hxp n).le
    · intro n
      apply div_le_div_of_nonneg_right _ (hxp n).le
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      apply mul_le_mul_of_nonneg_right _ (log_nonneg hj1)
      simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hh := ((hpoly.const_mul C).add (hlogj.const_mul p)).add (hlogx.const_mul q)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  field_simp [(hxp n).ne', (rpow_pos_of_pos (hjp n) A).ne']

/-- Explicit positive logarithmic errors from older stages are absorbed
by the source's negative exponential scale. No smallness guard is assumed. -/
theorem source_scale_exponential_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b c C p q : ℝ) (hA : 0 ≤ A) (hAB : A < B) (hb : 0 < b) :
    Summable (fun n => exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) := by
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x hx0 hx
  let e : ℕ → ℝ := fun n => c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
    C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
    have hh := ((stage_rpow_div_shifted_power_tendsto_zero J d B hJ A hAB).const_mul c).add
      (polynomial_log_relative_tendsto_zero J hJ1 x hx0 hx A C p q hA)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    apply Eventually.of_forall
    intro n
    have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
    have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
    dsimp only [e]
    field_simp [(hxp n).ne', (rpow_pos_of_pos hj A).ne', hp.ne']
    ring
  have hh := perturbed_exponential_decay_summable J hJ1 x hx0 hx A b hb e he
  simpa only [e, add_assoc] using hh

end EulerPacketScaleGeometry

end

section

open Filter
open scoped Topology

namespace EulerPacketSourceScales

open Real EulerScale EulerPacketScaleGeometry

/-- A fixed polynomial majorant for the dimensionless stage horizon. -/
noncomputable def sourceTheta (J : ℕ) (C : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * (1 + ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)

/-- The source upper bound for the square-root inverse parent shear. -/
noncomputable def sourceEpsilon (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The older gradient bound expressed using the quadratic recurrence. -/
noncomputable def sourceOlderGradient (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + exp (x n / (((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 2 + n : ℕ) : ℝ) ^ 7))

/-- The inverse fourth root of the preceding packet frequency. -/
noncomputable def sourcePriorError (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n / (4 * ((J - 1 + n : ℕ) : ℝ) ^ 4))

/-- The neighbor error with the support, frequency, and shear scales of (37). -/
noncomputable def sourceNeighborError (J : ℕ) (c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ) +
    c * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4 +
    c * x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)

/-- The full coefficient error entering the normalized ray and velocity equations. -/
noncomputable def sourceCoefficientError (J : ℕ) (C c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  16 * (sourceEpsilon J x n * sourceTheta J C x n * sourceOlderGradient J x n ^ 2 +
    sourcePriorError J x n + sourceNeighborError J c x n)

/-- The horizon majorant is bounded by a single monomial. -/
theorem sourceTheta_bounds {J : ℕ} (hJ : 1 ≤ J) {C : ℝ} (hC : 1 ≤ C)
    {x : ℕ → ℝ} (hx : ∀ n, 1 ≤ x n) (n : ℕ) :
    1 ≤ sourceTheta J C x n ∧
      sourceTheta J C x n ≤ 2 * C * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hjx : 1 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) (one_le_pow₀ (hx n))
  unfold sourceTheta
  have hC₀ : 0 ≤ C := by linarith
  constructor
  · nlinarith only [hC, hjx, mul_nonneg hC₀ (by nlinarith only [hjx] :
      0 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)]
  · have hh := mul_le_mul_of_nonneg_left hjx hC₀
    nlinarith only [hh]

/-- The explicit logarithmic scale comparison also allows an arbitrary
fixed polynomial prefactor. -/
theorem polynomial_source_scale_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b c C : ℝ) (p q : ℕ) (hA : 0 ≤ A) (hAB : A < B) (hb : 0 < b) (hC : 0 < C) :
    Summable (fun n => C * ((J + n : ℕ) : ℝ) ^ p * (x n) ^ q *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) +
        c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))) := by
  have hh := source_scale_exponential_summable J d B hJ x hx0 hx A b c (log C) p q hA hAB hb
  have hxp := quadratic_growth_pos J (by omega) x hx0 hx
  apply hh.congr
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  simp only [exp_add, exp_log hC, exp_nat_mul, exp_log hj, exp_log (hxp n)]
  ring




/-- The source shear/older-gradient product has an explicit decaying
exponential majorant at every normal stage after the two base exceptions. -/
theorem source_shear_gradient_bound
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (n : ℕ) :
    sourceEpsilon J x n * sourceOlderGradient J x n ^ 2 ≤
      8 * exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 7) +
        2 * (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9)) := by
  have ho : (1 : ℝ) ≤ (J - 2 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 2 + n by omega)
  have hop : ((J - 2 + n : ℕ) : ℝ) ≤ ((J - 1 + n : ℕ) : ℝ) := by
    exact_mod_cast (show J - 2 + n ≤ J - 1 + n by omega)
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := lt_of_lt_of_le (by linarith : (0 : ℝ) < (J - 2 + n : ℕ)) hop
  have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
    exact_mod_cast (show J - 1 + n ≤ J + n by omega)
  have hpow := pow_le_pow_left₀ hp.le hpj 7
  have hd := div_le_div_of_nonneg_left (hx n)
    (by positivity : 0 < 2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))
  have he : sourceEpsilon J x n ≤ 2 * exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 7)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply exp_le_exp.mpr
    convert! neg_le_neg hd using 1 <;> ring
  have hden : ((J - 2 + n : ℕ) : ℝ) ^ 9 ≤
      ((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 2 + n : ℕ) : ℝ) ^ 7 := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_trans zero_le_one ho) hop 2)
      (by positivity : 0 ≤ ((J - 2 + n : ℕ) : ℝ) ^ 7)
    simpa only [← pow_add] using hh
  have hdG := div_le_div_of_nonneg_left (hx n)
    (by positivity : 0 < ((J - 2 + n : ℕ) : ℝ) ^ 9) hden
  have hg : sourceOlderGradient J x n ≤ 2 * exp (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) := by
    have hle := exp_le_exp.mpr hdG
    have h1 : 1 ≤ exp (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) :=
      one_le_exp_iff.mpr (div_nonneg (hx n) (by positivity))
    unfold sourceOlderGradient
    linarith
  have hg₀ : 0 ≤ sourceOlderGradient J x n := by unfold sourceOlderGradient; positivity
  have hh := mul_le_mul he (pow_le_pow_left₀ hg₀ hg 2) (sq_nonneg _) (by positivity)
  convert! hh using 1
  rw [exp_add, show (2 : ℝ) * (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) =
    x n / ((J - 2 + n : ℕ) : ℝ) ^ 9 + x n / ((J - 2 + n : ℕ) : ℝ) ^ 9 by ring, exp_add]
  ring




end EulerPacketSourceScales

end

section

open Filter
open scoped Topology

namespace EulerPacketSourceTime

open Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales


/-- A frame normalization `a≤2` gives the explicit source epsilon bound. -/
theorem epsilon_of_shear_bound {a L : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    sqrt (a / exp L) ≤ 2 * exp (-L / 2) := by
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  rw [sqrt_div ha, ← exp_half]
  have hid : -L / 2 = -(L / 2) := by ring
  rw [hid, exp_neg]
  change sqrt a / exp (L / 2) ≤ 2 / exp (L / 2)
  exact div_le_div_of_nonneg_right hs (exp_pos (L / 2)).le

/-- The current time width in (37), after exact substitution of the scales. -/
noncomputable def sourceTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 *
    exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The following time width, using `x_j=j²x_{j-1}` twice. -/
noncomputable def sourceNextTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))

/-- The exact quotient of consecutive time widths. -/
noncomputable def sourceTimeRatio (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) +
      x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- Exact cancellation computes the consecutive time-width quotient. -/
theorem source_time_ratio_identity (J : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    sourceNextTimeWidth J x n = sourceTimeRatio J x n * sourceTimeWidth J x n := by
  unfold sourceNextTimeWidth sourceTimeRatio sourceTimeWidth
  rw [exp_add]
  have hc : exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) = 1 := by
    rw [← exp_add]
    convert! exp_zero using 1
    ring_nf
  linear_combination -(3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 *
    (x n) ^ 2 * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) * hc



/-- The extra normalized horizon length has the explicit polynomial/exponential
bound asserted after (39). -/
theorem source_extra_time_bound
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) * sourceNextTimeWidth J x n ≤
      48 * ((J + n : ℕ) : ℝ) ^ 6 * (x n) ^ 2 *
        exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) +
          (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hroot : sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) ≤
      2 * exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
    rw [sqrt_mul ha, ← exp_half]
    have hh := mul_le_mul_of_nonneg_right hs (exp_pos ((x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) / 2)).le
    convert! hh using 1
    congr 2
    ring
  have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by nlinarith only [hj]
  have hW : 0 ≤ sourceNextTimeWidth J x n := by unfold sourceNextTimeWidth; positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 2)) hW
  have hp' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ 12 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5)))
  unfold sourceNextTimeWidth at hh
  have hpE : x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by ring
  have hnE : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) := by ring
  rw [hpE, hnE] at hh hp'
  rw [exp_add]
  change 2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
    (3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) ≤ _
  rw [hnE]
  refine hh.trans ?_
  convert! hp' using 1 <;> ring




end EulerPacketSourceTime

end

section

open Filter
open scoped Topology

namespace EulerPacketBaseScales

open Real

/-- A negative total real power absorbs a fixed monomial horizon. -/
theorem base_power_decay (T p : ℝ) (m k : ℕ)
    (hp : p + 2 * m + k < 0) :
    Tendsto (fun x : ℝ => x ^ p * (T * x ^ 2) ^ m * x ^ k) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).const_mul (T ^ m)
  simp only [neg_neg, mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_add hx, rpow_add hx]
  have hm : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
  rw [hm, rpow_natCast, rpow_natCast]
  simp only [mul_pow, pow_mul]
  ring

/-- Exponential decay absorbs every fixed real polynomial power and
every fixed monomial horizon power. -/
theorem base_exponential_decay (T p b : ℝ) (m k : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ p * exp (-b * x) * (T * x ^ 2) ^ m * x ^ k)
      atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 2 * m + k) b hb).const_mul (T ^ m)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_add hx, rpow_add hx]
  have hm : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
  rw [hm, rpow_natCast, rpow_natCast]
  simp only [mul_pow, pow_mul]
  ring



/-- The exact base horizon `6 J² x₀^(2-1000/2)` tends to zero. -/
theorem base_horizon_tendsto_zero (J : ℝ) :
    Tendsto (fun x : ℝ => 6 * J ^ 2 * x ^ (2 - 1000 / 2 : ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 498)).const_mul (6 * J ^ 2)
  norm_num at hh ⊢
  exact hh

/-- The core-volume guard `h r³ Sbase`, with `r=x₀^-1000`,
also tends to zero from the explicit base choices. -/
theorem base_core_volume_cost_tendsto_zero (J : ℝ) :
    Tendsto (fun x : ℝ => x ^ (1000 : ℕ) * (x ^ (-1000 : ℝ)) ^ 3 *
      (6 * J ^ 2 * x ^ (-498 : ℝ))) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2498)).const_mul (6 * J ^ 2)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hid : (-2498 : ℝ) = 1000 + (-1000) * 3 + (-498) := by norm_num
  rw [hid, rpow_add hx, rpow_add hx, rpow_mul hx.le]
  norm_num only [rpow_ofNat]
  ring

end EulerPacketBaseScales

end

section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleSums

open Real EulerScale

/-- Once the initial stage dominates the fixed polynomial exponent,
the rescaled quadratic sequence grows by at least a factor two at every step. -/
theorem polynomial_scale_doubles
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) (n : ℕ) :
    2 * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤ x (n + 1) / ((J + (n + 1) : ℕ) : ℝ) ^ A := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hJj : (J : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show J ≤ J + n by omega)
  have hJ₀ : (0 : ℝ) ≤ J := by positivity
  have hpower : (2 : ℝ) ^ (A + 1) ≤ ((J + n : ℕ) : ℝ) ^ 2 :=
    hJA.trans (pow_le_pow_left₀ hJ₀ hJj 2)
  have hn : ((J + (n + 1) : ℕ) : ℝ) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
  have hden : (((J + n : ℕ) : ℝ) + 1) ^ A ≤ (2 : ℝ) ^ A * ((J + n : ℕ) : ℝ) ^ A := by
    have hh := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (J + n : ℕ) + 1)
      (by linarith : ((J + n : ℕ) : ℝ) + 1 ≤ 2 * ((J + n : ℕ) : ℝ)) A
    simpa only [mul_pow] using hh
  rw [hx, hn]
  calc
    2 * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤
        (((J + n : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ A) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (hxp n).le (pow_nonneg hj.le A))
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ A)).2
      simpa only [pow_succ, mul_comm] using hpower
    _ = (((J + n : ℕ) : ℝ) ^ 2 * x n) / ((2 : ℝ) ^ A * ((J + n : ℕ) : ℝ) ^ A) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (hxp n).le)
      (by positivity : 0 < (((J + n : ℕ) : ℝ) + 1) ^ A) hden

/-- The entire positive exponent sequence is bounded below by its first
term times `2^n`, uniformly in the initial scale. -/
theorem polynomial_scale_geometric_lower
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, (2 : ℝ) ^ n * (x 0 / (J : ℝ) ^ A) ≤ x n / ((J + n : ℕ) : ℝ) ^ A := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
      have hd := polynomial_scale_doubles J A hJ hJA x hx0 hx n
      rw [pow_succ]
      nlinarith only [hh, hd]

/-- A simple exact comparison between binary growth and the stage count. -/
theorem stage_count_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      push_cast
      rw [pow_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith only [ih, hn]

/-- Every term of the source exponential series is bounded by one
explicit geometric series whose ratio depends only on the first scale. -/
theorem source_exponential_geometric_majorant
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A)) ≤
      exp (-b * (x 0 / (J : ℝ) ^ A)) * exp (-b * (x 0 / (J : ℝ) ^ A)) ^ n := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hd := polynomial_scale_geometric_lower J A hJ hJA x hx0 hx n
  have hn := mul_le_mul_of_nonneg_right (stage_count_le_two_pow n)
    (div_nonneg hx0.le (pow_nonneg hJp.le A))
  have he : -b * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤
      -b * (x 0 / (J : ℝ) ^ A) + (n : ℝ) * (-b * (x 0 / (J : ℝ) ^ A)) := by
    have hh := mul_le_mul_of_nonpos_left (hn.trans hd) (neg_nonpos.mpr hb.le)
    nlinarith only [hh]
  have hh := exp_le_exp.mpr he
  simpa only [exp_add, exp_nat_mul] using hh

/-- The full exponential-cost sum has an explicit upper bound tending
to zero as the initial scale increases. This makes the uniform small-sum
choice in the source quantitative. -/
theorem source_exponential_tsum_bound
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (b : ℝ) (hb : 0 < b) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) ≤
      exp (-b * (x 0 / (J : ℝ) ^ A)) / (1 - exp (-b * (x 0 / (J : ℝ) ^ A))) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let r := exp (-b * (x 0 / (J : ℝ) ^ A))
  have hr₀ : 0 ≤ r := (exp_pos _).le
  have hr : |r| < 1 := by
    rw [abs_of_nonneg hr₀]
    apply exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hb) (div_pos hx0 (pow_pos hJp A))
  have hgeom := (summable_geometric_of_abs_lt_one hr).mul_left r
  have hsum := exponential_decay_summable J hJ x hx0 hx A b hb
  have hh := hsum.tsum_le_tsum (source_exponential_geometric_majorant J A hJ hJA x hx0 hx b hb) hgeom
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr] at hh
  simpa only [r, div_eq_mul_inv] using hh

/-- The explicit geometric-series bound vanishes as `x₀` tends to infinity. -/
theorem source_exponential_bound_tendsto_zero (J A : ℕ) (hJ : 1 ≤ J)
    (b : ℝ) (hb : 0 < b) :
    Tendsto (fun X : ℝ => exp (-b * (X / (J : ℝ) ^ A)) /
      (1 - exp (-b * (X / (J : ℝ) ^ A)))) atTop (𝓝 0) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hh := EulerPacketBaseScales.base_exponential_decay 1 0 (b / (J : ℝ) ^ A) 0 0
    (div_pos hb (pow_pos hJp A))
  simp only [rpow_zero, one_mul, pow_zero, mul_one] at hh
  have hh' : Tendsto (fun X : ℝ => exp (-b * (X / (J : ℝ) ^ A))) atTop (𝓝 0) := by
    convert! hh using 1
    ext X
    congr 1
    ring
  have hd := hh'.div (tendsto_const_nhds.sub hh') (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [sub_zero, zero_div] at hd
  convert! hd using 1

end EulerPacketUniformScaleSums

end

section

open Filter
open scoped Topology

namespace EulerPacketUniformLogBounds

open Real EulerScale EulerPacketUniformScaleSums

/-- Every fixed polynomial logarithm is bounded by a simple product of
the stage and the square root of the scale. -/
theorem polynomial_log_bound {j X C p q : ℝ} (hj : 1 ≤ j) (hX : 1 ≤ X) :
    C + p * log j + q * log X ≤ (|C| + |p| + 2 * |q|) * j * sqrt X := by
  have hjp : 0 < j := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ sqrt X := one_le_sqrt.mpr hX
  have hsj : 1 ≤ j * sqrt X := one_le_mul_of_one_le_of_one_le hj hs
  have hlj : 0 ≤ log j := log_nonneg hj
  have hlX : 0 ≤ log X := log_nonneg hX
  have hljb : log j ≤ j := (log_le_sub_one_of_pos hjp).trans (by linarith)
  have hlXb : log X ≤ 2 * sqrt X := by
    have hh := log_le_sub_one_of_pos (sqrt_pos.mpr hXp)
    rw [log_sqrt hXp.le] at hh
    linarith
  have hCb : C ≤ |C| * j * sqrt X := by
    have hh := mul_le_mul_of_nonneg_left hsj (abs_nonneg C)
    nlinarith only [hh, le_abs_self C]
  have hp₁ := mul_le_mul_of_nonneg_right (le_abs_self p) hlj
  have hp₂ := mul_le_mul_of_nonneg_left hljb (abs_nonneg p)
  have hp₃ := mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg p) hjp.le)
  have hq₁ := mul_le_mul_of_nonneg_right (le_abs_self q) hlX
  have hq₂ := mul_le_mul_of_nonneg_left hlXb (abs_nonneg q)
  have hq₃ := mul_le_mul_of_nonneg_right hj (mul_nonneg (by positivity : 0 ≤ 2 * |q|) (sqrt_nonneg X))
  nlinarith only [hCb, hp₁, hp₂, hp₃, hq₁, hq₂, hq₃]

/-- A single explicit lower bound on the initial scale absorbs the
polynomial logarithms at every subsequent quadratic stage. -/
theorem polynomial_logs_uniformly_absorbed
    (J A : ℕ) (hJ : 1 ≤ J)
    (hJA : (2 : ℝ) ^ (2 * A + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C p q b : ℝ) (hb : 0 < b)
    (hlarge : (2 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * A + 2) ≤ x 0) :
    ∀ n, C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
  let S := |C| + |p| + 2 * |q|
  let L := 2 * S / b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hgeom := polynomial_scale_geometric_lower J (2 * A + 2) hJ
    (by simpa only [show 2 * A + 2 + 1 = 2 * A + 3 by omega] using hJA) x (by linarith) hx
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hstart : L ^ 2 ≤ x 0 / (J : ℝ) ^ (2 * A + 2) := by
    apply (le_div_iff₀ (pow_pos hJp _)).2
    exact hlarge
  have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hone
    (div_nonneg (le_trans zero_le_one hx0) (pow_nonneg hJp.le (2 * A + 2)))
  have hscale : L ^ 2 ≤ x n / ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
    nlinarith only [hstart, hbase, hgeom n]
  have hsquare := (le_div_iff₀ (pow_pos hj (2 * A + 2))).mp hscale
  have hroot : L * ((J + n : ℕ) : ℝ) ^ (A + 1) ≤ sqrt (x n) := by
    have hp : (((J + n : ℕ) : ℝ) ^ (A + 1)) ^ 2 = ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hs := sq_sqrt (le_trans zero_le_one (hx1 n))
    have hn : 0 ≤ L * ((J + n : ℕ) : ℝ) ^ (A + 1) := by positivity
    nlinarith only [hsquare, hp, hs, hn, sqrt_nonneg (x n)]
  have hlog := polynomial_log_bound (C := C) (p := p) (q := q) hj1 (hx1 n)
  have hlogmul := mul_le_mul_of_nonneg_right hlog (pow_nonneg hj.le A)
  have hrootmul := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg (div_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2)) (sqrt_nonneg (x n)))
  have hLS : (b / 2) * L = S := by dsimp [L]; field_simp
  have hid : (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) =
      ((b / 2) * x n) / ((J + n : ℕ) : ℝ) ^ A := by ring
  rw [hid]
  apply (le_div_iff₀ (pow_pos hj A)).2
  have hmul : S * ((J + n : ℕ) : ℝ) ^ (A + 1) * sqrt (x n) ≤ (b / 2) * x n := by
    calc
      _ = (L * ((J + n : ℕ) : ℝ) ^ (A + 1)) * ((b / 2) * sqrt (x n)) := by rw [← hLS]; ring
      _ ≤ sqrt (x n) * ((b / 2) * sqrt (x n)) := hrootmul
      _ = (b / 2) * (sqrt (x n)) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt (le_trans zero_le_one (hx1 n))]
  rw [pow_succ] at hmul
  dsimp only [S] at hmul
  nlinarith only [hlogmul, hmul]

end EulerPacketUniformLogBounds

end

section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleChoice

open Real EulerScale EulerPacketScaleGeometry EulerPacketUniformScaleSums EulerPacketUniformLogBounds

/-- One sufficiently large initial stage makes every predecessor-log
coefficient small, uniformly over all subsequent stages. -/
theorem exists_uniform_stage_choice (d B N : ℕ) (a c b : ℝ)
    (haB : a < B) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ d < J ∧ (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2 ∧
      ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4 := by
  have hh := (stage_rpow_div_shifted_power_tendsto_zero (d + 1) d B (by omega) a haB).const_mul c
  simp only [mul_zero] at hh
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hh.eventually_le_const (by positivity : (0 : ℝ) < b / 4))
  let R : ℕ := 2 ^ (2 * N + 3) + 3
  let J : ℕ := (d + 1) + M + R
  have hR3 : 3 ≤ R := Nat.le_add_left 3 _
  have hJ3 : 3 ≤ J := by dsimp [J]; omega
  have hdJ : d < J := by dsimp [J]; omega
  have hpJ : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) := by
    exact_mod_cast (show 2 ^ (2 * N + 3) ≤ J by dsimp [J, R]; omega)
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  refine ⟨J, hJ3, hdJ, by nlinarith only [hpJ, hJr], ?_⟩
  intro n
  have h := hM (M + R + n) (by omega)
  have hj : d + 1 + (M + R + n) = J + n := by dsimp [J]; omega
  have hp : d + 1 - d + (M + R + n) = J - d + n := by dsimp [J]; omega
  simpa only [hj, hp] using h

/-- For a stage chosen above, one explicit lower bound on the initial
scale controls all logarithmic scale errors at once. -/
theorem uniform_source_exponent_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    ∀ n, -b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      -(b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ N) := by
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hlog := polynomial_logs_uniformly_absorbed J N hJ hJN x hx0 hx C p q (b / 2)
    (by positivity) (by convert! hlarge using 1; ring)
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
  have hxn : 0 < x n := by linarith [hx1 n]
  have hpow : ((J + n : ℕ) : ℝ) ^ a ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 haN
  have hscales := div_le_div_of_nonneg_left hxn.le (rpow_pos_of_pos hj a) hpow
  have hcm := mul_le_mul_of_nonneg_right (hcoeff n)
    (div_nonneg hxn.le (rpow_nonneg hj.le a))
  have hct : c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) ≤
      (b / 4) * (x n / ((J + n : ℕ) : ℝ) ^ a) := by
    convert! hcm using 1
    field_simp [(rpow_pos_of_pos hj a).ne', hp.ne']
  have hscaleB := mul_le_mul_of_nonneg_left hscales hb.le
  have hl := hlog n
  nlinarith only [hct, hscaleB, hl]

/-- The complete logarithmic source cost has a uniform geometric-series
bound after choosing the stage and then the initial scale. -/
theorem uniform_source_cost_tsum_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤
      exp (-(b / 2) * (x 0 / (J : ℝ) ^ N)) /
        (1 - exp (-(b / 2) * (x 0 / (J : ℝ) ^ N))) := by
  have hmajor := fun n => exp_le_exp.mpr
    (uniform_source_exponent_bound J d B N hJ hdJ hJN x hx0 hx a b c C p q haN hb hcoeff hlarge n)
  have hsum := exponential_decay_summable J hJ x (by linarith) hx N (b / 2) (by positivity)
  have hcost := hsum.of_nonneg_of_le (fun _ => (exp_pos _).le) hmajor
  have hh := hcost.tsum_le_tsum hmajor hsum
  have hpower : (2 : ℝ) ^ (N + 1) ≤ (J : ℝ) ^ 2 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : N + 1 ≤ 2 * N + 3)).trans hJN
  exact hh.trans (source_exponential_tsum_bound J N hJ hpower x (by linarith) hx (b / 2) (by positivity))


end EulerPacketUniformScaleChoice

end

section

open Filter
open scoped Topology

namespace EulerPacketFiniteScaleChoice

open Real EulerPacketUniformScaleChoice EulerPacketUniformScaleSums

/-- Every finite collection of scale inequalities allows the same
choices of `J` and then `x₀`. Thus the source's different coefficient,
neighbor, time, and pressure-cost requirements can be imposed together. -/
theorem finite_source_uniform_small_sum_choice
    {ι : Type*} [Fintype ι] (d B N : ι → ℕ) (a b c C p q : ι → ℝ)
    (haB : ∀ i, a i < B i) (haN : ∀ i, a i ≤ N i) (hb : ∀ i, 0 < b i) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) → ∀ i,
        (∑' n, exp (-(b i) * (x n / ((J + n : ℕ) : ℝ) ^ (a i)) +
          c i * (x n / ((J - d i + n : ℕ) : ℝ) ^ (B i)) +
          C i + p i * log ((J + n : ℕ) : ℝ) + q i * log (x n))) ≤ δ := by
  classical
  choose Ji hJi3 hJid hJiN hJiC using fun i =>
    exists_uniform_stage_choice (d i) (B i) (N i) (a i) (c i) (b i) (haB i) (hb i)
  let J := max 3 (Finset.univ.sup Ji)
  have hJ3 : 3 ≤ J := le_max_left _ _
  have hJ1 : 1 ≤ J := by omega
  have hJiLe (i : ι) : Ji i ≤ J :=
    (Finset.le_sup (f := Ji) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hdJ (i : ι) : d i < J := lt_of_lt_of_le (hJid i) (hJiLe i)
  have hJN (i : ι) : (2 : ℝ) ^ (2 * N i + 3) ≤ (J : ℝ) ^ 2 := by
    exact (hJiN i).trans (pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast hJiLe i) 2)
  have hcoeff (i : ι) (n : ℕ) :
      c i * (((J + n : ℕ) : ℝ) ^ (a i) / ((J - d i + n : ℕ) : ℝ) ^ (B i)) ≤ b i / 4 := by
    have hh := hJiC i (J - Ji i + n)
    have hj : Ji i + (J - Ji i + n) = J + n := by have hi := hJiLe i; omega
    have hp : Ji i - d i + (J - Ji i + n) = J - d i + n := by
      have hi := hJiLe i
      have hid := hJid i
      omega
    simpa only [hj, hp] using hh
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hboth : ∀ᶠ X : ℝ in atTop, ∀ i : ι,
      (4 * (|C i| + |p i| + 2 * |q i|) / b i) ^ 2 * (J : ℝ) ^ (2 * N i + 2) ≤ X ∧
      exp (-(b i / 2) * (X / (J : ℝ) ^ N i)) /
        (1 - exp (-(b i / 2) * (X / (J : ℝ) ^ N i))) ≤ δ := by
    apply eventually_all.2
    intro i
    have hi := source_exponential_bound_tendsto_zero J (N i) hJ1 (b i / 2)
      (div_pos (hb i) (by norm_num))
    exact (eventually_ge_atTop _).and (hi.eventually_le_const hδ)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hboth
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hx1 : 1 ≤ x 0 := (le_max_left 1 X).trans hx0
  have hall := hX (x 0) ((le_max_right 1 X).trans hx0) i
  exact (uniform_source_cost_tsum_bound J (d i) (B i) (N i) hJ1 (hdJ i) (hJN i)
    x hx1 hx (a i) (b i) (c i) (C i) (p i) (q i) (haN i) (hb i) (hcoeff i) hall.1).trans hall.2

end EulerPacketFiniteScaleChoice

end

section

namespace EulerPacketScaleActivation

open Real EulerPacketScaleGeometry

/-- The actual quadratic target and frame invariant imply every basic
small-beta and target-time guard used in the scalar ODE estimates. -/
theorem source_activation_ode_guards {j x β : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    0 < β ∧ β ≤ 1 / 16 ∧ 0 < sqrt β ∧ sqrt β ≤ 1 / 4 ∧
    1 / sqrt β ≤ (j ^ 2 * x) / sqrt β ∧
    (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 ∧
    0 < 1 / (j ^ 2 * x) ∧ 1 / (j ^ 2 * x) ≤ 1 / 2 := by
  have hxp : 0 < x := by linarith
  have hjp : 0 < j := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hx64 : 64 ≤ x ^ 2 := by nlinarith only [hx]
  have hm := mul_le_mul_of_nonneg_left hx64 hβ.le
  have hβsmall : β ≤ 1 / 16 := by nlinarith only [hm, hβx₂]
  have hσ : 0 < sqrt β := sqrt_pos.mpr hβ
  have hσsmall : sqrt β ≤ 1 / 4 := (sqrt_le_iff).2 ⟨by norm_num, by nlinarith only [hβsmall]⟩
  have hj2 : 9 ≤ j ^ 2 := by nlinarith only [hj]
  have hX : 2 ≤ j ^ 2 * x := by
    have hh := mul_le_mul hj2 hx (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg j)
    nlinarith only [hh]
  have htLow : 1 / sqrt β ≤ (j ^ 2 * x) / sqrt β :=
    div_le_div_of_nonneg_right (by linarith only [hX]) hσ.le
  have htime := activation_time_bounds (a := 1) (H := 1) (β := β) (x := x) (X := j ^ 2 * x)
    (by norm_num) (by norm_num) (by norm_num) hxp (by positivity) hβx hβx₂
  norm_num only [mul_one, sqrt_one, div_one] at htime
  have htUp : (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 := by nlinarith only [htime.2]
  have hy : 0 < 1 / (j ^ 2 * x) := by positivity
  have hy₂ : 1 / (j ^ 2 * x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < j ^ 2 * x)).2
    nlinarith only [hX]
  exact ⟨hβ, hβsmall, hσ, hσsmall, htLow, htUp, hy, hy₂⟩


end EulerPacketScaleActivation

end

end
