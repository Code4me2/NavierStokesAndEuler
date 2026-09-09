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
import Euler.EulerProof.CutoffsAndEnergy

/-!
# Packet growth: the Riccati ODE and the ray system

The ordinary-differential core of the construction:

* `EulerPacketGrowth` -- the Riccati comparison (`riccatiRoot`,
  `invertedRiccati`, `invertedScalar`) driving the growth of one packet.
* `EulerPacketPerturbation` -- stability of that comparison under perturbation.
* `EulerPacketRay` -- the ray system: the scaled matrix and velocity entries
  (`scaledRayEntry`, `velocityThird`, `scaledVelocityEntry`,
  `velocityFirstRhs`, `velocitySecondRhs`) and the estimates they satisfy.

This is part 6 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

/-!
Order estimates for the scalar ODE occurring in equation (30) of the proposed
Euler packet argument.  These are finite-dimensional ODE results only.
-/

namespace EulerPacketGrowth

open Set Filter Real
open scoped Topology

private theorem eventually_nonneg_right
    {f : ℝ → ℝ} {x d : ℝ} (hd : HasDerivAt f d x)
    (hx : 0 ≤ f x) (hboundary : f x = 0 → 0 < d) :
    ∀ᶠ y in 𝓝[>] x, 0 ≤ f y := by
  rcases hx.eq_or_lt with hx | hx
  · have hpos : 0 < d := hboundary hx.symm
    have hslope : ∀ᶠ y in 𝓝[>] x, 0 < slope f x y :=
      (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)) (Ioi_mem_nhds hpos)
    filter_upwards [hslope, self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field, ← hx] at hy
    have : 0 < y - x := sub_pos.mpr hxy
    simpa using ((div_pos_iff_of_pos_right this).mp hy).le
  · exact ((hd.continuousAt.eventually (Ioi_mem_nhds hx)).filter_mono
      nhdsWithin_le_nhds).mono fun _ hy => hy.le

/-- Two differentiable functions remain nonnegative if every boundary point
of the nonnegative quadrant has a strictly inward derivative. -/
theorem pair_nonneg_of_strict_boundary
    {f g df dg : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (hboundary : ∀ t ∈ Ico 0 T, 0 ≤ f t → 0 ≤ g t →
      (f t = 0 → 0 < df t) ∧ (g t = 0 → 0 < dg t)) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t := by
  let s : Set ℝ := {t | 0 ≤ f t ∧ 0 ≤ g t}
  have hfc : ContinuousOn f (Icc 0 T) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 T) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hs : IsClosed (s ∩ Icc 0 T) := by
    have hpair : ContinuousOn (fun t => (f t, g t)) (Icc 0 T) := hfc.prodMk hgc
    have hc : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
      (isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const continuous_snd)
    simpa [s, inter_comm] using
      hpair.preimage_isClosed_of_isClosed isClosed_Icc hc
  apply hs.Icc_subset_of_forall_exists_gt ⟨hf0, hg0⟩
  intro t ht y hy
  have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht.2
  have hb := hboundary t ht.2 ht.1.1 ht.1.2
  have he := (eventually_nonneg_right (hf t hti) ht.1.1 hb.1).and
    (eventually_nonneg_right (hg t hti) ht.1.2 hb.2)
  exact nonempty_of_mem (inter_mem he (Ioc_mem_nhdsGT hy))

/-- Positivity for a cooperative pair of differential inequalities.  The
nonnegative quadrant is invariant; positivity is not an additional hypothesis. -/
theorem cooperative_nonneg_of_bounded
    {f g df dg a b : ℝ → ℝ} {T K : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t ∧ a t ≤ K)
    (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t ∧ b t ≤ K)
    (hdf : ∀ t ∈ Icc 0 T, a t * g t ≤ df t)
    (hdg : ∀ t ∈ Icc 0 T, b t * f t ≤ dg t) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t := by
  have hpert : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc 0 T,
      0 ≤ f t + ε * exp ((K + 1) * t) ∧
        0 ≤ g t + ε * exp ((K + 1) * t) := by
    intro ε hε
    have hed : ∀ t : ℝ, HasDerivAt (fun s => ε * exp ((K + 1) * s))
        ((K + 1) * ε * exp ((K + 1) * t)) t := by
      intro t
      apply ((((hasDerivAt_id t).const_mul (K + 1)).exp).const_mul ε).congr_deriv
      dsimp
      ring
    apply pair_nonneg_of_strict_boundary
      (fun t ht => (hf t ht).add (hed t))
      (fun t ht => (hg t ht).add (hed t))
    · simpa using add_nonneg hf0 hε.le
    · simpa using add_nonneg hg0 hε.le
    · intro t ht hft hgt
      dsimp only [Pi.add_apply] at hft hgt ⊢
      have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have hat := ha t hti
      have hbt := hb t hti
      have hεE : 0 < ε * exp ((K + 1) * t) := mul_pos hε (exp_pos _)
      constructor
      · intro _
        have hmul : a t * (-(ε * exp ((K + 1) * t))) ≤ a t * g t :=
          mul_le_mul_of_nonneg_left (by linarith) hat.1
        have hpos : 0 < (K + 1 - a t) * (ε * exp ((K + 1) * t)) :=
          mul_pos (by linarith [hat.2]) hεE
        linarith [hdf t hti]
      · intro _
        have hmul : b t * (-(ε * exp ((K + 1) * t))) ≤ b t * f t :=
          mul_le_mul_of_nonneg_left (by linarith) hbt.1
        have hpos : 0 < (K + 1 - b t) * (ε * exp ((K + 1) * t)) :=
          mul_pos (by linarith [hbt.2]) hεE
        linarith [hdg t hti]
  intro t ht
  have hE : exp ((K + 1) * t) ≠ 0 := ne_of_gt (exp_pos _)
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [div_mul_cancel₀ _ hE] using
      (hpert (ε / exp ((K + 1) * t)) (div_pos hε (exp_pos _)) t ht).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [div_mul_cancel₀ _ hE] using
      (hpert (ε / exp ((K + 1) * t)) (div_pos hε (exp_pos _)) t ht).2

/-- A specialization of cooperative positivity with coefficient bound `2`. -/
theorem cooperative_nonneg
    {f g df dg a b : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t ∧ a t ≤ 2)
    (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t ∧ b t ≤ 2)
    (hdf : ∀ t ∈ Icc 0 T, a t * g t ≤ df t)
    (hdg : ∀ t ∈ Icc 0 T, b t * f t ≤ dg t) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t :=
  cooperative_nonneg_of_bounded hf hg hf0 hg0 ha hb hdf hdg

/-- The flux system `V' = F/D`, `F' = c V` dominates the constant-coefficient
system with `D = 2` and `c = 1`.  In particular, its solution is positive and
has a hyperbolic-cosine lower bound, for every nonnegative initial flux. -/
theorem cosh_lower_of_flux_system
    {V F D c : ℝ → ℝ} {T : ℝ}
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (F t / D t) t)
    (hF : ∀ t ∈ Icc 0 T, HasDerivAt F (c t * V t) t)
    (hV0 : V 0 = 1) (hF0 : 0 ≤ F 0)
    (hD : ∀ t ∈ Icc 0 T, 1 ≤ D t ∧ D t ≤ 2)
    (hc : ∀ t ∈ Icc 0 T, 1 ≤ c t ∧ c t ≤ 2) :
    ∀ t ∈ Icc 0 T,
      cosh (t / √2) ≤ V t ∧ √2 * sinh (t / √2) ≤ F t := by
  have hspos : (0 : ℝ) < √2 := by positivity
  have hsne : (√2 : ℝ) ≠ 0 := ne_of_gt hspos
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcd : ∀ t : ℝ, HasDerivAt (fun s => cosh (s / √2))
      (sinh (t / √2) / √2) t := by
    intro t
    convert (((hasDerivAt_id t).div_const (√2 : ℝ)).cosh) using 1 <;> simp [div_eq_mul_inv]
  have hsd : ∀ t : ℝ, HasDerivAt (fun s => √2 * sinh (s / √2))
      (cosh (t / √2)) t := by
    intro t
    apply ((((hasDerivAt_id t).div_const (√2 : ℝ)).sinh).const_mul (√2 : ℝ)).congr_deriv
    dsimp
    field_simp
  have hcompare := cooperative_nonneg
    (f := fun t => V t - cosh (t / √2))
    (g := fun t => F t - √2 * sinh (t / √2))
    (df := fun t => F t / D t - sinh (t / √2) / √2)
    (dg := fun t => c t * V t - cosh (t / √2))
    (a := fun t => 1 / D t) (b := c)
    (fun t ht => (hV t ht).sub (hcd t))
    (fun t ht => (hF t ht).sub (hsd t))
    (by simp [hV0]) (by simpa using hF0)
    (fun t ht => by
      have hdt := hD t ht
      have hdpos : 0 < D t := lt_of_lt_of_le zero_lt_one hdt.1
      constructor
      · positivity
      · have : 1 / D t ≤ 1 := (div_le_one hdpos).mpr hdt.1
        linarith)
    (fun t ht => ⟨le_trans zero_le_one (hc t ht).1, (hc t ht).2⟩)
    (fun t ht => by
      have hdt := hD t ht
      have hdpos : 0 < D t := lt_of_lt_of_le zero_lt_one hdt.1
      have hsinh : 0 ≤ sinh (t / √2) :=
        sinh_nonneg_iff.mpr (div_nonneg ht.1 hspos.le)
      have hinv : 1 / (√2 : ℝ) ≤ √2 / D t := by
        apply (div_le_div_iff₀ hspos hdpos).mpr
        nlinarith [hdt.2]
      have hmul := mul_nonneg hsinh (sub_nonneg.mpr hinv)
      simp only [div_eq_mul_inv] at hmul ⊢
      nlinarith)
    (fun t ht => by
      have hmul := mul_nonneg (sub_nonneg.mpr (hc t ht).1)
        (cosh_pos (t / √2)).le
      nlinarith)
  intro t ht
  exact ⟨sub_nonneg.mp (hcompare t ht).1, sub_nonneg.mp (hcompare t ht).2⟩

/-- The precise cosine-hyperbolic growth comparison used after equation (30).
The initial derivative is allowed to be arbitrarily large and nonnegative. -/
theorem equation30_cosh_lower
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Icc 0 T,
      cosh (t / √2) ≤ V t ∧
      √2 * sinh (t / √2) ≤ (1 + (β * t ^ 2) ^ 2) * V₁ t := by
  have hcoeff : ∀ t ∈ Icc 0 T,
      0 ≤ β * t ^ 2 ∧ β * t ^ 2 ≤ 1 := by
    intro t ht
    have ht2 : t ^ 2 ≤ T ^ 2 := (sq_le_sq₀ ht.1 hT).mpr ht.2
    exact ⟨mul_nonneg hβ (sq_nonneg _),
      le_trans (mul_le_mul_of_nonneg_left ht2 hβ) hscale⟩
  apply cosh_lower_of_flux_system
    (D := fun t => 1 + (β * t ^ 2) ^ 2)
    (c := fun t => 2 * (1 - β * (β * t ^ 2)))
    (F := fun t => (1 + (β * t ^ 2) ^ 2) * V₁ t)
  · intro t ht
    apply (hV t ht).congr_deriv
    have hD : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  · exact hflux
  · exact hV0
  · simpa using hV₁0
  · intro t ht
    obtain ⟨hl, hu⟩ := hcoeff t ht
    constructor <;> nlinarith [sq_nonneg (β * t ^ 2)]
  · intro t ht
    obtain ⟨hl, hu⟩ := hcoeff t ht
    have hp : 0 ≤ β * (β * t ^ 2) := mul_nonneg hβ hl
    have hq : β * (β * t ^ 2) ≤ β := by nlinarith
    constructor <;> nlinarith

/-- Equation (30) gives positivity and a nonnegative derivative from the
initial conditions alone, throughout the pre-inversion interval. -/
theorem equation30_positive
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Icc 0 T, 0 < V t ∧ 0 ≤ V₁ t := by
  intro t ht
  obtain ⟨hcosh, hfluxlower⟩ :=
    equation30_cosh_lower hβ hβsmall hT hscale hV hflux hV0 hV₁0 t ht
  constructor
  · exact lt_of_lt_of_le (cosh_pos _) hcosh
  · have hsinh : 0 ≤ √2 * sinh (t / √2) :=
      mul_nonneg (sqrt_nonneg _)
        (sinh_nonneg_iff.mpr (div_nonneg ht.1 (sqrt_nonneg _)))
    have hprod : 0 ≤ (1 + (β * t ^ 2) ^ 2) * V₁ t := hsinh.trans hfluxlower
    exact nonneg_of_mul_nonneg_right hprod (by positivity)

/-- A convenient pure exponential consequence of the hyperbolic-cosine bound. -/
theorem exp_quarter_le_cosh {t : ℝ} (ht : 4 ≤ t) :
    exp (t / 4) ≤ cosh (t / √2) := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hspos : (0 : ℝ) < √2 := by positivity
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : (√2 : ℝ) ≤ 2 := by nlinarith [sqrt_nonneg (2 : ℝ)]
  have hexp : 2 ≤ exp (t / 4) := by linarith [add_one_le_exp (t / 4)]
  have harg : t / 4 + t / 4 ≤ t / √2 := by
    apply (le_div_iff₀ hspos).mpr
    have := mul_le_mul_of_nonneg_left hsle ht0
    nlinarith
  have hprod : exp (t / 4) * exp (t / 4) ≤ exp (t / √2) := by
    rw [← exp_add]
    exact exp_le_exp.mpr harg
  rw [cosh_eq]
  nlinarith [exp_pos (-(t / √2))]

/-- At `T = 1 / sqrt β`, equation (30) amplifies by at least
`exp (1 / (4 sqrt β))`, uniformly over every nonnegative initial derivative. -/
theorem equation30_endpoint_exponential
    {β : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 1 / 16)
    (hV : ∀ t ∈ Icc 0 (1 / √β), HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 (1 / √β),
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    exp (1 / (4 * √β)) ≤ V (1 / √β) := by
  have hspos : 0 < √β := sqrt_pos.mpr hβ
  have hsne : √β ≠ 0 := ne_of_gt hspos
  have hsq : (√β) ^ 2 = β := sq_sqrt hβ.le
  have hT : 0 ≤ 1 / √β := by positivity
  have hscale : β * (1 / √β) ^ 2 ≤ 1 := by
    have : β * (1 / √β) ^ 2 = 1 := by
      field_simp
      exact hsq.symm
    exact this.le
  have hT4 : 4 ≤ 1 / √β := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith
  have hg := (equation30_cosh_lower hβ.le (by linarith) hT hscale hV hflux hV0 hV₁0
    (1 / √β) ⟨hT, le_rfl⟩).1
  have he := exp_quarter_le_cosh hT4
  have heq : (1 / √β) / 4 = 1 / (4 * √β) := by ring
  rw [heq] at he
  exact he.trans hg

/-- Nonnegative initial values give componentwise lower bounds for a
cooperative flux system, with no smallness restriction on the coefficients. -/
theorem flux_lower_initial
    {V F D c : ℝ → ℝ} {T K : ℝ}
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (F t / D t) t)
    (hF : ∀ t ∈ Icc 0 T, HasDerivAt F (c t * V t) t)
    (hV0 : 0 ≤ V 0) (hF0 : 0 ≤ F 0)
    (hD : ∀ t ∈ Icc 0 T, 0 ≤ 1 / D t ∧ 1 / D t ≤ K)
    (hc : ∀ t ∈ Icc 0 T, 0 ≤ c t ∧ c t ≤ K) :
    ∀ t ∈ Icc 0 T, V 0 ≤ V t ∧ F 0 ≤ F t := by
  have hp := cooperative_nonneg_of_bounded
    (f := fun t => V t - V 0) (g := fun t => F t - F 0)
    (df := fun t => F t / D t) (dg := fun t => c t * V t)
    (a := fun t => 1 / D t) (b := c)
    (fun t ht => (hV t ht).sub_const (V 0))
    (fun t ht => (hF t ht).sub_const (F 0))
    (by simp) (by simp) hD hc
    (fun t ht => by
      have hp := mul_nonneg (hD t ht).1 hF0
      simp only [div_eq_mul_inv] at hp ⊢
      nlinarith)
    (fun t ht => by nlinarith [mul_nonneg (hc t ht).1 hV0])
  intro t ht
  exact ⟨sub_nonneg.mp (hp t ht).1, sub_nonneg.mp (hp t ht).2⟩

/-- The inverted equation preserves positive `f` and negative `f'` when it is
integrated from `y = 1` towards smaller nonnegative `y`. -/
theorem inversion_positive
    {β a : ℝ} {f f₁ : ℝ → ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 1) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / β - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0) :
    ∀ y ∈ Icc a 1, f 1 ≤ f y ∧ 0 < f y ∧ f₁ y < 0 := by
  have htwo : (2 : ℝ) ≤ 2 / β := (le_div_iff₀ hβ).mpr (by nlinarith)
  have hmirror : ∀ t ∈ Icc 0 (1 - a), 1 - t ∈ Icc a 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hp := flux_lower_initial
    (V := fun t => f (1 - t))
    (F := fun t => -((1 + (1 - t) ^ 4) * f₁ (1 - t)))
    (D := fun t => 1 + (1 - t) ^ 4)
    (c := fun t => 2 / β - 2 * (1 - t) ^ 2)
    (T := 1 - a) (K := 2 / β + 1)
    (fun t ht => by
      apply ((hf (1 - t) (hmirror t ht)).comp t
        ((hasDerivAt_id t).const_sub 1)).congr_deriv
      have hd : 1 + (1 - t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
      field_simp)
    (fun t ht => by
      apply (((hflux (1 - t) (hmirror t ht)).comp t
        ((hasDerivAt_id t).const_sub 1)).neg).congr_deriv
      ring)
    (by simpa using hf1.le)
    (by norm_num; linarith)
    (fun t ht => by
      have hdpos : 0 < 1 + (1 - t) ^ 4 := by positivity
      have hdinv : 1 / (1 + (1 - t) ^ 4) ≤ 1 :=
        (div_le_one hdpos).mpr (by
          have : 0 ≤ (1 - t) ^ 4 := by positivity
          linarith)
      exact ⟨by positivity, by linarith⟩)
    (fun t ht => by
      obtain ⟨hyl, hyu⟩ := hmirror t ht
      have hy0 : 0 ≤ 1 - t := le_trans ha hyl
      have hy2 : (1 - t) ^ 2 ≤ 1 := by nlinarith
      constructor <;> nlinarith [sq_nonneg (1 - t)])
  intro y hy
  have htime : 1 - y ∈ Icc 0 (1 - a) := by constructor <;> linarith [hy.1, hy.2]
  have hp' := hp (1 - y) htime
  have hrefl : 1 - (1 - y) = y := by ring
  simp only [sub_zero, hrefl, one_pow, one_add_one_eq_two] at hp'
  refine ⟨hp'.1, hf1.trans_le hp'.1, ?_⟩
  have hpositive : 0 < -((1 + y ^ 4) * f₁ y) := lt_of_lt_of_le (by linarith) hp'.2
  have hnegative : (1 + y ^ 4) * f₁ y < 0 := by linarith
  exact neg_of_mul_neg_right hnegative (by positivity)

/-- A uniform Riccati upper bound that does not depend on the finite initial
value: a solution of `l' ≤ 2 - l²` obeys `l(t) ≤ 2 + 1/t` for `t > 0`. -/
theorem riccati_upper_bound
    {l dl : ℝ → ℝ} {T : ℝ}
    (hl : ∀ t ∈ Icc 0 T, HasDerivAt l (dl t) t)
    (hineq : ∀ t ∈ Ico 0 T, dl t ≤ 2 - (l t) ^ 2) :
    ∀ t ∈ Ioc 0 T, l t ≤ 2 + 1 / t := by
  have hp : ∀ t ∈ Icc 0 T, t * l t ≤ 1 + 2 * t := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => t * l t) (f' := fun t => l t + t * dl t)
      (B := fun t => 1 + 2 * t) (B' := fun _ => 2)
    · intro t ht
      exact ((hasDerivAt_id t).mul (hl t ht)).continuousAt.continuousWithinAt
    · intro t ht
      convert! ((hasDerivAt_id t).mul (hl t (Ico_subset_Icc_self ht))).hasDerivWithinAt using 1
      simp
    · norm_num
    · intro t
      simpa using ((hasDerivAt_id t).const_mul 2).const_add 1
    · intro t ht hboundary
      have htpos : 0 < t := by
        rcases ht.1.eq_or_lt with htzero | htpos
        · rw [← htzero] at hboundary
          norm_num at hboundary
        · exact htpos
      have hmul := mul_le_mul_of_nonneg_left (hineq t ht) (sq_nonneg t)
      have hsq := congrArg (fun x : ℝ => x ^ 2) hboundary
      apply (mul_lt_mul_iff_right₀ htpos).mp
      nlinarith
  intro t ht
  have htp := hp t ⟨ht.1.le, ht.2⟩
  calc
    l t = (t * l t) / t := by field_simp [ne_of_gt ht.1]
    _ ≤ (1 + 2 * t) / t := div_le_div_of_nonneg_right htp ht.1.le
    _ = 2 + 1 / t := by field_simp [ne_of_gt ht.1]; ring

/-- Recovering the ordinary second derivative from the differentiated flux. -/
theorem equation30_second_derivative
    {β t : ℝ} {V V₁ : ℝ → ℝ}
    (hflux : HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
      (2 * (1 - β * (β * t ^ 2)) * V t) t) :
    HasDerivAt V₁
      ((2 * (1 - β * (β * t ^ 2)) * V t - 4 * β ^ 2 * t ^ 3 * V₁ t) /
        (1 + (β * t ^ 2) ^ 2)) t := by
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2)
      (4 * β ^ 2 * t ^ 3) t := by
    apply (((((hasDerivAt_id t).fun_pow 2).const_mul β).fun_pow 2).const_add 1).congr_deriv
    dsimp
    ring
  have hDne : ∀ s : ℝ, 1 + (β * s ^ 2) ^ 2 ≠ 0 := fun _ => ne_of_gt (by positivity)
  have hq := hflux.div hD (hDne t)
  convert! hq using 1
  · ext s
    change V₁ s = ((1 + (β * s ^ 2) ^ 2) * V₁ s) / (1 + (β * s ^ 2) ^ 2)
    field_simp [hDne s]
  · field_simp

/-- The logarithmic derivative in equation (30) is uniformly bounded away
from the initial time, independently of the initial nonnegative slope. -/
theorem equation30_log_derivative_upper
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Ioc 0 T, V₁ t / V t ≤ 2 + 1 / t := by
  have hp := equation30_positive hβ hβsmall hT hscale hV hflux hV0 hV₁0
  let dl : ℝ → ℝ := fun t =>
    2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2) -
      (4 * β ^ 2 * t ^ 3 / (1 + (β * t ^ 2) ^ 2)) * (V₁ t / V t) -
      (V₁ t / V t) ^ 2
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => V₁ t / V t) (dl t) t := by
    intro t ht
    have hVne : V t ≠ 0 := ne_of_gt (hp t ht).1
    have hDne : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    apply ((equation30_second_derivative (hflux t ht)).div (hV t ht) hVne).congr_deriv
    dsimp [dl]
    field_simp
  apply riccati_upper_bound hd
  intro t ht
  have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hDpos : 0 < 1 + (β * t ^ 2) ^ 2 := by positivity
  have hDge : 1 ≤ 1 + (β * t ^ 2) ^ 2 := by nlinarith [sq_nonneg (β * t ^ 2)]
  have hcub : 2 * (1 - β * (β * t ^ 2)) ≤ 2 := by
    nlinarith [mul_nonneg hβ (mul_nonneg hβ (sq_nonneg t))]
  have hquot : 2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2) ≤ 2 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith
  have ht0 : 0 ≤ t := ht.1
  have hcoef : 0 ≤ 4 * β ^ 2 * t ^ 3 / (1 + (β * t ^ 2) ^ 2) := by positivity
  have hlog : 0 ≤ V₁ t / V t := div_nonneg (hp t hti).2 (hp t hti).1.le
  dsimp [dl]
  nlinarith [mul_nonneg hcoef hlog]

/-- A coarse Riccati upper barrier for the inverted equation. -/
theorem riccati_le_four
    {z a b : ℝ → ℝ} {T : ℝ}
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (a t - (z t) ^ 2 + b t * z t) t)
    (hz0 : z 0 ≤ 4)
    (ha : ∀ t ∈ Ico 0 T, a t ≤ 2)
    (hb : ∀ t ∈ Ico 0 T, b t ≤ 1) :
    ∀ t ∈ Icc 0 T, z t ≤ 4 := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f := z) (f' := fun t => a t - (z t) ^ 2 + b t * z t)
    (B := fun _ => 4) (B' := fun _ => 0)
    (fun t ht => (hz t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hz0 (fun t => hasDerivAt_const t 4)
  intro t ht hboundary
  rw [hboundary]
  linarith [ha t ht, hb t ht]

/-- Quantitative tracking of the stable positive Riccati branch.  This
abstract estimate is applied below with `μ = sqrt(2/(1+y^4))`; all constants
are explicit and do not involve the initial nonnegative slope. -/
theorem riccati_tracking
    {z μ dz dμ : ℝ → ℝ} {T ε : ℝ}
    (hε : 0 < ε)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (dz t) t)
    (hμ : ∀ t ∈ Icc 0 T, HasDerivAt μ (dμ t) t)
    (hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4)
    (hμrange : ∀ t ∈ Icc 0 T, 1 ≤ μ t ∧ μ t ≤ 2)
    (hres : ∀ t ∈ Ico 0 T, |dz t - ((μ t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε)
    (hμderiv : ∀ t ∈ Ico 0 T, |dμ t| ≤ 4 * ε) :
    ∀ t ∈ Icc 0 T, |z t - μ t| ≤ 6 * exp (-t) + 48 * ε := by
  have hBd : ∀ t : ℝ, HasDerivAt (fun s => 6 * exp (-s) + 48 * ε)
      (-6 * exp (-t)) t := by
    intro t
    apply (((hasDerivAt_id t).neg.exp.const_mul 6).add_const (48 * ε)).congr_deriv
    dsimp
    ring
  have hBpos : ∀ t : ℝ, 0 ≤ 6 * exp (-t) + 48 * ε := by
    intro t
    positivity
  by_cases hT : 0 ≤ T
  · have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have hupper : ∀ t ∈ Icc 0 T, z t - μ t ≤ 6 * exp (-t) + 48 * ε := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun t => z t - μ t) (f' := fun t => dz t - dμ t)
        (B := fun t => 6 * exp (-t) + 48 * ε) (B' := fun t => -6 * exp (-t))
        (fun t ht => ((hz t ht).sub (hμ t ht)).continuousAt.continuousWithinAt)
        (fun t ht => ((hz t (Ico_subset_Icc_self ht)).sub
          (hμ t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (by norm_num; linarith [(hzrange 0 hzero).2, (hμrange 0 hzero).1]) hBd
      intro t ht hboundary
      have hti := Ico_subset_Icc_self ht
      have hsum : 1 ≤ z t + μ t := by linarith [(hzrange t hti).1, (hμrange t hti).1]
      have hprod := mul_nonneg (sub_nonneg.mpr hsum) (hBpos t)
      obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hres t ht)
      obtain ⟨hμlo, hμhi⟩ := abs_le.mp (hμderiv t ht)
      nlinarith
    have hlower : ∀ t ∈ Icc 0 T, μ t - z t ≤ 6 * exp (-t) + 48 * ε := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun t => μ t - z t) (f' := fun t => dμ t - dz t)
        (B := fun t => 6 * exp (-t) + 48 * ε) (B' := fun t => -6 * exp (-t))
        (fun t ht => ((hμ t ht).sub (hz t ht)).continuousAt.continuousWithinAt)
        (fun t ht => ((hμ t (Ico_subset_Icc_self ht)).sub
          (hz t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (by norm_num; linarith [(hzrange 0 hzero).1, (hμrange 0 hzero).2]) hBd
      intro t ht hboundary
      have hti := Ico_subset_Icc_self ht
      have hsum : 1 ≤ z t + μ t := by linarith [(hzrange t hti).1, (hμrange t hti).1]
      have hprod := mul_nonneg (sub_nonneg.mpr hsum) (hBpos t)
      obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hres t ht)
      obtain ⟨hμlo, hμhi⟩ := abs_le.mp (hμderiv t ht)
      nlinarith
    intro t ht
    exact abs_le.mpr ⟨by linarith [hlower t ht], hupper t ht⟩
  · intro t ht
    exact False.elim (hT (le_trans ht.1 ht.2))

/-- After time `1/(2ε)` the Riccati tracking error is at most `60ε`. -/
theorem riccati_tracking_after_layer
    {z μ dz dμ : ℝ → ℝ} {T ε : ℝ}
    (hε : 0 < ε)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (dz t) t)
    (hμ : ∀ t ∈ Icc 0 T, HasDerivAt μ (dμ t) t)
    (hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4)
    (hμrange : ∀ t ∈ Icc 0 T, 1 ≤ μ t ∧ μ t ≤ 2)
    (hres : ∀ t ∈ Ico 0 T, |dz t - ((μ t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε)
    (hμderiv : ∀ t ∈ Ico 0 T, |dμ t| ≤ 4 * ε) :
    ∀ t ∈ Icc 0 T, 1 / (2 * ε) ≤ t → |z t - μ t| ≤ 60 * ε := by
  intro t ht hlayer
  have htime : 1 ≤ 2 * ε * t := by
    have := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hlayer
    nlinarith
  have hexp : exp (-t) ≤ 2 * ε := by
    rw [exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (exp_pos _)).mpr
    have hm := mul_le_mul_of_nonneg_left (add_one_le_exp t) (show 0 ≤ 2 * ε by positivity)
    nlinarith
  have htrack := riccati_tracking hε hz hμ hzrange hμrange hres hμderiv t ht
  linarith

/-- The positive stationary branch of the rescaled inverted Riccati equation. -/
noncomputable def riccatiRoot (ε t : ℝ) : ℝ :=
  sqrt (2 / (1 + (1 - ε * t) ^ 4))

/-- Its derivative as the spatial coordinate `y = 1 - εt` decreases. -/
noncomputable def riccatiRootDeriv (ε t : ℝ) : ℝ :=
  4 * ε * (1 - ε * t) ^ 3 /
    ((1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t)

theorem hasDerivAt_riccatiRoot (ε t : ℝ) :
    HasDerivAt (riccatiRoot ε) (riccatiRootDeriv ε t) t := by
  have hy : HasDerivAt (fun s : ℝ => 1 - ε * s) (-ε) t := by
    simpa using ((hasDerivAt_id t).const_mul ε).const_sub 1
  have hdne : 1 + (1 - ε * t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hqpos : 0 < 2 / (1 + (1 - ε * t) ^ 4) := by positivity
  have hq : HasDerivAt (fun s => 2 / (1 + (1 - ε * s) ^ 4))
      (8 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ^ 2) t := by
    apply ((hasDerivAt_const t 2).div ((hy.fun_pow 4).const_add 1) hdne).congr_deriv
    dsimp
    field_simp
    ring
  apply (hq.sqrt (ne_of_gt hqpos)).congr_deriv
  dsimp [riccatiRootDeriv, riccatiRoot]
  field_simp [hdne, ne_of_gt (sqrt_pos.mpr hqpos)]
  ring

theorem riccatiRoot_bounds {ε t : ℝ}
    (hy : 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1) :
    1 ≤ riccatiRoot ε t ∧ riccatiRoot ε t ≤ 2 := by
  have hy4 : (1 - ε * t) ^ 4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy.1 hy.2 4
  have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
  have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
    have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
    linarith
  constructor
  · apply one_le_sqrt.mpr
    apply (le_div_iff₀ hdpos).mpr
    linarith
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ hdpos).mpr
      nlinarith

theorem riccatiRootDeriv_bounds {ε t : ℝ} (hε : 0 ≤ ε)
    (hy : 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1) :
    0 ≤ riccatiRootDeriv ε t ∧ riccatiRootDeriv ε t ≤ 4 * ε := by
  have hμ := riccatiRoot_bounds hy
  have hy0 := hy.1
  have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy.1 hy.2 3
  have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
    have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
    linarith
  have hDsq : 1 ≤ (1 + (1 - ε * t) ^ 4) ^ 2 := by nlinarith
  have hden : 1 ≤ (1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t :=
    hDsq.trans (le_mul_of_one_le_right (sq_nonneg _) hμ.1)
  have hdenpos : 0 < (1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t := by linarith
  constructor
  · exact div_nonneg (by positivity) hdenpos.le
  · apply (div_le_iff₀ hdenpos).mpr
    exact mul_le_mul_of_nonneg_left (hy3.trans hden) (by positivity)

/-- Right-hand side of the inverted Riccati equation in the fast coordinate
`t = (1-y)/ε`, where `ε = sqrt β`. -/
noncomputable def invertedRiccati (ε t z : ℝ) : ℝ :=
  (2 - 2 * ε ^ 2 * (1 - ε * t) ^ 2) / (1 + (1 - ε * t) ^ 4) - z ^ 2 +
    (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z

/-- Explicit form of the uniform `O(sqrt β)` Riccati estimate in (31).
This theorem uses the exact rescaled ODE and an initial bound of `4`; the
preceding logarithmic-derivative estimate supplies that bound independently
of the nonnegative initial slope. -/
theorem inverted_riccati_squared_error
    {ε T : ℝ} {z : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hscale : ε * T ≤ 1)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (invertedRiccati ε t (z t)) t)
    (hz0 : z 0 ≤ 4) (hzn : ∀ t ∈ Icc 0 T, 0 ≤ z t) :
    ∀ t ∈ Icc 0 T, 1 / (2 * ε) ≤ t →
      |(z t) ^ 2 - 2 / (1 + (1 - ε * t) ^ 4)| ≤ 360 * ε := by
  have hy : ∀ t ∈ Icc 0 T, 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1 := by
    intro t ht
    have hu := mul_le_mul_of_nonneg_left ht.2 hε.le
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith
  have hcoeff : ∀ t ∈ Icc 0 T,
      (2 - 2 * ε ^ 2 * (1 - ε * t) ^ 2) / (1 + (1 - ε * t) ^ 4) ≤ 2 ∧
      0 ≤ 4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ∧
      4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ≤ 4 * ε := by
    intro t ht
    have hyt := hy t ht
    have hy0 := hyt.1
    have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
      simpa using pow_le_pow_left₀ hyt.1 hyt.2 3
    have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
      have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
      linarith
    have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    refine ⟨?_, by positivity, ?_⟩
    · apply (div_le_iff₀ hdpos).mpr
      nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (1 - ε * t))]
    · apply (div_le_iff₀ hdpos).mpr
      exact mul_le_mul_of_nonneg_left (hy3.trans hdge) (by positivity)
  have hzfour : ∀ t ∈ Icc 0 T, z t ≤ 4 := by
    apply riccati_le_four hz hz0
    · intro t ht
      exact (hcoeff t (Ico_subset_Icc_self ht)).1
    · intro t ht
      linarith [(hcoeff t (Ico_subset_Icc_self ht)).2.2]
  have hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4 :=
    fun t ht => ⟨hzn t ht, hzfour t ht⟩
  have hres : ∀ t ∈ Ico 0 T,
      |invertedRiccati ε t (z t) - ((riccatiRoot ε t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε := by
    intro t ht
    have hti := Ico_subset_Icc_self ht
    have hyt := hy t hti
    have hy0 := hyt.1
    have hy2 : (1 - ε * t) ^ 2 ≤ 1 := by nlinarith [hyt.1, hyt.2]
    have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
      have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
      linarith
    have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    have hqnonneg : 0 ≤ 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) := by positivity
    have hqupper : 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) ≤ 2 * ε ^ 2 := by
      apply (div_le_iff₀ hdpos).mpr
      exact mul_le_mul_of_nonneg_left (hy2.trans hdge) (by positivity)
    have hbn := (hcoeff t hti).2.1
    have hbu := (hcoeff t hti).2.2
    have hmulnonneg := mul_nonneg hbn (hzn t hti)
    have hmulupper :
        (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z t ≤ 16 * ε := by
      have hm := mul_le_mul hbu (hzfour t hti) (hzn t hti) (show 0 ≤ 4 * ε by positivity)
      nlinarith
    have hsquare : (riccatiRoot ε t) ^ 2 = 2 / (1 + (1 - ε * t) ^ 4) :=
      sq_sqrt (by positivity)
    have heq : invertedRiccati ε t (z t) - ((riccatiRoot ε t) ^ 2 - (z t) ^ 2) =
        -(2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4)) +
          (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z t := by
      rw [hsquare]
      unfold invertedRiccati
      field_simp
      ring
    rw [heq]
    apply abs_le.mpr
    constructor <;> nlinarith
  have hμderiv : ∀ t ∈ Ico 0 T, |riccatiRootDeriv ε t| ≤ 4 * ε := by
    intro t ht
    have hp := riccatiRootDeriv_bounds hε.le (hy t (Ico_subset_Icc_self ht))
    rw [abs_of_nonneg hp.1]
    exact hp.2
  intro t ht hlayer
  have htrack := riccati_tracking_after_layer hε hz
    (fun s _ => hasDerivAt_riccatiRoot ε s) hzrange
    (fun s hs => riccatiRoot_bounds (hy s hs)) hres hμderiv t ht hlayer
  have hμrange := riccatiRoot_bounds (hy t ht)
  have hsum : |z t + riccatiRoot ε t| ≤ 6 := by
    rw [abs_of_nonneg (by linarith [hzn t ht])]
    linarith [hzfour t ht]
  have hsquare : (riccatiRoot ε t) ^ 2 = 2 / (1 + (1 - ε * t) ^ 4) :=
    sq_sqrt (by positivity)
  rw [← hsquare, sq_sub_sq, abs_mul]
  have hm := mul_le_mul htrack hsum (abs_nonneg _) (show 0 ≤ 60 * ε by positivity)
  nlinarith

/-- The second derivative of a solution of the inverted scalar equation. -/
theorem inversion_second_derivative
    {β y : ℝ} {f f₁ : ℝ → ℝ}
    (hflux : HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / β - 2 * y ^ 2) * f y) y) :
    HasDerivAt f₁ (((2 / β - 2 * y ^ 2) * f y - 4 * y ^ 3 * f₁ y) /
      (1 + y ^ 4)) y := by
  have hD : HasDerivAt (fun z : ℝ => 1 + z ^ 4) (4 * y ^ 3) y := by
    convert! ((hasDerivAt_id y).fun_pow 4).const_add 1 using 1
    norm_num
  have hDne : ∀ z : ℝ, 1 + z ^ 4 ≠ 0 := fun _ => ne_of_gt (by positivity)
  have hq := hflux.div hD (hDne y)
  convert! hq using 1
  · ext z
    change f₁ z = ((1 + z ^ 4) * f₁ z) / (1 + z ^ 4)
    field_simp [hDne z]
  · field_simp

/-- The exact Riccati equation after the substitutions
`y = 1-εt` and `z = -ε f'/f`. -/
theorem hasDerivAt_inverted_logderivative
    {ε t : ℝ} {f f₁ : ℝ → ℝ}
    (hε : ε ≠ 0) (hfpos : f (1 - ε * t) ≠ 0)
    (hf : HasDerivAt f (f₁ (1 - ε * t)) (1 - ε * t))
    (hflux : HasDerivAt (fun y => (1 + y ^ 4) * f₁ y)
      ((2 / ε ^ 2 - 2 * (1 - ε * t) ^ 2) * f (1 - ε * t)) (1 - ε * t)) :
    HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
      (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
  have hy : HasDerivAt (fun s : ℝ => 1 - ε * s) (-ε) t := by
    simpa using ((hasDerivAt_id t).const_mul ε).const_sub 1
  have hDne : 1 + (1 - ε * t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hd := (((inversion_second_derivative hflux).comp t hy).const_mul (-ε)).div
    (hf.comp t hy) hfpos
  apply hd.congr_deriv
  dsimp [invertedRiccati]
  field_simp
  ring

/-- The uniform Riccati estimate directly for solutions of the inverted
scalar equation.  Positivity on the interval follows from the endpoint
conditions; it is not assumed. -/
theorem inversion_riccati_error
    {ε a : ℝ} {f f₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0)
    (hinit : -ε * f₁ 1 / f 1 ≤ 4) :
    ∀ y ∈ Icc a (1 / 2),
      |(-ε * f₁ y / f y) ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hp := inversion_positive (sq_pos_of_pos hε) (by nlinarith : ε ^ 2 ≤ 1)
    ha hf hflux hf1 hf₁1
  have hmirror : ∀ t ∈ Icc 0 ((1 - a) / ε), 1 - ε * t ∈ Icc a 1 := by
    intro t ht
    have hu : ε * t ≤ 1 - a := by
      have := (le_div_iff₀ hε).mp ht.2
      nlinarith
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith
  have hscale : ε * ((1 - a) / ε) ≤ 1 := by
    field_simp
    linarith
  have hz : ∀ t ∈ Icc 0 ((1 - a) / ε),
      HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
        (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
    intro t ht
    exact hasDerivAt_inverted_logderivative hεne
      (ne_of_gt (hp (1 - ε * t) (hmirror t ht)).2.1)
      (hf _ (hmirror t ht)) (hflux _ (hmirror t ht))
  have hznonneg : ∀ t ∈ Icc 0 ((1 - a) / ε),
      0 ≤ -ε * f₁ (1 - ε * t) / f (1 - ε * t) := by
    intro t ht
    have hpt := hp (1 - ε * t) (hmirror t ht)
    apply div_nonneg _ hpt.2.1.le
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hε.le) hpt.2.2.le
  have herr := inverted_riccati_squared_error hε hεsmall hscale hz
    (by simpa using hinit) hznonneg
  intro y hy
  have hy1 : y ≤ 1 := by linarith [hy.2]
  have ht : (1 - y) / ε ∈ Icc 0 ((1 - a) / ε) := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy1) hε.le
    · exact div_le_div_of_nonneg_right (by linarith [hy.1]) hε.le
  have hlayer : 1 / (2 * ε) ≤ (1 - y) / ε := by
    apply (div_le_div_iff₀ (show 0 < 2 * ε by positivity) hε).mpr
    nlinarith [hy.2]
  have heq : 1 - ε * ((1 - y) / ε) = y := by field_simp; ring
  simpa only [heq] using herr ((1 - y) / ε) ht hlayer

/-- Inversion of a solution in the original time variable, including the
rescaling `x = ετ`. -/
noncomputable def invertedScalar (ε : ℝ) (V : ℝ → ℝ) (y : ℝ) : ℝ :=
  V (y⁻¹ / ε) / y

/-- The exact derivative of `invertedScalar`, away from `y = 0`. -/
noncomputable def invertedScalarDeriv (ε : ℝ) (V V₁ : ℝ → ℝ) (y : ℝ) : ℝ :=
  -V (y⁻¹ / ε) / y ^ 2 - V₁ (y⁻¹ / ε) / (ε * y ^ 3)

/-- Both differential equations for the rescaled inversion, derived
algebraically from equation (30). -/
theorem invertedScalar_equations
    {ε y : ℝ} {V V₁ : ℝ → ℝ}
    (hε : ε ≠ 0) (hy : y ≠ 0)
    (hV : HasDerivAt V (V₁ (y⁻¹ / ε)) (y⁻¹ / ε))
    (hflux : HasDerivAt (fun t => (1 + (ε ^ 2 * t ^ 2) ^ 2) * V₁ t)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * (y⁻¹ / ε) ^ 2)) * V (y⁻¹ / ε)) (y⁻¹ / ε)) :
    HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ y) y ∧
    HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * invertedScalar ε V y) y := by
  have harg := (hasDerivAt_inv hy).div_const ε
  have h0 := hV.comp y harg
  have h1 := (equation30_second_derivative hflux).comp y harg
  have h2 := (hasDerivAt_id y).fun_pow 2
  have h3 := ((hasDerivAt_id y).fun_pow 3).const_mul ε
  have h4 := ((hasDerivAt_id y).fun_pow 4).const_add 1
  have hDne : 1 + (ε ^ 2 * (y⁻¹ / ε) ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  constructor
  · apply (h0.div (hasDerivAt_id y) hy).congr_deriv
    dsimp [invertedScalarDeriv]
    field_simp
    ring
  · apply (h4.mul ((h0.neg.div h2 (pow_ne_zero 2 hy)).sub
      (h1.div h3 (mul_ne_zero hε (pow_ne_zero 3 hy))))).congr_deriv
    dsimp [invertedScalar]
    field_simp
    ring

/-- At the start of inversion the Riccati variable has an absolute bound,
independent of the original initial nonnegative slope. -/
theorem invertedScalar_initial_bound
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t ∈ Icc 0 (1 / ε), HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 (1 / ε),
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    0 < invertedScalar ε V 1 ∧ invertedScalarDeriv ε V V₁ 1 < 0 ∧
      -ε * invertedScalarDeriv ε V V₁ 1 / invertedScalar ε V 1 ≤ 4 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hT : 0 ≤ 1 / ε := by positivity
  have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
  have hβsmall : ε ^ 2 ≤ 1 / 2 := by nlinarith
  have hp := equation30_positive (sq_nonneg ε) hβsmall hT hscale hV hflux hV0 hV₁0
    (1 / ε) ⟨hT, le_rfl⟩
  have hl := equation30_log_derivative_upper (sq_nonneg ε) hβsmall hT hscale
    hV hflux hV0 hV₁0 (1 / ε) ⟨by positivity, le_rfl⟩
  have hVne : V (1 / ε) ≠ 0 := ne_of_gt hp.1
  dsimp [invertedScalar, invertedScalarDeriv]
  simp only [inv_one, one_pow, div_one, mul_one, neg_mul]
  refine ⟨hp.1, ?_, ?_⟩
  · have hquot : 0 ≤ V₁ (1 / ε) / ε := div_nonneg hp.2 hε.le
    linarith
  · have heq : -(ε * (-(V (1 / ε)) - V₁ (1 / ε) / ε)) / V (1 / ε) =
        ε + V₁ (1 / ε) / V (1 / ε) := by field_simp; ring
    rw [heq]
    rw [one_div_one_div] at hl
    linarith

/-- The full uniform estimate (31) for the scalar equation, including the
rescaling, inversion, positivity, and removal of all dependence on the
original nonnegative initial slope. -/
theorem equation30_inverted_riccati_error
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 / 2 →
      |(-ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y) ^ 2 -
        2 / (1 + y ^ 4)| ≤ 360 * ε := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hyhalf
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_riccati_error hε hεsmall hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 hinit.2.2 y ⟨le_rfl, hyhalf⟩

/-- The Wronskian flux of two solutions of `(D u')' = c u` is conserved. -/
theorem flux_wronskian_constant
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t) :
    ∀ t ∈ Icc a b,
      u t * (D t * v₁ t) - (D t * u₁ t) * v t =
        u a * (D a * v₁ a) - (D a * u₁ a) * v a := by
  have hw : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => u s * (D s * v₁ s) - (D s * u₁ s) * v s) 0 t := by
    intro t ht
    apply (((hu t ht).mul (hfv t ht)).sub ((hfu t ht).mul (hv t ht))).congr_deriv
    ring
  exact constant_of_has_deriv_right_zero
    (fun t ht => (hw t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

/-- The derivative of the quotient of two scalar solutions, expressed using
their initial Wronskian rather than either exponentially large solution. -/
theorem quotient_derivative_of_flux
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      HasDerivAt (fun s => v s / u s)
        ((u a * (D a * v₁ a) - (D a * u₁ a) * v a) / (D t * (u t) ^ 2)) t := by
  intro t ht
  apply ((hv t ht).div (hu t ht) (hupos t ht)).congr_deriv
  have hw := flux_wronskian_constant hu hv hfu hfv t ht
  calc
    (v₁ t * u t - v t * u₁ t) / (u t) ^ 2 =
        (u t * (D t * v₁ t) - (D t * u₁ t) * v t) / (D t * (u t) ^ 2) := by
      field_simp [hD t ht, hupos t ht]
    _ = _ := by rw [hw]

/-- The exact reduction-of-order formula on a closed interval.  Its integral
contains the reciprocal square of the positive reference solution. -/
theorem reduction_of_order
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v t = u t * (v a / u a +
        (u a * (D a * v₁ a) - (D a * u₁ a) * v a) *
          ∫ s in a..t, 1 / (D s * (u s) ^ 2)) := by
  intro t ht
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have huc : ContinuousOn u (Icc a b) :=
    fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / (D s * (u s) ^ 2)) (Icc a b) :=
    continuousOn_const.div (hDc.mul (huc.pow 2))
      (fun s hs => mul_ne_zero (hD s hs) (pow_ne_zero 2 (hupos s hs)))
  have hii : IntervalIntegrable (fun s => 1 / (D s * (u s) ^ 2))
      MeasureTheory.volume a t := (hic.mono hsubset).intervalIntegrable
  have hdi := hii.const_mul (u a * (D a * v₁ a) - (D a * u₁ a) * v a)
  have hd := quotient_derivative_of_flux hu hv hfu hfv hD hupos
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => (hd s (hsubset hs)).congr_deriv
      (by simp only [div_eq_mul_inv]; ring)) hdi
  rw [intervalIntegral.integral_const_mul] at hint
  have hune : u t ≠ 0 := hupos t ht
  have hratio : v t / u t = v a / u a +
      (u a * (D a * v₁ a) - (D a * u₁ a) * v a) *
        ∫ s in a..t, 1 / (D s * (u s) ^ 2) := by linarith
  rw [← hratio]
  field_simp

/-- Positivity and decrease of the inverted scalar solution for every
positive inversion coordinate. -/
theorem invertedScalar_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 →
      invertedScalar ε V 1 ≤ invertedScalar ε V y ∧
      0 < invertedScalar ε V y ∧ invertedScalarDeriv ε V V₁ y < 0 := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hy1
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_positive (sq_pos_of_pos hε) (by nlinarith : ε ^ 2 ≤ 1) hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 y ⟨le_rfl, hy1⟩

/-- Growth remains at least the value at `x=1` divided by `x` after
inversion.  This is the lower bound used in the exponential gain estimate. -/
theorem equation30_post_inversion_lower
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ x, 1 ≤ x → V (1 / ε) / x ≤ V (x / ε) ∧ 0 < V (x / ε) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := (div_le_one hxpos).mpr hx
  have hp := invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0 (1 / x) hypos hy1
  have hid : invertedScalar ε V (1 / x) = x * V (x / ε) := by
    simp [invertedScalar, one_div, div_inv_eq_mul, mul_comm]
  have hid1 : invertedScalar ε V 1 = V (1 / ε) := by simp [invertedScalar]
  rw [hid, hid1] at hp
  constructor
  · apply (div_le_iff₀ hxpos).mpr
    nlinarith [hp.1]
  · exact pos_of_mul_pos_right hp.2.1 hxpos.le

/-- A solution with the source's initial conditions stays positive for every
nonnegative original time, including beyond the inversion point. -/
theorem equation30_global_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 0 ≤ t → 0 < V t := by
  intro t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    exact (equation30_positive (sq_nonneg ε) (by nlinarith) hT hscale
      (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨ht, hpre⟩).1
  · have hx : 1 ≤ ε * t := by
      have := (div_le_iff₀ hε).mp (le_of_not_ge hpre)
      nlinarith
    have hp := (equation30_post_inversion_lower hε hεsmall hV hflux hV0 hV₁0 (ε * t) hx).2
    simpa only [mul_div_cancel_left₀ t hεne] using hp

/-- Reduction of order in the source's normalization `V₀(0)=1`,
`V₀'(0)=0`, `Vλ(0)=1`, `Vλ'(0)=λ`. -/
theorem equation30_reduction_of_order
    {ε lam : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV0 : V 0 = 1) (hV₁0 : V₁ 0 = lam) :
    ∀ t, 0 ≤ t → V t = U t *
      (1 + lam * ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2)) := by
  have hup := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  intro t ht
  have hr := reduction_of_order
    (a := 0) (b := t)
    (D := fun s => 1 + (ε ^ 2 * s ^ 2) ^ 2)
    (c := fun s => 2 * (1 - ε ^ 2 * (ε ^ 2 * s ^ 2)))
    (fun s hs => hU s hs.1) (fun s hs => hV s hs.1)
    (fun s hs => hfluxU s hs.1) (fun s hs => hfluxV s hs.1)
    (by fun_prop) (fun _ _ => ne_of_gt (by positivity))
    (fun s hs => ne_of_gt (hup s hs.1)) t ⟨ht, le_rfl⟩
  simpa [hU0, hU₁0, hV0, hV₁0] using hr

/-- A fixed upper bound for the zero-slope reference solution on `[0,1]`. -/
theorem equation30_zero_slope_prefix_upper
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t ∈ Icc 0 1, HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t ∈ Icc 0 1, U t ≤ exp 3 := by
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith) (by norm_num : (0 : ℝ) ≤ 1)
    (by simp only [one_pow, mul_one]; nlinarith : ε ^ 2 * (1 : ℝ) ^ 2 ≤ 1)
    hU hfluxU hU0 (by rw [hU₁0])
  have hsum : ∀ t ∈ Icc 0 1,
      U t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t ≤ exp (3 * t) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => U t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t)
      (f' := fun t => U₁ t + 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t)
      (B := fun t => exp (3 * t)) (B' := fun t => 3 * exp (3 * t))
      (fun t ht => ((hU t ht).add (hfluxU t ht)).continuousAt.continuousWithinAt)
      (fun t ht => ((hU t (Ico_subset_Icc_self ht)).add
        (hfluxU t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (by simp [hU0, hU₁0])
      (fun t => by
        apply (((hasDerivAt_id t).const_mul 3).exp).congr_deriv
        dsimp
        ring)
    intro t ht hboundary
    have hti := Ico_subset_Icc_self ht
    have hpt := hp t hti
    have hD : 1 ≤ 1 + (ε ^ 2 * t ^ 2) ^ 2 := by nlinarith [sq_nonneg (ε ^ 2 * t ^ 2)]
    have hfirst := mul_le_mul_of_nonneg_right hD hpt.2
    have hc : 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) ≤ 2 := by
      nlinarith [mul_nonneg (sq_nonneg ε) (mul_nonneg (sq_nonneg ε) (sq_nonneg t))]
    have hsecond := mul_le_mul_of_nonneg_right hc hpt.1.le
    have hFn : 0 ≤ (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t := mul_nonneg (by positivity) hpt.2
    nlinarith [exp_pos (3 * t)]
  intro t ht
  have hpt := hp t ht
  have hFn : 0 ≤ (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t := mul_nonneg (by positivity) hpt.2
  have he : exp (3 * t) ≤ exp 3 := exp_le_exp.mpr (by linarith [ht.2])
  linarith [hsum t ht]

/-- The reduction-of-order integral at time `1` has a positive absolute
lower bound.  No numerical approximations occur in the constant. -/
theorem equation30_reduction_integral_one_lower
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t ∈ Icc 0 1, HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    1 / (2 * exp 6) ≤
      ∫ s in (0 : ℝ)..1, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith) (by norm_num : (0 : ℝ) ≤ 1)
    (by simp only [one_pow, mul_one]; nlinarith : ε ^ 2 * (1 : ℝ) ^ 2 ≤ 1)
    hU hfluxU hU0 (by rw [hU₁0])
  have hu := equation30_zero_slope_prefix_upper hε hεsmall hU hfluxU hU0 hU₁0
  have huc : ContinuousOn U (Icc 0 1) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      (Icc 0 1) := by
    apply continuousOn_const.div
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => 1 + (ε ^ 2 * s ^ 2) ^ 2) (Icc 0 1)).mul
        (huc.pow 2)
    · intro t ht
      exact ne_of_gt (mul_pos (by positivity) (sq_pos_of_pos (hp t ht).1))
  have hint : IntervalIntegrable (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hic
  have hbound : ∀ t ∈ Icc 0 1,
      1 / (2 * exp 6) ≤ 1 / ((1 + (ε ^ 2 * t ^ 2) ^ 2) * (U t) ^ 2) := by
    intro t ht
    have hpt := hp t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have heps : ε ^ 2 ≤ 1 := by nlinarith
    have hinside : 0 ≤ ε ^ 2 * t ^ 2 ∧ ε ^ 2 * t ^ 2 ≤ 1 := by
      constructor
      · positivity
      · nlinarith [mul_nonneg (sub_nonneg.mpr heps) (sq_nonneg t)]
    have hD : 1 + (ε ^ 2 * t ^ 2) ^ 2 ≤ 2 := by nlinarith [hinside.1, hinside.2]
    have hUsq : (U t) ^ 2 ≤ (exp 3) ^ 2 := (sq_le_sq₀ hpt.1.le (exp_pos 3).le).mpr (hu t ht)
    have hprod := mul_le_mul hD hUsq (sq_nonneg (U t)) (by norm_num : (0 : ℝ) ≤ 2)
    have he : (exp (3 : ℝ)) ^ 2 = exp 6 := by
      rw [pow_two, ← exp_add]
      norm_num
    rw [he] at hprod
    exact one_div_le_one_div_of_le
      (mul_pos (by positivity) (sq_pos_of_pos hpt.1)) hprod
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / (2 * exp 6))
      MeasureTheory.volume 0 1) hint hbound
  simpa using hi

/-- The same absolute lower bound holds for the reduction integral at every
later time, because its integrand is nonnegative. -/
theorem equation30_reduction_integral_lower
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t, 1 ≤ t → 1 / (2 * exp 6) ≤
      ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hI1 := equation30_reduction_integral_one_lower hε hεsmall
    (fun s hs => hU s hs.1) (fun s hs => hfluxU s hs.1) hU0 hU₁0
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have huc : ContinuousOn U (Icc 0 t) := fun s hs => (hU s hs.1).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      (Icc 0 t) := by
    apply continuousOn_const.div
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => 1 + (ε ^ 2 * s ^ 2) ^ 2) (Icc 0 t)).mul
        (huc.pow 2)
    · intro s hs
      exact ne_of_gt (mul_pos (by positivity) (sq_pos_of_pos (hpos s hs.1)))
  have hint : IntervalIntegrable (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ht0] using hic
  have hmono := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) (b := 1)
    (c := (0 : ℝ)) (d := t) le_rfl zero_le_one ht
    (Filter.Eventually.of_forall (fun s : ℝ => by positivity)) hint
  exact hI1.trans hmono

/-- The solution with slope `lam ≥ 0` dominates the zero-slope reference
solution by a fixed multiple of `(1+lam)` after time `1`. -/
theorem equation30_slope_uniform_lower
    {ε lam : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV0 : V 0 = 1) (hV₁0 : V₁ 0 = lam) :
    ∀ t, 1 ≤ t → ((1 + lam) / (2 * exp 6)) * U t ≤ V t := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  rw [equation30_reduction_of_order hε hεsmall hU hV hfluxU hfluxV hU0 hU₁0 hV0 hV₁0 t ht0]
  have hI := equation30_reduction_integral_lower hε hεsmall hU hfluxU hU0 hU₁0 t ht
  have hc : 1 / (2 * exp 6) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * exp 6)).mpr
    linarith [add_one_le_exp (6 : ℝ)]
  have hi : (1 + lam) / (2 * exp 6) ≤
      1 + lam * ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hI hlam
    simp only [div_eq_mul_inv] at hc hm ⊢
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hi (hpos t ht0).le]

/-- Before `x=1`, the original scalar solution is nondecreasing. -/
theorem equation30_prefix_monotone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    MonotoneOn V (Icc 0 (1 / ε)) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith)
    (by positivity : 0 ≤ 1 / ε) hscale
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / ε))
    (fun t ht => (hV t ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hV t (interior_subset ht).1).hasDerivWithinAt)
  intro t ht
  exact (hp t (interior_subset ht)).2

/-- In inversion coordinates the scalar solution is nonincreasing. -/
theorem invertedScalar_antitone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    AntitoneOn (invertedScalar ε V) (Ioc 0 1) := by
  have hd : ∀ y ∈ Ioc 0 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ y) y := by
    intro y hy
    have harg : 0 ≤ y⁻¹ / ε := div_nonneg (inv_nonneg.mpr hy.1.le) hε.le
    exact (invertedScalar_equations (ne_of_gt hε) (ne_of_gt hy.1)
      (hV _ harg) (hflux _ harg)).1
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc (0 : ℝ) 1)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
  intro y hy
  have hyy := interior_subset hy
  exact (invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0 y hyy.1 hyy.2).2.2.le

/-- After `x=1`, the product `t V(t)` is nondecreasing. -/
theorem equation30_weighted_monotone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    MonotoneOn (fun t => t * V t) (Ici (1 / ε)) := by
  have hanti := invertedScalar_antitone hε hεsmall hV hflux hV0 hV₁0
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcalc : ∀ r : ℝ, invertedScalar ε V (1 / (ε * r)) = ε * (r * V r) := by
    intro r
    have harg : (1 / (ε * r))⁻¹ / ε = r := by rw [one_div, inv_inv]; field_simp
    rw [invertedScalar, harg, one_div, div_inv_eq_mul]
    ring
  intro s hs t ht hst
  have hthreshold : 0 < 1 / ε := by positivity
  have hspos : 0 < s := hthreshold.trans_le hs
  have htpos : 0 < t := hthreshold.trans_le ht
  have hεs : 1 ≤ ε * s := by have := (div_le_iff₀ hε).mp hs; nlinarith
  have hεt : 1 ≤ ε * t := by have := (div_le_iff₀ hε).mp ht; nlinarith
  have hys : 1 / (ε * s) ∈ Ioc 0 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hεs⟩
  have hyt : 1 / (ε * t) ∈ Ioc 0 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hεt⟩
  have hyorder : 1 / (ε * t) ≤ 1 / (ε * s) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hst hε.le)
  have hm := hanti hyt hys hyorder
  rw [hcalc s, hcalc t] at hm
  exact (mul_le_mul_iff_right₀ hε).mp hm

/-- The reference solution can decrease only by a polynomial factor on a
bounded time interval.  This is the ratio estimate used in the relative
propagator argument. -/
theorem equation30_relative_ratio
    {ε Θ : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ Θ → V s ≤ Θ * V t := by
  have hpos := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0
  have hpre := equation30_prefix_monotone hε hεsmall hV hflux hV0 hV₁0
  have hpost := equation30_weighted_monotone hε hεsmall hV hflux hV0 hV₁0
  have hthreshold : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hthreshold0 : 0 ≤ 1 / ε := by positivity
  intro s t hs hst ht
  have ht0 : 0 ≤ t := hs.trans hst
  have htpos := hpos t ht0
  by_cases htp : t ≤ 1 / ε
  · have hm := hpre ⟨hs, hst.trans htp⟩ ⟨ht0, htp⟩ hst
    nlinarith
  · have htpost : 1 / ε ≤ t := le_of_not_ge htp
    by_cases hsp : s ≤ 1 / ε
    · have hbefore := hpre ⟨hs, hsp⟩ ⟨hthreshold0, le_rfl⟩ hsp
      have hafter := hpost (show 1 / ε ∈ Ici (1 / ε) by simp) htpost htpost
      have hmidpos := hpos (1 / ε) hthreshold0
      nlinarith
    · have hspost : 1 / ε ≤ s := le_of_not_ge hsp
      have hm := hpost hspost htpost hst
      have hspos := hpos s hs
      nlinarith

/-- The exact logarithmic-derivative equation wherever the scalar solution
does not vanish. -/
theorem equation30_hasDerivAt_logderivative
    {ε t : ℝ} {V V₁ : ℝ → ℝ}
    (hV : HasDerivAt V (V₁ t) t)
    (hflux : HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hVne : V t ≠ 0) :
    HasDerivAt (fun s => V₁ s / V s)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) / (1 + (ε ^ 2 * t ^ 2) ^ 2) -
        (4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2)) * (V₁ t / V t) -
        (V₁ t / V t) ^ 2) t := by
  have hDne : 1 + (ε ^ 2 * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply ((equation30_second_derivative hflux).div hV hVne).congr_deriv
  field_simp

/-- The derivative of `t V(t)` is strictly positive after inversion. -/
theorem equation30_post_inversion_positive_derivative
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 1 / ε ≤ t → 0 < V t + t * V₁ t := by
  intro t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 1 / ε) ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hεt : 1 ≤ ε * t := by have := (div_le_iff₀ hε).mp ht; nlinarith
  have hypos : 0 < 1 / (ε * t) := by positivity
  have hy1 : 1 / (ε * t) ≤ 1 := (div_le_one (by positivity)).mpr hεt
  have hp := (invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0
    (1 / (ε * t)) hypos hy1).2.2
  have harg : (1 / (ε * t))⁻¹ / ε = t := by rw [one_div, inv_inv]; field_simp
  have heq : invertedScalarDeriv ε V V₁ (1 / (ε * t)) =
      -((ε * t) ^ 2 * (V t + t * V₁ t)) := by
    rw [invertedScalarDeriv, harg]
    field_simp
    ring
  rw [heq] at hp
  have hprod : 0 < (ε * t) ^ 2 * (V t + t * V₁ t) := by linarith
  exact pos_of_mul_pos_right hprod (sq_nonneg _)

/-- A uniform absolute logarithmic-derivative bound for the zero-slope
reference solution, valid on the whole forward interval. -/
theorem equation30_zero_slope_logderivative_bound
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t, 0 ≤ t → |U₁ t / U t| ≤ 2 := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hupper : ∀ t, 0 ≤ t → U₁ t / U t ≤ 2 := by
    intro T hT
    have hd : ∀ t ∈ Icc 0 T,
        HasDerivAt (fun s => U₁ s / U s)
          (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) / (1 + (ε ^ 2 * t ^ 2) ^ 2) -
            (4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2)) * (U₁ t / U t) -
            (U₁ t / U t) ^ 2) t :=
      fun t ht => equation30_hasDerivAt_logderivative (hU t ht.1) (hfluxU t ht.1)
        (ne_of_gt (hpos t ht.1))
    have hfence := image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (B := fun _ => 2) (B' := fun _ => 0)
      (by simp [hU0, hU₁0]) (fun t => hasDerivAt_const t 2)
      (fun t ht hboundary => by
        have ht0 := ht.1
        have hDpos : 0 < 1 + (ε ^ 2 * t ^ 2) ^ 2 := by positivity
        have hDge : 1 ≤ 1 + (ε ^ 2 * t ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (ε ^ 2 * t ^ 2)]
        have hquo : 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) /
            (1 + (ε ^ 2 * t ^ 2) ^ 2) ≤ 2 := by
          apply (div_le_iff₀ hDpos).mpr
          nlinarith [mul_nonneg (sq_nonneg ε) (mul_nonneg (sq_nonneg ε) (sq_nonneg t))]
        have hcoef : 0 ≤ 4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2) := by positivity
        rw [hboundary]
        nlinarith)
    exact hfence ⟨hT, le_rfl⟩
  intro t ht
  apply abs_le.mpr
  refine ⟨?_, hupper t ht⟩
  by_cases hpre : t ≤ 1 / ε
  · have hεne : ε ≠ 0 := ne_of_gt hε
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := (equation30_positive (sq_nonneg ε) (by nlinarith)
      (by positivity : 0 ≤ 1 / ε) hscale
      (fun s hs => hU s hs.1) (fun s hs => hfluxU s hs.1) hU0 (by rw [hU₁0]) t ⟨ht, hpre⟩).2
    have hq := div_nonneg hp (hpos t ht).le
    linarith
  · have htpost : 1 / ε ≤ t := le_of_not_ge hpre
    have ht1 : 1 ≤ t := by
      have hbase : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
      exact hbase.trans htpost
    have hcomb := equation30_post_inversion_positive_derivative hε hεsmall hU hfluxU hU0
      (by rw [hU₁0]) t htpost
    have hprod : 0 < t * (U₁ t + U t) := by nlinarith [hpos t ht]
    have hsum := pos_of_mul_pos_right hprod ht
    apply (le_div_iff₀ (hpos t ht)).mpr
    linarith [hpos t ht]

/-- Reduction of order normalized by the reference value at the initial
time.  This is the form used for relative, rather than absolute, stability. -/
theorem reduction_of_order_relative
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v t = (u t / u a) * (v a + D a * (v₁ a - (u₁ a / u a) * v a) *
        ∫ s in a..t, (u a / u s) ^ 2 / D s) := by
  intro t ht
  have hane : u a ≠ 0 := hupos a ⟨le_rfl, ht.1.trans ht.2⟩
  have hint : (∫ s in a..t, (u a / u s) ^ 2 / D s) =
      (u a) ^ 2 * ∫ s in a..t, 1 / (D s * (u s) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hint, reduction_of_order hu hv hfu hfv hDc hD hupos t ht]
  field_simp

/-- The derivative counterpart of normalized reduction of order. -/
theorem reduction_of_order_derivative_relative
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v₁ t = (u₁ t / u t) * v t +
        (u a / u t) * D a * (v₁ a - (u₁ a / u a) * v a) / D t := by
  intro t ht
  have hane : u a ≠ 0 := hupos a ⟨le_rfl, ht.1.trans ht.2⟩
  have hw := flux_wronskian_constant hu hv hfu hfv t ht
  field_simp [hupos t ht, hD t ht]
  nlinarith [hw]

/-- A polynomial bound for the normalized reduction integral. -/
theorem relative_reduction_integral_bound
    {D u : ℝ → ℝ} {a b Θ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hDc : ContinuousOn D (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hD : ∀ s ∈ Icc a b, 1 ≤ D s)
    (hu : ∀ s ∈ Icc a b, 0 < u s)
    (hratio : ∀ s ∈ Icc a b, u a ≤ Θ * u s) :
    0 ≤ (∫ s in a..b, (u a / u s) ^ 2 / D s) ∧
      (∫ s in a..b, (u a / u s) ^ 2 / D s) ≤ Θ ^ 3 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcont : ContinuousOn (fun s => (u a / u s) ^ 2 / D s) (Icc a b) :=
    ((continuousOn_const.div huc (fun s hs => ne_of_gt (hu s hs))).pow 2).div hDc
      (fun s hs => ne_of_gt (lt_of_lt_of_le zero_lt_one (hD s hs)))
  have hint : IntervalIntegrable (fun s => (u a / u s) ^ 2 / D s) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hcont
  have hbound : ∀ s ∈ Icc a b, (u a / u s) ^ 2 / D s ≤ Θ ^ 2 := by
    intro s hs
    have hq0 : 0 ≤ u a / u s := div_nonneg (hu a haI).le (hu s hs).le
    have hq : u a / u s ≤ Θ := (div_le_iff₀ (hu s hs)).mpr (hratio s hs)
    have hΘ0 : 0 ≤ Θ := hq0.trans hq
    have hq2 : (u a / u s) ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hq0 hΘ0).mpr hq
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD s hs))).mpr
    have hm := mul_le_mul_of_nonneg_left (hD s hs) (sq_nonneg Θ)
    nlinarith
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro s hs
    exact div_nonneg (sq_nonneg _) (le_trans zero_le_one (hD s hs))
  · have hi := intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Θ ^ 2) MeasureTheory.volume a b) hbound
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ Θ by linarith) (sq_nonneg Θ)
    nlinarith

/-- A relative propagator estimate with an explicit polynomial loss.
The large reference amplitude enters only through `u b / u a`. -/
theorem relative_propagator_bound
    {D c u u₁ v v₁ : ℝ → ℝ} {a b Θ : ℝ}
    (hΘ : 1 ≤ Θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, 1 ≤ D t ∧ D t ≤ 2 * Θ ^ 4)
    (hupos : ∀ t ∈ Icc a b, 0 < u t)
    (hlog : ∀ t ∈ Icc a b, |u₁ t / u t| ≤ 2)
    (hratio : ∀ t ∈ Icc a b, u a ≤ Θ * u t) :
    |v b| + |v₁ b| ≤ 20 * Θ ^ 8 * (u b / u a) * (|v a| + |v₁ a|) := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have huane : u a ≠ 0 := ne_of_gt (hupos a haI)
  have hubne : u b ≠ 0 := ne_of_gt (hupos b hbI)
  have hDne : ∀ t ∈ Icc a b, D t ≠ 0 :=
    fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one (hD t ht).1)
  have huc : ContinuousOn u (Icc a b) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  let N : ℝ := |v a| + |v₁ a|
  let E : ℝ := v₁ a - (u₁ a / u a) * v a
  let R : ℝ := u b / u a
  let J : ℝ := ∫ s in a..b, (u a / u s) ^ 2 / D s
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hR : 0 < R := div_pos (hupos b hbI) (hupos a haI)
  have hJ := relative_reduction_integral_bound ha hab hb hDc huc
    (fun t ht => (hD t ht).1) hupos hratio
  change 0 ≤ J ∧ J ≤ Θ ^ 3 at hJ
  have hE : |E| ≤ 2 * N := by
    calc
      |E| ≤ |v₁ a| + |(u₁ a / u a) * v a| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (v₁ a) ((u₁ a / u a) * v a)
      _ = |v₁ a| + |u₁ a / u a| * |v a| := by rw [abs_mul]
      _ ≤ |v₁ a| + 2 * |v a| := by
        linarith [mul_le_mul_of_nonneg_right (hlog a haI) (abs_nonneg (v a))]
      _ ≤ 2 * N := by dsimp [N]; linarith [abs_nonneg (v₁ a)]
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hpow78 : Θ ^ 7 ≤ Θ ^ 8 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow68 : Θ ^ 6 ≤ Θ ^ 8 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow8 : 1 ≤ Θ ^ 8 := one_le_pow₀ hΘ
  have hDNJ : D a * |E| * J ≤ 4 * Θ ^ 8 * N := by
    have hm := mul_le_mul
      (mul_le_mul (hD a haI).2 hE (abs_nonneg _) (by positivity)) hJ.2 hJ.1 (by positivity)
    have hp := mul_le_mul_of_nonneg_right hpow78 (show 0 ≤ 4 * N by positivity)
    nlinarith
  have hval := reduction_of_order_relative hu hv hfu hfv hDc hDne
    (fun t ht => ne_of_gt (hupos t ht)) b hbI
  change v b = R * (v a + D a * E * J) at hval
  have hvbound : |v b| ≤ R * (5 * Θ ^ 8 * N) := by
    rw [hval, abs_mul, abs_of_pos hR]
    apply mul_le_mul_of_nonneg_left _ hR.le
    have htri := abs_add_le (v a) (D a * E * J)
    have hDan : 0 ≤ D a := le_trans zero_le_one (hD a haI).1
    rw [abs_mul, abs_mul, abs_of_nonneg hDan, abs_of_nonneg hJ.1] at htri
    have hn : |v a| ≤ N := by dsimp [N]; linarith [abs_nonneg (v₁ a)]
    have hp := mul_le_mul_of_nonneg_right hpow8 hN
    nlinarith
  have hq0 : 0 ≤ u a / u b := div_nonneg (hupos a haI).le (hupos b hbI).le
  have hq : u a / u b ≤ Θ := (div_le_iff₀ (hupos b hbI)).mpr (hratio b hbI)
  have hq2 : (u a / u b) ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hq0 hΘ0).mpr hq
  have hsecond : (u a / u b) ^ 2 * D a * |E| / D b ≤ 4 * Θ ^ 8 * N := by
    have hnum : (u a / u b) ^ 2 * D a * |E| ≤ 4 * Θ ^ 8 * N := by
      have hm := mul_le_mul
        (mul_le_mul hq2 (hD a haI).2 (le_trans zero_le_one (hD a haI).1) (sq_nonneg Θ))
        hE (abs_nonneg _) (by positivity)
      have hp := mul_le_mul_of_nonneg_right hpow68 (show 0 ≤ 4 * N by positivity)
      nlinarith
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD b hbI).1)).mpr
    have hm := mul_le_mul_of_nonneg_left (hD b hbI).1 (show 0 ≤ 4 * Θ ^ 8 * N by positivity)
    nlinarith
  have hder := reduction_of_order_derivative_relative hu hv hfu hfv hDne
    (fun t ht => ne_of_gt (hupos t ht)) b hbI
  have heq : (u a / u b) * D a * E / D b = R * ((u a / u b) ^ 2 * D a * E / D b) := by
    dsimp [R]
    field_simp
  change v₁ b = (u₁ b / u b) * v b + (u a / u b) * D a * E / D b at hder
  rw [heq] at hder
  have hv₁bound : |v₁ b| ≤ 2 * |v b| + R * (4 * Θ ^ 8 * N) := by
    rw [hder]
    calc
      |(u₁ b / u b) * v b + R * ((u a / u b) ^ 2 * D a * E / D b)|
          ≤ |(u₁ b / u b) * v b| + |R * ((u a / u b) ^ 2 * D a * E / D b)| := abs_add_le _ _
      _ = |u₁ b / u b| * |v b| + R * ((u a / u b) ^ 2 * D a * |E| / D b) := by
        simp only [abs_mul, abs_div, abs_pow, abs_of_pos hR,
          abs_of_pos (hupos a haI), abs_of_pos (hupos b hbI),
          abs_of_nonneg (le_trans zero_le_one (hD a haI).1),
          abs_of_nonneg (le_trans zero_le_one (hD b hbI).1)]
      _ ≤ 2 * |v b| + R * (4 * Θ ^ 8 * N) := by
        exact add_le_add (mul_le_mul_of_nonneg_right (hlog b hbI) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hsecond hR.le)
  change |v b| + |v₁ b| ≤ 20 * Θ ^ 8 * R * N
  have hRN : 0 ≤ Θ ^ 8 * R * N := by positivity
  nlinarith

/-- The ideal scalar propagator has only a polynomial loss relative to the
zero-slope growing solution.  This proves the reference propagator estimate
used before (32), with the explicit constant `20`. -/
theorem equation30_relative_propagator
    {ε Θ a b : ℝ} {U U₁ Y Y₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t) t) :
    |Y b| + |Y₁ b| ≤ 20 * Θ ^ 8 * (U b / U a) * (|Y a| + |Y₁ a|) := by
  have hp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hl := equation30_zero_slope_logderivative_bound hε hεsmall hU hfluxU hU0 hU₁0
  have hr := equation30_relative_ratio hε hεsmall hΘ hU hfluxU hU0 (by rw [hU₁0])
  apply relative_propagator_bound hΘ ha hab hb
    (fun t ht => hU t (ha.trans ht.1)) hY
    (fun t ht => hfluxU t (ha.trans ht.1)) hfluxY (by fun_prop)
  · intro t ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have htΘ : t ≤ Θ := ht.2.trans hb
    have heps4 : ε ^ 4 ≤ 1 := by
      simpa using pow_le_pow_left₀ hε.le (show ε ≤ 1 by linarith) 4
    have ht4 : t ^ 4 ≤ Θ ^ 4 := pow_le_pow_left₀ ht0 htΘ 4
    have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
    have hm := mul_le_mul heps4 ht4 (by positivity : 0 ≤ t ^ 4) (by norm_num : (0 : ℝ) ≤ 1)
    constructor <;> nlinarith [sq_nonneg (ε ^ 2 * t ^ 2)]
  · intro t ht
    exact hp t (ha.trans ht.1)
  · intro t ht
    exact hl t (ha.trans ht.1)
  · intro t ht
    exact hr a t ha ht.1 (ht.2.trans hb)

/-- The coarse upper barrier for the exact inverted Riccati equation. -/
theorem inverted_riccati_le_four
    {ε T : ℝ} {z : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hscale : ε * T ≤ 1)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (invertedRiccati ε t (z t)) t)
    (hz0 : z 0 ≤ 4) :
    ∀ t ∈ Icc 0 T, z t ≤ 4 := by
  apply riccati_le_four hz hz0
  · intro t ht
    have ht0 := ht.1
    have hDpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (1 - ε * t)),
      show 0 ≤ (1 - ε * t) ^ 4 by positivity]
  · intro t ht
    have hprod := mul_le_mul_of_nonneg_left ht.2.le hε.le
    have hprod0 := mul_nonneg hε.le ht.1
    have hy0 : 0 ≤ 1 - ε * t := by linarith
    have hy1 : 1 - ε * t ≤ 1 := by linarith
    have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
      simpa using pow_le_pow_left₀ hy0 hy1 3
    have hDpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hy3 (show 0 ≤ 4 * ε by positivity)
    nlinarith [show 0 ≤ (1 - ε * t) ^ 4 by positivity]

/-- The inverted logarithmic derivative remains in `[0,4]`, derived
directly from the scalar equation and its endpoint conditions. -/
theorem inversion_riccati_range
    {ε a : ℝ} {f f₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0)
    (hinit : -ε * f₁ 1 / f 1 ≤ 4) :
    ∀ y ∈ Icc a 1, 0 ≤ -ε * f₁ y / f y ∧ -ε * f₁ y / f y ≤ 4 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hp := inversion_positive (sq_pos_of_pos hε) (by nlinarith : ε ^ 2 ≤ 1)
    ha hf hflux hf1 hf₁1
  have hmirror : ∀ t ∈ Icc 0 ((1 - a) / ε), 1 - ε * t ∈ Icc a 1 := by
    intro t ht
    have hu : ε * t ≤ 1 - a := by
      have := (le_div_iff₀ hε).mp ht.2
      nlinarith
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith
  have hscale : ε * ((1 - a) / ε) ≤ 1 := by field_simp; linarith
  have hz : ∀ t ∈ Icc 0 ((1 - a) / ε),
      HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
        (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
    intro t ht
    exact hasDerivAt_inverted_logderivative hεne
      (ne_of_gt (hp (1 - ε * t) (hmirror t ht)).2.1)
      (hf _ (hmirror t ht)) (hflux _ (hmirror t ht))
  have hbound := inverted_riccati_le_four hε hεsmall hscale hz (by simpa using hinit)
  intro y hy
  have ht : (1 - y) / ε ∈ Icc 0 ((1 - a) / ε) :=
    ⟨div_nonneg (sub_nonneg.mpr hy.2) hε.le,
      div_le_div_of_nonneg_right (by linarith [hy.1]) hε.le⟩
  have heq : 1 - ε * ((1 - y) / ε) = y := by field_simp; ring
  constructor
  · exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hε.le) (hp y hy).2.2.le) (hp y hy).2.1.le
  · simpa only [heq] using hbound ((1 - y) / ε) ht

/-- The absolute Riccati range for the original scalar initial value problem. -/
theorem equation30_inverted_riccati_range
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 →
      0 ≤ -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y ∧
      -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y ≤ 4 := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hy1
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_riccati_range hε hεsmall hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 hinit.2.2 y ⟨le_rfl, hy1⟩

/-- The ideal next-frame numerator in inversion coordinates. -/
def idealFrameNumerator (ε y z : ℝ) : ℝ :=
  -1 + (1 + y ^ 4) * z ^ 2 + ε ^ 2 * y ^ 2 - 2 * ε * z * y ^ 3

/-- The ideal next-frame denominator divided by `x²`, where `y=1/x`. -/
def idealFrameDenominator (ε y z : ℝ) : ℝ :=
  1 - ε ^ 2 * y ^ 2 + 2 * ε * z * y ^ 3

/-- The two exact algebraic identities used for the ideal frame renewal. -/
theorem ideal_frame_identities {ε y z : ℝ} (hy : y ≠ 0) :
    (y⁻¹) ^ 2 + ε ^ 2 + (-2 * ε * y⁻¹) * (ε * y - z * y ^ 2) =
      idealFrameDenominator ε y z / y ^ 2 ∧
    -1 + ε ^ 2 * (y⁻¹) ^ 2 + (1 + (y⁻¹) ^ 4) * (ε * y - z * y ^ 2) ^ 2 +
      (y⁻¹) ^ 2 * (-2 * ε * y⁻¹) * (ε * y - z * y ^ 2) = idealFrameNumerator ε y z := by
  constructor <;> simp only [idealFrameDenominator, idealFrameNumerator] <;> field_simp <;> ring

/-- Explicit ideal frame-renewal bounds obtained from the Riccati estimate.
The constants are deliberately generous absolute constants. -/
theorem ideal_frame_bounds
    {ε y z : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2) (hz : 0 ≤ z) (hzupper : z ≤ 4)
    (herr : |z ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε) :
    1 / 2 ≤ idealFrameDenominator ε y z ∧
      |idealFrameNumerator ε y z - 1| ≤ 730 * ε ∧
      |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
        y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
      |idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1| ≤ 1500 * ε := by
  have hy1 : y ≤ 1 := by linarith
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hy3 : y ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hy hy1 3
  have hy4 : y ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ hy hy1 4
  have hy3n : 0 ≤ y ^ 3 := by positivity
  have hy4n : 0 ≤ y ^ 4 := by positivity
  have hDpos : 0 < 1 + y ^ 4 := by positivity
  have hDn : 0 ≤ 1 + y ^ 4 := hDpos.le
  have hTn : 0 ≤ ε ^ 2 * y ^ 2 := by positivity
  have hTsmall : ε ^ 2 * y ^ 2 ≤ 1 / 16 := by
    have hm := mul_le_mul_of_nonneg_left hy2 (sq_nonneg ε)
    nlinarith
  have hTε : ε ^ 2 * y ^ 2 ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hy2 (sq_nonneg ε)
    nlinarith
  have hUn : 0 ≤ 2 * ε * z * y ^ 3 := by positivity
  have hUlocal : 2 * ε * z * y ^ 3 ≤ 8 * ε * y ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hzupper (show 0 ≤ 2 * ε * y ^ 3 by positivity)
    nlinarith
  have hUε : 2 * ε * z * y ^ 3 ≤ 8 * ε := by
    have hm := mul_le_mul_of_nonneg_left hy3 (show 0 ≤ 8 * ε by positivity)
    nlinarith
  have hB : 1 / 2 ≤ idealFrameDenominator ε y z := by
    unfold idealFrameDenominator
    nlinarith only [hTsmall, hUn]
  have hroot : 1 ≤ sqrt (1 + y ^ 4) := one_le_sqrt.mpr (by linarith)
  have hrootpos : 0 < sqrt (1 + y ^ 4) := by linarith
  have hrootupper : sqrt (1 + y ^ 4) ≤ 1 + y ^ 4 :=
    sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hDerr : |(1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4))| ≤ 720 * ε := by
    rw [abs_mul, abs_of_nonneg hDn]
    have hm := mul_le_mul_of_nonneg_left herr hDn
    have hu := mul_le_mul_of_nonneg_right (show 1 + y ^ 4 ≤ 2 by linarith)
      (show 0 ≤ 360 * ε by positivity)
    nlinarith only [hm, hu]
  have hNrewrite : idealFrameNumerator ε y z - 1 =
      (1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4)) + ε ^ 2 * y ^ 2 - 2 * ε * z * y ^ 3 := by
    unfold idealFrameNumerator
    field_simp
    ring
  have hN : |idealFrameNumerator ε y z - 1| ≤ 730 * ε := by
    rw [hNrewrite]
    obtain ⟨hl, hu⟩ := abs_le.mp hDerr
    apply abs_le.mpr
    constructor <;> nlinarith only [hl, hu, hTn, hTε, hUn, hUε, hε]
  have hA : |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
      y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 := by
    have heq : idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1 =
        (idealFrameDenominator ε y z - sqrt (1 + y ^ 4)) / sqrt (1 + y ^ 4) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hrootpos]
    apply (div_le_iff₀ hrootpos).mpr
    have hsmall : |idealFrameDenominator ε y z - sqrt (1 + y ^ 4)| ≤
        y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 := by
      unfold idealFrameDenominator
      apply abs_le.mpr
      have h8 : 0 ≤ 8 * ε * y ^ 3 := by positivity
      constructor <;> nlinarith only [hroot, hrootupper, hUlocal, hTn, hUn, hy4n, h8]
    have hm := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 by positivity)
    nlinarith only [hsmall, hm]
  refine ⟨hB, hN, hA, ?_⟩
  have hBpos : 0 < idealFrameDenominator ε y z := by linarith
  have heq : idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1 =
      (idealFrameNumerator ε y z - idealFrameDenominator ε y z) / idealFrameDenominator ε y z := by
    field_simp
  rw [heq, abs_div, abs_of_pos hBpos]
  apply (div_le_iff₀ hBpos).mpr
  have hdiff : |idealFrameNumerator ε y z - idealFrameDenominator ε y z| ≤ 739 * ε := by
    obtain ⟨hl, hu⟩ := abs_le.mp hN
    unfold idealFrameDenominator
    apply abs_le.mpr
    constructor <;> nlinarith only [hl, hu, hTn, hTε, hUn, hUε]
  have hm := mul_le_mul_of_nonneg_left hB (show 0 ≤ 1500 * ε by positivity)
  nlinarith only [hdiff, hm, hε]

/-- Ideal frame renewal follows from the scalar initial value problem;
the Riccati range and approximation are proved upstream in this file. -/
theorem equation30_ideal_frame_bounds
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 / 2 →
      let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
      1 / 2 ≤ idealFrameDenominator ε y z ∧
        |idealFrameNumerator ε y z - 1| ≤ 730 * ε ∧
        |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
          y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
        |idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1| ≤ 1500 * ε := by
  intro y hy hysmall
  have hr := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy (by linarith)
  have he := equation30_inverted_riccati_error hε hεsmall hV hflux hV0 hV₁0 y hy hysmall
  exact ideal_frame_bounds hε.le hεsmall hy.le hysmall hr.1 hr.2 he


end EulerPacketGrowth

end

section

/-!
Relative perturbation estimates for the finite-dimensional scalar ODE in the
Euler packet proposal.  These results do not assert the PDE packet lemma.
-/

namespace EulerPacketPerturbation

open Set Filter Real EulerPacketGrowth
open scoped Topology

/-- A compact-interval Volterra absorption estimate with an explicit factor
of two and no exponential loss. -/
theorem integral_absorb
    {g : ℝ → ℝ} {a b A K : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hgn : ∀ t ∈ Icc a b, 0 ≤ g t) (hK : 0 ≤ K)
    (hsmall : K * (b - a) ≤ 1 / 2)
    (hineq : ∀ t ∈ Icc a b, g t ≤ A + K * ∫ s in a..t, g s) :
    ∀ t ∈ Icc a b, g t ≤ 2 * A := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ⟨le_rfl, hab⟩⟩ hg
  have hsubset : uIcc a c ⊆ Icc a b := by
    rw [uIcc_of_le hc.1]
    exact Icc_subset_Icc le_rfl hc.2
  have hgi : IntervalIntegrable g MeasureTheory.volume a c :=
    (hg.mono hsubset).intervalIntegrable
  have hi := intervalIntegral.integral_mono_on hc.1 hgi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => g c) MeasureTheory.volume a c)
    (fun t ht => hmax (Icc_subset_Icc le_rfl hc.2 ht))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hKi := mul_le_mul_of_nonneg_left hi hK
  have hKc : K * (c - a) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hc.2 hK
    nlinarith
  have hmaxn : 0 ≤ g c := hgn c hc
  have hscaled := mul_le_mul_of_nonneg_right hKc hmaxn
  have hgc : g c ≤ 2 * A := by nlinarith [hineq c hc]
  intro t ht
  exact (hmax ht).trans hgc

/-- Absorbing a Duhamel inequality after division by a positive reference
solution.  This preserves relative rather than absolute control. -/
theorem relative_integral_absorb
    {f U : ℝ → ℝ} {a b A K : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hU : ContinuousOn U (Icc a b))
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hUp : ∀ t ∈ Icc a b, 0 < U t)
    (hK : 0 ≤ K) (hsmall : K * (b - a) ≤ 1 / 2)
    (hineq : ∀ t ∈ Icc a b,
      f t ≤ U t * (A + K * ∫ s in a..t, f s / U s)) :
    ∀ t ∈ Icc a b, f t ≤ 2 * A * U t := by
  have hg := integral_absorb (g := fun t => f t / U t) (A := A) (K := K) hab
    (hf.div hU (fun t ht => ne_of_gt (hUp t ht)))
    (fun t ht => div_nonneg (hfn t ht) (hUp t ht).le) hK hsmall
    (fun t ht => by
      apply (div_le_iff₀ (hUp t ht)).mpr
      convert! hineq t ht using 1
      ring)
  intro t ht
  exact (div_le_iff₀ (hUp t ht)).mp (hg t ht)

/-- The Wronskian of a homogeneous solution and a forced solution obeys an
exact first-order forcing identity. -/
theorem forced_wronskian_derivative
    {D c u u₁ Y Y₁ f g : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u₁ t) t)
    (hfu : HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hY : HasDerivAt Y (Y₁ t + f t) t)
    (hfY : HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t) :
    HasDerivAt (fun s => u s * (D s * Y₁ s) - (D s * u₁ s) * Y s)
      (D t * (u t * g t - u₁ t * f t)) t := by
  apply ((hu.mul hfY).sub (hfu.mul hY)).congr_deriv
  ring

/-- The integrated forced Wronskian identity. -/
theorem forced_wronskian_integral
    {D c u u₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b,
      u t * (D t * Y₁ t) - (D t * u₁ t) * Y t =
        u a * (D a * Y₁ a) - (D a * u₁ a) * Y a +
          ∫ s in a..t, D s * (u s * g s - u₁ s * f s) := by
  intro t ht
  have huc : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hcont := hDc.mul ((huc.mul hgc).sub (hu₁c.mul hfc))
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (hcont.mono hsubset).intervalIntegrable (μ := MeasureTheory.volume)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => forced_wronskian_derivative (hu s (hsubset hs)) (hfu s (hsubset hs))
      (hY s (hsubset hs)) (hfY s (hsubset hs))) hint
  linarith

/-- Variation of constants from two homogeneous solutions whose Wronskian
flux is normalized to one.  This handles forcing in both state components. -/
theorem forced_variation_of_constants
    {D c u u₁ v v₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hv₁c : ContinuousOn v₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hW0 : u a * (D a * v₁ a) - (D a * u₁ a) * v a = 1) :
    ∀ t ∈ Icc a b,
      let A := u a * (D a * Y₁ a) - (D a * u₁ a) * Y a +
        ∫ s in a..t, D s * (u s * g s - u₁ s * f s)
      let B := v a * (D a * Y₁ a) - (D a * v₁ a) * Y a +
        ∫ s in a..t, D s * (v s * g s - v₁ s * f s)
      Y t = v t * A - u t * B ∧ Y₁ t = v₁ t * A - u₁ t * B := by
  intro t ht
  have hWu := forced_wronskian_integral hu hfu hY hfY hDc hu₁c hfc hgc t ht
  have hWv := forced_wronskian_integral hv hfv hY hfY hDc hv₁c hfc hgc t ht
  have hW := flux_wronskian_constant hu hv hfu hfv t ht
  rw [hW0] at hW
  dsimp only
  rw [← hWu, ← hWv]
  constructor
  · nlinarith [congrArg (fun r : ℝ => r * Y t) hW]
  · nlinarith [congrArg (fun r : ℝ => r * Y₁ t) hW]

/-- First displacement component of the scalar fundamental propagator. -/
def kernel11 (D u u₁ v v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (u t * v₁ s - v t * u₁ s)

/-- First velocity component of the scalar fundamental propagator. -/
def kernel12 (D u v : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (v t * u s - u t * v s)

/-- Second displacement component of the scalar fundamental propagator. -/
def kernel21 (D u₁ v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (u₁ t * v₁ s - v₁ t * u₁ s)

/-- Second velocity component of the scalar fundamental propagator. -/
def kernel22 (D u u₁ v v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (v₁ t * u s - u₁ t * v s)

/-- Duhamel's formula in component form, with an explicitly defined
fundamental kernel. -/
theorem forced_kernel_formula
    {D c u u₁ v v₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hv₁c : ContinuousOn v₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hW0 : u a * (D a * v₁ a) - (D a * u₁ a) * v a = 1) :
    ∀ t ∈ Icc a b,
      Y t = kernel11 D u u₁ v v₁ t a * Y a + kernel12 D u v t a * Y₁ a +
        ∫ s in a..t, kernel11 D u u₁ v v₁ t s * f s + kernel12 D u v t s * g s ∧
      Y₁ t = kernel21 D u₁ v₁ t a * Y a + kernel22 D u u₁ v v₁ t a * Y₁ a +
        ∫ s in a..t, kernel21 D u₁ v₁ t s * f s + kernel22 D u u₁ v v₁ t s * g s := by
  intro t ht
  have huc : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) := fun s hs => (hv s hs).continuousAt.continuousWithinAt
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hIu := ((hDc.mul ((huc.mul hgc).sub (hu₁c.mul hfc))).mono hsubset).intervalIntegrable
    (μ := MeasureTheory.volume)
  have hIv := ((hDc.mul ((hvc.mul hgc).sub (hv₁c.mul hfc))).mono hsubset).intervalIntegrable
    (μ := MeasureTheory.volume)
  change IntervalIntegrable (fun s => D s * (u s * g s - u₁ s * f s)) MeasureTheory.volume a t at hIu
  change IntervalIntegrable (fun s => D s * (v s * g s - v₁ s * f s)) MeasureTheory.volume a t at hIv
  have hInt (A B : ℝ) :
      (∫ s in a..t, D s * (A * v₁ s - B * u₁ s) * f s +
        D s * (B * u s - A * v s) * g s) =
      B * (∫ s in a..t, D s * (u s * g s - u₁ s * f s)) -
        A * (∫ s in a..t, D s * (v s * g s - v₁ s * f s)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hIu.const_mul B) (hIv.const_mul A)]
    congr 1
    ext s
    ring
  have hvar := forced_variation_of_constants hu hv hfu hfv hY hfY hDc hu₁c hv₁c hfc hgc hW0 t ht
  dsimp only at hvar
  constructor
  · unfold kernel11 kernel12
    rw [hInt (u t) (v t), hvar.1]
    ring
  · unfold kernel21 kernel22
    rw [hInt (u₁ t) (v₁ t), hvar.2]
    ring

/-- Linear combinations of homogeneous scalar solutions are homogeneous. -/
theorem linear_combination_solution
    {D c u u₁ v v₁ : ℝ → ℝ} {t A B : ℝ}
    (hu : HasDerivAt u (u₁ t) t) (hv : HasDerivAt v (v₁ t) t)
    (hfu : HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : HasDerivAt (fun s => D s * v₁ s) (c t * v t) t) :
    HasDerivAt (fun s => A * u s + B * v s) (A * u₁ t + B * v₁ t) t ∧
    HasDerivAt (fun s => D s * (A * u₁ s + B * v₁ s))
      (c t * (A * u t + B * v t)) t := by
  constructor
  · exact (hu.const_mul A).add (hv.const_mul B)
  · convert! (hfu.const_mul A).add (hfv.const_mul B) using 1
    · ext s
      dsimp only [Pi.add_apply]
      ring
    · ring

/-- The ideal fundamental kernel inherits the relative propagator bound
in each column. -/
theorem equation30_kernel_bound
    {ε Θ : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ Θ →
      let D := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
      |kernel11 D U U₁ V V₁ t s| + |kernel21 D U₁ V₁ t s| ≤
        20 * Θ ^ 8 * (U t / U s) ∧
      |kernel12 D U V t s| + |kernel22 D U U₁ V V₁ t s| ≤
        20 * Θ ^ 8 * (U t / U s) := by
  intro s t hs hst ht
  let D : ℝ → ℝ := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
  let c : ℝ → ℝ := fun r => 2 * (1 - ε ^ 2 * (ε ^ 2 * r ^ 2))
  have hW : U s * (D s * V₁ s) - (D s * U₁ s) * V s = 1 := by
    have hw := flux_wronskian_constant
      (a := 0) (b := s) (D := D) (c := c)
      (fun r hr => hU r hr.1) (fun r hr => hV r hr.1)
      (fun r hr => hfluxU r hr.1) (fun r hr => hfluxV r hr.1) s ⟨hs, le_rfl⟩
    simpa [D, hU0, hU₁0, hV₁0] using hw
  have hlin (A B : ℝ) :
      |A * U t + B * V t| + |A * U₁ t + B * V₁ t| ≤
        20 * Θ ^ 8 * (U t / U s) *
          (|A * U s + B * V s| + |A * U₁ s + B * V₁ s|) := by
    exact equation30_relative_propagator hε hεsmall hΘ hs hst ht hU hfluxU hU0 hU₁0
      (fun r hr => (linear_combination_solution (A := A) (B := B) (D := D) (c := c)
        (hU r (hs.trans hr.1)) (hV r (hs.trans hr.1))
        (hfluxU r (hs.trans hr.1)) (hfluxV r (hs.trans hr.1))).1)
      (fun r hr => (linear_combination_solution (A := A) (B := B) (D := D) (c := c)
        (hU r (hs.trans hr.1)) (hV r (hs.trans hr.1))
        (hfluxU r (hs.trans hr.1)) (hfluxV r (hs.trans hr.1))).2)
  constructor
  · have hb := hlin (D s * V₁ s) (-(D s * U₁ s))
    have hfirst : D s * V₁ s * U s + -(D s * U₁ s) * V s = 1 := by nlinarith [hW]
    have hsecond : D s * V₁ s * U₁ s + -(D s * U₁ s) * V₁ s = 0 := by ring
    rw [hfirst, hsecond] at hb
    norm_num at hb
    convert! hb using 1
    congr 2 <;> dsimp [kernel11, kernel21, D] <;> ring
  · have hb := hlin (-(D s * V s)) (D s * U s)
    have hfirst : -(D s * V s) * U s + D s * U s * V s = 0 := by ring
    have hsecond : -(D s * V s) * U₁ s + D s * U s * V₁ s = 1 := by nlinarith [hW]
    rw [hfirst, hsecond] at hb
    norm_num at hb
    convert! hb using 1
    congr 2 <;> dsimp [kernel12, kernel22, D] <;> ring

/-- The induced sum-of-absolute-values bound from two column bounds. -/
theorem two_column_bound {a b c d x y C : ℝ}
    (h1 : |a| + |c| ≤ C) (h2 : |b| + |d| ≤ C) :
    |a * x + b * y| + |c * x + d * y| ≤ C * (|x| + |y|) := by
  have hfirst := abs_add_le (a * x) (b * y)
  have hsecond := abs_add_le (c * x) (d * y)
  simp only [abs_mul] at hfirst hsecond
  have hx := mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
  have hy := mul_le_mul_of_nonneg_right h2 (abs_nonneg y)
  nlinarith

/-- Passing from Duhamel's formula and relative kernel bounds to a scalar
relative integral inequality, with the forcing in both components. -/
theorem kernel_integral_bound
    {K11 K12 K21 K22 f g U : ℝ → ℝ} {a b y0 y₁0 y y₁ C : ℝ}
    (hab : a ≤ b)
    (h11 : ContinuousOn K11 (Icc a b)) (h12 : ContinuousOn K12 (Icc a b))
    (h21 : ContinuousOn K21 (Icc a b)) (h22 : ContinuousOn K22 (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hUc : ContinuousOn U (Icc a b)) (hUp : ∀ s ∈ Icc a b, 0 < U s)
    (hcol1 : ∀ s ∈ Icc a b, |K11 s| + |K21 s| ≤ C * (U b / U s))
    (hcol2 : ∀ s ∈ Icc a b, |K12 s| + |K22 s| ≤ C * (U b / U s))
    (hy : y = K11 a * y0 + K12 a * y₁0 + ∫ s in a..b, K11 s * f s + K12 s * g s)
    (hy₁ : y₁ = K21 a * y0 + K22 a * y₁0 + ∫ s in a..b, K21 s * f s + K22 s * g s) :
    |y| + |y₁| ≤ C * (U b / U a) * (|y0| + |y₁0|) +
      C * U b * ∫ s in a..b, (|f s| + |g s|) / U s := by
  have hc1 := (h11.mul hfc).add (h12.mul hgc)
  have hc2 := (h21.mul hfc).add (h22.mul hgc)
  have hi1 : IntervalIntegrable (fun s => |K11 s * f s + K12 s * g s|)
      MeasureTheory.volume a b := hc1.abs.intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun s => |K21 s * f s + K22 s * g s|)
      MeasureTheory.volume a b := hc2.abs.intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun s => |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s|)
      MeasureTheory.volume a b := hi1.add hi2
  have hquot : ContinuousOn (fun s => (|f s| + |g s|) / U s) (Icc a b) :=
    (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s hs))
  have hmajor : IntervalIntegrable (fun s => (C * U b) * ((|f s| + |g s|) / U s))
      MeasureTheory.volume a b :=
    (hquot.intervalIntegrable_of_Icc hab).const_mul (C * U b)
  have hpoint : ∀ s ∈ Icc a b,
      |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s| ≤
        C * U b * ((|f s| + |g s|) / U s) := by
    intro s hs
    convert! two_column_bound (x := f s) (y := g s) (hcol1 s hs) (hcol2 s hs) using 1
    ring
  have hmono := intervalIntegral.integral_mono_on hab hsum hmajor hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI : |∫ s in a..b, K11 s * f s + K12 s * g s| +
      |∫ s in a..b, K21 s * f s + K22 s * g s| ≤
      ∫ s in a..b, |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s| := by
    rw [intervalIntegral.integral_add hi1 hi2]
    exact add_le_add (intervalIntegral.abs_integral_le_integral_abs hab)
      (intervalIntegral.abs_integral_le_integral_abs hab)
  have hbase := two_column_bound (x := y0) (y := y₁0)
    (hcol1 a ⟨le_rfl, hab⟩) (hcol2 a ⟨le_rfl, hab⟩)
  have hfirst : |y| ≤ |K11 a * y0 + K12 a * y₁0| +
      |∫ s in a..b, K11 s * f s + K12 s * g s| := by rw [hy]; exact abs_add_le _ _
  have hsecond : |y₁| ≤ |K21 a * y0 + K22 a * y₁0| +
      |∫ s in a..b, K21 s * f s + K22 s * g s| := by rw [hy₁]; exact abs_add_le _ _
  linarith

/-- Duhamel's inequality for the exact scalar ODE, measured relative to the
zero-slope reference solution.  The forcing may occur in both components. -/
theorem equation30_forced_bound
    {ε Θ a b : ℝ} {U U₁ V V₁ Y Y₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hb : b ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
        20 * Θ ^ 8 * U t * ∫ s in a..t, (|f s| + |g s|) / U s := by
  let D : ℝ → ℝ := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
  let c : ℝ → ℝ := fun r => 2 * (1 - ε ^ 2 * (ε ^ 2 * r ^ 2))
  have hUc : ContinuousOn U (Icc a b) :=
    fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc a b) :=
    fun t ht => (hV t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hU₁c : ContinuousOn U₁ (Icc a b) :=
    fun t ht => (equation30_second_derivative (hfluxU t (ha.trans ht.1))).continuousAt.continuousWithinAt
  have hV₁c : ContinuousOn V₁ (Icc a b) :=
    fun t ht => (equation30_second_derivative (hfluxV t (ha.trans ht.1))).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Icc a b) := by fun_prop
  have hW : U a * (D a * V₁ a) - (D a * U₁ a) * V a = 1 := by
    have hw := flux_wronskian_constant
      (a := 0) (b := a) (D := D) (c := c)
      (fun r hr => hU r hr.1) (fun r hr => hV r hr.1)
      (fun r hr => hfluxU r hr.1) (fun r hr => hfluxV r hr.1) a ⟨ha, le_rfl⟩
    simpa [D, hU0, hU₁0, hV₁0] using hw
  have hformula := forced_kernel_formula
    (D := D) (c := c)
    (fun r hr => hU r (ha.trans hr.1)) (fun r hr => hV r (ha.trans hr.1))
    (fun r hr => hfluxU r (ha.trans hr.1)) (fun r hr => hfluxV r (ha.trans hr.1))
    hY hfluxY hDc hU₁c hV₁c hfc hgc hW
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hkernel := equation30_kernel_bound hε hεsmall hΘ hU hV hfluxU hfluxV hU0 hU₁0 hV₁0
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hUc' := hUc.mono hsub
  have hVc' := hVc.mono hsub
  have hU₁c' := hU₁c.mono hsub
  have hV₁c' := hV₁c.mono hsub
  have hDc' := hDc.mono hsub
  have h11 : ContinuousOn (kernel11 D U U₁ V V₁ t) (Icc a t) := by
    unfold kernel11
    exact hDc'.mul ((continuousOn_const.mul hV₁c').sub (continuousOn_const.mul hU₁c'))
  have h12 : ContinuousOn (kernel12 D U V t) (Icc a t) := by
    unfold kernel12
    exact hDc'.mul ((continuousOn_const.mul hUc').sub (continuousOn_const.mul hVc'))
  have h21 : ContinuousOn (kernel21 D U₁ V₁ t) (Icc a t) := by
    unfold kernel21
    exact hDc'.mul ((continuousOn_const.mul hV₁c').sub (continuousOn_const.mul hU₁c'))
  have h22 : ContinuousOn (kernel22 D U U₁ V V₁ t) (Icc a t) := by
    unfold kernel22
    exact hDc'.mul ((continuousOn_const.mul hUc').sub (continuousOn_const.mul hVc'))
  exact kernel_integral_bound ht.1 h11 h12 h21 h22 (hfc.mono hsub) (hgc.mono hsub) hUc'
    (fun s hs => hUp s (ha.trans hs.1))
    (fun s hs => (hkernel s t (ha.trans hs.1) hs.2 (ht.2.trans hb)).1)
    (fun s hs => (hkernel s t (ha.trans hs.1) hs.2 (ht.2.trans hb)).2)
    (hformula t ht).1 (hformula t ht).2

/-- Continuity of the second state component follows from continuity of its
nonvanishing flux coefficient and of the flux. -/
theorem continuousOn_of_flux
    {D f : ℝ → ℝ} {S : Set ℝ}
    (hD : ContinuousOn D S) (hf : ContinuousOn (fun t => D t * f t) S)
    (hDn : ∀ t ∈ S, D t ≠ 0) : ContinuousOn f S := by
  apply (hf.div hD hDn).congr
  intro t ht
  change f t = D t * f t / D t
  field_simp [hDn t ht]

/-- A sufficiently small perturbation grows by at most twice the ideal
relative propagator bound.  Smallness is an explicit interval inequality. -/
theorem equation30_perturbed_bound
    {ε Θ a b δ : ℝ} {U U₁ V V₁ Y Y₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (b - a) ≤ 1 / 2)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hforcing : ∀ t ∈ Icc a b, |f t| + |g t| ≤ δ * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ 40 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) := by
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hUa : 0 < U a := hUp a ha
  have hUc : ContinuousOn U (Icc a b) := fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hYc : ContinuousOn Y (Icc a b) := fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hY₁c : ContinuousOn Y₁ (Icc a b) := continuousOn_of_flux
    (D := fun s => 1 + (ε ^ 2 * s ^ 2) ^ 2) (by fun_prop)
    (fun t ht => (hfluxY t ht).continuousAt.continuousWithinAt)
    (fun _ _ => ne_of_gt (by positivity))
  have hNc := hYc.abs.add hY₁c.abs
  have hforcingBound := equation30_forced_bound hε hεsmall hΘ ha hb hU hV hfluxU hfluxV
    hU0 hU₁0 hV₁0 hY hfluxY hfc hgc
  have hineq : ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ U t *
        (20 * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a +
          (20 * Θ ^ 8 * δ) * ∫ s in a..t, (|Y s| + |Y₁ s|) / U s) := by
    intro t ht
    have hsub : uIcc a t ⊆ Icc a b := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hFcont := (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
    have hNcont := hNc.div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
    have hFi : IntervalIntegrable (fun s => (|f s| + |g s|) / U s) MeasureTheory.volume a t :=
      (hFcont.mono hsub).intervalIntegrable
    have hNi : IntervalIntegrable (fun s => δ * ((|Y s| + |Y₁ s|) / U s))
        MeasureTheory.volume a t := ((hNcont.mono hsub).intervalIntegrable).const_mul δ
    have hpoint : ∀ s ∈ Icc a t,
        (|f s| + |g s|) / U s ≤ δ * ((|Y s| + |Y₁ s|) / U s) := by
      intro s hs
      have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
      have hm := div_le_div_of_nonneg_right (hforcing s hsab) (hUp s (ha.trans hs.1)).le
      convert! hm using 1
      ring
    have hi := intervalIntegral.integral_mono_on ht.1 hFi hNi hpoint
    rw [intervalIntegral.integral_const_mul] at hi
    have hUt : 0 < U t := hUp t (ha.trans ht.1)
    have hscaled := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 20 * Θ ^ 8 * U t by positivity)
    calc
      |Y t| + |Y₁ t| ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
          20 * Θ ^ 8 * U t * ∫ s in a..t, (|f s| + |g s|) / U s := hforcingBound t ht
      _ ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
          20 * Θ ^ 8 * U t * (δ * ∫ s in a..t, (|Y s| + |Y₁ s|) / U s) :=
        add_le_add le_rfl hscaled
      _ = _ := by ring
  have hresult := relative_integral_absorb
    (f := fun t => |Y t| + |Y₁ t|) (U := U)
    (A := 20 * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a) (K := 20 * Θ ^ 8 * δ)
    hab hNc hUc (fun _ _ => by positivity) (fun t ht => hUp t (ha.trans ht.1))
    (by positivity) hsmall hineq
  intro t ht
  convert! hresult t ht using 1
  ring

/-- Quantitative difference from an ideal solution.  A perturbation of
size `δ = O(e Θ^12)` produces the source's `O(e Θ^29)` relative error. -/
theorem equation30_perturbed_difference_bound
    {ε Θ a b δ : ℝ} {U U₁ V V₁ Y Y₁ Z Z₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (b - a) ≤ 1 / 2)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hZ : ∀ t ∈ Icc a b, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hforcing : ∀ t ∈ Icc a b, |f t| + |g t| ≤ δ * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc a b,
      |Y t - Z t| + |Y₁ t - Z₁ t| ≤
        20 * Θ ^ 8 * (U t / U a) * (|Y a - Z a| + |Y₁ a - Z₁ a|) +
          800 * δ * Θ ^ 17 * (U t / U a) * (|Y a| + |Y₁ a|) := by
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hUa : 0 < U a := hUp a ha
  have hUc : ContinuousOn U (Icc a b) := fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hpert := equation30_perturbed_bound hε hεsmall hΘ ha hab hb hδ hsmall
    hU hV hfluxU hfluxV hU0 hU₁0 hV₁0 hY hfluxY hfc hgc hforcing
  have hE : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => Y s - Z s) ((Y₁ t - Z₁ t) + f t) t := by
    intro t ht
    apply ((hY t ht).sub (hZ t ht)).congr_deriv
    ring
  have hfluxE : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * (Y₁ s - Z₁ s))
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * (Y t - Z t) +
          (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t := by
    intro t ht
    convert! (hfluxY t ht).sub (hfluxZ t ht) using 1
    · ext s
      dsimp only [Pi.sub_apply]
      ring
    · ring
  have hforced := equation30_forced_bound hε hεsmall hΘ ha hb hU hV hfluxU hfluxV
    hU0 hU₁0 hV₁0 hE hfluxE hfc hgc
  intro t ht
  have hUt : 0 < U t := hUp t (ha.trans ht.1)
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hFcont := (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
  have hFi : IntervalIntegrable (fun s => (|f s| + |g s|) / U s) MeasureTheory.volume a t :=
    (hFcont.mono hsub).intervalIntegrable
  have hpoint : ∀ s ∈ Icc a t,
      (|f s| + |g s|) / U s ≤ 40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a := by
    intro s hs
    have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    have hspos := hUp s (ha.trans hs.1)
    apply (div_le_iff₀ hspos).mpr
    have hm := (hforcing s hsab).trans (mul_le_mul_of_nonneg_left (hpert s hsab) hδ)
    convert! hm using 1
    ring
  have hi := intervalIntegral.integral_mono_on ht.1 hFi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => 40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a) MeasureTheory.volume a t) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (show 0 ≤ 20 * Θ ^ 8 * U t by positivity)
  have hduration : t - a ≤ Θ := by linarith [ht.2]
  have hlast : 20 * Θ ^ 8 * U t *
      ((t - a) * (40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a)) ≤
      800 * δ * Θ ^ 17 * (U t / U a) * (|Y a| + |Y₁ a|) := by
    have hm := mul_le_mul_of_nonneg_left hduration
      (show 0 ≤ 800 * δ * Θ ^ 16 * (U t / U a) * (|Y a| + |Y₁ a|) by positivity)
    convert! hm using 1 <;> ring
  exact (hforced t ht).trans (add_le_add le_rfl (hscaled.trans hlast))


end EulerPacketPerturbation

end

section

/-!
The triangular ray system and its perturbation estimates.  These results
derive ray closeness from the differential equations and coefficient errors.
-/

namespace EulerPacketRay

open Set Filter Real EulerPacketGrowth EulerPacketPerturbation
open scoped Topology

/-- The sum norm of three scalar coordinates. -/
def norm3 (p q n : ℝ) : ℝ := |p| + |q| + |n|

/-- Exact Duhamel formulas for the triangular ray system. -/
theorem triangular_ray_formula
    {β T : ℝ} {P Q N f g h : ℝ → ℝ}
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T)) :
    ∀ t ∈ Icc 0 T,
      P t = P 0 - t * Q 0 + β * t ^ 2 * N 0 +
        ∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s ∧
      Q t = Q 0 - 2 * β * t * N 0 +
        ∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s ∧
      N t = N 0 + ∫ s in (0 : ℝ)..t, h s := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have htc : ContinuousOn (fun s : ℝ => t - s) (Icc 0 T) := by fun_prop
  have hPc : ContinuousOn (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s) (Icc 0 T) :=
    (hfc.sub (htc.mul hgc)).add ((continuousOn_const.mul (htc.pow 2)).mul hhc)
  have hQc : ContinuousOn (fun s => g s - 2 * β * (t - s) * h s) (Icc 0 T) :=
    hgc.sub ((continuousOn_const.mul htc).mul hhc)
  have hPi : IntervalIntegrable (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
      MeasureTheory.volume 0 t := (hPc.mono hsub).intervalIntegrable
  have hQi : IntervalIntegrable (fun s => g s - 2 * β * (t - s) * h s)
      MeasureTheory.volume 0 t := (hQc.mono hsub).intervalIntegrable
  have hNi : IntervalIntegrable h MeasureTheory.volume 0 t := (hhc.mono hsub).intervalIntegrable
  have hdP : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun r => P r - (t - r) * Q r + β * (t - r) ^ 2 * N r)
        (f s - (t - s) * g s + β * (t - s) ^ 2 * h s) s := by
    intro s hs
    have hsab := hsub hs
    have hd := (hasDerivAt_id s).const_sub t
    apply (((hP s hsab).sub (hd.mul (hQ s hsab))).add
      (((hd.fun_pow 2).const_mul β).mul (hN s hsab))).congr_deriv
    dsimp
    ring
  have hdQ : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun r => Q r - 2 * β * (t - r) * N r)
        (g s - 2 * β * (t - s) * h s) s := by
    intro s hs
    have hsab := hsub hs
    have hd := ((hasDerivAt_id s).const_sub t).const_mul (2 * β)
    apply ((hQ s hsab).sub (hd.mul (hN s hsab))).congr_deriv
    dsimp
    ring
  have hFP := intervalIntegral.integral_eq_sub_of_hasDerivAt hdP hPi
  have hFQ := intervalIntegral.integral_eq_sub_of_hasDerivAt hdQ hQi
  have hFN := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hN s (hsub hs)) hNi
  simp only [sub_self, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] at hFP hFQ
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The triangular ray propagator has a polynomial norm bound. -/
theorem triangular_ray_kernel_bound
    {β Θ d p q n : ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hd : 0 ≤ d) (hdΘ : d ≤ Θ) :
    norm3 (p - d * q + β * d ^ 2 * n) (q - 2 * β * d * n) n ≤
      4 * Θ ^ 2 * norm3 p q n := by
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hd2 : d ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hd hΘ0).mpr hdΘ
  have h1 := abs_add_le (p - d * q) (β * d ^ 2 * n)
  have h2 : |p - d * q| ≤ |p| + |d * q| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le p (d * q)
  have h3 : |q - 2 * β * d * n| ≤ |q| + |2 * β * d * n| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le q (2 * β * d * n)
  simp only [abs_mul, abs_of_nonneg hβ, abs_of_nonneg hd, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg d)] at h1 h2 h3
  have hcol1 : 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hcol2 : d + 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hβd2 : β * d ^ 2 ≤ Θ ^ 2 :=
    (mul_le_mul_of_nonneg_right hβupper (sq_nonneg d)).trans (by simpa using hd2)
  have hβd : β * d ≤ Θ :=
    (mul_le_mul_of_nonneg_right hβupper hd).trans (by simpa using hdΘ)
  have hcol3 : β * d ^ 2 + 2 * β * d + 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hcol1 (abs_nonneg p)
  have hq := mul_le_mul_of_nonneg_right hcol2 (abs_nonneg q)
  have hn := mul_le_mul_of_nonneg_right hcol3 (abs_nonneg n)
  unfold norm3
  nlinarith

/-- The exact triangular ray equations imply a polynomial Duhamel bound. -/
theorem triangular_ray_forced_bound
    {β Θ T : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤
      4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) +
        4 * Θ ^ 2 * ∫ s in (0 : ℝ)..t, norm3 (f s) (g s) (h s) := by
  intro t ht
  have hformula := triangular_ray_formula hP hQ hN hfc hgc hhc t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have htc : ContinuousOn (fun s : ℝ => t - s) (Icc 0 T) := by fun_prop
  have hc1 : ContinuousOn (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s) (Icc 0 T) :=
    (hfc.sub (htc.mul hgc)).add ((continuousOn_const.mul (htc.pow 2)).mul hhc)
  have hc2 : ContinuousOn (fun s => g s - 2 * β * (t - s) * h s) (Icc 0 T) :=
    hgc.sub ((continuousOn_const.mul htc).mul hhc)
  have hi1 : IntervalIntegrable (fun s => |f s - (t - s) * g s + β * (t - s) ^ 2 * h s|)
      MeasureTheory.volume 0 t := (hc1.abs.mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => |g s - 2 * β * (t - s) * h s|)
      MeasureTheory.volume 0 t := (hc2.abs.mono hsub).intervalIntegrable
  have hi3 : IntervalIntegrable (fun s => |h s|) MeasureTheory.volume 0 t :=
    (hhc.abs.mono hsub).intervalIntegrable
  have himajor : IntervalIntegrable (fun s => (4 * Θ ^ 2) * norm3 (f s) (g s) (h s))
      MeasureTheory.volume 0 t :=
    (((hfc.abs.add hgc.abs).add hhc.abs).mono hsub).intervalIntegrable.const_mul (4 * Θ ^ 2)
  have hpoint : ∀ s ∈ Icc 0 t,
      norm3 (f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
        (g s - 2 * β * (t - s) * h s) (h s) ≤ 4 * Θ ^ 2 * norm3 (f s) (g s) (h s) := by
    intro s hs
    apply triangular_ray_kernel_bound hβ hβupper hΘ
    · linarith [hs.2]
    · linarith [hs.1, ht.2]
  have hmono := intervalIntegral.integral_mono_on ht.1 ((hi1.add hi2).add hi3) himajor hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI :
      |∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s| +
      |∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s| + |∫ s in (0 : ℝ)..t, h s| ≤
      ∫ s in (0 : ℝ)..t, norm3 (f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
        (g s - 2 * β * (t - s) * h s) (h s) := by
    unfold norm3
    rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2]
    exact add_le_add (add_le_add (intervalIntegral.abs_integral_le_integral_abs ht.1)
      (intervalIntegral.abs_integral_le_integral_abs ht.1)) (intervalIntegral.abs_integral_le_integral_abs ht.1)
  have hbase := triangular_ray_kernel_bound (p := P 0) (q := Q 0) (n := N 0)
    hβ hβupper hΘ ht.1 (ht.2.trans hT)
  have hPt : |P t| ≤ |P 0 - t * Q 0 + β * t ^ 2 * N 0| +
      |∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s| := by
    rw [hformula.1]
    exact abs_add_le _ _
  have hQt : |Q t| ≤ |Q 0 - 2 * β * t * N 0| +
      |∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s| := by
    rw [hformula.2.1]
    exact abs_add_le _ _
  have hNt : |N t| ≤ |N 0| + |∫ s in (0 : ℝ)..t, h s| := by
    rw [hformula.2.2]
    exact abs_add_le _ _
  unfold norm3 at hbase hI hmono ⊢
  linarith

/-- A small perturbation of the triangular ray system remains polynomially
bounded on the whole interval. -/
theorem triangular_ray_perturbed_bound
    {β Θ T δ : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (hδ : 0 ≤ δ) (hsmall : 4 * Θ ^ 2 * δ * T ≤ 1 / 2)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ δ * norm3 (P t) (Q t) (N t)) :
    ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤ 8 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) := by
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hstate : ContinuousOn (fun t => norm3 (P t) (Q t) (N t)) (Icc 0 T) :=
    (hPc.abs.add hQc.abs).add hNc.abs
  have hforce : ContinuousOn (fun t => norm3 (f t) (g t) (h t)) (Icc 0 T) :=
    (hfc.abs.add hgc.abs).add hhc.abs
  have hforced := triangular_ray_forced_bound hβ hβupper hΘ hT hP hQ hN hfc hgc hhc
  have hineq : ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤
      4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) +
        (4 * Θ ^ 2 * δ) * ∫ s in (0 : ℝ)..t, norm3 (P s) (Q s) (N s) := by
    intro t ht
    have hsub : uIcc 0 t ⊆ Icc 0 T := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hFi : IntervalIntegrable (fun s => norm3 (f s) (g s) (h s)) MeasureTheory.volume 0 t :=
      (hforce.mono hsub).intervalIntegrable
    have hSi : IntervalIntegrable (fun s => δ * norm3 (P s) (Q s) (N s)) MeasureTheory.volume 0 t :=
      ((hstate.mono hsub).intervalIntegrable).const_mul δ
    have hi := intervalIntegral.integral_mono_on ht.1 hFi hSi
      (fun s hs => hforcing s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [intervalIntegral.integral_const_mul] at hi
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Θ ^ 2 by positivity)
    nlinarith [hforced t ht]
  have hresult := integral_absorb
    (g := fun t => norm3 (P t) (Q t) (N t))
    (A := 4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0)) (K := 4 * Θ ^ 2 * δ)
    hT0 hstate (fun _ _ => by unfold norm3; positivity) (by positivity)
    (by simpa using hsmall) hineq
  intro t ht
  nlinarith [hresult t ht]

/-- Ray closeness is derived from the ODE and the forcing bound, with a
polynomial loss and arbitrary small initial ray error. -/
theorem triangular_ray_difference_bound
    {β Θ T δ η : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hsmall : 4 * Θ ^ 2 * δ * T ≤ 1 / 2)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ δ * norm3 (P t) (Q t) (N t))
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ η) :
    ∀ t ∈ Icc 0 T, norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤
      4 * Θ ^ 2 * η + 32 * δ * Θ ^ 5 * (1 + η) := by
  have hnorm0 : norm3 (P 0) (Q 0) (N 0) ≤ 1 + η := by
    have hn : |N 0| ≤ |N 0 - 1| + 1 := by
      have := abs_add_le (N 0 - 1) 1
      simpa using this
    unfold norm3 at hinitial ⊢
    linarith
  have hstate := triangular_ray_perturbed_bound hβ hβupper hΘ hT0 hT hδ hsmall
    hP hQ hN hfc hgc hhc hforcing
  have hPe : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => P s - β * s ^ 2) (-(Q t + 2 * β * t) + f t) t := by
    intro t ht
    apply ((hP t ht).sub (((hasDerivAt_id t).fun_pow 2).const_mul β)).congr_deriv
    dsimp
    ring
  have hQe : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => Q s + 2 * β * s) (-2 * β * (N t - 1) + g t) t := by
    intro t ht
    apply ((hQ t ht).add ((hasDerivAt_id t).const_mul (2 * β))).congr_deriv
    ring
  have hNe : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => N s - 1) (h t) t :=
    fun t ht => (hN t ht).sub_const 1
  have herror := triangular_ray_forced_bound hβ hβupper hΘ hT hPe hQe hNe hfc hgc hhc
  have hforce : ContinuousOn (fun t => norm3 (f t) (g t) (h t)) (Icc 0 T) :=
    (hfc.abs.add hgc.abs).add hhc.abs
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hFi : IntervalIntegrable (fun s => norm3 (f s) (g s) (h s)) MeasureTheory.volume 0 t :=
    (hforce.mono hsub).intervalIntegrable
  have hpoint : ∀ s ∈ Icc 0 t, norm3 (f s) (g s) (h s) ≤ δ * (8 * Θ ^ 2 * (1 + η)) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hm := mul_le_mul_of_nonneg_left hnorm0 (show 0 ≤ 8 * Θ ^ 2 by positivity)
    have hbound : norm3 (P s) (Q s) (N s) ≤ 8 * Θ ^ 2 * (1 + η) := (hstate s hsT).trans hm
    exact (hforcing s hsT).trans (mul_le_mul_of_nonneg_left hbound hδ)
  have hi := intervalIntegral.integral_mono_on ht.1 hFi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => δ * (8 * Θ ^ 2 * (1 + η)))
      MeasureTheory.volume 0 t) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hi
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Θ ^ 2 by positivity)
  have htΘ : t ≤ Θ := ht.2.trans hT
  have htime := mul_le_mul_of_nonneg_left htΘ (show 0 ≤ 32 * δ * Θ ^ 4 * (1 + η) by positivity)
  have hinit := mul_le_mul_of_nonneg_left hinitial (show 0 ≤ 4 * Θ ^ 2 by positivity)
  have herr := herror t ht
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at herr
  nlinarith

/-- Entries of the triangular ideal ray generator. -/
def idealRayEntry (β : ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 2 then -2 * β else 0

theorem three_term_bound {a b c p q n e : ℝ}
    (ha : |a| ≤ e) (hb : |b| ≤ e) (hc : |c| ≤ e) :
    |a * p + b * q + c * n| ≤ e * norm3 p q n := by
  have h1 := abs_add_le (a * p + b * q) (c * n)
  have h2 := abs_add_le (a * p) (b * q)
  simp only [abs_mul] at h1 h2
  have hp := mul_le_mul_of_nonneg_right ha (abs_nonneg p)
  have hq := mul_le_mul_of_nonneg_right hb (abs_nonneg q)
  have hn := mul_le_mul_of_nonneg_right hc (abs_nonneg n)
  unfold norm3
  nlinarith

/-- The ray closeness estimate follows from entrywise coefficient error.
No closeness of the ray itself is assumed.  The third component stays away
from zero, as required to eliminate the third velocity coordinate. -/
theorem ray_closeness_of_coefficient_error
    {β Θ T e : ℝ} {A : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hsmall : 400 * e * Θ ^ 5 ≤ 1)
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (A t 0 0 * P t + A t 0 1 * Q t + A t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (A t 1 0 * P t + A t 1 1 * Q t + A t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t) t)
    (hclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealRayEntry β i j| ≤ e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T,
      norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤ 200 * e * Θ ^ 5 ∧
        1 / 2 ≤ N t := by
  let f : ℝ → ℝ := fun t => A t 0 0 * P t + (A t 0 1 + 1) * Q t + A t 0 2 * N t
  let g : ℝ → ℝ := fun t => A t 1 0 * P t + A t 1 1 * Q t + (A t 1 2 + 2 * β) * N t
  let h : ℝ → ℝ := fun t => A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := by unfold f; fun_prop
  have hgc : ContinuousOn g (Icc 0 T) := by unfold g; fun_prop
  have hhc : ContinuousOn h (Icc 0 T) := by unfold h; fun_prop
  have hPf : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t := by
    intro t ht
    apply (hP t ht).congr_deriv
    dsimp [f]
    ring
  have hQg : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t := by
    intro t ht
    apply (hQ t ht).congr_deriv
    dsimp [g]
    ring
  have hNh : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t := hN
  have hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ (3 * e) * norm3 (P t) (Q t) (N t) := by
    intro t ht
    have hf : |f t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 0 0
      · simpa [idealRayEntry] using hclose t ht 0 1
      · simpa [idealRayEntry] using hclose t ht 0 2
    have hg : |g t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 1 0
      · simpa [idealRayEntry] using hclose t ht 1 1
      · simpa [idealRayEntry] using hclose t ht 1 2
    have hh : |h t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 2 0
      · simpa [idealRayEntry] using hclose t ht 2 1
      · simpa [idealRayEntry] using hclose t ht 2 2
    unfold norm3
    unfold norm3 at hf hg hh
    nlinarith
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hpow35 : Θ ^ 3 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow25 : Θ ^ 2 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow5 : 1 ≤ Θ ^ 5 := one_le_pow₀ hΘ
  have he1 : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow5 he
    nlinarith
  have hsm : 4 * Θ ^ 2 * (3 * e) * T ≤ 1 / 2 := by
    have ht := mul_le_mul_of_nonneg_left hT (show 0 ≤ 12 * e * Θ ^ 2 by positivity)
    have hp := mul_le_mul_of_nonneg_left hpow35 (show 0 ≤ 12 * e by positivity)
    nlinarith
  have hdiff := triangular_ray_difference_bound hβ hβupper hΘ hT0 hT
    (by positivity : 0 ≤ 3 * e) he hsm hPf hQg hNh hfc hgc hhc hforcing hinitial
  intro t ht
  have hbound : norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤ 200 * e * Θ ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hpow25 (show 0 ≤ 4 * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left (show 1 + e ≤ 2 by linarith)
      (show 0 ≤ 96 * e * Θ ^ 5 by positivity)
    have hp : 0 ≤ e * Θ ^ 5 := by positivity
    nlinarith [hdiff t ht]
  refine ⟨hbound, ?_⟩
  have hNabs : |N t - 1| ≤ 200 * e * Θ ^ 5 := by
    unfold norm3 at hbound
    linarith [abs_nonneg (P t - β * t ^ 2), abs_nonneg (Q t + 2 * β * t)]
  have hn := (abs_le.mp hNabs).1
  nlinarith

/-- The skew matrix of the moving orthonormal frame in the source. -/
def frameSkew (B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then (if j = 1 then B 0 1 else if j = 2 then B 0 2 else 0)
  else if i = 1 then (if j = 0 then -B 0 1 else if j = 2 then B 2 1 else 0)
  else if j = 0 then -B 0 2 else if j = 1 then -B 2 1 else 0

/-- The older gradient plus rank-one parent shear and error. -/
def parentEntry (B E : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i j : Fin 3) : ℝ :=
  B i j + E i j + (if i = 1 ∧ j = 0 then h else 0)

/-- Coordinate scaling for the normalized ray. -/
def rayScale (ε : ℝ) (i : Fin 3) : ℝ := if i = 1 then ε else 1

/-- Coefficients after the moving-frame transformation and the scaling
`m/s₀=(P,εQ,N)`, `dt/dτ=ε/a`. -/
noncomputable def scaledRayEntry (a ε : ℝ) (M S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  -(ε / a) * (rayScale ε j / rayScale ε i) * (M j i - S j i)

/-- The scaled moving-frame ray entries in normalized coefficients. -/
def normalizedRayEntry (ε H κ : ℝ) (B E : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then -B 0 0 - ε * E 0 0
      else if j = 1 then -H - ε * B 1 0 - ε * B 0 1 - ε ^ 2 * E 1 0
      else -B 2 0 - B 0 2 - ε * E 2 0)
  else if i = 1 then
    (if j = 0 then -E 0 1 else if j = 1 then -B 1 1 - ε * E 1 1 else -2 * κ - E 2 1)
  else if j = 0 then -ε * E 0 2
    else if j = 1 then -ε * B 1 2 + ε * B 2 1 - ε ^ 2 * E 1 2
    else -B 2 2 - ε * E 2 2

/-- Exact entries of the scaled moving-frame ray matrix. -/
theorem scaled_ray_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) :
    ∀ i j, scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j =
      normalizedRayEntry ε (ε ^ 2 * h / a) (B 2 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledRayEntry, parentEntry, frameSkew, rayScale, normalizedRayEntry,
      Fin.ext_iff] <;>
    field_simp <;> ring

/-- Each scaled matrix entry is close to the triangular ideal matrix when
the normalized older-gradient, error, shear, and coupling coefficients are
small. -/
theorem normalized_ray_entry_error
    {ε H κ β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hκ : |κ - β| ≤ e) :
    ∀ i j, |normalizedRayEntry ε H κ B E i j - idealRayEntry β i j| ≤ 4 * e := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    have hm := mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    have hm := mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hm := mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have b20 := abs_le.mp (hB 2 0)
  have b22 := abs_le.mp (hB 2 2)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε01 := abs_le.mp (hεBn 0 1)
  have bε12 := abs_le.mp (hεBn 1 2)
  have bε21 := abs_le.mp (hεBn 2 1)
  have e01 := abs_le.mp (hE 0 1)
  have e21 := abs_le.mp (hE 2 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε20 := abs_le.mp (hεEn 2 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε22 := abs_le.mp (hεEn 2 2)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hκb := abs_le.mp hκ
  intro i j
  fin_cases i <;> fin_cases j <;>
    apply abs_le.mpr <;> constructor <;>
    norm_num [normalizedRayEntry, idealRayEntry, Fin.ext_iff] <;>
    linarith only [he, b00, b02, b11, b20, b22, bε10, bε01, bε12, bε21,
      e01, e21, eε00, eε11, eε20, eε02, eε22, eε210, eε212, hHb, hκb]

/-- The original moving-frame entries imply the coefficient hypothesis of
`ray_closeness_of_coefficient_error`. -/
theorem scaled_ray_entry_error
    {a ε h β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |ε * B i j / a| ≤ e) (hE : ∀ i j, |E i j / a| ≤ e)
    (hH : |ε ^ 2 * h / a - 1| ≤ e) (hκ : |B 2 1 / a - β| ≤ e) :
    ∀ i j, |scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j - idealRayEntry β i j| ≤ 4 * e := by
  intro i j
  rw [scaled_ray_entry_identity ha (ne_of_gt hε)]
  exact normalized_ray_entry_error hε.le hεupper he hB hE hH hκ i j

/-- A product difference estimate used to control the projection denominator. -/
theorem abs_product_difference
    {a b c d ea eb A B : ℝ}
    (ha : |a - c| ≤ ea) (hb : |b - d| ≤ eb)
    (hc : |c| ≤ A) (hd : |b| ≤ B) :
    |a * b - c * d| ≤ ea * B + A * eb := by
  have hea : 0 ≤ ea := le_trans (abs_nonneg _) ha
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hc
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |a - c| * |b| + |c| * |b - d| := by
      simpa only [abs_mul] using abs_add_le ((a - c) * b) (c * (b - d))
    _ ≤ ea * B + A * eb := add_le_add
      (mul_le_mul ha hd (abs_nonneg _) hea)
      (mul_le_mul hc hb (abs_nonneg _) hA)

/-- The third velocity coordinate imposed by ray orthogonality. -/
noncomputable def velocityThird (P Q N U V : ℝ) : ℝ := -(P * U + Q * V) / N

/-- Squared norm of the scaled ray. -/
def rayDenominator (ε P Q N : ℝ) : ℝ := P ^ 2 + ε ^ 2 * Q ^ 2 + N ^ 2

/-- Elimination of the third velocity component and the denominator estimate
are consequences of the proved ray error. -/
theorem ray_geometric_bounds
    {Θ ρ ε P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρupper : ρ ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ) :
    1 / 2 ≤ N ∧ |P| ≤ 2 * Θ ^ 2 ∧ |Q| ≤ 3 * Θ ^ 2 ∧ |N| ≤ 2 ∧
      |velocityThird P Q N U V| ≤ 6 * Θ ^ 2 * (|U| + |V|) ∧
      1 / 4 ≤ rayDenominator ε P Q N ∧
      |rayDenominator ε P Q N - (1 + P₀ ^ 2)| ≤
        6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hn : 1 / 2 ≤ N := by have := (abs_le.mp hN).1; linarith
  have hnpos : 0 < N := by linarith
  have hp : |P| ≤ 2 * Θ ^ 2 := by
    have hh := abs_add_le (P - P₀) P₀
    have hh' : |P| ≤ ρ + Θ ^ 2 := by
      calc
        |P| = |(P - P₀) + P₀| := by congr 1; ring
        _ ≤ |P - P₀| + |P₀| := hh
        _ ≤ ρ + Θ ^ 2 := add_le_add hP hP₀
    linarith
  have hq : |Q| ≤ 3 * Θ ^ 2 := by
    have hh' : |Q| ≤ ρ + 2 * Θ ^ 2 := by
      calc
        |Q| = |(Q - Q₀) + Q₀| := by congr 1; ring
        _ ≤ |Q - Q₀| + |Q₀| := abs_add_le _ _
        _ ≤ ρ + 2 * Θ ^ 2 := add_le_add hQ hQ₀
    linarith
  have hnabs : |N| ≤ 2 := by rw [abs_of_pos hnpos]; have := (abs_le.mp hN).2; linarith
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw : |velocityThird P Q N U V| ≤ 6 * Θ ^ 2 * (|U| + |V|) := by
    unfold velocityThird
    rw [abs_div, abs_neg, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have hb : |P * U + Q * V| ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
      calc
        |P * U + Q * V| ≤ |P| * |U| + |Q| * |V| := by simpa only [abs_mul] using abs_add_le (P * U) (Q * V)
        _ ≤ (2 * Θ ^ 2) * |U| + (3 * Θ ^ 2) * |V| :=
          add_le_add (mul_le_mul_of_nonneg_right hp (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hq (abs_nonneg _))
        _ ≤ 3 * Θ ^ 2 * (|U| + |V|) := by nlinarith [sq_nonneg Θ, abs_nonneg U]
    have hmul := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 6 * Θ ^ 2 * (|U| + |V|))
    nlinarith only [hb, hmul]
  have hD : 1 / 4 ≤ rayDenominator ε P Q N := by
    unfold rayDenominator
    nlinarith [sq_nonneg P, mul_nonneg (sq_nonneg ε) (sq_nonneg Q)]
  have hPsum : |P + P₀| ≤ 3 * Θ ^ 2 := by linarith [abs_add_le P P₀]
  have hNsum : |N + 1| ≤ 3 := by have hh := abs_add_le N 1; norm_num at hh; linarith
  have hPsq : |P ^ 2 - P₀ ^ 2| ≤ 3 * ρ * Θ ^ 2 := by
    calc
      |P ^ 2 - P₀ ^ 2| = |P - P₀| * |P + P₀| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ρ * (3 * Θ ^ 2) := mul_le_mul hP hPsum (abs_nonneg _) hρ
      _ = 3 * ρ * Θ ^ 2 := by ring
  have hNsq : |N ^ 2 - 1| ≤ 3 * ρ := by
    calc
      |N ^ 2 - 1| = |N - 1| * |N + 1| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ρ * 3 := mul_le_mul hN hNsum (abs_nonneg _) hρ
      _ = 3 * ρ := by ring
  have hQsq : Q ^ 2 ≤ 9 * Θ ^ 4 := by
    have hsq := sq_le_sq₀ (abs_nonneg Q) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hh := hsq.mpr hq
    rw [sq_abs] at hh
    nlinarith only [hh]
  refine ⟨hn, hp, hq, hnabs, hw, hD, ?_⟩
  calc
    |rayDenominator ε P Q N - (1 + P₀ ^ 2)| =
        |(P ^ 2 - P₀ ^ 2) + (N ^ 2 - 1) + ε ^ 2 * Q ^ 2| := by
      unfold rayDenominator; congr 1; ring
    _ ≤ |P ^ 2 - P₀ ^ 2| + |N ^ 2 - 1| + ε ^ 2 * Q ^ 2 := by
      have h₁ := abs_add_le (P ^ 2 - P₀ ^ 2) (N ^ 2 - 1)
      have h₂ := abs_add_le ((P ^ 2 - P₀ ^ 2) + (N ^ 2 - 1)) (ε ^ 2 * Q ^ 2)
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg Q))] at h₂
      linarith
    _ ≤ 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4 := by
      have hqq := mul_le_mul_of_nonneg_left hQsq (sq_nonneg ε)
      have hrr := mul_le_mul_of_nonneg_left hΘ2 (by positivity : 0 ≤ 3 * ρ)
      nlinarith only [hPsq, hNsq, hqq, hrr]

/-- The three rows entering `J_v`, with the middle row multiplied by ε. -/
def normalizedVelocityEntry (ε H α κ : ℝ) (B E : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then B 0 0 + ε * E 0 0 else if j = 1 then α + E 0 1
      else B 0 2 + ε * E 0 2)
  else if i = 1 then
    (if j = 0 then H + ε * B 1 0 + ε ^ 2 * E 1 0
      else if j = 1 then B 1 1 + ε * E 1 1 else ε * B 1 2 + ε ^ 2 * E 1 2)
  else if j = 0 then B 2 0 + ε * E 2 0
    else if j = 1 then κ + E 2 1 else B 2 2 + ε * E 2 2

/-- The ideal scaled parent action on velocity coordinates. -/
def idealVelocityEntry (β : ℝ) (i j : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1
  else if i = 2 ∧ j = 1 then β else 0

/-- Parent-gradient entries after ray and velocity rescaling. -/
noncomputable def scaledVelocityEntry (a ε : ℝ) (M : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  (if i = 1 then ε else 1) * (if j = 1 then 1 else ε) * M i j / a

theorem scaled_velocity_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) :
    ∀ i j, scaledVelocityEntry a ε (parentEntry B E h) i j =
      normalizedVelocityEntry ε (ε ^ 2 * h / a) (B 0 1 / a) (B 2 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledVelocityEntry, parentEntry, normalizedVelocityEntry, Fin.ext_iff] <;>
    field_simp
  all_goals ring

theorem normalized_velocity_entry_error
    {ε H α κ β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hα : |α - 1| ≤ e) (hκ : |κ - β| ≤ e) :
    ∀ i j, |normalizedVelocityEntry ε H α κ B E i j - idealVelocityEntry β i j| ≤ 3 * e := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    simpa using mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have b20 := abs_le.mp (hB 2 0)
  have b22 := abs_le.mp (hB 2 2)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε12 := abs_le.mp (hεBn 1 2)
  have e01 := abs_le.mp (hE 0 1)
  have e21 := abs_le.mp (hE 2 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε20 := abs_le.mp (hεEn 2 0)
  have eε22 := abs_le.mp (hεEn 2 2)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hαb := abs_le.mp hα
  have hκb := abs_le.mp hκ
  intro i j
  fin_cases i <;> fin_cases j <;> apply abs_le.mpr <;> constructor <;>
    norm_num [normalizedVelocityEntry, idealVelocityEntry, Fin.ext_iff] <;>
    linarith only [he, b00, b02, b11, b20, b22, bε10, bε12,
      e01, e21, eε00, eε02, eε11, eε20, eε22, eε210, eε212, hHb, hαb, hκb]

/-- The scalar pressure numerator in the scaled coordinates. -/
def velocityNumerator (A : Fin 3 → Fin 3 → ℝ) (P Q N U V W : ℝ) : ℝ :=
  P * (A 0 0 * U + A 0 1 * V + A 0 2 * W) +
  Q * (A 1 0 * U + A 1 1 * V + A 1 2 * W) +
  N * (A 2 0 * U + A 2 1 * V + A 2 2 * W)

theorem velocity_numerator_error
    {A : Fin 3 → Fin 3 → ℝ} {Θ ρ e β P Q N P₀ Q₀ U V W : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e)
    (hp : |P| ≤ 2 * Θ ^ 2) (hq : |Q| ≤ 3 * Θ ^ 2) (hn : |N| ≤ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hw : |W| ≤ 6 * Θ ^ 2 * (|U| + |V|)) :
    |velocityNumerator A P Q N U V W - ((P₀ + β) * V + Q₀ * U)| ≤
      (49 * e * Θ ^ 4 + 2 * ρ) * (|U| + |V|) := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm : norm3 U V W ≤ 7 * Θ ^ 2 * (|U| + |V|) := by
    unfold norm3
    have hm := mul_le_mul_of_nonneg_right hΘ2 hL
    nlinarith only [hw, hm]
  have hrow : ∀ i, |(A i 0 - idealVelocityEntry β i 0) * U +
      (A i 1 - idealVelocityEntry β i 1) * V +
      (A i 2 - idealVelocityEntry β i 2) * W| ≤
      7 * e * Θ ^ 2 * (|U| + |V|) := by
    intro i
    have hh := three_term_bound (p := U) (q := V) (n := W) (hA i 0) (hA i 1) (hA i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm he
    nlinarith only [hh, hm]
  have hrow0 := hrow 0
  have hrow1 := hrow 1
  have hrow2 := hrow 2
  norm_num [idealVelocityEntry, Fin.ext_iff] at hrow0 hrow1 hrow2
  have hJnear : |velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V)| ≤
      49 * e * Θ ^ 4 * (|U| + |V|) := by
    let r0 := A 0 0 * U + (A 0 1 - 1) * V + A 0 2 * W
    let r1 := (A 1 0 - 1) * U + A 1 1 * V + A 1 2 * W
    let r2 := A 2 0 * U + (A 2 1 - β) * V + A 2 2 * W
    have htri : |P * r0 + Q * r1 + N * r2| ≤
        (|P| + |Q| + |N|) * (7 * e * Θ ^ 2 * (|U| + |V|)) := by
      have h0 := mul_le_mul_of_nonneg_left hrow0 (abs_nonneg P)
      have h1 := mul_le_mul_of_nonneg_left hrow1 (abs_nonneg Q)
      have h2 := mul_le_mul_of_nonneg_left hrow2 (abs_nonneg N)
      have ht0 := abs_add_le (P * r0) (Q * r1)
      have ht1 := abs_add_le (P * r0 + Q * r1) (N * r2)
      simp only [abs_mul] at ht0 ht1
      dsimp [r0, r1, r2] at *
      nlinarith only [h0, h1, h2, ht0, ht1]
    have hs : |P| + |Q| + |N| ≤ 7 * Θ ^ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_right hs
      (by positivity : 0 ≤ 7 * e * Θ ^ 2 * (|U| + |V|))
    have hid : velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V) =
        P * r0 + Q * r1 + N * r2 := by unfold velocityNumerator r0 r1 r2; ring
    rw [hid]
    nlinarith only [htri, hm]
  have hRay : |P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U)| ≤
      2 * ρ * (|U| + |V|) := by
    have hNb : |(N - 1) * β| ≤ ρ := by
      rw [abs_mul]
      exact (mul_le_mul hN hβ (abs_nonneg _) hρ).trans_eq (mul_one ρ)
    have hv : |P - P₀ + (N - 1) * β| ≤ 2 * ρ := by linarith [abs_add_le (P - P₀) ((N - 1) * β)]
    have hu : |Q - Q₀| ≤ 2 * ρ := by linarith
    have hh := three_term_bound (p := V) (q := U) (n := (0 : ℝ)) hv hu
      (show |(0 : ℝ)| ≤ 2 * ρ by simpa using (show 0 ≤ 2 * ρ by positivity))
    have hid : P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U) =
        (P - P₀ + (N - 1) * β) * V + (Q - Q₀) * U + 0 * 0 := by ring
    rw [hid]
    simpa only [norm3, abs_zero, add_zero, add_comm] using hh
  have ht := abs_add_le
    (velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V))
    (P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U))
  have hid : velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V) +
      (P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U)) =
      velocityNumerator A P Q N U V W - ((P₀ + β) * V + Q₀ * U) := by ring
  rw [hid] at ht
  nlinarith only [ht, hJnear, hRay]

/-- The first two velocity rows before pressure projection. -/
def normalizedUnprojectedEntry (ε H α : ℝ) (B E : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then B 0 0 + ε * E 0 0 else if j = 1 then 2 * α + E 0 1
      else 2 * B 0 2 + ε * E 0 2)
  else if j = 0 then H + ε * B 1 0 - ε ^ 2 * α + ε ^ 2 * E 1 0
    else if j = 1 then B 1 1 + ε * E 1 1
    else ε * B 1 2 + ε * B 2 1 + ε ^ 2 * E 1 2

/-- Ideal entries of the unprojected two-component velocity equation. -/
def idealUnprojectedEntry (i j : Fin 3) : ℝ :=
  if i = 0 then (if j = 1 then 2 else 0) else if j = 0 then 1 else 0

/-- Exact first and second rows of the moving-frame velocity operator. -/
theorem scaled_unprojected_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) :
    ∀ j, (scaledVelocityEntry a ε
        (fun i j => parentEntry B E h i j + frameSkew B i j) 0 j =
      normalizedUnprojectedEntry ε (ε ^ 2 * h / a) (B 0 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) 0 j) ∧
      (scaledVelocityEntry a ε
        (fun i j => parentEntry B E h i j + frameSkew B i j) 1 j =
      normalizedUnprojectedEntry ε (ε ^ 2 * h / a) (B 0 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) 1 j) := by
  intro j
  fin_cases j <;> constructor <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledVelocityEntry, parentEntry, frameSkew,
      normalizedUnprojectedEntry, Fin.ext_iff] <;> field_simp <;> ring

theorem normalized_unprojected_entry_error
    {ε H α e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεe : ε ≤ e) (he : 0 ≤ e) (heupper : e ≤ 1)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hα : |α - 1| ≤ e) :
    ∀ i j, |normalizedUnprojectedEntry ε H α B E i j - idealUnprojectedEntry i j| ≤ 5 * e := by
  have hεupper : ε ≤ 1 := hεe.trans heupper
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε2e : ε ^ 2 ≤ e := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    simpa using mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
  have hαabs : |α| ≤ 2 := by
    have hh := abs_add_le (α - 1) 1
    norm_num at hh
    linarith
  have hαε : |ε ^ 2 * α| ≤ 2 * e := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hε2e hαabs (abs_nonneg α) he
    nlinarith only [hh]
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε12 := abs_le.mp (hεBn 1 2)
  have bε21 := abs_le.mp (hεBn 2 1)
  have e01 := abs_le.mp (hE 0 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hαb := abs_le.mp hα
  have hαεb := abs_le.mp hαε
  intro i j
  fin_cases i <;> fin_cases j <;> apply abs_le.mpr <;> constructor <;>
    norm_num [normalizedUnprojectedEntry, idealUnprojectedEntry, Fin.ext_iff] <;>
    linarith only [he, b00, b02, b11, bε10, bε12, bε21,
      e01, eε00, eε02, eε11, eε210, eε212, hHb, hαb, hαεb]

/-- A quotient difference bound requiring only the quantitative lower
bounds actually available for the ray denominator. -/
theorem quotient_difference_bound
    {P P₀ D D₀ ρ d A : ℝ}
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀)
    (hP : |P - P₀| ≤ ρ) (hP₀ : |P₀| ≤ A) (hDD : |D - D₀| ≤ d) :
    |P / D - P₀ / D₀| ≤ 4 * ρ + 4 * A * d := by
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hP
  have hd : 0 ≤ d := (abs_nonneg _).trans hDD
  have hA : 0 ≤ A := (abs_nonneg _).trans hP₀
  have hprod : 1 / 4 ≤ D * D₀ := by nlinarith only [hD, hD₀, hDp]
  have hn := abs_product_difference hP
    (show |D₀ - D| ≤ d by simpa only [abs_sub_comm] using hDD)
    hP₀ (le_of_eq (abs_of_pos hD₀p))
  have hid : P / D - P₀ / D₀ = (P * D₀ - P₀ * D) / (D * D₀) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hDp hD₀p), div_le_iff₀ (mul_pos hDp hD₀p)]
  have h₁ := mul_le_mul_of_nonneg_left hD (mul_nonneg hρ hD₀p.le)
  have h₂ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hA hd)
  nlinarith only [hn, h₁, h₂]

/-- Quantitative stability of the two pressure projection components. -/
theorem velocity_projection_error
    {Θ ρ d j ε P Q D P₀ D₀ J J₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (_hj : 0 ≤ j) (hjupper : j ≤ 1)
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀)
    (hP : |P - P₀| ≤ ρ) (hP₀ : |P₀| ≤ Θ ^ 2)
    (hp : |P| ≤ 2 * Θ ^ 2) (hq : |Q| ≤ 3 * Θ ^ 2)
    (hDD : |D - D₀| ≤ d) (hJ : |J - J₀| ≤ j * (|U| + |V|))
    (hJ₀ : |J₀| ≤ 2 * Θ ^ 2 * (|U| + |V|)) :
    |2 * P * J / D - 2 * P₀ * J₀ / D₀| + |2 * ε ^ 2 * Q * J / D| ≤
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d +
        72 * ε ^ 2 * Θ ^ 4) * (|U| + |V|) := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have hratio := quotient_difference_bound hD hD₀ hP hP₀ hDD
  have hratio0 : |P₀ / D₀| ≤ Θ ^ 2 := by
    rw [abs_div, abs_of_pos hD₀p, div_le_iff₀ hD₀p]
    have hm := mul_le_mul_of_nonneg_left hD₀ (sq_nonneg Θ)
    nlinarith only [hP₀, hm]
  have hJabs : |J| ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
    have ht := abs_add_le (J - J₀) J₀
    have hid : J - J₀ + J₀ = J := by ring
    rw [hid] at ht
    have hm₁ := mul_le_mul_of_nonneg_right hjupper hL
    have hm₂ := mul_le_mul_of_nonneg_right hΘ2 hL
    nlinarith only [ht, hJ, hJ₀, hm₁, hm₂]
  have hratioP : |P / D| ≤ 8 * Θ ^ 2 := by
    rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 8 * Θ ^ 2)
    nlinarith only [hp, hm]
  have hU : |2 * P * J / D - 2 * P₀ * J₀ / D₀| ≤
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d) * (|U| + |V|) := by
    have hh := abs_product_difference hratio hJ hratio0 hJabs
    have hbetter : |(P / D) * J - (P₀ / D₀) * J₀| ≤
        (8 * Θ ^ 2) * (j * (|U| + |V|)) +
          (4 * ρ + 4 * Θ ^ 2 * d) * (2 * Θ ^ 2 * (|U| + |V|)) := by
      have ht := abs_add_le ((P / D) * (J - J₀)) (((P / D) - (P₀ / D₀)) * J₀)
      have h₁ := mul_le_mul hratioP hJ (abs_nonneg _) (by positivity : 0 ≤ 8 * Θ ^ 2)
      have h₂ := mul_le_mul hratio hJ₀ (abs_nonneg _)
        (by positivity : 0 ≤ 4 * ρ + 4 * Θ ^ 2 * d)
      have hid : (P / D) * (J - J₀) + ((P / D) - (P₀ / D₀)) * J₀ =
          (P / D) * J - (P₀ / D₀) * J₀ := by ring
      rw [hid] at ht
      simp only [abs_mul] at ht
      nlinarith only [ht, h₁, h₂]
    have hid : 2 * P * J / D - 2 * P₀ * J₀ / D₀ =
        2 * ((P / D) * J - (P₀ / D₀) * J₀) := by ring
    rw [hid, abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith only [hbetter]
  have hV : |2 * ε ^ 2 * Q * J / D| ≤ 72 * ε ^ 2 * Θ ^ 4 * (|U| + |V|) := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg ε), abs_of_pos hDp, div_le_iff₀ hDp]
    have hh := mul_le_mul hq hJabs (abs_nonneg J) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm₁ := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * ε ^ 2)
    have hm₂ := mul_le_mul_of_nonneg_left hD
      (by positivity : 0 ≤ 72 * ε ^ 2 * Θ ^ 4 * (|U| + |V|))
    nlinarith only [hm₁, hm₂]
  nlinarith only [hU, hV]

/-- The first normalized velocity equation with pressure projection. -/
noncomputable def velocityFirstRhs
    (A C : Fin 3 → Fin 3 → ℝ) (ε P Q N U V : ℝ) : ℝ :=
  let W := velocityThird P Q N U V;
  -(C 0 0 * U + C 0 1 * V + C 0 2 * W) +
    2 * P * velocityNumerator A P Q N U V W / rayDenominator ε P Q N

/-- The second normalized velocity equation with pressure projection. -/
noncomputable def velocitySecondRhs
    (A C : Fin 3 → Fin 3 → ℝ) (ε P Q N U V : ℝ) : ℝ :=
  let W := velocityThird P Q N U V;
  -(C 1 0 * U + C 1 1 * V + C 1 2 * W) +
    2 * ε ^ 2 * Q * velocityNumerator A P Q N U V W / rayDenominator ε P Q N

/-- The full pressure projection is a small matrix perturbation, with an
explicit constant and the power of Θ used in the source. -/
theorem velocity_rhs_error
    {A C : Fin 3 → Fin 3 → ℝ} {Θ e ε β P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 10000 * e * Θ ^ 5 ≤ 1) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hC : ∀ i j, |C i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    |velocityFirstRhs A C ε P Q N U V -
        (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2))| +
      |velocitySecondRhs A C ε P Q N U V + U| ≤
        200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hΘ0 : 0 ≤ Θ := by linarith
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hΘ5 : 1 ≤ Θ ^ 5 := one_le_pow₀ hΘ
  have heupper : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hΘ5 he
    nlinarith only [hsmall, hm]
  have hεupper : ε ≤ 1 := hεe.trans heupper
  have hε2e : ε ^ 2 ≤ e := by nlinarith only [hε, hεupper, hεe]
  let ρ := 800 * e * Θ ^ 5
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρupper : ρ ≤ 1 / 2 := by dsimp [ρ]; nlinarith only [hsmall]
  obtain ⟨hn, hp, hq, hnabs, hw, hD, hDD⟩ :=
    ray_geometric_bounds (ε := ε) (U := U) (V := V) hΘ hρ hρupper hP₀ hQ₀ hP hQ hN
  let W := velocityThird P Q N U V
  let D := rayDenominator ε P Q N
  let D₀ := 1 + P₀ ^ 2
  let J := velocityNumerator A P Q N U V W
  let J₀ := (P₀ + β) * V + Q₀ * U
  let j := 147 * e * Θ ^ 4 + 2 * ρ
  let d := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have h45 : Θ ^ 4 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by decide)
  have hjupper : j ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left h45 (by positivity : 0 ≤ 147 * e)
    dsimp [j, ρ]
    nlinarith only [hsmall, hm]
  have hJ : |J - J₀| ≤ j * (|U| + |V|) := by
    have hh := velocity_numerator_error hΘ hρ (by positivity : 0 ≤ 3 * e) hβ hA hp hq hnabs hP hQ hN hw
    dsimp [J, J₀, W, j]
    nlinarith only [hh]
  have hJ₀ : |J₀| ≤ 2 * Θ ^ 2 * (|U| + |V|) := by
    have hcoef : |P₀ + β| ≤ 2 * Θ ^ 2 := by linarith [abs_add_le P₀ β]
    have hh := three_term_bound (p := V) (q := U) (n := (0 : ℝ)) hcoef hQ₀
      (show |(0 : ℝ)| ≤ 2 * Θ ^ 2 by simp; positivity)
    dsimp [J₀]
    simpa only [zero_mul, add_zero, norm3, abs_zero, add_comm] using hh
  have hD₀ : 1 ≤ D₀ := by dsimp [D₀]; nlinarith [sq_nonneg P₀]
  have hproj := velocity_projection_error (ε := ε) hΘ hρ hd hj hjupper hD hD₀ hP hP₀ hp hq hDD hJ hJ₀
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm : norm3 U V W ≤ 7 * Θ ^ 2 * (|U| + |V|) := by
    unfold norm3
    have hm := mul_le_mul_of_nonneg_right hΘ2 hL
    nlinarith only [hw, hm]
  have hrow : ∀ i, |(C i 0 - idealUnprojectedEntry i 0) * U +
      (C i 1 - idealUnprojectedEntry i 1) * V +
      (C i 2 - idealUnprojectedEntry i 2) * W| ≤
      35 * e * Θ ^ 2 * (|U| + |V|) := by
    intro i
    have hh := three_term_bound (p := U) (q := V) (n := W) (hC i 0) (hC i 1) (hC i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 5 * e)
    nlinarith only [hh, hm]
  have hu := hrow 0
  have hv := hrow 1
  norm_num [idealUnprojectedEntry, Fin.ext_iff] at hu hv
  have htU := abs_add_le (-(C 0 0 * U + (C 0 1 - 2) * V + C 0 2 * W))
    (2 * P * J / D - 2 * P₀ * J₀ / D₀)
  have htV := abs_add_le (-((C 1 0 - 1) * U + C 1 1 * V + C 1 2 * W))
    (2 * ε ^ 2 * Q * J / D)
  rw [abs_neg] at htU htV
  have hUeq : velocityFirstRhs A C ε P Q N U V -
      (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2)) =
      -(C 0 0 * U + (C 0 1 - 2) * V + C 0 2 * W) +
        (2 * P * J / D - 2 * P₀ * J₀ / D₀) := by
    dsimp [velocityFirstRhs, W, J, J₀, D, D₀]; ring
  have hVeq : velocitySecondRhs A C ε P Q N U V + U =
      -((C 1 0 - 1) * U + C 1 1 * V + C 1 2 * W) + 2 * ε ^ 2 * Q * J / D := by
    dsimp [velocitySecondRhs, W, J, D]; ring
  rw [hUeq, hVeq]
  have hcoefficient : 70 * e * Θ ^ 2 +
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d + 72 * ε ^ 2 * Θ ^ 4) ≤
      200000 * e * Θ ^ 12 := by
    have h2 : Θ ^ 2 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h4 : Θ ^ 4 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h6 : Θ ^ 6 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h7 : Θ ^ 7 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h8 : Θ ^ 8 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h11 : Θ ^ 11 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have he2 := mul_le_mul_of_nonneg_left h2 he
    have he4 := mul_le_mul_of_nonneg_left h4 he
    have he6 := mul_le_mul_of_nonneg_left h6 he
    have he7 := mul_le_mul_of_nonneg_left h7 he
    have he8 := mul_le_mul_of_nonneg_left h8 he
    have he11 := mul_le_mul_of_nonneg_left h11 he
    have hε4 := mul_le_mul_of_nonneg_right hε2e (by positivity : 0 ≤ Θ ^ 4)
    have hε8 := mul_le_mul_of_nonneg_right hε2e (by positivity : 0 ≤ Θ ^ 8)
    dsimp [j, d, ρ]
    nlinarith only [he2, he4, he6, he7, he8, he11, hε4, hε8,
      mul_nonneg he (pow_nonneg hΘ0 12)]
  have hm := mul_le_mul_of_nonneg_right hcoefficient hL
  nlinarith only [htU, htV, hu, hv, hproj, hm]

end EulerPacketRay

end

end
