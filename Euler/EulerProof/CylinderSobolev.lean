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
import Euler.EulerProof.LiftedTransport

/-!
# Sobolev spaces on Euclidean space and on the cylinder

Fourier-analytic Sobolev norms and their transfer to the periodic cylinder:

* `EulerSmoothLimit` -- `divergence` and the smooth-limit vocabulary.
* `EulerSobolev`, `EulerSobolevProducts`, `EulerSobolevTransport`,
  `EulerSobolevDerivativeNorm` -- the Bessel-weighted Sobolev norm on
  `Domain d`, products, transport commutators and derivative norms.
* `EulerCylinderCoordinates` -- the chart identifying `Domain 4` with the lift
  tangent space, together with the covering and chart measures.
* `EulerCylinderSobolev`, `EulerCylinderAlgebra`, `EulerRealCylinder`,
  `EulerVectorCylinder` -- Sobolev norms for functions on the cylinder, the
  algebra property, and the real and vector-valued versions.

This is part 3 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

/-!
The smooth compactly supported limit step for the proposed Euler construction.
The hypotheses are summable uniform estimates for every actual iterated Fréchet
derivative of the increments. Smoothness and convergence of the limit are proved,
not assumed. The divergence is the usual coordinate trace of the first derivative.
-/

namespace EulerSmoothLimit

open Filter MeasureTheory
open scoped Topology ContDiff ENNReal

/-- The physical three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The trace of a continuous linear map, written in the standard Euclidean coordinates. -/
noncomputable def coordinateTrace : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single i 1))

/-- The coordinate formula is exactly the basis-independent linear-algebraic trace. -/
theorem coordinateTrace_eq_linearTrace (A : Space →L[ℝ] Space) :
    coordinateTrace A = LinearMap.trace ℝ Space A.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [coordinateTrace, Matrix.trace, LinearMap.toMatrix_apply]

/-- Classical divergence, defined canonically as the trace of the Fréchet derivative. -/
noncomputable def divergence (f : Space → Space) (x : Space) : ℝ :=
  LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap

theorem divergence_eq_coordinate_sum (f : Space → Space) (x : Space) :
    divergence f x = ∑ i : Fin 3, (fderiv ℝ f x (EuclideanSpace.single i 1)) i := by
  rw [divergence, ← coordinateTrace_eq_linearTrace]
  simp [coordinateTrace]

theorem divergence_eq_trace (f : Space → Space) (x : Space) :
    divergence f x = LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap :=
  rfl















end EulerSmoothLimit

end

section

/-!
Actual Fourier Sobolev estimates on Euclidean spaces. The Sobolev norm below is
the L² norm of `(1 + |ξ|²)^(s/2) 𝓕f(ξ)`, so its relation to the represented
function is explicit. All estimates are proved from inversion and Hölder.
-/

namespace EulerSobolev

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

/-- The real Euclidean domain of dimension `d`. -/
abbrev Domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Fourier weight defining the inhomogeneous Sobolev order `s`. -/
noncomputable def besselWeight (d : ℕ) (s : ℝ) (ξ : Domain d) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

theorem besselWeight_temperate (d : ℕ) (s : ℝ) :
    (besselWeight d s).HasTemperateGrowth :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow (Domain d) (s / 2)

theorem besselWeight_pos (d : ℕ) (s : ℝ) (ξ : Domain d) : 0 < besselWeight d s ξ := by
  unfold besselWeight
  positivity

theorem besselWeight_neg_mul (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d (-s) ξ * besselWeight d s ξ = 1 := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  have he : -s / 2 + s / 2 = 0 := by ring
  rw [he, Real.rpow_zero]

theorem besselWeight_add (d : ℕ) (s t : ℝ) (ξ : Domain d) :
    besselWeight d (s + t) ξ = besselWeight d s ξ * besselWeight d t ξ := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

/-- The reciprocal Bessel weight is in L² exactly in the range needed here. -/
theorem reciprocal_weight_memLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    MemLp (besselWeight d (-s)) 2 (volume : Measure (Domain d)) := by
  have hm : AEStronglyMeasurable (besselWeight d (-s)) (volume : Measure (Domain d)) :=
    (besselWeight_temperate d (-s)).1.continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have hi : Integrable (fun ξ : Domain d => (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa [Domain] using hs)
  apply hi.congr
  filter_upwards with ξ
  dsimp only [besselWeight]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- The reciprocal Fourier weight represented as a genuine `L²` element. -/
noncomputable def reciprocalWeightLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (reciprocal_weight_memLp d s hs).toLp (besselWeight d (-s))

/-- A finite Sobolev embedding constant: the `L²` norm of the reciprocal weight. -/
noncomputable def embeddingConstant (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) : ℝ :=
  ‖reciprocalWeightLp d s hs‖

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Fourier transform multiplied by the Sobolev weight. -/
noncomputable def weightedFourier (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) :=
  SchwartzMap.smulLeftCLM F (besselWeight d s) (𝓕 f)

omit [CompleteSpace F] in
theorem weightedFourier_apply (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    weightedFourier d s f ξ = besselWeight d s ξ • 𝓕 f ξ := by
  simp [weightedFourier, SchwartzMap.smulLeftCLM_apply_apply (besselWeight_temperate d s)]

/-- The inhomogeneous Fourier `Hˢ` norm of a Schwartz function. -/
noncomputable def sobolevNorm (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) : ℝ :=
  ‖(weightedFourier d s f).toLp 2‖

/-- Fourier inversion bounds a Schwartz function pointwise by the L¹ norm of its transform. -/
theorem norm_apply_le_fourier_L1 (d : ℕ) (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖ := by
  have h := SchwartzMap.norm_fourier_apply_le_toLp_one (𝓕 f) (-x)
  have he : ‖f x‖ = ‖𝓕 (𝓕 f) (-x)‖ := by
    change ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖
    rw [fourierInv_fourier_eq]
  exact he ▸ h

omit [CompleteSpace F] in
/-- Hölder with the reciprocal weight converts the Fourier L¹ norm into the Hˢ norm. -/
theorem fourier_L1_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) :
    ‖(𝓕 f).toLp 1‖ ≤ embeddingConstant d s hs * sobolevNorm d s f := by
  have hid : (besselWeight d (-s) • (weightedFourier d s f : Domain d → F)) =
      ((𝓕 f : 𝓢(Domain d, F)) : Domain d → F) := by
    ext ξ
    simp only [Pi.smul_apply', weightedFourier_apply, smul_smul, besselWeight_neg_mul, one_smul]
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    ((weightedFourier d s f).memLp 2 volume).1 (reciprocal_weight_memLp d s hs).1
  rw [hid] at hh
  have hfin : eLpNorm (besselWeight d (-s)) 2 volume *
      eLpNorm (weightedFourier d s f) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (reciprocal_weight_memLp d s hs).eLpNorm_ne_top
      ((weightedFourier d s f).memLp 2 volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono hfin hh
  simpa only [SchwartzMap.norm_toLp, embeddingConstant, reciprocalWeightLp,
    Lp.norm_toLp, sobolevNorm, ENNReal.toReal_mul] using h

/-- A genuine pointwise Sobolev embedding for every `s > d/2`. -/
theorem norm_apply_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ embeddingConstant d s hs * sobolevNorm d s f :=
  (norm_apply_le_fourier_L1 d f x).trans (fourier_L1_le_sobolevNorm d s hs f)

open scoped LineDeriv





/-- Coordinatewise complexification is an actual linear isometry of Euclidean spaces. -/
noncomputable def complexify (q : ℕ) :
    Domain q →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin q) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp









open Filter EulerSmoothLimit


end EulerSobolev

end

section

namespace EulerSobolevProducts

open MeasureTheory FourierTransform EulerSobolev
open scoped SchwartzMap ENNReal ContDiff LineDeriv Convolution




/-- Repeated differentiation in one fixed direction, as a Schwartz function. -/
noncomputable def directional (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) := ∂^{fun _ : Fin n => v} f

theorem directional_eq_iteratedDeriv (d n : ℕ) (v x : Domain d)
    (f : 𝓢(Domain d, ℂ)) :
    directional d n v f x = iteratedDeriv n (fun t : ℝ => f (x + t • v)) 0 := by
  rw [directional, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] Domain d := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hC : ContDiff ℝ ∞ (fun z => f (x + z)) := f.smooth'.comp (contDiff_const.add contDiff_id)
  have he := L.iteratedFDeriv_comp_right hC (0 : ℝ) (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change iteratedFDeriv ℝ n f x (fun _ => v) = _
  change _ = iteratedFDeriv ℝ n ((fun z => f (x + z)) ∘ L) 0 (fun _ => 1)
  rw [he]
  simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]

/-- Pointwise multiplication of two complex Schwartz functions. -/
noncomputable def product (d : ℕ) (f g : 𝓢(Domain d, ℂ)) : 𝓢(Domain d, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem product_apply (d : ℕ) (f g : 𝓢(Domain d, ℂ)) (x : Domain d) :
    product d f g x = f x * g x := rfl

theorem directional_product (d n : ℕ) (v : Domain d) (f g : 𝓢(Domain d, ℂ)) :
    directional d n v (product d f g) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) •
        product d (directional d j v f) (directional d (n-j) v g) := by
  ext x
  simp only [directional_eq_iteratedDeriv, product_apply, sum_apply,
    smul_apply, smul_eq_mul]
  have hf : ContDiff ℝ ∞ (fun t : ℝ => f (x + t • v)) :=
    f.smooth'.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hg : ContDiff ℝ ∞ (fun t : ℝ => g (x + t • v)) :=
    g.smooth'.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  simpa only [Pi.mul_apply, mul_assoc] using iteratedDeriv_fun_mul
    (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt



theorem fourier_directional_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, ℂ)) (ξ : Domain d) :
    ‖𝓕 (directional d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖ := by
  induction n with
  | zero => simp [directional]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : directional d (n+1) v f = ∂_{v} (directional d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, ℂ))
    (g : ι → 𝓢(Domain d, ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ∑ i, ‖g i x‖) :
    ‖f.toLp 2‖ ≤ C * ∑ i, ‖(g i).toLp 2‖ := by
  have hs : ∀ᵐ x ∂(volume : Measure (Domain d)), ∀ i, normLp d (g i) x = ‖g i x‖ :=
    Filter.eventually_all.2 (fun i => coe_normLp d (g i))
  have hb : ‖f.toLp 2‖ ≤ C * ‖∑ i, normLp d (g i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [f.coeFn_toLp 2, Lp.coeFn_finsetSum Finset.univ (fun i => normLp d (g i)), hs]
      with x hf hsum hx
    rw [hf, hsum]
    simp only [Finset.sum_apply, hx, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact h x
  refine hb.trans ?_
  calc
    _ ≤ C * ∑ i, ‖normLp d (g i)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = _ := by simp only [norm_normLp]





attribute [local irreducible] sobolevNorm embeddingConstant






end EulerSobolevProducts

end

-- Component: SobolevTransport.lean

section

/-!
The fixed-order transport commutator estimate.
-/

namespace EulerSobolevTransport

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts
open scoped SchwartzMap ENNReal ContDiff LineDeriv




attribute [local irreducible] sobolevNorm embeddingConstant



/-- The actual commutator of an iterated directional derivative with multiplication. -/
noncomputable def commutator (d n : ℕ) (v : Domain d) (b h : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) :=
  directional d n v (product d b h) - product d b (directional d n v h)





end EulerSobolevTransport

end

section

/-! The Fourier H³ norm is controlled by genuine third directional derivatives in L². -/

namespace EulerSobolevDerivativeNorm

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts
open scoped SchwartzMap ENNReal ContDiff LineDeriv


theorem norm_le_sum_coordinates (d : ℕ) (ξ : Domain d) : ‖ξ‖ ≤ ∑ i, ‖ξ i‖ := by
  have he : (∑ i : Fin d, EuclideanSpace.single i (ξ i)) = ξ := by
    ext j
    simp
  calc
    ‖ξ‖ = ‖∑ i : Fin d, EuclideanSpace.single i (ξ i)‖ := by rw [he]
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (ξ i)‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The operator norm of a derivative tensor is bounded by the sum of its coordinate entries. -/
theorem multilinear_norm_le_coordinate_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d n : ℕ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Domain d) F) :
    ‖T‖ ≤ ∑ w : Fin n → Fin d,
      ‖T (fun j => EuclideanSpace.single (w j) 1)‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro m
  have hm (j : Fin n) : (∑ i : Fin d, (m j i) • EuclideanSpace.single i (1 : ℝ)) = m j := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hexpand : T m = ∑ w : Fin n → Fin d,
      T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ)) := by
    change T.toMultilinearMap m = ∑ w : Fin n → Fin d,
      T.toMultilinearMap (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))
    have h := T.toMultilinearMap.map_sum
      (fun (j : Fin n) (i : Fin d) => (m j i) • EuclideanSpace.single i (1 : ℝ))
    simpa only [hm] using h
  rw [hexpand]
  calc
    _ ≤ ∑ w : Fin n → Fin d,
        ‖T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ w : Fin n → Fin d, (∏ j, ‖m j (w j)‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [T.map_smul_univ, norm_smul, norm_prod]
    _ ≤ ∑ w : Fin n → Fin d, (∏ j, ‖m j‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => PiLp.norm_apply_le (m j) (w j))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem besselWeight_one_le_coordinate_sum (d : ℕ) (ξ : Domain d) :
    besselWeight d 1 ξ ≤ 1 + ∑ i, ‖ξ i‖ := by
  have h : besselWeight d 1 ξ ≤ 1 + ‖ξ‖ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [norm_nonneg ξ]
  exact h.trans (by linarith [norm_le_sum_coordinates d ξ])

theorem besselWeight_three_le_pure_three (d : ℕ) (ξ : Domain d) :
    besselWeight d 3 ξ ≤ ((d : ℝ) + 1) ^ 2 * (1 + ∑ i, ‖ξ i‖ ^ 3) := by
  let a : Option (Fin d) → ℝ := fun i => match i with
    | none => 1
    | some i => ‖ξ i‖
  have ha : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ a i := by
    intro i _
    cases i <;> simp only [a] <;> positivity
  have h := pow_sum_le_card_mul_sum_pow ha 2
  have he : besselWeight d 3 ξ = (besselWeight d 1 ξ) ^ 3 := by
    unfold besselWeight
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    norm_num
  rw [he]
  apply (pow_le_pow_left₀ (besselWeight_pos d 1 ξ).le
    (besselWeight_one_le_coordinate_sum d ξ) 3).trans
  simpa [a, Fintype.sum_option] using h

theorem sobolevNorm_three_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 3 f ≤ ((d : ℝ) + 1) ^ 2 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin d, ‖(directional d 3 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, ℂ) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-3 : ℤ) : ℝ) •
        𝓕 (directional d 3 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 3 f ξ‖ ≤ ((d : ℝ) + 1) ^ 2 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 3 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 3) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-3 : ℤ)),
        fourier_directional_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-3 : ℤ) * (2 * Real.pi) ^ (3 : ℕ) = 1 := by
        rw [show (-3 : ℤ) = -(3 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (besselWeight_three_le_pure_three d ξ) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 3 f) g (((d : ℝ) + 1) ^ 2)
    (sq_nonneg _) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-3 : ℤ) * ∑ i : Fin d,
        ‖(directional d 3 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (((2 * Real.pi) ^ (-3 : ℤ)) •
        𝓕 (directional d 3 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-3 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- Four-dimensional Sobolev embedding stated solely with actual L² derivative norms. -/
theorem pointwise_le_L2_third_derivatives (f : 𝓢(Domain 4, ℂ)) (x : Domain 4) :
    ‖f x‖ ≤ embeddingConstant 4 3 (by norm_num) * 25 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin 4, ‖(directional 4 3 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 4 3 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_three_le_pure_derivatives 4 f)
    (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _)
  refine hA.trans (hB.trans_eq ?_)
  norm_num
  ring

end EulerSobolevDerivativeNorm

end

section

/-! Measure-preserving Euclidean coordinates and the actual L² bridge to the cylinder. -/

namespace EulerCylinderCoordinates

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal NNReal Topology SchwartzMap


/-- Euclidean coordinate zero is the angle; coordinates one through three are spatial. -/
noncomputable def coordinateLinearEquiv : Domain 4 ≃ₗ[ℝ] LiftTangent where
  toFun z := (WithLp.toLp 2 (fun i : Fin 3 => z i.succ), z 0)
  invFun p := WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i))
  left_inv z := by
    ext i
    cases i using Fin.cases <;> simp
  right_inv p := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_add' z w := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_smul' c z := by
    apply Prod.ext
    · ext i
      simp
    · simp

/-- The coordinate isomorphism, continuous in both directions. -/
noncomputable def coordinateEquiv : Domain 4 ≃L[ℝ] LiftTangent :=
  coordinateLinearEquiv.toContinuousLinearEquiv

@[simp] theorem coordinateEquiv_apply (z : Domain 4) :
    coordinateEquiv z = (WithLp.toLp 2 (fun i : Fin 3 => z i.succ), z 0) := rfl

@[simp] theorem coordinateEquiv_symm_apply (p : LiftTangent) :
    coordinateEquiv.symm p = WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i)) := rfl

/-- The coordinate change preserves the genuine product Lebesgue measure exactly. -/
theorem coordinateEquiv_measurePreserving :
    MeasurePreserving coordinateEquiv (volume : Measure (Domain 4))
      ((volume : Measure Vector3).prod (volume : Measure ℝ)) := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin 4)
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have h₃ : MeasurePreserving (Prod.swap : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  have h₄ := (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id (μ := volume (α := ℝ)))
  have h := h₄.comp (h₃.comp (h₂.comp h₁))
  convert! h using 1

variable (period : ℝ) [Fact (0 < period)]

/-- A fundamental strip in the real covering space. -/
noncomputable def fundamentalMeasure (a : ℝ) : Measure LiftTangent :=
  (volume : Measure Vector3).prod (volume.restrict (Set.Ioc a (a + period)))

/-- Covering coordinates restricted to one period preserve the cylinder's measure. -/
theorem covering_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving (coveringMap period) (fundamentalMeasure period a) (liftMeasure period) :=
  (MeasurePreserving.id (μ := (volume : Measure Vector3))).prod (AddCircle.measurePreserving_mk period a)

/-- Euclidean coordinates for the actual quotient covering map. -/
noncomputable def euclideanCover : Domain 4 → LiftDomain period :=
  coveringMap period ∘ coordinateEquiv

/-- Euclidean measure restricted to one fundamental angular strip. -/
noncomputable def stripMeasure (a : ℝ) : Measure (Domain 4) :=
  volume.restrict {z : Domain 4 | z 0 ∈ Set.Ioc a (a + period)}

omit [Fact (0 < period)] in
theorem coordinateEquiv_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving coordinateEquiv (stripMeasure period a) (fundamentalMeasure period a) := by
  have hm : MeasurableSet ((Set.univ : Set Vector3) ×ˢ Set.Ioc a (a + period)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have h := coordinateEquiv_measurePreserving.restrict_preimage hm
  have he : coordinateEquiv ⁻¹' ((Set.univ : Set Vector3) ×ˢ Set.Ioc a (a + period)) =
      {z : Domain 4 | z 0 ∈ Set.Ioc a (a + period)} := by
    ext z
    simp
  rw [he] at h
  simpa only [stripMeasure, fundamentalMeasure, ← Measure.prod_restrict,
    Measure.restrict_univ] using h

theorem euclideanCover_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving (euclideanCover period) (stripMeasure period a) (liftMeasure period) :=
  (covering_fundamental_measurePreserving period a).comp
    (coordinateEquiv_fundamental_measurePreserving period a)


/-- Square integrability of actual fields transfers to their Euclidean periodic lifts. -/
theorem memLp_cover {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) (a : ℝ) :
    MemLp (f ∘ euclideanCover period) 2 (stripMeasure period a) :=
  hf.comp_measurePreserving (euclideanCover_fundamental_measurePreserving period a)


/-- Six consecutive fundamental strips, retaining the actual Euclidean measures. -/
noncomputable def chartMeasure : Measure (Domain 4) :=
  Measure.sum (fun i : Fin 6 => stripMeasure period (((i : ℝ) - 3) * period))

theorem chartSupport_cover : ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) ⊆
    ⋃ i : Fin 6, {z : Domain 4 | z 0 ∈
      Set.Ioc (((i : ℝ)-3)*period) ((((i : ℝ)-3)*period)+period)} := by
  intro z hz
  have hT : 0 < period := Fact.out
  have hz' := abs_le.1 (show |z 0| ≤ 2 * period from hz)
  by_cases h₀ : z 0 ≤ -2 * period
  · apply Set.mem_iUnion.2 ⟨0, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₁ : z 0 ≤ -period
  · apply Set.mem_iUnion.2 ⟨1, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₂ : z 0 ≤ 0
  · apply Set.mem_iUnion.2 ⟨2, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₃ : z 0 ≤ period
  · apply Set.mem_iUnion.2 ⟨3, ?_⟩
    norm_num
    constructor <;> linarith
  · apply Set.mem_iUnion.2 ⟨4, ?_⟩
    norm_num
    constructor <;> linarith

theorem chartSupport_measure_le :
    volume.restrict (({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period})) ≤ chartMeasure period :=
  (Measure.restrict_mono_set volume (chartSupport_cover period)).trans Measure.restrict_iUnion_le

/-- The finite chart cover has exactly six times the cylinder measure. -/
theorem euclideanCover_chart_measurePreserving :
    MeasurePreserving (euclideanCover period) (chartMeasure period)
      ((6 : ℝ≥0∞) • liftMeasure period) := by
  have hm := (euclideanCover_fundamental_measurePreserving period 0).measurable
  refine ⟨hm, ?_⟩
  rw [chartMeasure, Measure.sum_fintype, Measure.map_finset_sum' hm.aemeasurable]
  simp only [(euclideanCover_fundamental_measurePreserving period _).map_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℝ≥0∞ 6 (liftMeasure period)).symm

theorem eLpNorm_cover_chart {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period)) :
    eLpNorm (f ∘ euclideanCover period) 2 (chartMeasure period) =
      (6 : ℝ≥0∞) ^ (1/2 : ℝ) * eLpNorm f 2 (liftMeasure period) := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure _)
    (euclideanCover_chart_measurePreserving period)]
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
  norm_num

/-- A localized lift is controlled by the genuine cylinder norm, with explicit chart multiplicity. -/
theorem eLpNorm_localized_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period))
    (g : Domain 4 → G) (hsupp : Function.support g ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}))
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B * ‖f (euclideanCover period z)‖) :
    eLpNorm g 2 volume ≤ (B : ℝ≥0∞) * (6 : ℝ≥0∞) ^ (1/2 : ℝ) *
      eLpNorm f 2 (liftMeasure period) := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  calc
    _ ≤ eLpNorm g 2 (chartMeasure period) := eLpNorm_mono_measure g (chartSupport_measure_le period)
    _ ≤ (B : ℝ≥0∞) * eLpNorm (f ∘ euclideanCover period) 2 (chartMeasure period) :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall hb) 2
    _ = _ := by rw [eLpNorm_cover_chart period f hf, mul_assoc]

/-- The localized-lift estimate as an inequality between ordinary real L² norms. -/
theorem localized_L2_le {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period))
    (g : 𝓢(Domain 4, ℂ)) (hsupp : Function.support g ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}))
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B * ‖f (euclideanCover period z)‖) :
    ‖g.toLp 2‖ ≤ (B : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * ‖hf.toLp f‖ := by
  have h := eLpNorm_localized_le period f hf.1 g hsupp B hb
  have hfin : (B : ℝ≥0∞) * (6 : ℝ≥0∞) ^ (1/2 : ℝ) *
      eLpNorm f 2 (liftMeasure period) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfin h
  simpa only [SchwartzMap.norm_toLp, Lp.norm_toLp, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] using hreal

end EulerCylinderCoordinates

end

section

/-! Actual derivative-word Sobolev norms on R³ × T and compact localizations. -/

namespace EulerCylinderSobolev

open MeasureTheory EulerSobolev EulerSobolevProducts EulerSobolevDerivativeNorm
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open EulerCylinderCoordinates
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv


/-- The four coordinate directions, with angle first and the spatial coordinates following. -/
noncomputable def standardDirection (i : Fin 4) : LiftTangent :=
  coordinateEquiv (EuclideanSpace.single i 1)

@[simp] theorem standardDirection_zero : standardDirection 0 = (0,1) := by
  apply Prod.ext
  · ext i
    simp [standardDirection]
  · simp [standardDirection]

@[simp] theorem standardDirection_succ (i : Fin 3) :
    standardDirection i.succ = (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [standardDirection]
  · simp [standardDirection]

variable (period : ℝ)

section Fields

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordered actual derivatives on the cylinder; the head is differentiated last. -/
noncomputable def iteratedFieldDerivative : {n : ℕ} → (Fin n → Fin 4) →
    (LiftDomain period → F) → LiftDomain period → F
  | 0, _, f => f
  | _n+1, w, f => fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative (Fin.tail w) f)

@[simp] theorem iteratedFieldDerivative_zero (w : Fin 0 → Fin 4) (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = f := rfl

@[simp] theorem iteratedFieldDerivative_succ {n : ℕ} (w : Fin (n+1) → Fin 4)
    (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative period (Fin.tail w) f) := rfl

/-- A concrete norm: the sum of L² norms of all ordered coordinate derivatives up to order `s`. -/
noncomputable def liftSobolevNorm (s : ℕ) (f : LiftDomain period → F)
    [Fact (0 < period)] : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun n => ∑ w : Fin n → Fin 4,
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal)

theorem iteratedFieldDerivative_smooth {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (iteratedFieldDerivative period w f) x) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact fieldDerivative_smooth period _ _ (ih (Fin.tail w))

/-- The actual field lifted to Euclidean coordinates centered at a cylinder point. -/
noncomputable def euclideanLift (f : LiftDomain period → F) (x : LiftDomain period) : Domain 4 → F :=
  localFieldLift period f x ∘ coordinateEquiv

theorem euclideanLift_smooth (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (euclideanLift period f x) := (hf x).comp coordinateEquiv.contDiff

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem euclideanLift_zero (f : LiftDomain period → F) (x : LiftDomain period) :
    euclideanLift period f x 0 = f x := by
  change localFieldLift period f x (coordinateEquiv 0) = _
  rw [map_zero]
  simp [localFieldLift]

theorem euclideanLift_fieldDerivative (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (v z : Domain 4)
    (x : LiftDomain period) :
    euclideanLift period (fieldDerivative period (coordinateEquiv v) f) x z =
      fderiv ℝ (euclideanLift period f x) z v := by
  have hchain := ((hf x).differentiable (by simp) (coordinateEquiv z)).hasFDerivAt.comp z
    coordinateEquiv.hasFDerivAt
  rw [euclideanLift, localFieldLift_fieldDerivative]
  change fderiv ℝ (localFieldLift period f x) (coordinateEquiv z) (coordinateEquiv v) = _
  rw [show fderiv ℝ (euclideanLift period f x) z =
      (fderiv ℝ (localFieldLift period f x) (coordinateEquiv z)).comp
        coordinateEquiv.toContinuousLinearMap from hchain.fderiv]
  rfl

/-- The word derivative is exactly the corresponding coordinate entry of the Fréchet tensor. -/
theorem euclideanLift_iteratedFieldDerivative {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : LiftDomain period) (z : Domain 4) :
    euclideanLift period (iteratedFieldDerivative period w f) x z =
      iteratedFDeriv ℝ n (euclideanLift period f x) z
        (fun j => EuclideanSpace.single (w j) 1) := by
  induction n generalizing z with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, standardDirection,
      euclideanLift_fieldDerivative _ _ (iteratedFieldDerivative_smooth period (Fin.tail w) f hf),
      iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply]
    · congr 2
      funext y
      exact ih (Fin.tail w) y
    · exact (euclideanLift_smooth period f hf x).differentiable_iteratedFDeriv
        (show (n : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top n) z

/-- Tensor operator norms are controlled by the actual coordinate-word derivatives. -/
theorem euclideanLift_tensor_norm_le (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) z‖ ≤
      ∑ w : Fin n → Fin 4, ‖euclideanLift period (iteratedFieldDerivative period w f) x z‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 n (iteratedFDeriv ℝ n (euclideanLift period f x) z)
  simpa only [euclideanLift_iteratedFieldDerivative period _ f hf] using h

/-- Sum of the norms of all coordinate words of one fixed order. -/
noncomputable def wordMagnitude (n : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) : ℝ :=
  ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w f x‖

theorem wordMagnitude_nonneg (n : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) :
    0 ≤ wordMagnitude period n f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The sum of all coordinate derivative magnitudes through a given order. -/
noncomputable def totalMagnitude (s : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun n => wordMagnitude period n f x)

theorem totalMagnitude_nonneg (s : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) :
    0 ≤ totalMagnitude period s f x :=
  Finset.sum_nonneg (fun n _ => wordMagnitude_nonneg period n f x)

theorem wordMagnitude_le_total (s n : ℕ) (hn : n ≤ s) (f : LiftDomain period → F)
    (x : LiftDomain period) : wordMagnitude period n f x ≤ totalMagnitude period s f x :=
  Finset.single_le_sum (fun j _ => wordMagnitude_nonneg period j f x)
    (Finset.mem_range.2 (by omega))

end Fields

section Translations

variable [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F]

/-- Translation of an actual cylinder function. -/
noncomputable def translated (f : LiftDomain period → F) (x : LiftDomain period) :
    LiftDomain period → F := fun y => f (y + x)

theorem eLpNorm_translated (f : LiftDomain period → F)
    (hf : AEStronglyMeasurable f (liftMeasure period)) (x : LiftDomain period) :
    eLpNorm (translated period f x) 2 (liftMeasure period) = eLpNorm f 2 (liftMeasure period) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_translation period x)

theorem memLp_translated (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) (x : LiftDomain period) :
    MemLp (translated period f x) 2 (liftMeasure period) :=
  hf.comp_measurePreserving (measurePreserving_translation period x)

variable [NormedSpace ℝ F]

omit [Fact (0 < period)] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem euclideanLift_eq_translated_cover (f : LiftDomain period → F)
    (x : LiftDomain period) (z : Domain 4) :
    euclideanLift period f x z = translated period f x (euclideanCover period z) := by
  change f (x.1 + (coordinateEquiv z).1, x.2 + ((coordinateEquiv z).2 : AddCircle period)) =
    f ((coveringMap period (coordinateEquiv z)) + x)
  congr 1
  ext <;> simp [coveringMap, add_comm]

theorem wordMagnitude_memLp (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    MemLp (wordMagnitude period n f) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun w _ => (hf w).norm)

theorem eLpNorm_wordMagnitude_le (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    eLpNorm (wordMagnitude period n f) 2 (liftMeasure period) ≤
      ∑ w : Fin n → Fin 4, eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period) := by
  have he : wordMagnitude period n f = ∑ w : Fin n → Fin 4,
      (fun x => ‖iteratedFieldDerivative period w f x‖) := by
    funext x
    simp [wordMagnitude]
  rw [he]
  simpa only [eLpNorm_norm] using eLpNorm_sum_le
    (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) => (hf w).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem totalMagnitude_memLp (s : ℕ) (f : LiftDomain period → F)
    (hf : ∀ n ≤ s, ∀ w : Fin n → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    MemLp (totalMagnitude period s f) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun n hn => wordMagnitude_memLp period n f (hf n (by simpa using Finset.mem_range.1 hn)))

theorem totalMagnitude_L2_le (s : ℕ) (f : LiftDomain period → F)
    (hf : ∀ n ≤ s, ∀ w : Fin n → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    ‖(totalMagnitude_memLp period s f hf).toLp (totalMagnitude period s f)‖ ≤
      liftSobolevNorm period s f := by
  have he : totalMagnitude period s f = ∑ n ∈ Finset.range (s+1), wordMagnitude period n f := by
    funext x
    simp [totalMagnitude]
  have hA : eLpNorm (totalMagnitude period s f) 2 (liftMeasure period) ≤
      ∑ n ∈ Finset.range (s+1), eLpNorm (wordMagnitude period n f) 2 (liftMeasure period) := by
    rw [he]
    exact eLpNorm_sum_le (fun n hn =>
      (wordMagnitude_memLp period n f (hf n (by simpa using Finset.mem_range.1 hn))).1) (by norm_num)
  have hB : (∑ n ∈ Finset.range (s+1), eLpNorm (wordMagnitude period n f) 2 (liftMeasure period)) ≤
      ∑ n ∈ Finset.range (s+1), ∑ w : Fin n → Fin 4,
        eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period) := by
    exact Finset.sum_le_sum (fun n hn => eLpNorm_wordMagnitude_le period n f
      (hf n (by simpa using Finset.mem_range.1 hn)))
  have hfin (n : ℕ) (hn : n ∈ Finset.range (s+1)) :
      (∑ w : Fin n → Fin 4, eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun w _ => (hf n (by simpa using Finset.mem_range.1 hn) w).eLpNorm_ne_top)
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) (hA.trans hB)
  rw [Lp.norm_toLp]
  convert hreal using 1
  rw [ENNReal.toReal_sum hfin]
  apply Finset.sum_congr rfl
  intro n hn
  exact (ENNReal.toReal_sum (fun w _ =>
    (hf n (by simpa using Finset.mem_range.1 hn) w).eLpNorm_ne_top)).symm

end Translations

variable [Fact (0 < period)]

/-- A fixed compact smooth localizer, supported in the chart neighborhood and equal to one at zero. -/
noncomputable def localBump : ContDiffBump (0 : Domain 4) where
  rIn := period
  rOut := 2 * period
  rIn_pos := Fact.out
  rIn_lt_rOut := by have h : 0 < period := Fact.out; linarith

theorem localBump_smooth : ContDiff ℝ ∞ (localBump period) := (localBump period).contDiff

theorem localBump_zero : localBump period 0 = 1 :=
  (localBump period).one_of_mem_closedBall
    (by simpa [localBump] using (show 0 ≤ period from (Fact.out : 0 < period).le))

theorem localBump_support : tsupport (localBump period) ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) := by
  rw [(localBump period).tsupport_eq]
  intro z hz
  have hnorm : ‖z‖ ≤ 2 * period := by simpa [localBump] using hz
  exact (PiLp.norm_apply_le z 0).trans hnorm

/-- The local bump regarded as a real Schwartz function. -/
noncomputable def bumpSchwartz : 𝓢(Domain 4, ℝ) :=
  (localBump period).hasCompactSupport.toSchwartzMap (localBump_smooth period)

/-- A finite, explicitly defined bound for each derivative of the fixed local bump. -/
noncomputable def bumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j (bumpSchwartz period), apply_nonneg _ _⟩

theorem localBump_derivative_bound (j : ℕ) (z : Domain 4) :
    ‖iteratedFDeriv ℝ j (localBump period) z‖ ≤ bumpBound period j :=
  SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (bumpSchwartz period) j z

/-- Finite Leibniz coefficient controlling localization at derivative order `n`. -/
noncomputable def bumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * bumpBound period j)

/-- An actual compactly supported localization of an arbitrary smooth cylinder field. -/
noncomputable def localized (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) : 𝓢(Domain 4, ℂ) :=
  ((localBump period).hasCompactSupport.smul_right (f' := euclideanLift period f x)).toSchwartzMap
    ((localBump_smooth period).smul (euclideanLift_smooth period f hf x))

@[simp] theorem localized_apply (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    localized period f hf x z = localBump period z • euclideanLift period f x z := rfl

theorem localized_zero (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    localized period f hf x 0 = f x := by
  rw [localized_apply, localBump_zero, one_smul, euclideanLift_zero]

theorem localized_tsupport (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    tsupport (localized period f hf x) ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) :=
  (tsupport_smul_subset_left (localBump period) (euclideanLift period f x)).trans
    (localBump_support period)

/-- The actual Leibniz rule controls every localized derivative by cylinder derivative words. -/
theorem localized_tensor_norm_le (n : ℕ) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ n (localized period f hf x) z‖ ≤
      bumpCoefficient period n * translated period (totalMagnitude period n f) x
        (euclideanCover period z) := by
  have hA := norm_iteratedFDeriv_smul_le (localBump_smooth period)
    (euclideanLift_smooth period f hf x) z (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  change (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
    ‖iteratedFDeriv ℝ j (localBump period) z‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period f x) z‖) ≤ _
  have hB (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period f x) z‖ ≤
        translated period (totalMagnitude period n f) x (euclideanCover period z) := by
    have hT := euclideanLift_tensor_norm_le period (n-j) f hf x z
    simp only [euclideanLift_eq_translated_cover, translated] at hT
    exact hT.trans (wordMagnitude_le_total period n (n-j) (by omega) f _)
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * bumpBound period j) *
        translated period (totalMagnitude period n f) x (euclideanCover period z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (localBump_derivative_bound period j z) (Nat.cast_nonneg _))
        (hB j hj) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (bumpBound period j).coe_nonneg)
    _ = _ := by simp only [bumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast,
      Finset.sum_mul]

/-- Each pure directional derivative of the localization has the same chart support. -/
theorem directional_localized_support (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    Function.support (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x)) ⊆
      ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) := by
  have he : (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x) :
      Domain 4 → ℂ) = (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Domain 4) ℂ =>
        T (fun _ => EuclideanSpace.single i 1)) ∘ iteratedFDeriv ℝ n (localized period f hf x) := by
    funext z
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
  rw [he]
  exact subset_closure.trans ((tsupport_comp_subset (by simp) _).trans
    ((tsupport_iteratedFDeriv_subset n).trans (localized_tsupport period f hf x)))

/-- Every localized pure derivative is controlled by the actual cylinder derivative L² sum. -/
theorem localized_directional_L2_le (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ n, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖(directional 4 n (EuclideanSpace.single i 1) (localized period f hf x)).toLp 2‖ ≤
      (bumpCoefficient period n : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * liftSobolevNorm period n f := by
  let q := totalMagnitude period n f
  have hq : MemLp q 2 (liftMeasure period) := totalMagnitude_memLp period n f hfL2
  have hqt := memLp_translated period q hq x
  have hb (z : Domain 4) :
      ‖directional 4 n (EuclideanSpace.single i 1) (localized period f hf x) z‖ ≤
        (bumpCoefficient period n : ℝ) * ‖translated period q x (euclideanCover period z)‖ := by
    rw [directional, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    have hA := (iteratedFDeriv ℝ n (localized period f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    have hB := localized_tensor_norm_le period n f hf x z
    change _ ≤ (bumpCoefficient period n : ℝ) * ‖totalMagnitude period n f (_ + x)‖
    rw [Real.norm_of_nonneg (totalMagnitude_nonneg period n f _)]
    exact hA.trans hB
  have hA := localized_L2_le period (translated period q x) hqt
    (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x))
    (directional_localized_support period n i f hf x) (bumpCoefficient period n) hb
  have hnorm : ‖hqt.toLp (translated period q x)‖ = ‖hq.toLp q‖ := by
    simp only [Lp.norm_toLp, eLpNorm_translated period q hq.1]
  rw [hnorm] at hA
  exact hA.trans (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period n f hfL2)
    (mul_nonneg (bumpCoefficient period n).coe_nonneg (Real.rpow_nonneg (by norm_num) _)))

theorem liftSobolevNorm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℕ) (f : LiftDomain period → F) : 0 ≤ liftSobolevNorm period s f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem liftSobolevNorm_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s t : ℕ} (hst : s ≤ t) (f : LiftDomain period → F) :
    liftSobolevNorm period s f ≤ liftSobolevNorm period t f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro n _ _
  exact Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

/-- A concrete finite embedding constant depending only on the circle period. -/
noncomputable def cylinderEmbeddingConstant : ℝ :=
  embeddingConstant 4 3 (by norm_num) * 25 * (6 : ℝ) ^ (1/2 : ℝ) *
    ((bumpCoefficient period 0 : ℝ) + (2 * Real.pi) ^ (-3 : ℤ) * 4 * bumpCoefficient period 3)

theorem cylinderEmbeddingConstant_nonneg : 0 ≤ cylinderEmbeddingConstant period := by
  unfold cylinderEmbeddingConstant
  have hc : 0 ≤ embeddingConstant 4 3 (by norm_num) := norm_nonneg _
  positivity

/-- Genuine H³ to L∞ embedding on R³ × T for arbitrary smooth fields with square-integrable derivatives. -/
theorem cylinder_pointwise_le_H3 (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
  have hbase := localized_directional_L2_le period 0 0 f hf
    (fun j hj => hfL2 j (by omega)) x
  have he : directional 4 0 (EuclideanSpace.single 0 1) (localized period f hf x) =
      localized period f hf x := by ext z; simp [directional]
  rw [he] at hbase
  have hbase' := hbase.trans (mul_le_mul_of_nonneg_left
    (liftSobolevNorm_mono period (show 0 ≤ 3 by omega) f)
    (mul_nonneg (bumpCoefficient period 0).coe_nonneg (Real.rpow_nonneg (by norm_num) _)))
  have hthird : (∑ i : Fin 4,
      ‖(directional 4 3 (EuclideanSpace.single i 1) (localized period f hf x)).toLp 2‖) ≤
        4 * ((bumpCoefficient period 3 : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * liftSobolevNorm period 3 f) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      localized_directional_L2_le period 3 i f hf hfL2 x)
  have hA := pointwise_le_L2_third_derivatives (localized period f hf x) 0
  rw [localized_zero] at hA
  have hB := add_le_add hbase' (mul_le_mul_of_nonneg_left hthird
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (-3 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB
    (mul_nonneg (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 25))
  refine hA.trans (hC.trans_eq ?_)
  unfold cylinderEmbeddingConstant
  ring

section WordComposition
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
/-- Composing two actual derivative words gives a word of the combined length. -/
theorem iteratedFieldDerivative_comp_exists {m n : ℕ} (v : Fin n → Fin 4)
    (w : Fin m → Fin 4) (f : LiftDomain period → F) :
    ∃ u : Fin (m+n) → Fin 4, iteratedFieldDerivative period v
      (iteratedFieldDerivative period w f) = iteratedFieldDerivative period u f := by
  induction n with
  | zero => exact ⟨w, rfl⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih (Fin.tail v)
    refine ⟨Fin.cons (v 0) u, ?_⟩
    simp only [iteratedFieldDerivative_succ, Fin.cons_zero, Fin.tail_cons, hu]

theorem word_L2_le_liftSobolevNorm {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → F) :
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      liftSobolevNorm period s f := by
  have hA : (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      ∑ v : Fin n → Fin 4, (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal :=
    Finset.single_le_sum (f := fun v : Fin n → Fin 4 =>
      (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ w)
  have hB : (∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal) ≤
        liftSobolevNorm period s f :=
    Finset.single_le_sum (s := Finset.range (s+1)) (a := n)
      (f := fun j => ∑ v : Fin j → Fin 4,
        (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
      (Finset.mem_range.2 (by omega))
  exact hA.trans hB

theorem word_memLp {s m n : ℕ} (h : m+n ≤ s) (v : Fin n → Fin 4) (w : Fin m → Fin 4)
    (f : LiftDomain period → F)
    (hfL2 : ∀ j ≤ s, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
      (liftMeasure period) := by
  obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
  rw [hu]
  exact hfL2 (m+n) h u

theorem word_H3_le_H6 {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → F) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period 6 f := by
  have hA : (∑ n ∈ Finset.range (3+1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3+1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period 6 f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

end WordComposition

/-- Uniform control of any derivative word of order at most three by the H⁶ norm. -/
theorem cylinder_word_pointwise_le_H6 {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      cylinderEmbeddingConstant period * (85 * liftSobolevNorm period 6 f) := by
  have hA := cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 6) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_H6 period hm w f)
    (cylinderEmbeddingConstant_nonneg period))

end EulerCylinderSobolev

end

section

/-! Actual H⁶ multiplication on the three-dimensional cylinder. -/

namespace EulerCylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The low-order tensor bound furnished by the cylinder embedding. -/
noncomputable def lowDerivativeConstant : ℝ := 64 * 85 * cylinderEmbeddingConstant period

theorem lowDerivativeConstant_nonneg : 0 ≤ lowDerivativeConstant period :=
  mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)

theorem tensor_low_le_H6 {m : ℕ} (hm : m ≤ 3) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) 0‖ ≤
      lowDerivativeConstant period * liftSobolevNorm period 6 f := by
  have hA := euclideanLift_tensor_norm_le period m f hf x 0
  simp only [euclideanLift_zero] at hA
  have hB := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin m → Fin 4))) =>
    cylinder_word_pointwise_le_H6 period hm w f hf hfL2 x)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hB
  have hp : (4 : ℝ) ^ m ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hm
    norm_num at h ⊢
    exact h
  have hC := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (cylinderEmbeddingConstant_nonneg period) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 85) (liftSobolevNorm_nonneg period 6 f)))
  have he (C A : ℝ) : 64 * (C * (85 * A)) = (64 * 85 * C) * A := by ring
  exact hA.trans (hB.trans (hC.trans_eq (he _ _)))

omit [Fact (0 < period)] in
theorem tensor_le_totalMagnitude {n : ℕ} (hn : n ≤ 6) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) 0‖ ≤ totalMagnitude period 6 f x := by
  have hA := euclideanLift_tensor_norm_le period n f hf x 0
  simp only [euclideanLift_zero] at hA
  exact hA.trans (wordMagnitude_le_total period 6 n hn f x)

/-- The real-valued envelope arising from the low/high derivative split. -/
noncomputable def productEnvelope (f g : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  liftSobolevNorm period 6 f • totalMagnitude period 6 g +
    liftSobolevNorm period 6 g • totalMagnitude period 6 f

theorem productEnvelope_nonneg (f g : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ productEnvelope period f g x :=
  add_nonneg (mul_nonneg (liftSobolevNorm_nonneg period 6 f) (totalMagnitude_nonneg period 6 g x))
    (mul_nonneg (liftSobolevNorm_nonneg period 6 g) (totalMagnitude_nonneg period 6 f x))

omit [Fact (0 < period)] in
theorem product_smooth (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (f*g) x) := fun x => (hf x).mul (hg x)

theorem product_tensor_term_le {n j : ℕ} (hn : n ≤ 6) (hj : j ≤ n)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period g x) 0‖ ≤
        lowDerivativeConstant period * productEnvelope period f g x := by
  by_cases hj3 : j ≤ 3
  · have hA := mul_le_mul (tensor_low_le_H6 period hj3 f hf hfL2 x)
      (tensor_le_totalMagnitude period (by omega : n-j ≤ 6) g hg x) (norm_nonneg _)
      (mul_nonneg (lowDerivativeConstant_nonneg period) (liftSobolevNorm_nonneg period 6 f))
    have hB : liftSobolevNorm period 6 f * totalMagnitude period 6 g x ≤ productEnvelope period f g x := by
      exact le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 6 g)
        (totalMagnitude_nonneg period 6 f x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period)
    rw [mul_assoc] at hA
    exact hA.trans hC
  · have hA := mul_le_mul (tensor_le_totalMagnitude period (by omega : j ≤ 6) f hf x)
      (tensor_low_le_H6 period (by omega : n-j ≤ 3) g hg hgL2 x) (norm_nonneg _)
      (totalMagnitude_nonneg period 6 f x)
    have hB : liftSobolevNorm period 6 g * totalMagnitude period 6 f x ≤ productEnvelope period f g x := by
      exact le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 6 f)
        (totalMagnitude_nonneg period 6 g x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period)
    have he (A B C : ℝ) : A * (B*C) = B*(C*A) := by ring
    exact hA.trans ((he _ _ _).trans_le hC)

/-- Actual Leibniz derivatives of a product have a square-integrable low/high envelope. -/
theorem product_word_pointwise_le {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w (f*g) x‖ ≤
      64 * lowDerivativeConstant period * productEnvelope period f g x := by
  have he := euclideanLift_iteratedFieldDerivative period w (f*g) (product_smooth period f g hf hg) x 0
  rw [euclideanLift_zero] at he
  rw [he]
  have hA := (iteratedFDeriv ℝ n (euclideanLift period (f*g) x) 0).le_opNorm
    (fun j => EuclideanSpace.single (w j) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
  have hB := norm_iteratedFDeriv_mul_le (euclideanLift_smooth period f hf x)
    (euclideanLift_smooth period g hg x) 0 (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hC : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period g x) 0‖) ≤
        2^n * (lowDerivativeConstant period * productEnvelope period f g x) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
          (lowDerivativeConstant period * productEnvelope period f g x) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (product_tensor_term_le period hn
          (by simpa using Finset.mem_range.1 hj) f g hf hg hfL2 hgL2 x) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hp : (2 : ℝ)^n ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hD := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (lowDerivativeConstant_nonneg period) (productEnvelope_nonneg period f g x))
  exact hA.trans (hB.trans (hC.trans (hD.trans_eq (mul_assoc _ _ _).symm)))

theorem productEnvelope_memLp (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (productEnvelope period f g) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 6 g hgL2).const_smul (liftSobolevNorm period 6 f)).add
    ((totalMagnitude_memLp period 6 f hfL2).const_smul (liftSobolevNorm period 6 g))

theorem productEnvelope_L2_le (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    ‖(productEnvelope_memLp period f g hfL2 hgL2).toLp (productEnvelope period f g)‖ ≤
      2 * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  change ‖liftSobolevNorm period 6 f • (totalMagnitude_memLp period 6 g hgL2).toLp _ +
    liftSobolevNorm period 6 g • (totalMagnitude_memLp period 6 f hfL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (liftSobolevNorm period 6 f • (totalMagnitude_memLp period 6 g hgL2).toLp (totalMagnitude period 6 g))
    (liftSobolevNorm period 6 g • (totalMagnitude_memLp period 6 f hfL2).toLp (totalMagnitude period 6 f))
  simp only [norm_smul, Real.norm_of_nonneg (liftSobolevNorm_nonneg period 6 f),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 6 g)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 6 g hgL2) (liftSobolevNorm_nonneg period 6 f))
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 6 f hfL2) (liftSobolevNorm_nonneg period 6 g))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

/-- Every derivative word through order six of the product is genuinely square-integrable. -/
theorem product_word_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period) := by
  apply (productEnvelope_memLp period f g hfL2 hgL2).of_le_mul
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f*g)
      (product_smooth period f g hf hg))).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (productEnvelope_nonneg period f g x)]
  exact product_word_pointwise_le period hn w f g hf hg hfL2 hgL2 x

/-- An explicit bound for each actual product derivative in L². -/
theorem product_word_L2_le {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period)).toReal ≤
      128 * lowDerivativeConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hq := productEnvelope_memLp period f g hfL2 hgL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖iteratedFieldDerivative period w (f*g) x‖ ≤
      (64 * lowDerivativeConstant period) * ‖productEnvelope period f g x‖ by
        rw [Real.norm_of_nonneg (productEnvelope_nonneg period f g x)]
        exact product_word_pointwise_le period hn w f g hf hg hfL2 hgL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 64 * lowDerivativeConstant period := mul_nonneg (by norm_num) (lowDerivativeConstant_nonneg period)
  have hfin : ENNReal.ofReal (64 * lowDerivativeConstant period) *
      eLpNorm (productEnvelope period f g) 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left (productEnvelope_L2_le period f g hfL2 hgL2) hc
  rw [Lp.norm_toLp] at hC
  have he (L A B : ℝ) : (64*L)*(2*A*B) = 128*L*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

/-- The H⁶ algebra estimate on the actual cylinder, with a finite explicit constant. -/
theorem cylinder_H6_algebra (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (f*g) ≤
      (5461 * 128 * lowDerivativeConstant period) *
        liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hA : liftSobolevNorm period 6 (f*g) ≤
      ∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4,
        128 * lowDerivativeConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact product_word_L2_le period (by have := Finset.mem_range.1 hn; omega) w f g hf hg hfL2 hgL2
  have hcard (A : ℝ) : (∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4, A) = 5461*A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Finset.sum_range_succ]
    ring
  rw [hcard] at hA
  have he (L A B : ℝ) : 5461*(128*L*A*B) = (5461*128*L)*A*B := by ring
  exact hA.trans_eq (he _ _ _)

end EulerCylinderAlgebra

end

section

/-! Real-valued forms of the cylinder Sobolev and multiplication estimates. -/

namespace EulerRealCylinder

open MeasureTheory EulerCylinderSobolev EulerCylinderAlgebra
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff

variable (period : ℝ)

section LinearMaps
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fieldDerivative_postcomp (L : F →L[ℝ] G) (a : LiftTangent)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    fieldDerivative period a (L ∘ f) = L ∘ fieldDerivative period a f := by
  funext x
  have h := L.hasFDerivAt.comp 0 (((hf x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] G => A a) h.fderiv

theorem iteratedFieldDerivative_postcomp {n : ℕ} (L : F →L[ℝ] G) (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (L ∘ f) = L ∘ iteratedFieldDerivative period w f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w), fieldDerivative_postcomp period L _ _
      (iteratedFieldDerivative_smooth period (Fin.tail w) f hf)]
    rfl

end LinearMaps

/-- Isometric complexification of a real scalar cylinder field. -/
noncomputable def complexField (f : LiftDomain period → ℝ) : LiftDomain period → ℂ :=
  Complex.ofRealCLM ∘ f

theorem complexField_smooth (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (complexField period f) x) :=
  fun x => Complex.ofRealCLM.contDiff.comp (hf x)

theorem complexField_word {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (complexField period f) =
      complexField period (iteratedFieldDerivative period w f) :=
  iteratedFieldDerivative_postcomp period Complex.ofRealCLM w f hf

variable [Fact (0 < period)]

theorem complexField_eLpNorm (f : LiftDomain period → ℝ) :
    eLpNorm (complexField period f) 2 (liftMeasure period) = eLpNorm f 2 (liftMeasure period) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [] with x
  exact Complex.norm_real _

theorem complexField_memLp (f : LiftDomain period → ℝ) (hf : MemLp f 2 (liftMeasure period)) :
    MemLp (complexField period f) 2 (liftMeasure period) :=
  Complex.ofRealCLM.comp_memLp' hf

theorem complexField_sobolevNorm (s : ℕ) (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    liftSobolevNorm period s (complexField period f) = liftSobolevNorm period s f := by
  unfold liftSobolevNorm
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro w _
  rw [complexField_word period w f hf, complexField_eLpNorm]

/-- The actual real H³ to L∞ embedding on the cylinder. -/
theorem real_cylinder_pointwise_le_H3 (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
  have h := cylinder_pointwise_le_H3 period (complexField period f) (complexField_smooth period f hf)
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2 j hj w)) x
  rw [complexField_sobolevNorm period 3 f hf] at h
  simpa only [complexField, Function.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real] using h

/-- The real H⁶ algebra estimate on the actual cylinder. -/
theorem real_cylinder_H6_algebra (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (f*g) ≤ (5461 * 128 * lowDerivativeConstant period) *
      liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have h := cylinder_H6_algebra period (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2 j hj w))
    (fun j hj w => by rw [complexField_word period w g hg]; exact complexField_memLp period _ (hgL2 j hj w))
  have he : complexField period f * complexField period g = complexField period (f*g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_sobolevNorm period 6 (f*g) (fun x => (hf x).mul (hg x)),
    complexField_sobolevNorm period 6 f hf, complexField_sobolevNorm period 6 g hg] at h
  exact h

end EulerRealCylinder

end

section

/-! Real Euclidean vector wrappers for the actual cylinder Sobolev estimates. -/

namespace EulerVectorCylinder

open MeasureTheory EulerSobolev EulerSobolevDerivativeNorm EulerRealCylinder
open EulerCylinderSobolev EulerCylinderAlgebra EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

section Postcomposition
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [Fact (0 < period)] in
theorem postcomp_smooth (L : F →L[ℝ] G) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (L ∘ f) x) := fun x => L.contDiff.comp (hf x)

theorem postcomp_word_memLp {s n : ℕ} (hn : n ≤ s) (L : F →L[ℝ] G)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ s, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (w : Fin n → Fin 4) :
    MemLp (iteratedFieldDerivative period w (L ∘ f)) 2 (liftMeasure period) := by
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  exact L.comp_memLp' (hfL2 n hn w)

theorem postcomp_sobolevNorm_le (s : ℕ) (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ s, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    liftSobolevNorm period s (L ∘ f) ≤ liftSobolevNorm period s f := by
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro w _
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  apply ENNReal.toReal_mono (hfL2 n (by have := Finset.mem_range.1 hn; omega) w).eLpNorm_ne_top
  apply eLpNorm_mono
  intro x
  have h := L.le_opNorm (iteratedFieldDerivative period w f x)
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

end Postcomposition

/-- A coordinate projection on a real Euclidean target, of operator norm at most one. -/
noncomputable def coordinate (q : ℕ) (i : Fin q) : Domain q →L[ℝ] ℝ := EuclideanSpace.proj i

theorem coordinate_norm_le (q : ℕ) (i : Fin q) : ‖coordinate q i‖ ≤ 1 := by
  apply (coordinate q i).opNorm_le_bound (by norm_num)
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

/-- H³ controls the pointwise norm of a genuine real Euclidean cylinder field. -/
theorem vector_cylinder_pointwise_le_H3 (q : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ ((q : ℝ) * cylinderEmbeddingConstant period) * liftSobolevNorm period 3 f := by
  have hA := norm_le_sum_coordinates q (f x)
  have hB (i : Fin q) : ‖f x i‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
    have h := real_cylinder_pointwise_le_H3 period (coordinate q i ∘ f)
      (postcomp_smooth period _ f hf) (fun j hj w => postcomp_word_memLp period hj _ f hf hfL2 w) x
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 3 _ (coordinate_norm_le q i) f hf hfL2)
      (cylinderEmbeddingConstant_nonneg period))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  exact hA.trans (hC.trans_eq (mul_assoc _ _ _).symm)

omit [Fact (0 < period)] in
/-- The coordinate of a classical derivative is the derivative of the coordinate. -/
theorem coordinate_word {n : ℕ} (q : ℕ) (i : Fin q) (w : Fin n → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    iteratedFieldDerivative period w (coordinate q i ∘ f) x = iteratedFieldDerivative period w f x i := by
  rw [iteratedFieldDerivative_postcomp period _ w f hf]
  rfl

theorem vector_eLpNorm_le_sum_coordinates (q : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ i : Fin q, MemLp (fun x => f x i) 2 (liftMeasure period)) :
    eLpNorm f 2 (liftMeasure period) ≤ ∑ i : Fin q, eLpNorm (fun x => f x i) 2 (liftMeasure period) := by
  have hA : eLpNorm f 2 (liftMeasure period) ≤
      eLpNorm (fun x => ∑ i : Fin q, ‖f x i‖) 2 (liftMeasure period) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact norm_le_sum_coordinates q (f x)
  have he : (fun x => ∑ i : Fin q, ‖f x i‖) = ∑ i : Fin q, (fun x => ‖f x i‖) := by
    funext x
    simp
  rw [he] at hA
  have hB := eLpNorm_sum_le
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => (hf i).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [eLpNorm_norm] using hA.trans hB

theorem vector_word_L2_le_sum_coordinates {s n : ℕ} (hn : n ≤ s) (q : ℕ) (w : Fin n → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ i : Fin q, ∀ j ≤ s, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ f)) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      ∑ i : Fin q, (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure period)).toReal := by
  have hc (i : Fin q) : MemLp (fun x => iteratedFieldDerivative period w f x i) 2 (liftMeasure period) := by
    have h := hfL2 i n hn w
    rw [iteratedFieldDerivative_postcomp period _ w f hf] at h
    exact h
  have hA := vector_eLpNorm_le_sum_coordinates period q (iteratedFieldDerivative period w f) hc
  have hfin : (∑ i : Fin q, eLpNorm (fun x => iteratedFieldDerivative period w f x i) 2 (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun i _ => (hc i).eLpNorm_ne_top)
  have hB := ENNReal.toReal_mono hfin hA
  rw [ENNReal.toReal_sum (fun i _ => (hc i).eLpNorm_ne_top)] at hB
  have he (i : Fin q) : (fun x => iteratedFieldDerivative period w f x i) =
      iteratedFieldDerivative period w (coordinate q i ∘ f) := by
    funext x
    exact (coordinate_word period q i w f hf x).symm
  simp_rw [he] at hB
  exact hB

/-- A vector Sobolev norm is controlled by the sum of its scalar coordinate norms. -/
theorem vector_sobolevNorm_le_sum_coordinates (q s : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ i : Fin q, ∀ j ≤ s, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ f)) 2 (liftMeasure period)) :
    liftSobolevNorm period s f ≤ ∑ i : Fin q, liftSobolevNorm period s (coordinate q i ∘ f) := by
  have hA : liftSobolevNorm period s f ≤
      ∑ n ∈ Finset.range (s+1), ∑ w : Fin n → Fin 4, ∑ i : Fin q,
        (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure period)).toReal := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact vector_word_L2_le_sum_coordinates period (by have := Finset.mem_range.1 hn; omega) q w f hf hfL2
  apply hA.trans_eq
  calc
    _ = ∑ n ∈ Finset.range (s+1), ∑ i : Fin q, ∑ w : Fin n → Fin 4,
        (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure period)).toReal := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem real_product_word_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period) := by
  have h := product_word_memLp period hn w (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj v => by rw [complexField_word period v f hf]; exact complexField_memLp period _ (hfL2 j hj v))
    (fun j hj v => by rw [complexField_word period v g hg]; exact complexField_memLp period _ (hgL2 j hj v))
  have he : complexField period f * complexField period g = complexField period (f*g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_word period w (f*g) (fun x => (hf x).mul (hg x))] at h
  apply h.of_le
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f*g)
      (fun x => (hf x).mul (hg x)))).aestronglyMeasurable)
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

omit [Fact (0 < period)] in
theorem coordinate_smul (q : ℕ) (i : Fin q) (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain q) :
    coordinate q i ∘ (fun x => f x • g x) = f * (coordinate q i ∘ g) := by
  funext x
  simp [Function.comp_def, map_smul, smul_eq_mul]

/-- Multiplication of an actual vector field by a scalar field is bounded in H⁶. -/
theorem cylinder_H6_scalar_vector_product (q : ℕ) (f : LiftDomain period → ℝ)
    (g : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (fun x => f x • g x) ≤
      ((q : ℝ) * (5461 * 128 * lowDerivativeConstant period)) *
        liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => f x • g x) x) :=
    fun x => (hf x).smul (hg x)
  have hcomp (i : Fin q) : ∀ j ≤ 6, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ g)) 2 (liftMeasure period) :=
    fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v
  have hA := vector_sobolevNorm_le_sum_coordinates period q 6 (fun x => f x • g x) hs
    (fun i j hj v => by
      rw [coordinate_smul]
      exact real_product_word_memLp period hj v f (coordinate q i ∘ g) hf
        (postcomp_smooth period _ g hg) hfL2 (hcomp i))
  have hB (i : Fin q) : liftSobolevNorm period 6 (coordinate q i ∘ (fun x => f x • g x)) ≤
      (5461 * 128 * lowDerivativeConstant period) * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
    rw [coordinate_smul]
    have h := real_cylinder_H6_algebra period f (coordinate q i ∘ g) hf (postcomp_smooth period _ g hg) hfL2 (hcomp i)
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 6 _ (coordinate_norm_le q i) g hg hgL2)
      (mul_nonneg (mul_nonneg (by norm_num) (lowDerivativeConstant_nonneg period)) (liftSobolevNorm_nonneg period 6 f)))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  have he (q C A B : ℝ) : q*(C*A*B) = (q*C)*A*B := by ring
  exact hA.trans (hC.trans_eq (he _ _ _ _))

end EulerVectorCylinder

end

end
