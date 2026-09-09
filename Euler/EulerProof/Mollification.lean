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
import Euler.EulerProof.CylinderSobolev

/-!
# Mollification and smooth representatives

Smoothing operators on the cylinder and the smooth representatives they
produce:

* `EulerSmoothSobolev`, `EulerStrongSmoothJet` -- Sobolev norms for smooth
  tensor fields and the strong jet bounds attached to them.
* `EulerCylinderGradient`, `EulerCylinderMollifier`, `EulerSetIntegralL2` --
  gradients on the cylinder, the mollifier itself and the set-integral `L^2`
  estimates it uses.
* `EulerCoverMollification`, `EulerCoverMollificationFubini` -- mollification
  through the Euclidean cover and the Fubini identities it needs.
* `EulerMollifierRepresentative`, `EulerMollifierUniform`,
  `EulerMollifierTensors`, `EulerSmoothTensorLimit`,
  `EulerSmoothPressureRepresentative` -- the smooth representative of an `L^2`
  class, uniform bounds for it, and the limits of the mollified tensors.

This is part 4 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

/-! Sobolev embedding for general smooth fields on R³, without Schwartz assumptions. -/

namespace EulerSmoothSobolev

open MeasureTheory FourierTransform EulerSobolev
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Repeated directional derivatives of a vector-valued Schwartz function. -/
noncomputable def pureDerivative (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) := ∂^{fun _ : Fin n => v} f

omit [CompleteSpace F] in
theorem fourier_pureDerivative_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    ‖𝓕 (pureDerivative d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖ := by
  induction n with
  | zero => simp [pureDerivative]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : pureDerivative d (n+1) v f = ∂_{v} (pureDerivative d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

omit [CompleteSpace F] in
theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

omit [CompleteSpace F] in
theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

omit [CompleteSpace F] in
theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, F))
    (g : ι → 𝓢(Domain d, F)) (C : ℝ) (hC : 0 ≤ C)
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

theorem sobolevNorm_two_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, F)) :
    sobolevNorm d 2 f ≤ 1 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin d, ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, F) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-2 : ℤ) : ℝ) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 2 f ξ‖ ≤ 1 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 2 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 2) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
        fourier_pureDerivative_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-2 : ℤ) * (2 * Real.pi) ^ (2 : ℕ) = 1 := by
        rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (le_of_eq (show besselWeight d 2 ξ = 1 + ∑ i, ‖ξ i‖ ^ 2 by norm_num [besselWeight, EuclideanSpace.norm_sq_eq])) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 2 f) g 1
    (by norm_num) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-2 : ℤ) * ∑ i : Fin d,
        ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ F 2 volume (((2 * Real.pi) ^ (-2 : ℤ)) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- The sharp three-dimensional H² pointwise bound in terms of actual second derivatives. -/
theorem pointwise_le_L2_second_derivatives (f : 𝓢(Domain 3, F)) (x : Domain 3) :
    ‖f x‖ ≤ embeddingConstant 3 2 (by norm_num) *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 3 2 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_two_le_pure_derivatives 3 f)
    (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  simpa only [one_mul] using hA.trans hB

/-- The sum of the actual L² norms of Fréchet derivatives through order `s`. -/
noncomputable def tensorSobolevNorm (s : ℕ) (f : Domain 3 → F) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)


omit [CompleteSpace F] in
theorem tensorSobolevNorm_mono {s t : ℕ} (hst : s ≤ t) (f : Domain 3 → F) :
    tensorSobolevNorm s f ≤ tensorSobolevNorm t f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => ENNReal.toReal_nonneg)

/-- Sum of the pointwise norms of all derivatives through a fixed order. -/
noncomputable def derivativeMagnitude (s : ℕ) (f : Domain 3 → F) (x : Domain 3) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => ‖iteratedFDeriv ℝ j f x‖)

omit [CompleteSpace F] in
theorem derivativeMagnitude_nonneg (s : ℕ) (f : Domain 3 → F) (x : Domain 3) :
    0 ≤ derivativeMagnitude s f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [CompleteSpace F] in
theorem derivativeMagnitude_memLp (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (derivativeMagnitude s f) 2 volume :=
  memLp_finsetSum _ (fun j hj => (hfL2 j (by have := Finset.mem_range.1 hj; omega)).norm)

omit [CompleteSpace F] in
theorem derivativeMagnitude_L2_le (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    ‖(derivativeMagnitude_memLp s f hfL2).toLp (derivativeMagnitude s f)‖ ≤ tensorSobolevNorm s f := by
  have he : derivativeMagnitude s f = ∑ j ∈ Finset.range (s+1), fun x => ‖iteratedFDeriv ℝ j f x‖ := by
    funext x
    simp [derivativeMagnitude]
  have hA : eLpNorm (derivativeMagnitude s f) 2 volume ≤
      ∑ j ∈ Finset.range (s+1), eLpNorm (iteratedFDeriv ℝ j f) 2 volume := by
    rw [he]
    simpa only [eLpNorm_norm] using eLpNorm_sum_le (fun j hj =>
      (hfL2 j (by have := Finset.mem_range.1 hj; omega)).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin (j : ℕ) (hj : j ∈ Finset.range (s+1)) : eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≠ ⊤ :=
    (hfL2 j (by have := Finset.mem_range.1 hj; omega)).eLpNorm_ne_top
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) hA
  rw [ENNReal.toReal_sum hfin] at hB
  rw [Lp.norm_toLp]
  exact hB

/-- A fixed bump equal to one near zero, independent of the function being estimated. -/
noncomputable def unitBump : ContDiffBump (0 : Domain 3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The same fixed bump as a Schwartz function. -/
noncomputable def unitBumpSchwartz : 𝓢(Domain 3, ℝ) :=
  unitBump.hasCompactSupport.toSchwartzMap unitBump.contDiff

/-- A finite derivative bound for the fixed bump. -/
noncomputable def unitBumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j unitBumpSchwartz, apply_nonneg _ _⟩

/-- The finite Leibniz coefficient for localizing an order `n` derivative. -/
noncomputable def unitBumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * unitBumpBound j)

/-- An actual smooth compact localization of an arbitrary smooth function about `x`. -/
noncomputable def localize (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) : 𝓢(Domain 3, F) :=
  (unitBump.hasCompactSupport.smul_right (f' := fun z => f (x+z))).toSchwartzMap
    (unitBump.contDiff.smul (hf.comp (contDiff_const.add contDiff_id)))

omit [CompleteSpace F] in
@[simp] theorem localize_apply (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    localize f hf x z = unitBump z • f (x+z) := rfl

omit [CompleteSpace F] in
theorem localize_zero (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    localize f hf x 0 = f x := by
  rw [localize_apply, unitBump.one_of_mem_closedBall (by simp [unitBump]), one_smul, add_zero]

omit [CompleteSpace F] in
/-- Localization obeys the actual tensor Leibniz estimate. -/
theorem localize_tensor_bound (n : ℕ) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    ‖iteratedFDeriv ℝ n (localize f hf x) z‖ ≤
      (unitBumpCoefficient n : ℝ) * derivativeMagnitude n f (x+z) := by
  have hshift : ContDiff ℝ ∞ (fun z => f (x+z)) := hf.comp (contDiff_const.add contDiff_id)
  have hA := norm_iteratedFDeriv_smul_le unitBump.contDiff
    hshift z (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  have hb (j : ℕ) : ‖iteratedFDeriv ℝ j unitBump z‖ ≤ unitBumpBound j :=
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ unitBumpSchwartz j z
  have hd (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (fun z => f (x+z)) z‖ ≤ derivativeMagnitude n f (x+z) := by
    rw [iteratedFDeriv_comp_add_left]
    exact Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k f (x+z)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * unitBumpBound j) * derivativeMagnitude n f (x+z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)) (hd j hj)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (unitBumpBound j).coe_nonneg)
    _ = _ := by simp only [unitBumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast, Finset.sum_mul]

omit [CompleteSpace F] in
/-- Each localized pure derivative is controlled by the global physical Sobolev norm. -/
theorem localize_pureDerivative_L2_le (n : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ n, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖(pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖ ≤
      (unitBumpCoefficient n : ℝ) * tensorSobolevNorm n f := by
  have hq := derivativeMagnitude_memLp n f hfL2
  have htrans := measurePreserving_add_left (volume : Measure (Domain 3)) x
  have hqt : MemLp (fun z => derivativeMagnitude n f (x+z)) 2 volume := hq.comp_measurePreserving htrans
  have hb (z : Domain 3) :
      ‖pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x) z‖ ≤
        (unitBumpCoefficient n : ℝ) * ‖derivativeMagnitude n f (x+z)‖ := by
    rw [pureDerivative, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      Real.norm_of_nonneg (derivativeMagnitude_nonneg n f (x+z))]
    have hA := (iteratedFDeriv ℝ n (localize f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    exact hA.trans (localize_tensor_bound n f hf x z)
  have hA := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Domain 3)))
    (Filter.Eventually.of_forall hb) 2
  have hfin : (unitBumpCoefficient n : ℝ≥0∞) *
      eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  have he : eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume =
      eLpNorm (derivativeMagnitude n f) 2 volume := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hq.1 htrans
  rw [he] at hB
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hB
  rw [SchwartzMap.norm_toLp]
  have hC := mul_le_mul_of_nonneg_left (derivativeMagnitude_L2_le n f hfL2) (unitBumpCoefficient n).coe_nonneg
  rw [Lp.norm_toLp] at hC
  exact hB.trans hC

/-- A fixed finite three-dimensional H² embedding constant. -/
noncomputable def smoothEmbeddingConstant : ℝ :=
  embeddingConstant 3 2 (by norm_num) *
    ((unitBumpCoefficient 0 : ℝ) + (2 * Real.pi)^(-2 : ℤ) * 3 * unitBumpCoefficient 2)

theorem smoothEmbeddingConstant_nonneg : 0 ≤ smoothEmbeddingConstant := by
  have h : 0 ≤ embeddingConstant 3 2 (by norm_num) := norm_nonneg _
  unfold smoothEmbeddingConstant
  positivity

/-- Genuine H² to L∞ embedding for every smooth Hilbert-valued function on R³. -/
theorem smooth_pointwise_le_H2 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖f x‖ ≤ smoothEmbeddingConstant * tensorSobolevNorm 2 f := by
  have hzero := localize_pureDerivative_L2_le 0 0 f hf (fun j hj => hfL2 j (by omega)) x
  have he : pureDerivative 3 0 (EuclideanSpace.single 0 1) (localize f hf x) = localize f hf x := by
    ext z
    simp [pureDerivative]
  rw [he] at hzero
  have hzero' := hzero.trans (mul_le_mul_of_nonneg_left (tensorSobolevNorm_mono (show 0 ≤ 2 by omega) f)
    (unitBumpCoefficient 0).coe_nonneg)
  have htwo : (∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖) ≤
      3 * ((unitBumpCoefficient 2 : ℝ) * tensorSobolevNorm 2 f) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      localize_pureDerivative_L2_le 2 i f hf hfL2 x)
  have hA := pointwise_le_L2_second_derivatives (localize f hf x) 0
  rw [localize_zero] at hA
  have hB := add_le_add hzero' (mul_le_mul_of_nonneg_left htwo
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.pi) (-2 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  have harith (C A B p S : ℝ) : C * (A*S+p*(3*(B*S))) = (C*(A+p*3*B))*S := by ring
  exact hA.trans (hC.trans_eq (harith _ _ _ _ _))

/-- The actual derivative in one Euclidean coordinate direction. -/
noncomputable def coordinateDerivative (i : Fin 3) (f : Domain 3 → F) : Domain 3 → F :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

omit [CompleteSpace F] in
theorem coordinateDerivative_smooth (i : Fin 3) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordinateDerivative i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [CompleteSpace F] in
theorem coordinateDerivative_tensor_bound (j : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (coordinateDerivative i f) x‖ ≤ ‖iteratedFDeriv ℝ (j+1) f x‖ := by
  let L : (Domain 3 →L[ℝ] F) →L[ℝ] F :=
    ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i 1)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro A
    simpa only [L, ContinuousLinearMap.apply_apply, PiLp.norm_single, norm_one, one_mul, mul_one] using
      A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  have hA := L.norm_iteratedFDeriv_comp_left (x := x)
    (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).contDiffAt
    (by simp : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change ‖iteratedFDeriv ℝ j (coordinateDerivative i f) x‖ ≤ _ at hA
  have hB := mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ j (fderiv ℝ f) x))
  rw [one_mul, norm_iteratedFDeriv_fderiv] at hB
  rw [norm_iteratedFDeriv_fderiv] at hA
  exact hA.trans hB

omit [CompleteSpace F] in
theorem coordinateDerivative_tensor_memLp {j : ℕ} (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ (j+1) f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (coordinateDerivative i f)) 2 volume :=
  hfL2.of_le ((coordinateDerivative_smooth i f hf).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    (Filter.Eventually.of_forall (coordinateDerivative_tensor_bound j i f hf))

omit [CompleteSpace F] in
theorem coordinateDerivative_H2_le_H3 (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    tensorSobolevNorm 2 (coordinateDerivative i f) ≤ 3 * tensorSobolevNorm 3 f := by
  have hA : tensorSobolevNorm 2 (coordinateDerivative i f) ≤
      ∑ _j ∈ Finset.range 3, tensorSobolevNorm 3 f := by
    apply Finset.sum_le_sum
    intro j hj
    have hj3 : j+1 ≤ 3 := by have := Finset.mem_range.1 hj; omega
    have hB := ENNReal.toReal_mono (hfL2 (j+1) hj3).eLpNorm_ne_top
      (eLpNorm_mono (coordinateDerivative_tensor_bound j i f hf))
    have hC : (eLpNorm (iteratedFDeriv ℝ (j+1) f) 2 volume).toReal ≤ tensorSobolevNorm 3 f :=
      Finset.single_le_sum (f := fun k => (eLpNorm (iteratedFDeriv ℝ k f) 2 volume).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.2 (by omega))
    exact hB.trans hC
  simpa using hA

omit [CompleteSpace F] in
/-- A linear map is controlled by the sum of its values on the coordinate basis. -/
theorem linear_norm_le_coordinate_sum (A : Domain 3 →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hx : (∑ i : Fin 3, (x i) • EuclideanSpace.single i (1 : ℝ)) = x := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hA : A x = ∑ i : Fin 3, (x i) • A (EuclideanSpace.single i (1 : ℝ)) := by
    simp_rw [← map_smul]
    rw [← map_sum, hx]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 3, ‖(x i) • A (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The exact regularity needed in the limiting Euler contradiction: H³ controls the C¹ derivative. -/
theorem smooth_fderiv_le_H3 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖fderiv ℝ f x‖ ≤ (9 * smoothEmbeddingConstant) * tensorSobolevNorm 3 f := by
  have hA := linear_norm_le_coordinate_sum (fderiv ℝ f x)
  have hB (i : Fin 3) : ‖coordinateDerivative i f x‖ ≤
      smoothEmbeddingConstant * (3 * tensorSobolevNorm 3 f) := by
    have hC := smooth_pointwise_le_H2 (coordinateDerivative i f) (coordinateDerivative_smooth i f hf)
      (fun j hj => coordinateDerivative_tensor_memLp i f hf (hfL2 (j+1) (by omega))) x
    exact hC.trans (mul_le_mul_of_nonneg_left (coordinateDerivative_H2_le_H3 i f hf hfL2)
      smoothEmbeddingConstant_nonneg)
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  have he (C A : ℝ) : (3 : ℝ)*(C*(3*A)) = (9*C)*A := by ring
  exact hA.trans (hC.trans_eq (he _ _))

/-- The physical tensor Sobolev norm for real Euclidean vector fields. -/
noncomputable def realTensorSobolevNorm (q s : ℕ) (f : Domain 3 → Domain q) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

theorem complexification_tensor_norm (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (complexify q ∘ f) x‖ = ‖iteratedFDeriv ℝ j f x‖ :=
  (complexify q).norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)

theorem complexification_tensor_memLp (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (complexify q ∘ f)) 2 volume := by
  have hc : Continuous (iteratedFDeriv ℝ j (complexify q ∘ f)) :=
    ((complexify q).contDiff.comp hf).continuous_iteratedFDeriv (by simp)
  apply hfL2.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  exact (complexification_tensor_norm q j f hf x).le

theorem complexification_sobolevNorm (q s : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) :
    tensorSobolevNorm s (complexify q ∘ f) = realTensorSobolevNorm q s f := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (complexification_tensor_norm q j f hf))

/-- Real vector-valued H³ to C¹ on R³, for general smooth functions with actual L² derivatives. -/
theorem real_smooth_fderiv_le_H3 (q : ℕ) (f : Domain 3 → Domain q) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖fderiv ℝ f x‖ ≤ (9 * smoothEmbeddingConstant) * realTensorSobolevNorm q 3 f := by
  have h := smooth_fderiv_le_H3 (complexify q ∘ f) ((complexify q).contDiff.comp hf)
    (fun j hj => complexification_tensor_memLp q j f hf (hfL2 j hj)) x
  have he : ‖fderiv ℝ (complexify q ∘ f) x‖ = ‖fderiv ℝ f x‖ := by
    simpa only [norm_iteratedFDeriv_one] using complexification_tensor_norm q 1 f hf x
  rw [he, complexification_sobolevNorm q 3 f hf] at h
  exact h

end EulerSmoothSobolev

end

section

/-! Strong L² derivatives of smooth representatives are their actual classical derivatives. -/

namespace EulerStrongSmoothJet

open MeasureTheory Filter EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerSpatialSobolevInverse EulerPressureSpatialRegularity
open scoped ContDiff ENNReal Topology

section General
variable {X F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A strong L² derivative agrees almost everywhere with a pointwise derivative.
The proof extracts an almost-everywhere convergent subsequence of the difference quotients. -/
theorem lp_derivative_ae (U : ℝ → Lp F 2 μ) (V : Lp F 2 μ)
    (u : ℝ → X → F) (v : X → F) (hrep : ∀ t, (U t : X → F) =ᵐ[μ] u t)
    (hU : HasDerivAt U V 0) (hu : ∀ x, HasDerivAt (fun t => u t x) (v x) 0) :
    (V : X → F) =ᵐ[μ] v := by
  have hQ (t : ℝ) : (slope U 0 t : X → F) =ᵐ[μ] (fun x => slope (fun r => u r x) 0 t) := by
    filter_upwards [Lp.coeFn_smul (t-0)⁻¹ (U t-U 0), Lp.coeFn_sub (U t) (U 0), hrep t, hrep 0]
      with x hsm hsub ht hzero
    simp only [Pi.smul_apply, Pi.sub_apply] at hsm hsub
    simp only [slope, vsub_eq_sub]
    rw [hsm, hsub, ht, hzero]
  obtain ⟨ts, hts, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hU.tendsto_slope).exists_seq_tendsto_ae'
  have hrepseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (slope U 0 (ts n)) x = slope (fun r => u r x) 0 (ts n) :=
    ae_all_iff.mpr (fun n => hQ (ts n))
  filter_upwards [hlim, hrepseq] with x hx hqx
  have hpoint := (hu x).tendsto_slope.comp hts
  have he : (fun n => (slope U 0 (ts n)) x) = (fun n => slope (fun r => u r x) 0 (ts n)) :=
    funext hqx
  rw [he] at hx
  exact tendsto_nhds_unique hx hpoint

end General

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- The pointwise translation orbit of a smooth cylinder field has its actual directional derivative. -/
theorem pointwise_translation_hasDerivAt (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : LiftDomain period) :
    HasDerivAt (fun t => f (x + translationPath period a t)) (fieldDerivative period a f x) 0 := by
  have hF := (((hf x).differentiable (by simp)) ((0 : ℝ) • a)).hasFDerivAt
  have h := hF.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const a)
  convert! h using 1
  simp [fieldDerivative]

/-- Any strong translation derivative of a smooth representative is its classical derivative,
without compactness or a priori integrability of that classical derivative. -/
theorem translation_derivative_ae (a : LiftTangent) (U V : LiftL2 period)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : HasDerivAt (fun t => translation period (translationPath period a t) U) V 0) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] fieldDerivative period a f := by
  apply lp_derivative_ae (liftMeasure period)
    (fun t => translation period (translationPath period a t) U) V
    (fun t x => f (x + translationPath period a t)) (fieldDerivative period a f)
    ?_ hD (pointwise_translation_hasDerivAt period a f hf)
  intro t
  filter_upwards [translation_ae period (translationPath period a t) U,
    (measurePreserving_translation period (translationPath period a t)).quasiMeasurePreserving.ae hrep]
    with x htrans hx
  exact htrans.trans hx

/-- Every word of a strong Sobolev jet agrees with the actual classical word of a smooth representative. -/
theorem jet_word_ae {s n : ℕ} (hn : n ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (J.word w : LiftDomain period → Vector3) =ᵐ[liftMeasure period] iteratedFieldDerivative period w f := by
  induction n with
  | zero => simpa only [SpatialJet.word_zero, iteratedFieldDerivative_zero] using hrep
  | succ n ih =>
    have hbase := ih (by omega : n ≤ s) (Fin.tail w)
    have hD := J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0)
    have h := translation_derivative_ae period (standardDirection (w 0)) (J.word (Fin.tail w))
      (J.word (Fin.cons (w 0) (Fin.tail w))) (iteratedFieldDerivative period (Fin.tail w) f)
      hbase (iteratedFieldDerivative_smooth period (Fin.tail w) f hf) hD
    simpa only [Fin.cons_self_tail, iteratedFieldDerivative_succ] using h

/-- Strong jets force all actual classical derivatives through the corresponding order to lie in L². -/
theorem jet_classical_memLp {s n : ℕ} (hn : n ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period) :=
  (Lp.memLp (J.word w)).ae_eq (jet_word_ae period hn U J w f hrep hf)

/-- The strong Sobolev jet norm is exactly the classical derivative Sobolev norm for any smooth representative. -/
theorem jet_sobolevNorm_eq {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    J.sobolevNorm = liftSobolevNorm period s f := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w _
  have h := eLpNorm_congr_ae (p := (2 : ℝ≥0∞))
    (jet_word_ae period (by have := Finset.mem_range.1 hn; omega) U J w f hrep hf)
  simpa only [Lp.norm_def] using congrArg ENNReal.toReal h

end EulerStrongSmoothJet

end

section

/-! Actual full cylinder gradients from the coordinate derivative Sobolev norms. -/

namespace EulerCylinderGradient

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative
open scoped ENNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]


section General
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem tangent_coordinate_norm_le (v : LiftTangent) (i : Fin 4) :
    ‖coordinateEquiv.symm v i‖ ≤ ‖v‖ := by
  cases i using Fin.cases with
  | zero => simpa using norm_snd_le v
  | succ i => exact (PiLp.norm_apply_le v.1 i).trans (norm_fst_le v)

omit [Fact (0 < period)] in
/-- The full product-tangent operator norm is bounded by its four coordinate values. -/
theorem linear_norm_le_standard_sum (A : LiftTangent →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 4, ‖A (standardDirection i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have he : (∑ i : Fin 4, (coordinateEquiv.symm v i) • EuclideanSpace.single i (1 : ℝ)) = coordinateEquiv.symm v := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hv : (∑ i : Fin 4, (coordinateEquiv.symm v i) • standardDirection i) = v := by
    change (∑ i : Fin 4, (coordinateEquiv.symm v i) • coordinateEquiv (EuclideanSpace.single i (1 : ℝ))) = v
    simp_rw [← map_smul]
    rw [← map_sum, he, ContinuousLinearEquiv.apply_symm_apply]
  have hA : A v = ∑ i : Fin 4, (coordinateEquiv.symm v i) • A (standardDirection i) := by
    simp_rw [← map_smul]
    rw [← map_sum, hv]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 4, ‖(coordinateEquiv.symm v i) • A (standardDirection i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖coordinateEquiv.symm v i‖ * ‖A (standardDirection i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 4, ‖v‖ * ‖A (standardDirection i)‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (tangent_coordinate_norm_le v i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

omit [Fact (0 < period)] in
theorem fieldFDeriv_norm_le_standard_sum (f : LiftDomain period → F) (x : LiftDomain period) :
    ‖fieldFDeriv period f x‖ ≤ ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖ :=
  linear_norm_le_standard_sum (fieldFDeriv period f x)

/-- Actual full gradient integrability follows from the four genuine coordinate derivatives. -/
theorem fieldFDeriv_memLp_of_coordinates (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure period)) :
    MemLp (fieldFDeriv period f) 2 (liftMeasure period) := by
  have hsum : MemLp (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2 (liftMeasure period) :=
    memLp_finsetSum _ (fun i _ => (hD i).norm)
  have hc : Continuous (fieldFDeriv period f) := smoothField_continuous period _ (fieldFDeriv_smooth period f hf)
  apply hsum.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  exact fieldFDeriv_norm_le_standard_sum period f x


end General
end EulerCylinderGradient

end

section

/-! Genuine approximate identities for the lifted L² translation representation. -/


namespace EulerCylinderMollifier

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderCoordinates
  EulerSobolev EulerNoncompactTransport EulerSpatialSobolevInverse
open scoped ContDiff ENNReal NNReal Topology Convolution

variable (period : ℝ) [Fact (0 < period)]

/-- Actual cylinder translations act strongly continuously on L². -/
theorem translation_continuous (f : LiftL2 period) :
    Continuous (fun a : LiftDomain period => translation period a f) := by
  let g : LiftDomain period → C(LiftDomain period, LiftDomain period) :=
    fun a => ⟨fun x => x + a, continuous_id.add_const a⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  have h := (continuous_const : Continuous (fun _ : LiftDomain period => f)).compMeasurePreservingLp
    hg (fun a => measurePreserving_translation period a) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  convert h using 1
  funext a
  rfl

omit [Fact (0 < period)] in
theorem euclideanCover_continuous : Continuous (euclideanCover period) := by
  exact ((continuous_fst).prodMk ((AddCircle.continuous_mk' period).comp continuous_snd)).comp coordinateEquiv.continuous

omit [Fact (0 < period)] in
theorem euclideanCover_add (x y : Domain 4) :
    euclideanCover period (x + y) = euclideanCover period x + euclideanCover period y := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_zero : euclideanCover period 0 = 0 := by
  ext i <;> simp [euclideanCover, coveringMap]

/-- The actual L² translation orbit in Euclidean covering coordinates. -/
def orbit (f : LiftL2 period) (x : Domain 4) : LiftL2 period :=
  translation period (euclideanCover period x) f

theorem orbit_continuous (f : LiftL2 period) : Continuous (orbit period f) :=
  (translation_continuous period f).comp (euclideanCover_continuous period)

@[simp]
theorem orbit_zero (f : LiftL2 period) : orbit period f 0 = f := by
  simp [orbit, euclideanCover_zero, translation_zero]

theorem orbit_norm (f : LiftL2 period) (x : Domain 4) : ‖orbit period f x‖ = ‖f‖ :=
  translation_norm period _ f

/-- A normalized approximate-identity bump with radii tending to zero. -/
def mollifierBump (n : ℕ) : ContDiffBump (0 : Domain 4) where
  rIn := cutoffScale n
  rOut := 2 * cutoffScale n
  rIn_pos := cutoffScale_pos n
  rIn_lt_rOut := by have h := cutoffScale_pos n; linarith

/-- The real smooth compact approximate-identity kernel. -/
def mollifierKernel (n : ℕ) : Domain 4 → ℝ := (mollifierBump n).normed volume

theorem mollifierKernel_smooth (n : ℕ) : ContDiff ℝ ∞ (mollifierKernel n) :=
  (mollifierBump n).contDiff_normed

theorem mollifierKernel_compact (n : ℕ) : HasCompactSupport (mollifierKernel n) :=
  (mollifierBump n).hasCompactSupport_normed

theorem mollifierKernel_nonneg (n : ℕ) (x : Domain 4) : 0 ≤ mollifierKernel n x :=
  (mollifierBump n).nonneg_normed x


/-- Bochner convolution of the actual L² orbit with the smooth approximate identity. -/
def smoothOrbit (n : ℕ) (f : LiftL2 period) : Domain 4 → LiftL2 period :=
  convolution (mollifierKernel n) (orbit period f) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The actual L² mollification; its expected representative is the classical periodic convolution. -/
def mollify (n : ℕ) (f : LiftL2 period) : LiftL2 period := smoothOrbit period n f 0

theorem smoothOrbit_contDiff (n : ℕ) (f : LiftL2 period) : ContDiff ℝ ∞ (smoothOrbit period n f) :=
  (mollifierKernel_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifierKernel_smooth n) (orbit_continuous period f).locallyIntegrable

/-- These actual smoothings converge strongly in the genuine cylinder L² space. -/
theorem mollify_tendsto (f : LiftL2 period) :
    Filter.Tendsto (fun n => mollify period n f) Filter.atTop (𝓝 f) := by
  have hr : Filter.Tendsto (fun n => (mollifierBump n).rOut) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mollifierBump, mul_zero] using cutoffScale_tendsto.const_mul 2
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (Domain 4)))
    hr (orbit_continuous period f) 0
  simpa only [orbit_zero, mollify, smoothOrbit, mollifierKernel] using h

theorem mollify_eq_integral (n : ℕ) (f : LiftL2 period) :
    mollify period n f = ∫ y : Domain 4, mollifierKernel n y • orbit period f (-y) := by
  simp only [mollify, smoothOrbit, convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub]

theorem kernel_orbit_integrable (n : ℕ) (f : LiftL2 period) :
    Integrable (fun y : Domain 4 => mollifierKernel n y • orbit period f (-y)) :=
  ((mollifierKernel_smooth n).continuous.smul ((orbit_continuous period f).comp continuous_neg)).integrable_of_hasCompactSupport
    (mollifierKernel_compact n).smul_right

/-- Smoothing is contractive in the actual cylinder L² norm. -/
theorem mollify_norm_le (n : ℕ) (f : LiftL2 period) : ‖mollify period n f‖ ≤ ‖f‖ := by
  rw [mollify_eq_integral]
  have h := norm_integral_le_of_norm_le
    (((mollifierBump n).integrable_normed (μ := (volume : Measure (Domain 4)))).mul_const ‖f‖)
    (f := fun y : Domain 4 => mollifierKernel n y • orbit period f (-y)) ?_
  · simpa only [integral_mul_const, mollifierKernel, (mollifierBump n).integral_normed, one_mul] using h
  apply Filter.Eventually.of_forall
  intro y
  rw [norm_smul, orbit_norm, Real.norm_eq_abs, abs_of_nonneg (mollifierKernel_nonneg n y)]
  exact le_rfl

theorem mollify_add (n : ℕ) (f g : LiftL2 period) :
    mollify period n (f + g) = mollify period n f + mollify period n g := by
  simp only [mollify_eq_integral, orbit, map_add, smul_add]
  exact integral_add (kernel_orbit_integrable period n f) (kernel_orbit_integrable period n g)

theorem mollify_smul (n : ℕ) (c : ℝ) (f : LiftL2 period) :
    mollify period n (c • f) = c • mollify period n f := by
  simp only [mollify_eq_integral, orbit, map_smul]
  simp_rw [smul_comm (mollifierKernel n _) c]
  exact integral_smul c _

/-- The actual linear averaging map associated with a smooth compact kernel. -/
def mollifierLinearMap (n : ℕ) : LiftL2 period →ₗ[ℝ] LiftL2 period where
  toFun := mollify period n
  map_add' := mollify_add period n
  map_smul' := mollify_smul period n

/-- The bounded L² approximate-identity operator, with operator norm at most one. -/
def mollifierOperator (n : ℕ) : LiftL2 period →L[ℝ] LiftL2 period :=
  (mollifierLinearMap period n).mkContinuous 1 (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa using mollify_norm_le period n f)


theorem mollifierOperator_norm_le (n : ℕ) : ‖mollifierOperator period n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa using mollify_norm_le period n f)

/-- The averaging operator commutes with every actual spatial or angular translation. -/
theorem mollify_translation (n : ℕ) (a : LiftDomain period) (f : LiftL2 period) :
    translation period a (mollify period n f) = mollify period n (translation period a f) := by
  rw [mollify_eq_integral, mollify_eq_integral]
  change (translation period a).toContinuousLinearMap
    (∫ y : Domain 4, mollifierKernel n y • orbit period f (-y)) = _
  rw [← (translation period a).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [map_smul, orbit]
  change mollifierKernel n y • translation period a (translation period (euclideanCover period (-y)) f) = _
  rw [translation_add, translation_add, add_comm a]

/-- Smoothing produces actual strong Sobolev jets and commutes with every derivative word. -/
def mollifyJet {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) :
    SpatialJet period directions s (mollify period n f) :=
  EulerPressureJetIdentities.SpatialJet.map (mollifierOperator period n)
    (mollify_translation period n) J

theorem mollifyJet_word {directions : Fin 4 → LiftTangent} {s k : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) (w : Fin k → Fin 4) :
    (mollifyJet period J n).word w = mollify period n (J.word w) :=
  EulerPressureJetIdentities.SpatialJet.map_word J (mollifierOperator period n)
    (mollify_translation period n) w


theorem sub_word {directions : Fin 4 → LiftTangent} {s k : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g)
    (w : Fin k → Fin 4) : (J.sub K).word w = J.word w - K.word w := by
  induction s generalizing f g k with
  | zero => cases J; cases K; cases k <;> simp [SpatialJet.sub, SpatialJet.word]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases k with
        | zero => simp
        | succ k =>
          simp only [SpatialJet.sub, SpatialJet.word_succ]
          exact ih (lower _) (lowerG _) _

/-- The same genuine mollifiers converge in every finite Sobolev jet norm. -/
theorem mollifyJet_sobolevNorm_tendsto {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) :
    Filter.Tendsto (fun n => ((mollifyJet period J n).sub J).sobolevNorm) Filter.atTop (𝓝 0) := by
  have hword : ∀ k (w : Fin k → Fin 4), Filter.Tendsto
      (fun n => ‖mollify period n (J.word w) - J.word w‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro k w
    simpa using ((mollify_tendsto period (J.word w)).sub_const (J.word w)).norm
  have hlevel : ∀ k, Filter.Tendsto (fun n => ∑ w : Fin k → Fin 4,
      ‖mollify period n (J.word w) - J.word w‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro k
    simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin k → Fin 4))) (fun w _ => hword k w)
  have h := tendsto_finsetSum (s := Finset.range (s + 1)) (fun k _ => hlevel k)
  simpa only [SpatialJet.sobolevNorm_eq_sum_words, sub_word, mollifyJet_word, Finset.sum_const_zero] using h

/-- The smooth Hilbert-valued convolution is exactly the translation orbit of the mollified field. -/
theorem smoothOrbit_eq_orbit_mollify (n : ℕ) (f : LiftL2 period) (x : Domain 4) :
    smoothOrbit period n f x = orbit period (mollify period n f) x := by
  rw [orbit, mollify_eq_integral]
  change _ = (translation period (euclideanCover period x)).toContinuousLinearMap
    (∫ y : Domain 4, mollifierKernel n y • orbit period f (-y))
  rw [← (translation period (euclideanCover period x)).toContinuousLinearMap.integral_comp_comm
    (kernel_orbit_integrable period n f)]
  simp only [smoothOrbit, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [map_smul, orbit]
  change mollifierKernel n y • translation period (euclideanCover period (x - y)) f =
    mollifierKernel n y • translation period (euclideanCover period x)
      (translation period (euclideanCover period (-y)) f)
  rw [translation_add, ← euclideanCover_add, sub_eq_add_neg]

/-- Mollification produces C∞ vectors for the genuine L² translation representation. -/
theorem mollify_orbit_contDiff (n : ℕ) (f : LiftL2 period) :
    ContDiff ℝ ∞ (orbit period (mollify period n f)) := by
  have heq : orbit period (mollify period n f) = smoothOrbit period n f := by
    funext x
    exact (smoothOrbit_eq_orbit_mollify period n f x).symm
  rw [heq]
  exact smoothOrbit_contDiff period n f


end EulerCylinderMollifier

end

section

/-! Set integration as a bounded functional on L², and its commutation with Bochner averages. -/


namespace EulerSetIntegralL2

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Integration on a finite-measure set as a genuine bounded linear map on L². -/
def setIntegralL2 (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) : Lp V 2 μ →L[ℝ] V :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 2 2
    (indicatorConstLp 2 hs hμs (1 : ℝ))

theorem setIntegralL2_apply (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (f : Lp V 2 μ) : setIntegralL2 s hs hμs f = ∫ x in s, f x ∂μ := by
  rw [setIntegralL2, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    _ = ∫ x, s.indicator (fun y => f y) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs]
    _ = _ := integral_indicator hs

/-- Bochner averaging of L² elements commutes with integration on every finite-measure set. -/
theorem setIntegral_integral_L2 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (F : Y → Lp V 2 μ) (hF : Integrable F ν) :
    (∫ x in s, (∫ y, F y ∂ν) x ∂μ) = ∫ y, ∫ x in s, F y x ∂μ ∂ν := by
  rw [← setIntegralL2_apply s hs hμs,
    ← (setIntegralL2 s hs hμs).integral_comp_comm hF]
  simp_rw [setIntegralL2_apply]

section Cylinder

open EulerLiftedGradientSpace EulerCylinderCoordinates EulerCylinderMollifier EulerSobolev

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_neg (y : Domain 4) : euclideanCover period (-y) = -euclideanCover period y := by
  simp [euclideanCover, coveringMap, map_neg]

/-- The Bochner L² mollifier and the classical convolution have the same iterated finite-set integrals. -/
theorem mollify_setIntegral (n : ℕ) (f : LiftL2 period) (s : Set (LiftDomain period))
    (hs : MeasurableSet s) (hμs : liftMeasure period s ≠ ⊤) :
    (∫ x in s, mollify period n f x ∂liftMeasure period) =
      ∫ y : Domain 4, ∫ x in s, mollifierKernel n y • f (x - euclideanCover period y)
        ∂liftMeasure period := by
  rw [mollify_eq_integral, setIntegral_integral_L2 s hs hμs _ (kernel_orbit_integrable period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (mollifierKernel n y) (orbit period f (-y))),
    ae_restrict_of_ae (translation_ae period (euclideanCover period (-y)) f)] with x hx hy
  rw [hx]
  change mollifierKernel n y • (translation period (euclideanCover period (-y)) f) x = _
  rw [hy, euclideanCover_neg, sub_eq_add_neg]

end Cylinder

end EulerSetIntegralL2

end

section

/-! Classical smooth cylinder representatives obtained by Euclidean mollification. -/

namespace EulerCoverMollification

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal Convolution Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_add (z w : Domain 4) :
    euclideanCover period (z+w) = euclideanCover period z + euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_sub (z w : Domain 4) :
    euclideanCover period (z-w) = euclideanCover period z - euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_sub]

omit [Fact (0 < period)] in
theorem euclideanCover_surjective : Function.Surjective (euclideanCover period) := by
  intro x
  obtain ⟨v, hv⟩ := (coveringMap_isOpenQuotient period).surjective x
  refine ⟨coordinateEquiv.symm v, ?_⟩
  simpa only [euclideanCover, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hv

section Integrability
variable {F : Type*} [NormedAddCommGroup F]

/-- L² cylinder fields have locally integrable periodic lifts to the Euclidean covering space. -/
theorem locallyIntegrable_cover (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    LocallyIntegrable (f ∘ euclideanCover period) (volume : Measure (Domain 4)) := by
  intro x
  have hT : 0 < period := Fact.out
  let a : ℝ := x 0 - period/2
  have hsubset : Metric.ball x (period/4) ⊆ {z : Domain 4 | z 0 ∈ Set.Ioc a (a+period)} := by
    intro z hz
    have hd : ‖z-x‖ < period/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hc : |z 0-x 0| ≤ ‖z-x‖ := PiLp.norm_apply_le (z-x) 0
    have hh := abs_le.mp (hc.trans hd.le)
    change a < z 0 ∧ z 0 ≤ a+period
    dsimp [a]
    constructor <;> linarith
  have hmeasure : (volume : Measure (Domain 4)).restrict (Metric.ball x (period/4)) ≤ stripMeasure period a :=
    Measure.restrict_mono hsubset le_rfl
  have hb : MemLp (f ∘ euclideanCover period) 2
      ((volume : Measure (Domain 4)).restrict (Metric.ball x (period/4))) :=
    MemLp.mono_measure hmeasure (memLp_cover period f hf a)
  have : Fact ((volume : Measure (Domain 4)) (Metric.ball x (period/4)) < ⊤) := ⟨measure_ball_lt_top⟩
  exact ⟨Metric.ball x (period/4), Metric.ball_mem_nhds x (by positivity), hb.integrable (by norm_num)⟩

end Integrability

section Convolution
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Euclidean convolution of the periodic lift with a normalized compact bump. -/
noncomputable def coverConvolution (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) : Domain 4 → F :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f ∘ euclideanCover period)

/-- The same convolution defined directly on the cylinder, with the usual negative translation. -/
noncomputable def cylinderConvolution (φ : ContDiffBump (0 : Domain 4))
    (f : LiftDomain period → F) (x : LiftDomain period) : F :=
  ∫ y : Domain 4, φ.normed volume y • f (x - euclideanCover period y)

omit [Fact (0 < period)] [CompleteSpace F] in
theorem cylinderConvolution_cover (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (z : Domain 4) :
    cylinderConvolution period φ f (euclideanCover period z) = coverConvolution period φ f z := by
  rw [coverConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply, Function.comp_apply, euclideanCover_sub]

omit [CompleteSpace F] in
/-- The classical covering-space convolution is genuinely C∞. -/
theorem coverConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) : ContDiff ℝ ∞ (coverConvolution period φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (n := (⊤ : ℕ∞))) (locallyIntegrable_cover period f hf)

omit [CompleteSpace F] in
/-- The convolution descends to a C∞ cylinder field in the actual local covering coordinates. -/
theorem cylinderConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (cylinderConvolution period φ f) x) := by
  intro x
  obtain ⟨z, hz⟩ := euclideanCover_surjective period x
  have he : localFieldLift period (cylinderConvolution period φ f) x =
      fun v => coverConvolution period φ f (z + coordinateEquiv.symm v) := by
    funext v
    rw [← cylinderConvolution_cover, euclideanCover_add, hz]
    congr 1
  rw [he]
  exact (coverConvolution_smooth period φ f hf).comp (contDiff_const.add coordinateEquiv.symm.contDiff)



end Convolution
end EulerCoverMollification

end

section

/-! The finite-set Fubini bridge identifying classical and L² cylinder mollification. -/

namespace EulerCoverMollificationFubini

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCoverMollification EulerLiftedGradientSpace
open scoped ENNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The elementary L²-to-L¹ bound on an arbitrary finite-measure set. -/
theorem finite_set_integral_norm_le (f : LiftDomain period → Vector3)
    (hf : MemLp f 2 (liftMeasure period)) (K : Set (LiftDomain period))
    (hK : liftMeasure period K < ⊤) :
    (∫ x in K, ‖f x‖ ∂liftMeasure period) ≤
      (eLpNorm f 2 (liftMeasure period)).toReal * (liftMeasure period K).toReal ^ (1/2 : ℝ) := by
  have hA := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞)) (q := 2)
    (by norm_num) (hf.restrict K).1
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one, Measure.restrict_apply_univ] at hA
  have hB : eLpNorm f 2 ((liftMeasure period).restrict K) * (liftMeasure period K)^(1/2 : ℝ) ≤
      eLpNorm f 2 (liftMeasure period) * (liftMeasure period K)^(1/2 : ℝ) :=
    mul_le_mul' (eLpNorm_mono_measure f (Measure.restrict_le_self (s := K))) le_rfl
  have hfin : eLpNorm f 2 (liftMeasure period) * (liftMeasure period K) ^ (1/2 : ℝ) ≠ ⊤ := by finiteness
  have hC := ENNReal.toReal_mono hfin (hA.trans hB)
  rw [integral_norm_eq_lintegral_enorm (hf.restrict K).1, ← eLpNorm_one_eq_lintegral_enorm]
  convert hC using 1
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

omit [Fact (0 < period)] in
/-- The Euclidean covering map is continuous. -/
theorem euclideanCover_continuous : Continuous (euclideanCover period) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp coordinateEquiv.continuous

/-- The convolution kernel is jointly integrable over the kernel variable and any finite cylinder set. -/
theorem kernel_integrable_prod (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    Integrable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1))
      ((volume : Measure (Domain 4)).prod ((liftMeasure period).restrict K)) := by
  have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
  have hmap : Measurable (fun p : Domain 4 × LiftDomain period => p.2 - euclideanCover period p.1) :=
    (continuous_snd.sub ((euclideanCover_continuous period).comp continuous_fst)).measurable
  have hsm : StronglyMeasurable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1)) :=
    ((φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.comp continuous_fst).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable U).comp_measurable hmap)
  have hshift (y : Domain 4) : MemLp (fun x => U (x - euclideanCover period y)) 2 (liftMeasure period) := by
    convert! (Lp.memLp U).comp_measurePreserving
      (measurePreserving_translation period (-euclideanCover period y)) using 1
  apply (integrable_prod_iff hsm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with y
    have hint : Integrable (fun x => U (x-euclideanCover period y)) ((liftMeasure period).restrict K) :=
      ((hshift y).restrict K).integrable (by norm_num)
    exact hint.smul (φ.normed volume y)
  · have hbound (y : Domain 4) : (∫ x in K, ‖φ.normed volume y • U (x - euclideanCover period y)‖ ∂liftMeasure period) ≤
        ‖φ.normed volume y‖ * (‖U‖ * (liftMeasure period K).toReal ^ (1/2 : ℝ)) := by
      simp only [norm_smul, integral_const_mul]
      have he : eLpNorm (fun x => U (x - euclideanCover period y)) 2 (liftMeasure period) =
          eLpNorm U 2 (liftMeasure period) := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable U)
            (measurePreserving_translation period (-euclideanCover period y))
      have h := finite_set_integral_norm_le period _ (hshift y) K hK
      rw [he, ← Lp.norm_def] at h
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    exact (φ.integrable_normed.norm.mul_const (‖U‖ * (liftMeasure period K).toReal ^ (1/2 : ℝ))).mono'
      hsm.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
        exact hbound y))

/-- The classical cylinder convolution is integrable on each finite-measure set. -/
theorem cylinderConvolution_integrableOn (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    IntegrableOn (cylinderConvolution period φ U) K (liftMeasure period) := by
  exact (kernel_integrable_prod period φ U K hK).integral_prod_right

/-- Exact Fubini identity for every finite cylinder set. -/
theorem setIntegral_cylinderConvolution (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    (∫ x in K, cylinderConvolution period φ U x ∂liftMeasure period) =
      ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure period) := by
  have h := integral_integral_swap (f := fun (y : Domain 4) (x : LiftDomain period) =>
      φ.normed volume y • U (x-euclideanCover period y))
    (μ := (volume : Measure (Domain 4))) (ν := (liftMeasure period).restrict K)
    (kernel_integrable_prod period φ U K hK)
  change (∫ x in K, ∫ y : Domain 4, φ.normed volume y • U (x-euclideanCover period y) ∂volume ∂liftMeasure period) = _
  rw [← h]
  simp only [integral_smul]

/-- Equality of finite-set integrals identifies a Bochner L² mollifier with the classical smooth field. -/
theorem ae_eq_cylinderConvolution_of_setIntegrals (φ : ContDiffBump (0 : Domain 4)) (U V : LiftL2 period)
    (hV : ∀ K : Set (LiftDomain period), MeasurableSet K → liftMeasure period K < ⊤ →
      (∫ x in K, V x ∂liftMeasure period) =
        ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure period)) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] cylinderConvolution period φ U := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro K _ hK
    have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
    exact ((Lp.memLp V).restrict K).integrable (by norm_num)
  · intro K _ hK
    exact cylinderConvolution_integrableOn period φ U K hK
  · intro K hK hfin
    exact (hV K hK hfin).trans (setIntegral_cylinderConvolution period φ U K hfin).symm

end EulerCoverMollificationFubini

end

section

/-! Actual classical smooth representatives of the strong L² cylinder mollifiers. -/

namespace EulerMollifierRepresentative

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev
open EulerLiftedGradientSpace EulerMetricTransport EulerCoverMollification
open EulerCoverMollificationFubini EulerCylinderMollifier EulerSpatialSobolevInverse EulerStrongSmoothJet
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The concrete classical convolution representing the Bochner L² mollifier. -/
noncomputable def smoothMollifier (n : ℕ) (U : LiftL2 period) : LiftDomain period → Vector3 :=
  cylinderConvolution period (mollifierBump n) U

/-- The smooth convolution and the Bochner convolution are the same almost everywhere. -/
theorem mollify_ae_smoothMollifier (n : ℕ) (U : LiftL2 period) :
    (mollify period n U : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      smoothMollifier period n U := by
  apply ae_eq_cylinderConvolution_of_setIntegrals period (mollifierBump n) U (mollify period n U)
  intro K hK hfin
  simpa only [mollifierKernel, integral_smul] using
    EulerSetIntegralL2.mollify_setIntegral period n U K hK hfin.ne

/-- Every strong L² mollifier has an actual C∞ representative on the cylinder. -/
theorem smoothMollifier_smooth (n : ℕ) (U : LiftL2 period) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (smoothMollifier period n U) x) :=
  cylinderConvolution_smooth period (mollifierBump n) U (Lp.memLp U)

/-- Strong mollified jets are precisely the classical derivatives of the smooth convolution. -/
theorem smoothMollifier_word_ae {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    (mollify period n (J.word w) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      iteratedFieldDerivative period w (smoothMollifier period n U) := by
  rw [← mollifyJet_word period J n w]
  exact jet_word_ae period hk _ (mollifyJet period J n) w _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)



end EulerMollifierRepresentative

end

section

/-! Uniform control of every classical derivative word by actual strong Sobolev jets. -/


namespace EulerMollifierUniform

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerSpatialSobolevInverse
  EulerStrongSmoothJet EulerCylinderMollifier EulerMollifierRepresentative
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- An arbitrary derivative word has H³ norm controlled by the full norm three orders higher. -/
theorem word_H3_le_higher {m : ℕ} (w : Fin m → Fin 4) (f : LiftDomain period → Vector3) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period (m + 3) f := by
  have hA : (∑ n ∈ Finset.range (3+1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3+1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period (m + 3) f := by
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

/-- Every actual smooth derivative word is uniformly controlled by its genuine strong jet. -/
theorem jet_word_pointwise_bound {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4)
    (f : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      (3 * cylinderEmbeddingConstant period) * (85 * J.sobolevNorm) := by
  have hLp : ∀ j ≤ m + 3, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period) :=
    fun j hj u => jet_classical_memLp period hj U J u f hrep hf
  have hA := vector_cylinder_pointwise_le_H3 period 3 (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ m+3) v w f hLp) x
  have hB := word_H3_le_higher period w f
  rw [← jet_sobolevNorm_eq period U J f hrep hf] at hB
  exact hA.trans (mul_le_mul_of_nonneg_left hB
    (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)))

omit [Fact (0 < period)] in
theorem fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    fieldDerivative period a (fun y => f y - g y) x =
      fieldDerivative period a f x - fieldDerivative period a g x := by
  have h := ((((hf x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)).sub
    (((hg x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0))).fderiv
  have h' := congrArg (fun L : LiftTangent →L[ℝ] Vector3 => L a) h
  simpa +unfoldPartialApp [fieldDerivative, localFieldLift, Pi.sub_def] using h'

omit [Fact (0 < period)] in
theorem word_sub {m : ℕ} (w : Fin m → Fin 4) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    iteratedFieldDerivative period w (fun y => f y - g y) =
      fun x => iteratedFieldDerivative period w f x - iteratedFieldDerivative period w g x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w)]
    funext x
    exact fieldDerivative_sub period (standardDirection (w 0)) _ _
      (iteratedFieldDerivative_smooth period (Fin.tail w) f hf)
      (iteratedFieldDerivative_smooth period (Fin.tail w) g hg) x

/-- Uniform derivative differences are controlled by the actual L² Sobolev difference jet. -/
theorem jet_word_difference_bound {m : ℕ} (U V : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U)
    (K : SpatialJet period standardDirection (m + 3) V) (w : Fin m → Fin 4)
    (f g : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hrepG : (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x - iteratedFieldDerivative period w g x‖ ≤
      (3 * cylinderEmbeddingConstant period) * (85 * (J.sub K).sobolevNorm) := by
  have hrepD : ((U - V : LiftL2 period) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      fun x => f x - g x := by
    filter_upwards [Lp.coeFn_sub U V, hrep, hrepG] with y hy hfy hgy
    simpa [hfy, hgy] using hy
  have h := jet_word_pointwise_bound period (U - V) (J.sub K) w (fun x => f x - g x)
    hrepD (fun x => (hf x).sub (hg x)) x
  simpa only [word_sub period w f g hf hg] using h

/-- A genuine Sobolev difference is bounded through any third jet at the same order. -/
theorem jet_sub_triangle {s : ℕ} {U V W : LiftL2 period}
    (J : SpatialJet period standardDirection s U) (K : SpatialJet period standardDirection s V)
    (L : SpatialJet period standardDirection s W) :
    (J.sub K).sobolevNorm ≤ (J.sub L).sobolevNorm + (K.sub L).sobolevNorm := by
  simp only [SpatialJet.sobolevNorm_eq_sum_words, sub_word]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  calc
    ‖J.word w - K.word w‖ = ‖(J.word w - L.word w) + (L.word w - K.word w)‖ := by congr 1; abel
    _ ≤ ‖J.word w - L.word w‖ + ‖L.word w - K.word w‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev (L.word w) (K.word w)]

/-- Every actual classical derivative word of the mollifiers is uniformly Cauchy. -/
theorem smoothMollifier_word_uniformCauchy {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4) :
    UniformCauchySeqOn (fun n x => iteratedFieldDerivative period w (smoothMollifier period n U) x)
      Filter.atTop Set.univ := by
  let C : ℝ := (3 * cylinderEmbeddingConstant period) * 85
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)) (by norm_num)
  have hlim : Filter.Tendsto (fun n => C * ((mollifyJet period J n).sub J).sobolevNorm)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (mollifyJet_sobolevNorm_tendsto period J).const_mul C
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hsmall := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨N, fun a ha b hb x _ => ?_⟩
  have hab := jet_word_difference_bound period (mollify period a U) (mollify period b U)
    (mollifyJet period J a) (mollifyJet period J b) w
    (smoothMollifier period a U) (smoothMollifier period b U)
    (mollify_ae_smoothMollifier period a U) (mollify_ae_smoothMollifier period b U)
    (smoothMollifier_smooth period a U) (smoothMollifier_smooth period b U) x
  have htri := jet_sub_triangle period (mollifyJet period J a) (mollifyJet period J b) J
  have hna := hN a ha
  have hnb := hN b hb
  calc
    _ = ‖iteratedFieldDerivative period w (smoothMollifier period a U) x -
        iteratedFieldDerivative period w (smoothMollifier period b U) x‖ := dist_eq_norm _ _
    _ ≤ (3 * cylinderEmbeddingConstant period) *
        (85 * ((mollifyJet period J a).sub (mollifyJet period J b)).sobolevNorm) := hab
    _ = C * ((mollifyJet period J a).sub (mollifyJet period J b)).sobolevNorm := by dsimp [C]; ring
    _ ≤ C * (((mollifyJet period J a).sub J).sobolevNorm +
        ((mollifyJet period J b).sub J).sobolevNorm) := mul_le_mul_of_nonneg_left htri hC
    _ < ε := by linarith

/-- Completeness produces a uniform limit for every actual derivative word. -/
theorem exists_smoothMollifier_word_uniform_limit {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4) :
    ∃ g : LiftDomain period → Vector3,
      TendstoUniformly (fun n => iteratedFieldDerivative period w (smoothMollifier period n U))
        g Filter.atTop := by
  have hC := smoothMollifier_word_uniformCauchy period U J w
  have hex : ∀ x : LiftDomain period, ∃ v : Vector3,
      Filter.Tendsto (fun n => iteratedFieldDerivative period w (smoothMollifier period n U) x)
        Filter.atTop (𝓝 v) := fun x => cauchySeq_tendsto_of_complete (hC.cauchySeq (Set.mem_univ x))
  choose g hg using hex
  exact ⟨g, tendstoUniformlyOn_univ.mp (hC.tendstoUniformlyOn_of_tendsto (fun x _ => hg x))⟩

/-- The uniform classical word limit represents the actual strong L² derivative word. -/
theorem smoothMollifier_word_limit_ae {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4)
    (g : LiftDomain period → Vector3)
    (hlim : TendstoUniformly (fun n => iteratedFieldDerivative period w (smoothMollifier period n U))
      g Filter.atTop) : (J.word w : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  obtain ⟨index, hindex, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (mollify_tendsto period (J.word w))).exists_seq_tendsto_ae'
  have hrep : ∀ᵐ x ∂liftMeasure period, ∀ n : ℕ,
      mollify period (index n) (J.word w) x =
        iteratedFieldDerivative period w (smoothMollifier period (index n) U) x :=
    ae_all_iff.mpr (fun n => smoothMollifier_word_ae period (by omega) U J (index n) w)
  filter_upwards [hsub, hrep] with x hx hxr
  have heq : (fun n => mollify period (index n) (J.word w) x) =
      fun n => iteratedFieldDerivative period w (smoothMollifier period (index n) U) x := funext hxr
  rw [heq] at hx
  exact tendsto_nhds_unique hx ((hlim.tendsto_at x).comp hindex)

/-- Strong H³ cylinder jets have genuine continuous representatives. -/
theorem exists_continuous_representative (U : LiftL2 period)
    (J : SpatialJet period standardDirection 3 U) :
    ∃ g : LiftDomain period → Vector3, Continuous g ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U J w
  refine ⟨g, ?_, ?_⟩
  · apply hg.continuous
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall fun n =>
      smoothField_continuous period _ (smoothMollifier_smooth period n U)
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U J w g hg

end EulerMollifierUniform

end

section

/-! Full Fréchet tensor convergence from the genuine cylinder derivative words. -/

namespace EulerMollifierTensors

open MeasureTheory Filter EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerSobolevDerivativeNorm
open scoped ContDiff Topology

variable (period : ℝ)

/-- The operator norm of a difference of derivative tensors is controlled by the finite coordinate sum. -/
theorem tensor_difference_le_word_sum (m : ℕ) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z‖ ≤
    ∑ w : Fin m → Fin 4,
      ‖iteratedFieldDerivative period w f (euclideanCover period z + x) -
        iteratedFieldDerivative period w g (euclideanCover period z + x)‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 m
    (iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z)
  simpa only [sub_apply,
    ← euclideanLift_iteratedFieldDerivative period _ f hf,
    ← euclideanLift_iteratedFieldDerivative period _ g hg,
    euclideanLift_eq_translated_cover, translated] using h

/-- Uniform Cauchy convergence of every coordinate word gives uniform Cauchy convergence of the full tensor. -/
theorem tensor_uniformCauchy_of_words (m : ℕ) (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ w : Fin m → Fin 4,
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (x : LiftDomain period) :
    UniformCauchySeqOn
      (fun k => iteratedFDeriv ℝ m (euclideanLift period (f k) x)) atTop Set.univ := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hc : 0 < (4 : ℝ)^m := pow_pos (by norm_num) _
  have hsmall := fun w : Fin m → Fin 4 =>
    Metric.uniformCauchySeqOn_iff.mp (hC w) (ε / (4 : ℝ)^m) (div_pos hε hc)
  choose N hN using hsmall
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl z _
  have hword (w : Fin m → Fin 4) :
      ‖iteratedFieldDerivative period w (f k) (euclideanCover period z + x) -
        iteratedFieldDerivative period w (f l) (euclideanCover period z + x)‖ < ε / (4 : ℝ)^m := by
    simpa only [dist_eq_norm] using hN w k
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hk) l
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hl)
      (euclideanCover period z + x) (Set.mem_univ _)
  rw [dist_eq_norm]
  apply (tensor_difference_le_word_sum period m (f k) (f l) (hf k) (hf l) x z).trans_lt
  calc
    _ < ∑ _w : Fin m → Fin 4, ε / (4 : ℝ)^m := by
      apply Finset.sum_lt_sum (fun w _ => (hword w).le)
      exact ⟨fun _ => 0, Finset.mem_univ _, hword _⟩
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      exact mul_div_cancel₀ ε hc.ne'

end EulerMollifierTensors

end

section

/-! Smoothness of uniform limits of complete Fréchet derivative towers. -/

namespace EulerSmoothTensorLimit

open Filter
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A uniformly Cauchy sequence at every actual Fréchet derivative order has a genuine smooth limit. -/
theorem exists_smooth_limit (f : ℕ → E → F) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hC : ∀ m, UniformCauchySeqOn (fun k => iteratedFDeriv ℝ m (f k)) atTop Set.univ) :
    ∃ g : E → F, TendstoUniformly f g atTop ∧ ContDiff ℝ ∞ g := by
  let L (m : ℕ) : (E [×(m+1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×m]→L[ℝ] F)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
  have hD (m k : ℕ) (x : E) : HasFDerivAt (iteratedFDeriv ℝ m (f k))
      (L m (iteratedFDeriv ℝ (m+1) (f k) x)) x := by
    have hd := (hf k).differentiable_iteratedFDeriv
      (show (m : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top m) x
    exact hd.hasFDerivAt
  obtain ⟨J, hJ, hJs⟩ := EulerSmoothUniformLimit.exists_smooth_limit_of_uniform_cauchy_tower
    (fun m k => iteratedFDeriv ℝ m (f k)) L hD hC
  let A := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨fun x => A (J 0 x), ?_, A.contDiff.comp (hJs 0)⟩
  have h := A.uniformContinuous.comp_tendstoUniformly (hJ 0)
  simpa only [A, Function.comp_def, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply] using h

section Cylinder

open EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev EulerLiftedGradientSpace
open EulerMetricTransport EulerMollifierTensors

/-- A pointwise cylinder limit is C∞ when every coordinate derivative word is uniformly Cauchy. -/
theorem cylinder_smooth_of_uniformCauchy_words (period : ℝ)
    (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ m (w : Fin m → Fin 4),
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (g : LiftDomain period → Vector3)
    (hpoint : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := by
  intro x
  obtain ⟨G, hG, hGs⟩ := exists_smooth_limit
    (fun k => euclideanLift period (f k) x)
    (fun k => euclideanLift_smooth period (f k) (hf k) x)
    (fun m => tensor_uniformCauchy_of_words period m f hf (hC m) x)
  have he : euclideanLift period g x = G := by
    funext z
    have hp : Tendsto (fun k => euclideanLift period (f k) x z) atTop
        (𝓝 (euclideanLift period g x z)) := by
      simpa only [euclideanLift_eq_translated_cover, translated] using
        hpoint (euclideanCover period z + x)
    exact tendsto_nhds_unique hp (hG.tendsto_at z)
  have hlocal : localFieldLift period g x = G ∘ coordinateEquiv.symm := by
    rw [← he]
    funext v
    simp only [euclideanLift, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hlocal]
  exact hGs.comp coordinateEquiv.symm.contDiff

end Cylinder

end EulerSmoothTensorLimit

end

section

/-! Actual C∞ representatives obtained from all-order strong cylinder jets. -/


namespace EulerSmoothPressureRepresentative

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMollifierRepresentative EulerMollifierUniform
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- All-order strong cylinder jets produce an actual C∞ representative of the L² field. -/
theorem exists_smooth_representative (U : LiftL2 period)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s U) :
    ∃ g : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U (J 3) w
  have hpoint : ∀ x, Filter.Tendsto (fun n => smoothMollifier period n U x)
      Filter.atTop (𝓝 (g x)) := fun x => hg.tendsto_at x
  have hC : ∀ m (v : Fin m → Fin 4), UniformCauchySeqOn
      (fun n => iteratedFieldDerivative period v (smoothMollifier period n U)) Filter.atTop Set.univ :=
    fun m v => smoothMollifier_word_uniformCauchy period U (J (m + 3)) v
  refine ⟨g, ?_, ?_⟩
  · exact EulerSmoothTensorLimit.cylinder_smooth_of_uniformCauchy_words period
      (fun n => smoothMollifier period n U) (fun n => smoothMollifier_smooth period n U) hC g hpoint
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U (J 3) w g hg


end EulerSmoothPressureRepresentative

end

end
