import NavierStokes.SimilarityProfile
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Radial divisibility and regular slow-order sources

This module removes the apparent `1/X` singularities in the radial source
of equation (22), using the actual differential operators from SimilarityProfile.
-/

noncomputable section

namespace NavierStokes.AxisSourceRegularity

open SimilarityProfile Set Filter
open scoped BigOperators Topology ContDiff

noncomputable def axisFactor (v : InnerProfile) (w : InnerPoint) : ℝ := w.1 * v w

theorem partialX_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    partialX (axisFactor v) w = v w + w.1 * partialX v w := by
  change (fderiv ℝ (fun y : InnerPoint => y.1 * v y) w) (1, 0) = _
  rw [(hasFDerivAt_fst.fun_mul hv.hasFDerivAt).fderiv]
  simp [partialX]
  ring

theorem partialEta_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    partialEta (axisFactor v) w = w.1 * partialEta v w := by
  change (fderiv ℝ (fun y : InnerPoint => y.1 * v y) w) (0, 1) = _
  rw [(hasFDerivAt_fst.fun_mul hv.hasFDerivAt).fderiv]
  simp [partialEta]

/-- Factoring out X shifts the similarity exponent by one. -/
theorem T_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    T h b (axisFactor v) w = w.1 * T h (b - 1) v w := by
  simp only [T, CoordinateAlgebra.timeCoeff, partialX_axisFactor hv,
    partialEta_axisFactor hv, axisFactor]
  ring

theorem Z_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : DifferentiableAt ℝ v w) :
    Z h b (axisFactor v) w = w.1 * Z h (b - 1) v w := by
  simp only [Z, CoordinateAlgebra.axialCoeff, partialX_axisFactor hv,
    partialEta_axisFactor hv, axisFactor]
  ring

theorem Z_congr_germ (h b : ℝ) {f g : InnerProfile} {w : InnerPoint}
    (hfg : f =ᶠ[𝓝 w] g) : Z h b f w = Z h b g w := by
  simp only [Z, CoordinateAlgebra.axialCoeff, partialX, partialEta,
    hfg.eq_of_nhds, hfg.fderiv_eq]

theorem partialXX_axisFactor {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) :
    partialX (partialX (axisFactor v)) w =
      2 * partialX v w + w.1 * partialX (partialX v) w := by
  have heq : partialX (axisFactor v) =ᶠ[𝓝 w] (fun y => v y + y.1 * partialX v y) := by
    filter_upwards [hv.eventually (by norm_num)] with y hy
    exact partialX_axisFactor (hy.differentiableAt (by norm_num))
  have hx := (partialX_smoothAt hv (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change (fderiv ℝ (partialX (axisFactor v)) w) (1, 0) = _
  rw [heq.fderiv_eq,
    ((hv.differentiableAt (by norm_num)).hasFDerivAt.fun_add
      (hasFDerivAt_fst.fun_mul hx.hasFDerivAt)).fderiv]
  simp [partialX]
  ring

noncomputable def Z2 (h b : ℝ) (v : InnerProfile) : InnerProfile :=
  Z h (b - D h) (Z h b v)

theorem Z2_axisFactor (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ 2 v w) (hL : L h w.2 ≠ 0) :
    Z2 h b (axisFactor v) w = w.1 * Z2 h (b - 1) v w := by
  have heq : Z h b (axisFactor v) =ᶠ[𝓝 w] axisFactor (Z h (b - 1) v) := by
    filter_upwards [hv.eventually (by norm_num)] with y hy
    exact Z_axisFactor h b (hy.differentiableAt (by norm_num))
  change Z h (b - D h) (Z h b (axisFactor v)) w = _
  rw [Z_congr_germ h (b - D h) heq,
    Z_axisFactor h (b - D h) ((Z_smoothAt hv hL).differentiableAt (by norm_num))]
  have he : b - D h - 1 = b - 1 - D h := by ring
  rw [he]
  rfl

theorem radial_advection_axisFactor {vi vj : InnerProfile} {w : InnerPoint}
    (hvj : DifferentiableAt ℝ vj w) :
    axisFactor vi w * (partialX (axisFactor vj) w - axisFactor vj w / (2 * w.1)) =
      w.1 * (vi w * (vj w / 2 + w.1 * partialX vj w)) := by
  rw [partialX_axisFactor hvj]
  unfold axisFactor
  by_cases hX : w.1 = 0
  · simp [hX]
  · field_simp [hX]
    ring

noncomputable def slowOrder (h : ℝ) (k : ℕ) : ℝ := 2 * (k : ℝ) * h

noncomputable def shiftedAxial (h : ℝ) (V : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k) (V k)

noncomputable def shiftedAxialFactor (h : ℝ) (v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => Z2 h (slowOrder h k - 1) (v k)

/-- The displayed Ω_k source before canceling its radial factor. -/
noncomputable def omega (h : ℝ) (U V : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint) : ℝ :=
  T h (slowOrder h k) (V k) w +
    (∑ ij ∈ Finset.antidiagonal k,
      (V ij.1 w * (partialX (V ij.2) w - V ij.2 w / (2 * w.1)) +
        U ij.1 w * Z h (slowOrder h ij.2) (V ij.2) w)) -
    2 * w.1 * partialX (partialX (V k)) w - shiftedAxial h V k w

/-- An explicit expression for Ω_k/X with no division by X. -/
noncomputable def omegaDivX (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint) : ℝ :=
  T h (slowOrder h k - 1) (v k) w +
    (∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 w * (v ij.2 w / 2 + w.1 * partialX (v ij.2) w) +
        U ij.1 w * Z h (slowOrder h ij.2 - 1) (v ij.2) w)) -
    (4 * partialX (v k) w + 2 * w.1 * partialX (partialX (v k)) w) -
    shiftedAxialFactor h v k w

theorem shiftedAxial_axisFactor (h : ℝ) (v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    shiftedAxial h (fun j => axisFactor (v j)) k w = w.1 * shiftedAxialFactor h v k w := by
  cases k with
  | zero => simp [shiftedAxial, shiftedAxialFactor]
  | succ k => exact Z2_axisFactor h (slowOrder h k) (hv k (Nat.le_succ k)) hL

/-- Every term in the actual finite Ω_k source has the factor X. -/
theorem omega_axisFactor (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) :
    omega h U (fun j => axisFactor (v j)) k w = w.1 * omegaDivX h U v k w := by
  have hpair : ∀ ij ∈ Finset.antidiagonal k,
      axisFactor (v ij.1) w * (partialX (axisFactor (v ij.2)) w - axisFactor (v ij.2) w / (2 * w.1)) +
        U ij.1 w * Z h (slowOrder h ij.2) (axisFactor (v ij.2)) w =
      w.1 * (v ij.1 w * (v ij.2 w / 2 + w.1 * partialX (v ij.2) w) +
        U ij.1 w * Z h (slowOrder h ij.2 - 1) (v ij.2) w) := by
    intro ij hij
    have hj : ij.2 ≤ k := by
      have he := Finset.mem_antidiagonal.mp hij
      omega
    rw [radial_advection_axisFactor ((hv ij.2 hj).differentiableAt (by norm_num)),
      Z_axisFactor h (slowOrder h ij.2) ((hv ij.2 hj).differentiableAt (by norm_num))]
    ring
  unfold omega omegaDivX
  rw [T_axisFactor h (slowOrder h k) ((hv k le_rfl).differentiableAt (by norm_num)),
    Finset.sum_congr rfl hpair, ← Finset.mul_sum,
    partialXX_axisFactor (hv k le_rfl), shiftedAxial_axisFactor h v k w hv hL]
  ring

theorem omega_quotient_eq (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ 2 (v j) w) (hL : L h w.2 ≠ 0) (hX : w.1 ≠ 0) :
    omega h U (fun j => axisFactor (v j)) k w / w.1 = omegaDivX h U v k w := by
  rw [omega_axisFactor h U v k w hv hL, mul_div_cancel_left₀ _ hX]

theorem partialX_smooth {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) : ContDiffAt ℝ ∞ (partialX v) w :=
  partialX_smoothAt hv (by simp)

theorem partialEta_smooth {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) : ContDiffAt ℝ ∞ (partialEta v) w :=
  partialEta_smoothAt hv (by simp)

theorem T_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (T h b v) w := by
  exact (((contDiffAt_const.mul hv).add
    ((contDiffAt_const.mul contDiffAt_snd).mul (partialEta_smooth hv))).add
    (contDiffAt_fst.mul (partialX_smooth hv))).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem Z_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (Z h b v) w := by
  exact ((((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_const).mul hv).add
    ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul (partialEta_smooth hv)) |>.sub
    (((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_fst).mul (partialX_smooth hv))).div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL

theorem Z2_smooth (h b : ℝ) {v : InnerProfile} {w : InnerPoint}
    (hv : ContDiffAt ℝ ∞ v w) (hL : L h w.2 ≠ 0) : ContDiffAt ℝ ∞ (Z2 h b v) w :=
  Z_smooth h (b - D h) (Z_smooth h b hv hL) hL

theorem antidiagonal_indices_le {i j k : ℕ} (hij : (i, j) ∈ Finset.antidiagonal k) :
    i ≤ k ∧ j ≤ k := by
  have he := Finset.mem_antidiagonal.mp hij
  omega

/-- The quotient formula is smooth at the axis, using only the finite input
profiles occurring at this order. No division by the radial coordinate remains. -/
theorem omegaDivX_smooth (h : ℝ) (U v : ℕ → InnerProfile) (k : ℕ) (w : InnerPoint)
    (hU : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (U j) w)
    (hv : ∀ j, j ≤ k → ContDiffAt ℝ ∞ (v j) w) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (omegaDivX h U v k) w := by
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ ij ∈ Finset.antidiagonal k,
      (v ij.1 y * (v ij.2 y / 2 + y.1 * partialX (v ij.2) y) +
        U ij.1 y * Z h (slowOrder h ij.2 - 1) (v ij.2) y)) w := by
    apply ContDiffAt.sum
    intro ij hij
    obtain ⟨hi, hj⟩ := antidiagonal_indices_le hij
    exact ((hv ij.1 hi).mul (((hv ij.2 hj).div contDiffAt_const (by norm_num)).add
      (contDiffAt_fst.mul (partialX_smooth (hv ij.2 hj))))).add
      ((hU ij.1 hi).mul (Z_smooth h _ (hv ij.2 hj) hL))
  have hp : ContDiffAt ℝ ∞ (shiftedAxialFactor h v k) w := by
    cases k with
    | zero => exact contDiffAt_const
    | succ k => exact Z2_smooth h _ (hv k (Nat.le_succ k)) hL
  exact (((T_smooth h _ (hv k le_rfl) hL).add hs).sub
    ((contDiffAt_const.mul (partialX_smooth (hv k le_rfl))).add
      ((contDiffAt_const.mul contDiffAt_fst).mul
        (partialX_smooth (partialX_smooth (hv k le_rfl)))))).sub hp








/-! ## Explicit finite jets and parameter-analytic source formulas -/

structure Jet2 (K : Type*) where
  value : K
  dx : K
  de : K
  dxx : K
  dxe : K
  dex : K
  dee : K

noncomputable def profileJet (v : InnerProfile) (w : InnerPoint) : Jet2 ℝ where
  value := v w
  dx := partialX v w
  de := partialEta v w
  dxx := partialX (partialX v) w
  dxe := partialEta (partialX v) w
  dex := partialX (partialEta v) w
  dee := partialEta (partialEta v) w

















/-- Holomorphic extensions of the seven actual input jets. This is stronger
than separate analyticity of v alone and is the precise parameter hypothesis used. -/
structure AnalyticJetAt (J : ℂ → Jet2 ℂ) (e : ℂ) : Prop where
  value : AnalyticAt ℂ (fun z => (J z).value) e
  dx : AnalyticAt ℂ (fun z => (J z).dx) e
  de : AnalyticAt ℂ (fun z => (J z).de) e
  dxx : AnalyticAt ℂ (fun z => (J z).dxx) e
  dxe : AnalyticAt ℂ (fun z => (J z).dxe) e
  dex : AnalyticAt ℂ (fun z => (J z).dex) e
  dee : AnalyticAt ℂ (fun z => (J z).dee) e














noncomputable def lowerPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal n).filter (fun ij => 0 < ij.1 ∧ 0 < ij.2)


noncomputable def lowerConvolution (a b : ℕ → InnerProfile) (n : ℕ) (w : InnerPoint) : ℝ :=
  ∑ ij ∈ lowerPairs n, a ij.1 w * b ij.2 w

noncomputable def previousOmegaDivX (h : ℝ) (U v : ℕ → InnerProfile) : ℕ → InnerProfile
  | 0 => fun _ => 0
  | k + 1 => omegaDivX h U v k













/-! ## The other finite lower-order transport sources -/













end NavierStokes.AxisSourceRegularity
