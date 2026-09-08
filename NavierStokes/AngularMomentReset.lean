import NavierStokes.LocalizedMomentRepair
import NavierStokes.SmoothMomentRepair
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases

/-!
# A pressure-neutral angular-moment reset

Two identical translated smooth relative bumps repair the angular moment while
preserving the pressure integral exactly. The actual two-row derivative matrix
is proved nonsingular, and the small smooth nonlinear branch is constructed.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace NavierStokes.AngularMomentReset

abbrev Coeff := Fin 2 → ℝ

def template : ℝ → ℝ := LocalizedMomentRepair.bump (-3 / 10) (3 / 10)

def bump (j : Fin 2) (y : ℝ) : ℝ := template (y - 2 * (j.val : ℝ))

theorem template_contDiff : ContDiff ℝ ∞ template :=
  LocalizedMomentRepair.bump_contDiff _ _

theorem template_at_zero : template 0 = 1 := by
  have h := LocalizedMomentRepair.bump_at_center (-3 / 10) (3 / 10)
  norm_num at h
  simpa [template, neg_div] using h

theorem template_support : support template ⊆ Icc (-3 / 20 : ℝ) (3 / 20) := by
  have h := LocalizedMomentRepair.bump_support_subset (-3 / 10) (3 / 10) (by norm_num)
  norm_num [LocalizedMomentRepair.innerLower, LocalizedMomentRepair.innerUpper] at h
  simpa [template, neg_div] using h

theorem template_hasCompactSupport : HasCompactSupport template :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc template_support

theorem bump_contDiff (j : Fin 2) : ContDiff ℝ ∞ (bump j) :=
  template_contDiff.comp (contDiff_id.sub contDiff_const)

theorem bump_nonneg (j : Fin 2) (y : ℝ) : 0 ≤ bump j y :=
  LocalizedMomentRepair.bump_nonneg _ _ _

theorem bump_le_one (j : Fin 2) (y : ℝ) : bump j y ≤ 1 :=
  LocalizedMomentRepair.bump_le_one _ _ _

theorem bump_support (j : Fin 2) :
    support (bump j) ⊆ Icc (2 * (j.val : ℝ) - 3 / 20) (2 * (j.val : ℝ) + 3 / 20) := by
  intro y hy
  have h := template_support hy
  change (-3 : ℝ) / 20 ≤ y - 2 * (j.val : ℝ) ∧ y - 2 * (j.val : ℝ) ≤ 3 / 20 at h
  constructor <;> linarith [h.1, h.2]

theorem bump_hasCompactSupport (j : Fin 2) : HasCompactSupport (bump j) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support j)

theorem bumps_disjoint (y : ℝ) : bump 0 y * bump 1 y = 0 := by
  by_cases h0 : bump 0 y = 0
  · simp [h0]
  by_cases h1 : bump 1 y = 0
  · simp [h1]
  have hs0 := bump_support 0 h0
  have hs1 := bump_support 1 h1
  norm_num at hs0 hs1
  linarith [hs0.2, hs1.1]

def moment (s : ℝ) : ℝ := ∫ y, Real.exp (s * y) * template y

theorem weighted_bump_integrable (s : ℝ) (j : Fin 2) :
    Integrable (fun y => Real.exp (s * y) * bump j y) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (bump_contDiff j).continuous).integrable_of_hasCompactSupport
      (bump_hasCompactSupport j).mul_left

theorem weighted_bump_sq_integrable (s : ℝ) (j : Fin 2) :
    Integrable (fun y => Real.exp (s * y) * (bump j y) ^ 2) := by
  have hc : HasCompactSupport (fun y => (bump j y) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (bump_hasCompactSupport j).mul_right (f' := bump j)
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((bump_contDiff j).continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left

theorem moment_pos (s : ℝ) : 0 < moment s := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul template_contDiff.continuous)
    template_hasCompactSupport.mul_left
  · intro y
    exact mul_nonneg (Real.exp_pos _).le (LocalizedMomentRepair.bump_nonneg _ _ _)
  · exact (show Real.exp (s * 0) * template 0 ≠ 0 by simp [template_at_zero])

/-- Translation multiplies an exponential bump moment by its exact exponential factor. -/
theorem bump_moment (s : ℝ) (j : Fin 2) :
    (∫ y, Real.exp (s * y) * bump j y) =
      Real.exp (s * (2 * (j.val : ℝ))) * moment s := by
  rw [← integral_add_right_eq_self (fun y => Real.exp (s * y) * bump j y)
    (2 * (j.val : ℝ))]
  have hf : (fun y => Real.exp (s * (y + 2 * (j.val : ℝ))) * bump j (y + 2 * (j.val : ℝ))) =
      (fun y => Real.exp (s * (2 * (j.val : ℝ))) * (Real.exp (s * y) * template y)) := by
    funext y
    simp only [bump, add_sub_cancel_right, mul_add, Real.exp_add]
    ring
  rw [hf, integral_const_mul]
  rfl

def angularSlope (lam : ℝ) : ℝ := 1 - lam
def pressureSlope (lam : ℝ) : ℝ := -1 - 2 * lam

/-- The actual derivative matrix of the two integral changes at zero coefficients. -/
def linearMatrix (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![moment (angularSlope lam), Real.exp (2 * angularSlope lam) * moment (angularSlope lam);
      2 * moment (pressureSlope lam),
        2 * (Real.exp (2 * pressureSlope lam) * moment (pressureSlope lam))]

theorem linearMatrix_det (lam : ℝ) :
    (linearMatrix lam).det = 2 * moment (angularSlope lam) * moment (pressureSlope lam) *
      (Real.exp (2 * pressureSlope lam) - Real.exp (2 * angularSlope lam)) := by
  simp [linearMatrix, Matrix.det_fin_two]
  ring

theorem linearMatrix_det_ne_zero (lam : ℝ) (hlam : 0 < lam) :
    (linearMatrix lam).det ≠ 0 := by
  rw [linearMatrix_det]
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (moment_pos _).ne') (moment_pos _).ne'
  · apply ne_of_lt
    apply sub_neg.mpr
    apply Real.exp_lt_exp.mpr
    unfold angularSlope pressureSlope
    linarith

/-- The integral derivative is an actual continuous linear equivalence. -/
def linearEquiv (lam : ℝ) (hlam : 0 < lam) : Coeff ≃L[ℝ] Coeff :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := (linearMatrix lam).mulVec
      invFun := (linearMatrix lam)⁻¹.mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c
      left_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero lam hlam)), Matrix.one_mulVec]
      right_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero lam hlam)), Matrix.one_mulVec] }

def relative (c : Coeff) (y : ℝ) : ℝ := c 0 * bump 0 y + c 1 * bump 1 y

theorem relative_contDiff (c : Coeff) : ContDiff ℝ ∞ (relative c) :=
  (contDiff_const.mul (bump_contDiff 0)).add (contDiff_const.mul (bump_contDiff 1))

theorem relative_support (c : Coeff) : support (relative c) ⊆ Icc (-3 / 20 : ℝ) (43 / 20) := by
  intro y hy
  by_cases h0 : bump 0 y = 0
  · have h1 : bump 1 y ≠ 0 := by intro h1; exact hy (by simp [relative, h0, h1])
    have hs := bump_support 1 h1
    norm_num at hs
    constructor <;> linarith [hs.1, hs.2]
  · have hs := bump_support 0 h0
    norm_num at hs
    constructor <;> linarith [hs.1, hs.2]

theorem relative_hasCompactSupport (c : Coeff) : HasCompactSupport (relative c) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (relative_support c)

def quadraticMoment (lam : ℝ) (j : Fin 2) : ℝ :=
  ∫ y, Real.exp (pressureSlope lam * y) * (bump j y) ^ 2

def quadraticBilin (lam : ℝ) : Coeff →ₗ[ℝ] Coeff →ₗ[ℝ] Coeff where
  toFun c :=
    { toFun := fun d => ![0, quadraticMoment lam 0 * c 0 * d 0 + quadraticMoment lam 1 * c 1 * d 1]
      map_add' := fun d e => by
        ext i
        fin_cases i <;> simp [Pi.add_apply]
        ring
      map_smul' := fun r d => by
        ext i
        fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
        ring }
  map_add' c d := by
    ext e i
    fin_cases i <;> simp [Pi.add_apply]
    ring
  map_smul' r c := by
    ext e i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    ring

def quadraticCLM (lam : ℝ) : Coeff →L[ℝ] Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
      (quadraticBilin lam))

theorem linearEquiv_apply (lam : ℝ) (hlam : 0 < lam) (c : Coeff) :
    linearEquiv lam hlam c = (linearMatrix lam).mulVec c := rfl

theorem quadraticCLM_apply (lam : ℝ) (c d : Coeff) :
    quadraticCLM lam c d =
      ![0, quadraticMoment lam 0 * c 0 * d 0 + quadraticMoment lam 1 * c 1 * d 1] := rfl

theorem weighted_relative_integrable (s : ℝ) (c : Coeff) :
    Integrable (fun y => Real.exp (s * y) * relative c y) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (relative_contDiff c).continuous).integrable_of_hasCompactSupport
      (relative_hasCompactSupport c).mul_left

theorem weighted_relative_sq_integrable (s : ℝ) (c : Coeff) :
    Integrable (fun y => Real.exp (s * y) * (relative c y) ^ 2) := by
  have hc : HasCompactSupport (fun y => (relative c y) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (relative_hasCompactSupport c).mul_right (f' := relative c)
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((relative_contDiff c).continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left

theorem relative_moment (s : ℝ) (c : Coeff) :
    (∫ y, Real.exp (s * y) * relative c y) =
      moment s * c 0 + Real.exp (2 * s) * moment s * c 1 := by
  have hf : (fun y => Real.exp (s * y) * relative c y) =
      (fun y => c 0 * (Real.exp (s * y) * bump 0 y) +
        c 1 * (Real.exp (s * y) * bump 1 y)) := by
    funext y
    dsimp [relative]
    ring
  rw [hf, integral_add ((weighted_bump_integrable s 0).const_mul _)
    ((weighted_bump_integrable s 1).const_mul _), integral_const_mul, integral_const_mul,
    bump_moment, bump_moment]
  norm_num
  rw [mul_comm s 2]
  ring

theorem relative_square (c : Coeff) (y : ℝ) :
    (relative c y) ^ 2 = (c 0) ^ 2 * (bump 0 y) ^ 2 + (c 1) ^ 2 * (bump 1 y) ^ 2 := by
  calc
    _ = (c 0) ^ 2 * (bump 0 y) ^ 2 + (c 1) ^ 2 * (bump 1 y) ^ 2 +
        2 * c 0 * c 1 * (bump 0 y * bump 1 y) := by dsimp [relative]; ring
    _ = _ := by rw [bumps_disjoint]; ring

theorem relative_square_moment (lam : ℝ) (c : Coeff) :
    (∫ y, Real.exp (pressureSlope lam * y) * (relative c y) ^ 2) =
      quadraticMoment lam 0 * (c 0) ^ 2 + quadraticMoment lam 1 * (c 1) ^ 2 := by
  have hf : (fun y => Real.exp (pressureSlope lam * y) * (relative c y) ^ 2) =
      (fun y => (c 0) ^ 2 * (Real.exp (pressureSlope lam * y) * (bump 0 y) ^ 2) +
        (c 1) ^ 2 * (Real.exp (pressureSlope lam * y) * (bump 1 y) ^ 2)) := by
    funext y
    rw [relative_square]
    ring
  rw [hf, integral_add ((weighted_bump_sq_integrable _ 0).const_mul _)
    ((weighted_bump_sq_integrable _ 1).const_mul _), integral_const_mul, integral_const_mul]
  dsimp [quadraticMoment]
  ring


theorem pressure_change_moment (lam : ℝ) (c : Coeff) :
    (∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)) =
      2 * (moment (pressureSlope lam) * c 0 +
        Real.exp (2 * pressureSlope lam) * moment (pressureSlope lam) * c 1) +
      quadraticMoment lam 0 * (c 0) ^ 2 + quadraticMoment lam 1 * (c 1) ^ 2 := by
  have hf : (fun y => Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)) =
      (fun y => 2 * (Real.exp (pressureSlope lam * y) * relative c y) +
        Real.exp (pressureSlope lam * y) * (relative c y) ^ 2) := by funext y; ring
  rw [hf, integral_add ((weighted_relative_integrable _ c).const_mul 2)
    (weighted_relative_sq_integrable _ c), integral_const_mul, relative_moment, relative_square_moment]
  ring


def debt (δ : ℝ) : Coeff := ![δ, 0]

theorem debt_contDiff : ContDiff ℝ ∞ debt := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

theorem debt_norm_le (δ : ℝ) : ‖debt δ‖ ≤ |δ| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg δ)).mpr
  intro i
  fin_cases i <;> simp [debt]


theorem relative_deriv (c : Coeff) (y : ℝ) :
    deriv (relative c) y = c 0 * deriv (bump 0) y + c 1 * deriv (bump 1) y := by
  have h0 := (bump_contDiff 0).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 := (bump_contDiff 1).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  unfold relative
  rw [deriv_fun_add (h0.differentiableAt.const_mul _) (h1.differentiableAt.const_mul _),
    deriv_const_mul _ h0.differentiableAt, deriv_const_mul _ h1.differentiableAt]

/-- The fixed finite family controls both the relative perturbation and its first derivative. -/
theorem relative_first_jet_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (c : Coeff) (y : ℝ),
      |relative c y| ≤ D * ‖c‖ ∧ |deriv (relative c) y| ≤ D * ‖c‖ := by
  obtain ⟨D0, hD0, hb0⟩ := LocalizedMomentRepair.smooth_compact_derivative_bound
    (bump 0) (bump_contDiff 0) (bump_hasCompactSupport 0) 1
  obtain ⟨D1, hD1, hb1⟩ := LocalizedMomentRepair.smooth_compact_derivative_bound
    (bump 1) (bump_contDiff 1) (bump_hasCompactSupport 1) 1
  simp only [iteratedDeriv_one] at hb0 hb1
  refine ⟨2 + D0 + D1, by linarith, ?_⟩
  intro c y
  have hc0 : |c 0| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 0
  have hc1 : |c 1| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 1
  have ha0 : |bump 0 y| ≤ 1 := by rw [abs_of_nonneg (bump_nonneg 0 y)]; exact bump_le_one 0 y
  have ha1 : |bump 1 y| ≤ 1 := by rw [abs_of_nonneg (bump_nonneg 1 y)]; exact bump_le_one 1 y
  constructor
  · calc
      |relative c y| ≤ |c 0| * |bump 0 y| + |c 1| * |bump 1 y| := by
        simpa only [relative, abs_mul] using abs_add_le (c 0 * bump 0 y) (c 1 * bump 1 y)
      _ ≤ ‖c‖ * 1 + ‖c‖ * 1 := add_le_add
        (mul_le_mul hc0 ha0 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hc1 ha1 (abs_nonneg _) (norm_nonneg _))
      _ ≤ (2 + D0 + D1) * ‖c‖ := by nlinarith [norm_nonneg c]
  · rw [relative_deriv]
    calc
      _ ≤ |c 0| * |deriv (bump 0) y| + |c 1| * |deriv (bump 1) y| := by
        simpa only [abs_mul] using abs_add_le (c 0 * deriv (bump 0) y) (c 1 * deriv (bump 1) y)
      _ ≤ ‖c‖ * D0 + ‖c‖ * D1 := add_le_add
        (mul_le_mul hc0 (hb0 y) (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hc1 (hb1 y) (abs_nonneg _) (norm_nonneg _))
      _ ≤ (2 + D0 + D1) * ‖c‖ := by nlinarith [norm_nonneg c]

theorem positive_and_slope_of_small (lam : ℝ) (hlam : 0 < lam) (c : Coeff) (y : ℝ)
    (h0 : |relative c y| ≤ 1 / 2) (h1 : |deriv (relative c) y| ≤ lam / 4) :
    0 < 1 + relative c y ∧ -lam + deriv (relative c) y / (1 + relative c y) ≤ -lam / 2 := by
  have hlo : -(1 / 2 : ℝ) ≤ relative c y := (abs_le.mp h0).1
  have hden : 0 < 1 + relative c y := by linarith
  refine ⟨hden, ?_⟩
  have hd : deriv (relative c) y ≤ lam / 4 := (le_abs_self _).trans h1
  have hratio : deriv (relative c) y / (1 + relative c y) ≤ lam / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

/-- A constructed branch, with exact normalized integrals and quantitative first-jet control. -/
structure ResetBranch (lam : ℝ) where
  coefficients : ℝ → Coeff
  radius : ℝ
  bound : ℝ
  radius_pos : 0 < radius
  bound_pos : 0 < bound
  smooth : ContDiffOn ℝ ∞ coefficients (Ioo (-radius) radius)
  at_zero : coefficients 0 = 0
  angular : ∀ δ ∈ Ioo (-radius) radius,
    (∫ y, Real.exp (angularSlope lam * y) * relative (coefficients δ) y) = δ
  pressure : ∀ δ ∈ Ioo (-radius) radius,
    (∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative (coefficients δ) y) ^ 2 - 1)) = 0
  coefficient_bound : ∀ δ ∈ Ioo (-radius) radius, ‖coefficients δ‖ ≤ bound * |δ|
  first_jet_bound : ∀ δ ∈ Ioo (-radius) radius, ∀ y,
    |relative (coefficients δ) y| ≤ bound * |δ| ∧
    |deriv (relative (coefficients δ)) y| ≤ bound * |δ|
  small_jets : ∀ δ ∈ Ioo (-radius) radius, ∀ y,
    |relative (coefficients δ) y| ≤ 1 / 2 ∧
    |deriv (relative (coefficients δ)) y| ≤ lam / 4



/-! ## Actual modified angular fields -/

def baseE (lam e0 y : ℝ) : ℝ := e0 * Real.exp ((-1 / 2 - lam) * y)

/-- The first bump is centered at `y0`, and the second at `y0 + 2`. -/
def modifiedE (lam e0 y0 : ℝ) (c : Coeff) (y : ℝ) : ℝ :=
  baseE lam e0 y * (1 + relative c (y - y0))

def radiusX (X0 y : ℝ) : ℝ := X0 * Real.exp y

def baseH (lam e0 X0 y : ℝ) : ℝ := Real.sqrt (2 * radiusX X0 y) * baseE lam e0 y

def modifiedH (lam e0 X0 y0 : ℝ) (c : Coeff) (y : ℝ) : ℝ :=
  Real.sqrt (2 * radiusX X0 y) * modifiedE lam e0 y0 c y

def angularScale (lam e0 X0 y0 : ℝ) : ℝ :=
  X0 * Real.sqrt (2 * X0) * e0 * Real.exp (angularSlope lam * y0)

def logSlope (E : ℝ → ℝ) (y : ℝ) : ℝ := 1 / 2 + deriv E y / E y

theorem baseE_contDiff (lam e0 : ℝ) : ContDiff ℝ ∞ (baseE lam e0) :=
  contDiff_const.mul (contDiff_const.mul contDiff_id).exp

theorem modifiedE_contDiff (lam e0 y0 : ℝ) (c : Coeff) :
    ContDiff ℝ ∞ (modifiedE lam e0 y0 c) :=
  (baseE_contDiff lam e0).mul
    (contDiff_const.add ((relative_contDiff c).comp (contDiff_id.sub contDiff_const)))

theorem baseE_pos (lam e0 y : ℝ) (he0 : 0 < e0) : 0 < baseE lam e0 y :=
  mul_pos he0 (Real.exp_pos _)

theorem modifiedE_sub_support (lam e0 y0 : ℝ) (c : Coeff) :
    support (modifiedE lam e0 y0 c - baseE lam e0) ⊆
      Icc (y0 - 3 / 20) (y0 + 43 / 20) := by
  intro y hy
  have hn : relative c (y - y0) ≠ 0 := by
    intro hz
    exact hy (by simp [modifiedE, hz])
  have hs := relative_support c hn
  constructor <;> linarith [hs.1, hs.2]


/-- Choosing `y0 = T - 3` places the whole edit strictly inside `(T - 4, T)`. -/
theorem modifiedE_sub_tsupport (lam e0 y0 : ℝ) (c : Coeff) :
    tsupport (modifiedE lam e0 y0 c - baseE lam e0) ⊆ Ioo (y0 - 1) (y0 + 3) := by
  apply (closure_minimal (modifiedE_sub_support lam e0 y0 c) isClosed_Icc).trans
  intro y hy
  constructor <;> linarith [hy.1, hy.2]

theorem modifiedE_unchanged (lam e0 y0 : ℝ) (c : Coeff) {y : ℝ}
    (hy : y ∉ Ioo (y0 - 1) (y0 + 3)) : modifiedE lam e0 y0 c y = baseE lam e0 y := by
  by_contra hn
  apply hy
  apply modifiedE_sub_tsupport lam e0 y0 c
  exact subset_closure (show (modifiedE lam e0 y0 c - baseE lam e0) y ≠ 0 from sub_ne_zero.mpr hn)

theorem baseE_hasDerivAt (lam e0 y : ℝ) :
    HasDerivAt (baseE lam e0) (baseE lam e0 y * (-1 / 2 - lam)) y := by
  convert! (((hasDerivAt_id y).const_mul (-1 / 2 - lam)).exp).const_mul e0 using 1
  simp [baseE]
  ring

theorem modifiedE_hasDerivAt (lam e0 y0 : ℝ) (c : Coeff) (y : ℝ) :
    HasDerivAt (modifiedE lam e0 y0 c)
      (baseE lam e0 y * (-1 / 2 - lam) * (1 + relative c (y - y0)) +
        baseE lam e0 y * deriv (relative c) (y - y0)) y := by
  have hr := (((relative_contDiff c).differentiable (by simp)).differentiableAt.hasDerivAt).comp y
    ((hasDerivAt_id y).sub_const y0)
  convert! (baseE_hasDerivAt lam e0 y).mul (hr.const_add 1) using 1
  simp

theorem modifiedE_logSlope (lam e0 y0 : ℝ) (c : Coeff) (y : ℝ) (he0 : e0 ≠ 0)
    (hpos : 1 + relative c (y - y0) ≠ 0) :
    logSlope (modifiedE lam e0 y0 c) y =
      -lam + deriv (relative c) (y - y0) / (1 + relative c (y - y0)) := by
  have hb : baseE lam e0 y ≠ 0 := mul_ne_zero he0 (Real.exp_ne_zero _)
  unfold logSlope
  rw [(modifiedE_hasDerivAt lam e0 y0 c y).deriv]
  change 1 / 2 +
    (baseE lam e0 y * (-1 / 2 - lam) * (1 + relative c (y - y0)) +
      baseE lam e0 y * deriv (relative c) (y - y0)) /
    (baseE lam e0 y * (1 + relative c (y - y0))) = _
  field_simp ; ring

theorem weighted_translate_integral (s y0 : ℝ) (f : ℝ → ℝ) :
    (∫ y, Real.exp (s * y) * f (y - y0)) =
      Real.exp (s * y0) * ∫ y, Real.exp (s * y) * f y := by
  rw [← integral_add_right_eq_self (fun y => Real.exp (s * y) * f (y - y0)) y0]
  have hf : (fun y => Real.exp (s * (y + y0)) * f (y + y0 - y0)) =
      (fun y => Real.exp (s * y0) * (Real.exp (s * y) * f y)) := by
    funext y
    simp only [add_sub_cancel_right, mul_add, Real.exp_add]
    ring
  rw [hf, integral_const_mul]

theorem baseE_square (lam e0 y : ℝ) :
    (baseE lam e0 y) ^ 2 = e0 ^ 2 * Real.exp (pressureSlope lam * y) := by
  unfold baseE
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  unfold pressureSlope
  ring

theorem pressure_integral_formula (lam e0 y0 : ℝ) (c : Coeff) :
    (∫ y, (modifiedE lam e0 y0 c y) ^ 2 - (baseE lam e0 y) ^ 2) =
      e0 ^ 2 * Real.exp (pressureSlope lam * y0) *
        ∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1) := by
  have hf : (fun y => (modifiedE lam e0 y0 c y) ^ 2 - (baseE lam e0 y) ^ 2) =
      (fun y => e0 ^ 2 * (Real.exp (pressureSlope lam * y) * ((1 + relative c (y - y0)) ^ 2 - 1))) := by
    funext y
    calc
      _ = (baseE lam e0 y) ^ 2 * ((1 + relative c (y - y0)) ^ 2 - 1) := by
        unfold modifiedE
        ring
      _ = _ := by rw [baseE_square]; ring
  rw [hf, integral_const_mul,
    weighted_translate_integral (pressureSlope lam) y0 (fun y => (1 + relative c y) ^ 2 - 1)]
  ring

theorem sqrt_exp_half (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem angular_weight_formula (lam e0 X0 y : ℝ) (hX : 0 ≤ X0) :
    radiusX X0 y * baseH lam e0 X0 y =
      X0 * Real.sqrt (2 * X0) * e0 * Real.exp (angularSlope lam * y) := by
  have hs : Real.sqrt (2 * radiusX X0 y) = Real.sqrt (2 * X0) * Real.exp (y / 2) := by
    unfold radiusX
    rw [← mul_assoc, Real.sqrt_mul (by positivity), sqrt_exp_half]
  unfold baseH
  rw [hs]
  unfold radiusX baseE
  calc
    _ = X0 * Real.sqrt (2 * X0) * e0 *
        (Real.exp y * Real.exp (y / 2) * Real.exp ((-1 / 2 - lam) * y)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      unfold angularSlope
      ring

theorem angular_integral_formula (lam e0 X0 y0 : ℝ) (c : Coeff) (hX : 0 ≤ X0) :
    (∫ y, radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) =
      angularScale lam e0 X0 y0 * ∫ y, Real.exp (angularSlope lam * y) * relative c y := by
  have hf : (fun y => radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) =
      (fun y => (X0 * Real.sqrt (2 * X0) * e0) *
        (Real.exp (angularSlope lam * y) * relative c (y - y0))) := by
    funext y
    calc
      _ = (radiusX X0 y * baseH lam e0 X0 y) * relative c (y - y0) := by
        unfold modifiedH modifiedE baseH
        ring
      _ = _ := by rw [angular_weight_formula lam e0 X0 y hX]; ring
  rw [hf, integral_const_mul, weighted_translate_integral]
  unfold angularScale
  ring

theorem angularScale_pos (lam e0 X0 y0 : ℝ) (he0 : 0 < e0) (hX : 0 < X0) :
    0 < angularScale lam e0 X0 y0 := by
  unfold angularScale
  exact mul_pos (mul_pos (mul_pos hX (Real.sqrt_pos.mpr (by positivity))) he0) (Real.exp_pos _)




namespace ResetBranch

variable {lam : ℝ} (B : ResetBranch lam)

theorem pressure_neutral (e0 y0 δ : ℝ) (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    (∫ y, (modifiedE lam e0 y0 (B.coefficients δ) y) ^ 2 - (baseE lam e0 y) ^ 2) = 0 := by
  rw [pressure_integral_formula, B.pressure δ hδ, mul_zero]

theorem angular_change (e0 X0 y0 δ : ℝ) (hX : 0 ≤ X0)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    (∫ y, radiusX X0 y *
      (modifiedH lam e0 X0 y0 (B.coefficients δ) y - baseH lam e0 X0 y)) =
      angularScale lam e0 X0 y0 * δ := by
  rw [angular_integral_formula lam e0 X0 y0 (B.coefficients δ) hX, B.angular δ hδ]

theorem positive (hlam : 0 < lam) (e0 y0 δ y : ℝ) (he0 : 0 < e0)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    0 < modifiedE lam e0 y0 (B.coefficients δ) y := by
  apply mul_pos (baseE_pos lam e0 y he0)
  exact (positive_and_slope_of_small lam hlam (B.coefficients δ) (y - y0)
    (B.small_jets δ hδ (y - y0)).1 (B.small_jets δ hδ (y - y0)).2).1

theorem logSlope_le (hlam : 0 < lam) (e0 y0 δ y : ℝ) (he0 : 0 < e0)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    logSlope (modifiedE lam e0 y0 (B.coefficients δ)) y ≤ -lam / 2 := by
  have hp := positive_and_slope_of_small lam hlam (B.coefficients δ) (y - y0)
    (B.small_jets δ hδ (y - y0)).1 (B.small_jets δ hδ (y - y0)).2
  rw [modifiedE_logSlope lam e0 y0 (B.coefficients δ) y he0.ne' hp.1.ne']
  exact hp.2


end ResetBranch

/-! ## Finite-interval moments, including an arbitrary earlier prefix -/




theorem outside_window {a b y0 y : ℝ} (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b)
    (hy : y ∉ Icc a b) : y ∉ Ioo (y0 - 1) (y0 + 3) := by
  intro h
  exact hy ⟨ha.trans h.1.le, h.2.le.trans hb⟩


theorem pressure_interval_change (lam e0 y0 a b : ℝ) (c : Coeff)
    (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b) :
    (∫ y in Icc a b, (modifiedE lam e0 y0 c y) ^ 2) -
      (∫ y in Icc a b, (baseE lam e0 y) ^ 2) =
      e0 ^ 2 * Real.exp (pressureSlope lam * y0) *
        ∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1) := by
  have hm : IntegrableOn (fun y => (modifiedE lam e0 y0 c y) ^ 2) (Icc a b) :=
    ((modifiedE_contDiff lam e0 y0 c).continuous.pow 2).continuousOn.integrableOn_Icc
  have he : IntegrableOn (fun y => (baseE lam e0 y) ^ 2) (Icc a b) :=
    ((baseE_contDiff lam e0).continuous.pow 2).continuousOn.integrableOn_Icc
  rw [← integral_sub hm he, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact pressure_integral_formula lam e0 y0 c
  · intro y hy
    rw [modifiedE_unchanged lam e0 y0 c (outside_window ha hb hy), sub_self]

theorem ResetBranch.pressure_interval_neutral {lam : ℝ} (B : ResetBranch lam)
    (e0 y0 a b δ : ℝ) (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    (∫ y in Icc a b, (modifiedE lam e0 y0 (B.coefficients δ) y) ^ 2) =
      ∫ y in Icc a b, (baseE lam e0 y) ^ 2 := by
  apply sub_eq_zero.mp
  rw [pressure_interval_change lam e0 y0 a b (B.coefficients δ) ha hb, B.pressure δ hδ, mul_zero]



/-! ## Smooth dependence on the angular parameter -/

theorem relative_joint_contDiff :
    ContDiff ℝ ∞ (fun z : Coeff × ℝ => relative z.1 z.2) := by
  have h0 : ContDiff ℝ ∞ (fun z : Coeff × ℝ => z.1 0) :=
    contDiff_pi.mp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Coeff × ℝ → Coeff)) 0
  have h1 : ContDiff ℝ ∞ (fun z : Coeff × ℝ => z.1 1) :=
    contDiff_pi.mp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Coeff × ℝ → Coeff)) 1
  exact (h0.mul ((bump_contDiff 0).comp contDiff_snd)).add
    (h1.mul ((bump_contDiff 1).comp contDiff_snd))


end NavierStokes.AngularMomentReset
