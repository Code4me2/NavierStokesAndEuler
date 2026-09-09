import NavierStokes.UniformAngularReset
import NavierStokes.HeatTailEdit
import Mathlib.Tactic.FinCases

/-!
# Three exact terminal compensation moments

Three constructed, separated additive bumps in a positive interval repair the
pressure, energy, and angular moments. Factoring out the positive shaped-wait
amplitude leaves one fixed quadratic map, so its smooth inverse and estimates
are uniform in the transverse parameter.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace NavierStokes.TerminalCompensation

abbrev Coeff := Fin 3 → ℝ

/-- An arbitrary reserved interval in the normalized positive radial coordinate. -/
structure Patch where
  left : ℝ
  right : ℝ
  left_pos : 0 < left
  ordered : left < right

noncomputable def lower (P : Patch) (j : Fin 3) : ℝ :=
  P.left + (2 * (j.val : ℝ) + 1) * (P.right - P.left) / 7

noncomputable def upper (P : Patch) (j : Fin 3) : ℝ :=
  P.left + (2 * (j.val : ℝ) + 2) * (P.right - P.left) / 7

theorem lower_gt_left (P : Patch) (j : Fin 3) : P.left < lower P j := by
  fin_cases j <;> simp only [lower] <;>
    norm_num <;> linarith [P.ordered]

theorem lower_lt_upper (P : Patch) (j : Fin 3) : lower P j < upper P j := by
  dsimp [lower, upper]
  nlinarith [P.ordered]

theorem upper_lt_right (P : Patch) (j : Fin 3) : upper P j < P.right := by
  fin_cases j <;> simp only [upper] <;>
    norm_num <;> linarith [P.ordered]

theorem intervals_separated (P : Patch) (i j : Fin 3) (hij : i < j) :
    upper P i ≤ lower P j := by
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num <;>
    dsimp [upper, lower] <;> norm_num <;> linarith [P.ordered]

noncomputable def bump (P : Patch) (j : Fin 3) : ℝ → ℝ :=
  LocalizedMomentRepair.bump (lower P j) (upper P j)

theorem bump_contDiff (P : Patch) (j : Fin 3) : ContDiff ℝ ∞ (bump P j) :=
  LocalizedMomentRepair.bump_contDiff _ _

theorem bump_nonneg (P : Patch) (j : Fin 3) (x : ℝ) : 0 ≤ bump P j x :=
  LocalizedMomentRepair.bump_nonneg _ _ _

theorem bump_le_one (P : Patch) (j : Fin 3) (x : ℝ) : bump P j x ≤ 1 :=
  LocalizedMomentRepair.bump_le_one _ _ _

theorem bump_tsupport (P : Patch) (j : Fin 3) :
    tsupport (bump P j) ⊆ Ioo (lower P j) (upper P j) :=
  LocalizedMomentRepair.bump_tsupport_subset_open _ _ (lower_lt_upper P j)

theorem bump_support_patch (P : Patch) (j : Fin 3) :
    support (bump P j) ⊆ Icc P.left P.right := by
  intro x hx
  have ht := bump_tsupport P j (subset_tsupport _ hx)
  exact ⟨(lower_gt_left P j).le.trans ht.1.le,
    ht.2.le.trans (upper_lt_right P j).le⟩

theorem bumps_disjoint (P : Patch) (i j : Fin 3) (hij : i ≠ j) (x : ℝ) :
    bump P i x * bump P j x = 0 := by
  by_cases hi : bump P i x = 0
  · simp [hi]
  by_cases hj : bump P j x = 0
  · simp [hj]
  have hix := bump_tsupport P i (subset_tsupport _ hi)
  have hjx := bump_tsupport P j (subset_tsupport _ hj)
  rcases lt_or_gt_of_ne hij with h | h
  · have hs := intervals_separated P i j h
    linarith [hix.2, hjx.1]
  · have hs := intervals_separated P j i h
    linarith [hjx.2, hix.1]

noncomputable def correction (P : Patch) (c : Coeff) (x : ℝ) : ℝ :=
  ∑ j, c j * bump P j x

theorem correction_contDiff (P : Patch) (c : Coeff) :
    ContDiff ℝ ∞ (correction P c) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (bump_contDiff P j))

theorem correction_support (P : Patch) (c : Coeff) :
    support (correction P c) ⊆ Icc P.left P.right := by
  intro x hx
  by_contra hnot
  apply hx
  apply Finset.sum_eq_zero
  intro j _
  have hb : bump P j x = 0 := by
    by_contra hn
    exact hnot (bump_support_patch P j hn)
  simp [hb]

theorem correction_tsupport (P : Patch) (c : Coeff) :
    tsupport (correction P c) ⊆ Ioo P.left P.right := by
  have hs : support (correction P c) ⊆ LocalizedMomentRepair.repairRegion (lower P) (upper P) := by
    intro x hx
    by_contra hnot
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    have hb : bump P j x = 0 := by
      by_contra hn
      exact hnot (mem_iUnion.mpr ⟨j,
        LocalizedMomentRepair.bump_support_subset _ _ (lower_lt_upper P j) hn⟩)
    simp [hb]
  have ht := closure_minimal hs
    (LocalizedMomentRepair.repairRegion_isCompact (lower P) (upper P)).isClosed
  intro x hx
  have hm := LocalizedMomentRepair.repairRegion_subset_open (lower P) (upper P)
    (lower_lt_upper P) (ht hx)
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact ⟨(lower_gt_left P j).trans hj.1, hj.2.trans (upper_lt_right P j)⟩

theorem correction_hasCompactSupport (P : Patch) (c : Coeff) :
    HasCompactSupport (correction P c) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (correction_support P c)

theorem weighted_integrable (P : Patch) (s : ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (hs : support g ⊆ Icc P.left P.right) :
    Integrable (fun x => x ^ s * g x) := by
  have hsupport : support (fun x => x ^ s * g x) ⊆ Icc P.left P.right := by
    intro x hx
    apply hs
    intro hz
    exact hx (by simp [hz])
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul _ hg.continuousOn
  apply continuousOn_id.rpow_const
  intro x hx
  exact Or.inl (ne_of_gt (P.left_pos.trans_le hx.1))

theorem weighted_bump_integrable (P : Patch) (s : ℝ) (j : Fin 3) :
    Integrable (fun x => x ^ s * bump P j x) :=
  weighted_integrable P s _ (bump_contDiff P j).continuous (bump_support_patch P j)

theorem weighted_bump_sq_integrable (P : Patch) (s : ℝ) (j : Fin 3) :
    Integrable (fun x => x ^ s * (bump P j x) ^ 2) := by
  apply weighted_integrable P s _ ((bump_contDiff P j).continuous.pow 2)
  intro x hx
  apply bump_support_patch P j
  intro hz
  exact hx (by simp [hz])

theorem correction_square (P : Patch) (c : Coeff) (x : ℝ) :
    (correction P c x) ^ 2 = ∑ j, (c j) ^ 2 * (bump P j x) ^ 2 := by
  have h01 := bumps_disjoint P 0 1 (by decide) x
  have h02 := bumps_disjoint P 0 2 (by decide) x
  have h12 := bumps_disjoint P 1 2 (by decide) x
  simp only [correction, Fin.sum_univ_three]
  calc
    _ = c 0 ^ 2 * bump P 0 x ^ 2 + c 1 ^ 2 * bump P 1 x ^ 2 +
        c 2 ^ 2 * bump P 2 x ^ 2 +
        2 * c 0 * c 1 * (bump P 0 x * bump P 1 x) +
        2 * c 0 * c 2 * (bump P 0 x * bump P 2 x) +
        2 * c 1 * c 2 * (bump P 1 x * bump P 2 x) := by ring
    _ = _ := by rw [h01, h02, h12]; ring

noncomputable def bumpMoment (P : Patch) (s : ℝ) (j : Fin 3) : ℝ :=
  ∫ x, x ^ s * bump P j x

noncomputable def squareMoment (P : Patch) (s : ℝ) (j : Fin 3) : ℝ :=
  ∫ x, x ^ s * (bump P j x) ^ 2

theorem correction_moment (P : Patch) (s : ℝ) (c : Coeff) :
    (∫ x, x ^ s * correction P c x) = ∑ j, c j * bumpMoment P s j := by
  have hf : (fun x => x ^ s * correction P c x) =
      (fun x => ∑ j, c j * (x ^ s * bump P j x)) := by
    funext x
    simp only [correction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, bumpMoment]
  · intro j _
    exact (weighted_bump_integrable P s j).const_mul _

theorem correction_square_moment (P : Patch) (s : ℝ) (c : Coeff) :
    (∫ x, x ^ s * (correction P c x) ^ 2) = ∑ j, (c j) ^ 2 * squareMoment P s j := by
  have hf : (fun x => x ^ s * (correction P c x) ^ 2) =
      (fun x => ∑ j, (c j) ^ 2 * (x ^ s * (bump P j x) ^ 2)) := by
    funext x
    rw [correction_square, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, squareMoment]
  · intro j _
    exact (weighted_bump_sq_integrable P s j).const_mul _

noncomputable def slope (lam : ℝ) : ℝ := -1 / 2 - lam

noncomputable def powers (lam : ℝ) : Coeff := ![-1 + slope lam, slope lam, 1 / 2]

theorem powers_injective (lam : ℝ) (hlam : 0 ≤ lam) : Injective (powers lam) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [powers, slope] at hij <;> norm_num <;> linarith

noncomputable def linearMatrix (P : Patch) (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  LocalizedMomentRepair.matrix (powers lam) (lower P) (upper P)

theorem linearMatrix_entry (P : Patch) (lam : ℝ) (i j : Fin 3) :
    linearMatrix P lam i j = bumpMoment P (powers lam i) j := rfl

/-- The three powers are those of pressure, energy, and angular momentum. -/
theorem linearMatrix_det_ne_zero (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) :
    (linearMatrix P lam).det ≠ 0 :=
  LocalizedMomentRepair.matrix_det_ne_zero (powers lam) (lower P) (upper P)
    (powers_injective lam hlam) (fun j => P.left_pos.trans (lower_gt_left P j))
    (lower_lt_upper P) (intervals_separated P)

noncomputable def linearEquiv (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) :
    Coeff ≃L[ℝ] Coeff :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := (linearMatrix P lam).mulVec
      invFun := (linearMatrix P lam)⁻¹.mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c
      left_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero P lam hlam)), Matrix.one_mulVec]
      right_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero P lam hlam)), Matrix.one_mulVec] }

theorem linearEquiv_apply (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) (c : Coeff) :
    linearEquiv P lam hlam c = (linearMatrix P lam).mulVec c := rfl

noncomputable def quadraticBilin (P : Patch) : Coeff →ₗ[ℝ] Coeff →ₗ[ℝ] Coeff where
  toFun c :=
    { toFun := fun d =>
        ![(1 / 2) * ∑ j, squareMoment P (-1) j * c j * d j,
          (1 / 2) * ∑ j, squareMoment P 0 j * c j * d j, 0]
      map_add' := fun d e => by
        ext i
        fin_cases i <;> simp [Fin.sum_univ_three] <;> ring
      map_smul' := fun r d => by
        ext i
        fin_cases i <;> simp [smul_eq_mul, Fin.sum_univ_three] <;> ring }
  map_add' c d := by
    ext e i
    fin_cases i <;> simp [Fin.sum_univ_three] <;> ring
  map_smul' r c := by
    ext e i
    fin_cases i <;> simp [smul_eq_mul, Fin.sum_univ_three] <;> ring

noncomputable def quadraticCLM (P : Patch) : Coeff →L[ℝ] Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
      (quadraticBilin P))

theorem quadraticCLM_apply (P : Patch) (c d : Coeff) :
    quadraticCLM P c d =
      ![(1 / 2) * ∑ j, squareMoment P (-1) j * c j * d j,
        (1 / 2) * ∑ j, squareMoment P 0 j * c j * d j, 0] := rfl

noncomputable def baseProfile (lam x : ℝ) : ℝ := x ^ slope lam

/-- One half of a squared-profile change, against a power weight. -/
noncomputable def weightedChange (P : Patch) (lam : ℝ) (c : Coeff) (w x : ℝ) : ℝ :=
  x ^ w * ((baseProfile lam x + correction P c x) ^ 2 - (baseProfile lam x) ^ 2) / 2

theorem weightedChange_identity (P : Patch) (lam : ℝ) (c : Coeff) (w x : ℝ) :
    weightedChange P lam c w x =
      x ^ (w + slope lam) * correction P c x + x ^ w * (correction P c x) ^ 2 / 2 := by
  by_cases hc : correction P c x = 0
  · simp [weightedChange, hc]
  have hx : 0 < x := P.left_pos.trans_le (correction_support P c hc).1
  rw [Real.rpow_add hx]
  unfold weightedChange baseProfile
  ring

theorem weighted_correction_integrable (P : Patch) (s : ℝ) (c : Coeff) :
    Integrable (fun x => x ^ s * correction P c x) :=
  weighted_integrable P s _ (correction_contDiff P c).continuous (correction_support P c)

theorem weighted_correction_sq_integrable (P : Patch) (s : ℝ) (c : Coeff) :
    Integrable (fun x => x ^ s * (correction P c x) ^ 2) := by
  apply weighted_integrable P s _ ((correction_contDiff P c).continuous.pow 2)
  intro x hx
  apply correction_support P c
  intro hz
  exact hx (by simp [hz])

theorem weightedChange_integrable (P : Patch) (lam : ℝ) (c : Coeff) (w : ℝ) :
    Integrable (weightedChange P lam c w) := by
  simp only [funext (weightedChange_identity P lam c w)]
  exact (weighted_correction_integrable P (w + slope lam) c).add
    ((weighted_correction_sq_integrable P w c).div_const 2)

theorem weightedChange_integral (P : Patch) (lam : ℝ) (c : Coeff) (w : ℝ) :
    (∫ x, weightedChange P lam c w x) =
      (∑ j, c j * bumpMoment P (w + slope lam) j) +
        (∑ j, (c j) ^ 2 * squareMoment P w j) / 2 := by
  simp only [funext (weightedChange_identity P lam c w)]
  rw [integral_add (weighted_correction_integrable P (w + slope lam) c)
    ((weighted_correction_sq_integrable P w c).div_const 2), integral_div,
    correction_moment, correction_square_moment]

/-- Actual normalized pressure, energy, and angular moment changes. -/
noncomputable def momentMap (P : Patch) (lam : ℝ) (c : Coeff) : Coeff :=
  ![∫ x, weightedChange P lam c (-1) x,
    ∫ x, weightedChange P lam c 0 x,
    ∫ x, x ^ (1 / 2 : ℝ) * correction P c x]

theorem momentMap_identity (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) (c : Coeff) :
    linearEquiv P lam hlam c + quadraticCLM P c c = momentMap P lam c := by
  rw [linearEquiv_apply, quadraticCLM_apply]
  ext i
  fin_cases i <;>
    simp [momentMap, weightedChange_integral, correction_moment, Matrix.mulVec, dotProduct,
      linearMatrix_entry, powers, Fin.sum_univ_three] <;> ring

theorem correction_iteratedDeriv (P : Patch) (c : Coeff) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (correction P c) x = ∑ j, c j * iteratedDeriv k (bump P j) x := by
  change iteratedDeriv k (fun y => ∑ j, c j * bump P j y) x = _
  rw [LocalizedMomentRepair.iteratedDeriv_finite_sum Finset.univ
    (fun j x => c j * bump P j x)
    (fun j => contDiff_const.mul (bump_contDiff P j)) k x]
  apply Finset.sum_congr rfl
  intro j _
  exact iteratedDeriv_const_mul
    (c j) ((bump_contDiff P j).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt

theorem correction_derivative_bound (P : Patch) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Coeff) (x : ℝ),
      |iteratedDeriv k (correction P c) x| ≤ C * ‖c‖ := by
  have hb : ∀ j : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv k (bump P j) x| ≤ C := fun j =>
    LocalizedMomentRepair.smooth_compact_derivative_bound _ (bump_contDiff P j)
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support_patch P j)) k
  choose C hC hbound using hb
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun c x => ?_⟩
  rw [correction_iteratedDeriv]
  calc
    |∑ j, c j * iteratedDeriv k (bump P j) x| ≤
        ∑ j, |c j * iteratedDeriv k (bump P j) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖c‖ * C j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul _ (hbound j x) (abs_nonneg _) (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm c j
    _ = (∑ j, C j) * ‖c‖ := by rw [← Finset.mul_sum, mul_comm]

theorem correction_first_jet_bound (P : Patch) :
    ∃ D : ℝ, 0 < D ∧ ∀ (c : Coeff) (x : ℝ),
      |correction P c x| ≤ D * ‖c‖ ∧ |deriv (correction P c) x| ≤ D * ‖c‖ := by
  obtain ⟨C₀, hC₀, hb₀⟩ := correction_derivative_bound P 0
  obtain ⟨C₁, hC₁, hb₁⟩ := correction_derivative_bound P 1
  refine ⟨C₀ + C₁ + 1, by linarith, fun c x => ⟨?_, ?_⟩⟩
  · exact (hb₀ c x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg c))
  · have ht : |iteratedDeriv 1 (correction P c) x| ≤ (C₀ + C₁ + 1) * ‖c‖ :=
      (hb₁ c x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg c))
    simpa only [iteratedDeriv_one] using ht

theorem baseProfile_positive (lam : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < baseProfile lam x := Real.rpow_pos_of_pos hx _

theorem baseProfile_lower_bound (P : Patch) (lam : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc P.left P.right, m ≤ baseProfile lam x := by
  apply isCompact_Icc.exists_forall_le'
  · apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (P.left_pos.trans_le hx.1))
  · intro x hx
    exact baseProfile_positive lam (P.left_pos.trans_le hx.1)

/-- A single smooth inverse repairs all three actual moments and has uniform
value, derivative, and spatial first-jet bounds. Smallness also preserves positivity. -/
theorem exists_normalized_compensation (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ (g : Coeff → Coeff) (ε C : ℝ), 0 < ε ∧ 0 < C ∧
      ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧ g 0 = 0 ∧
      ∀ d ∈ Metric.ball (0 : Coeff) ε,
        momentMap P lam (g d) = d ∧ ‖g d‖ ≤ C * ‖d‖ ∧ ‖fderiv ℝ g d‖ ≤ C ∧
        ∀ x : ℝ,
          (|correction P (g d) x| ≤ C * ‖d‖ ∧
            |deriv (correction P (g d)) x| ≤ C * ‖d‖) ∧
          (0 < x → 0 < baseProfile lam x + correction P (g d) x) := by
  let B := linearEquiv P lam hlam
  let A := quadraticCLM P
  let β : ℝ := ‖B.symm.toContinuousLinearMap‖ + 1
  let K : ℝ := ‖A‖ + 1
  let r : ℝ := 1 / (4 * β * K)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hinv : ∀ v, ‖B.symm v‖ ≤ β * ‖v‖ := by
    intro v
    exact (B.symm.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by dsimp [β]; linarith) (norm_nonneg v))
  have hA : ‖A‖ ≤ K := by dsimp [K]; linarith
  have hsmall : 4 * β * K * r ≤ 1 := by dsimp [r]; field_simp ; rfl
  obtain ⟨g, hg, hgeq, hglip⟩ := UniformAngularReset.exists_smooth_solver_on_ball
    B A β K r hβ hK.le hr hinv hA hsmall
  obtain ⟨D, hD, hjet⟩ := correction_first_jet_bound P
  obtain ⟨m, hm, hmin⟩ := baseProfile_lower_bound P lam
  let C : ℝ := (1 + D) * (2 * β)
  let ε : ℝ := min (r / (4 * β)) (m / (2 * C))
  have hC : 0 < C := mul_pos (by linarith) (by positivity)
  have hε : 0 < ε := lt_min (div_pos hr (by positivity)) (div_pos hm (by positivity))
  have hsub : Metric.ball (0 : Coeff) ε ⊆ Metric.ball 0 (r / (4 * β)) :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hC₀ : 2 * β ≤ C := by dsimp [C]; nlinarith
  have hC₁ : D * (2 * β) ≤ C := by dsimp [C]; nlinarith
  have hzero : g 0 = 0 := by
    have hz := (hgeq 0 (Metric.mem_ball_self (div_pos hr (by positivity)))).2
    simpa only [norm_zero, mul_zero, norm_le_zero_iff] using hz
  refine ⟨g, ε, C, hε, hC, hg.mono hsub, hzero, ?_⟩
  intro d hd
  have hnorm : ‖g d‖ ≤ (2 * β) * ‖d‖ := (hgeq d (hsub hd)).2
  have hbound : D * ‖g d‖ ≤ C * ‖d‖ :=
    (mul_le_mul_of_nonneg_left hnorm hD.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC₁ (norm_nonneg d))
  have heq := (hgeq d (hsub hd)).1
  change linearEquiv P lam hlam (g d) + quadraticCLM P (g d) (g d) = d at heq
  rw [momentMap_identity] at heq
  refine ⟨heq, hnorm.trans (mul_le_mul_of_nonneg_right hC₀ (norm_nonneg d)), ?_, ?_⟩
  · apply le_trans _ hC₀
    apply norm_fderiv_le_of_lip' ℝ (by positivity : 0 ≤ 2 * β)
    filter_upwards [Metric.isOpen_ball.mem_nhds (hsub hd)] with e he
    exact hglip e he d (hsub hd)
  · intro x
    have hval := (hjet (g d) x).1.trans hbound
    refine ⟨⟨hval, (hjet (g d) x).2.trans hbound⟩, ?_⟩
    intro hx
    by_cases hc : correction P (g d) x = 0
    · simpa only [hc, add_zero] using baseProfile_positive lam hx
    have hbase := hmin x (correction_support P (g d) hc)
    have hd' : ‖d‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hd
    have hsize : C * ‖d‖ < m / 2 := by
      have ht := mul_lt_mul_of_pos_left (hd'.trans_le (min_le_right _ _)) hC
      have hcancel : C * (m / (2 * C)) = m / 2 := by field_simp
      rwa [hcancel] at ht
    have hlow := neg_abs_le (correction P (g d) x)
    linarith

/-- Evaluation of the finite bump combination is an actual bounded linear map. -/
noncomputable def correctionCLM (P : Patch) (x : ℝ) : Coeff →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => correction P c x
      map_add' := fun c d => by
        simp only [correction, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [correction, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
          RingHom.id_apply] }



theorem correction_family_contDiffOn (P : Patch) {U : Set ℝ} {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => correction P (c z.1) z.2) (U ×ˢ univ) := by
  apply ContDiffOn.sum
  intro j _
  exact ((contDiffOn_pi.mp hc j).comp contDiffOn_fst (fun z hz => hz.1)).mul
    ((bump_contDiff P j).comp_contDiffOn contDiffOn_snd)


/-- The physical profile uses the actual additive bumps at scale `R`. -/
noncomputable def physicalProfile (P : Patch) (lam R a : ℝ) (c : Coeff) (X : ℝ) : ℝ :=
  a * (baseProfile lam (X / R) + correction P c (X / R))

noncomputable def cleanProfile (lam R a X : ℝ) : ℝ := a * baseProfile lam (X / R)

noncomputable def physicalMoments (P : Patch) (lam R a : ℝ) (c : Coeff) : Coeff :=
  ![∫ X, ((physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) / X,
    ∫ X, (physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2,
    ∫ X, Real.sqrt (2 * X) * (physicalProfile P lam R a c X - cleanProfile lam R a X)]

theorem integral_rescale (R : ℝ) (hR : 0 < R) (F : ℝ → ℝ) :
    (∫ X, F X) = R * ∫ x, F (R * x) := by
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hR), smul_eq_mul]
  field_simp

theorem pressure_density_rescale (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) (x : ℝ) :
    ((physicalProfile P lam R a c (R * x)) ^ 2 - (cleanProfile lam R a (R * x)) ^ 2) /
        (R * x) = (2 * a ^ 2 / R) * weightedChange P lam c (-1) x := by
  simp only [physicalProfile, cleanProfile, mul_div_cancel_left₀ x hR.ne',
    weightedChange, Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev]
  ring

theorem energy_density_rescale (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) (x : ℝ) :
    (physicalProfile P lam R a c (R * x)) ^ 2 - (cleanProfile lam R a (R * x)) ^ 2 =
      (2 * a ^ 2) * weightedChange P lam c 0 x := by
  simp only [physicalProfile, cleanProfile, mul_div_cancel_left₀ x hR.ne',
    weightedChange, Real.rpow_zero]
  ring

theorem angular_density_rescale (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) (x : ℝ) :
    Real.sqrt (2 * (R * x)) *
      (physicalProfile P lam R a c (R * x) - cleanProfile lam R a (R * x)) =
      (Real.sqrt (2 * R) * a) * (x ^ (1 / 2 : ℝ) * correction P c x) := by
  simp only [physicalProfile, cleanProfile, mul_div_cancel_left₀ x hR.ne']
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * R)]
  simp only [Real.sqrt_eq_rpow]
  ring

/-- The normalization constants follow from the actual change of variable `X=R*x`. -/
theorem physicalMoments_eq (P : Patch) (lam R a : ℝ) (hR : 0 < R) (c : Coeff) :
    physicalMoments P lam R a c =
      ![2 * a ^ 2 * momentMap P lam c 0,
        2 * R * a ^ 2 * momentMap P lam c 1,
        R * Real.sqrt (2 * R) * a * momentMap P lam c 2] := by
  ext i
  fin_cases i
  · change (∫ X, ((physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) / X) =
      2 * a ^ 2 * ∫ x, weightedChange P lam c (-1) x
    rw [integral_rescale R hR]
    simp only [pressure_density_rescale P lam R a hR c, integral_const_mul]
    field_simp
  · change (∫ X, (physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) =
      2 * R * a ^ 2 * ∫ x, weightedChange P lam c 0 x
    rw [integral_rescale R hR]
    simp only [energy_density_rescale P lam R a hR c, integral_const_mul]
    ring
  · change (∫ X, Real.sqrt (2 * X) *
      (physicalProfile P lam R a c X - cleanProfile lam R a X)) =
      R * Real.sqrt (2 * R) * a * ∫ x, x ^ (1 / 2 : ℝ) * correction P c x
    rw [integral_rescale R hR]
    simp only [angular_density_rescale P lam R a hR c, integral_const_mul]
    ring

noncomputable def normalizationFactors (R a : ℝ) : Coeff :=
  ![(2 * a ^ 2)⁻¹, (2 * R * a ^ 2)⁻¹, (R * Real.sqrt (2 * R) * a)⁻¹]

/-- Signed debts are negated so that their sum with the patch changes is zero. -/
noncomputable def normalizedDebt (R a : ℝ) (d : Coeff) : Coeff :=
  -(normalizationFactors R a * d)

theorem physicalMoments_cancel (P : Patch) (lam R a : ℝ) (hR : 0 < R) (ha : 0 < a)
    (c d : Coeff) (heq : momentMap P lam c = normalizedDebt R a d) :
    physicalMoments P lam R a c + d = 0 := by
  have hs : Real.sqrt (2 * R) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have cancel (t y : ℝ) (ht : t ≠ 0) : t * (-(t⁻¹ * y)) + y = 0 := by
    rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ ht, one_mul, neg_add_cancel]
  rw [physicalMoments_eq P lam R a hR c, heq]
  ext i
  fin_cases i
  · exact cancel (2 * a ^ 2) (d 0) (by positivity)
  · exact cancel (2 * R * a ^ 2) (d 1) (by positivity)
  · exact cancel (R * Real.sqrt (2 * R) * a) (d 2) (by positivity)

/-- Radial normalization, independent of the shaped-wait amplitude. -/
noncomputable def scaledDebt (R : ℝ) (d : Coeff) : Coeff :=
  ![d 0, d 1 / R, d 2 / (R * Real.sqrt (2 * R))]

noncomputable def amplitudeFactors (a : ℝ) : Coeff :=
  ![(2 * a ^ 2)⁻¹, (2 * a ^ 2)⁻¹, a⁻¹]

noncomputable def amplitudeDebt (a : ℝ) (v : Coeff) : Coeff := -(amplitudeFactors a * v)

theorem normalizedDebt_eq (R a : ℝ) (d : Coeff) :
    normalizedDebt R a d = amplitudeDebt a (scaledDebt R d) := by
  ext i
  fin_cases i <;> simp [normalizedDebt, normalizationFactors, amplitudeDebt, amplitudeFactors,
    scaledDebt, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem amplitudeFactors_contDiffOn {U : Set ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ η ∈ U, 0 < a η) :
    ContDiffOn ℝ ∞ (fun η => amplitudeFactors (a η)) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (contDiffOn_const.mul (ha.pow 2)).inv (fun η hη => by have := hpos η hη; positivity)
  · exact (contDiffOn_const.mul (ha.pow 2)).inv (fun η hη => by have := hpos η hη; positivity)
  · exact ha.inv (fun η hη => (hpos η hη).ne')




/-- The value, normalized radial derivative, and parameter derivative of the
actual additive profile perturbation are all small. -/
noncomputable def FirstJetBound (P : Patch) (a : ℝ → ℝ) (c : ℝ → Coeff)
    (η L : ℝ) : Prop :=
  ∀ x : ℝ, |a η * correction P (c η) x| ≤ L ∧
    |a η * deriv (correction P (c η)) x| ≤ L ∧
    |deriv (fun θ => a θ * correction P (c θ) x) η| ≤ L


theorem physicalProfile_eq_clean_outside (P : Patch) (lam R a : ℝ) (c : Coeff) (X : ℝ)
    (hX : X / R ∉ Ioo P.left P.right) :
    physicalProfile P lam R a c X = cleanProfile lam R a X := by
  have hz : correction P c (X / R) = 0 := by
    by_contra hn
    exact hX (correction_tsupport P c (subset_tsupport _ hn))
  simp only [physicalProfile, cleanProfile, hz, add_zero]







theorem FirstJetBound.mono {P : Patch} {a : ℝ → ℝ} {c : ℝ → Coeff} {η L M : ℝ}
    (h : FirstJetBound P a c η L) (hLM : L ≤ M) : FirstJetBound P a c η M := by
  intro x
  exact ⟨(h x).1.trans hLM, (h x).2.1.trans hLM, (h x).2.2.trans hLM⟩


/-- All three physical moment changes are genuine integrable functions. -/
theorem physicalMoments_integrable (P : Patch) (lam R a : ℝ) (hR : 0 < R) (c : Coeff) :
    Integrable (fun X => ((physicalProfile P lam R a c X) ^ 2 -
      (cleanProfile lam R a X) ^ 2) / X) ∧
    Integrable (fun X => (physicalProfile P lam R a c X) ^ 2 -
      (cleanProfile lam R a X) ^ 2) ∧
    Integrable (fun X => Real.sqrt (2 * X) *
      (physicalProfile P lam R a c X - cleanProfile lam R a X)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (integrable_comp_mul_left_iff _ hR.ne').mp
    simp only [pressure_density_rescale P lam R a hR c]
    exact (weightedChange_integrable P lam c (-1)).const_mul _
  · apply (integrable_comp_mul_left_iff _ hR.ne').mp
    simp only [energy_density_rescale P lam R a hR c]
    exact (weightedChange_integrable P lam c 0).const_mul _
  · apply (integrable_comp_mul_left_iff _ hR.ne').mp
    simp only [angular_density_rescale P lam R a hR c]
    exact (weighted_correction_integrable P (1 / 2) c).const_mul _

theorem physicalProfile_eq_clean_of_nonpos (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) {X : ℝ} (hX : X ≤ 0) :
    physicalProfile P lam R a c X = cleanProfile lam R a X := by
  apply physicalProfile_eq_clean_outside
  intro hx
  have hdiv := div_nonpos_of_nonpos_of_nonneg hX hR.le
  linarith [hx.1, P.left_pos]

/-- The whole-line definitions equal the usual positive-radius moment integrals. -/
theorem physicalMoments_positive_radius (P : Patch) (lam R a : ℝ) (hR : 0 < R) (c : Coeff) :
    physicalMoments P lam R a c =
      ![∫ X in Ioi 0, ((physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) / X,
        ∫ X in Ioi 0, (physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2,
        ∫ X in Ioi 0, Real.sqrt (2 * X) *
          (physicalProfile P lam R a c X - cleanProfile lam R a X)] := by
  ext i
  fin_cases i <;> symm <;>
    apply setIntegral_eq_integral_of_forall_compl_eq_zero <;>
    intro X hX <;>
    rw [physicalProfile_eq_clean_of_nonpos P lam R a hR c (le_of_not_gt hX)] <;> simp




end NavierStokes.TerminalCompensation
