import Euler.EulerProof.Mollification

/-!
# Gevrey cutoffs, vector calculus and weighted energies

The classical-analysis toolbox used to build and control the packets:

* `EulerTerminalEnergy`, `EulerIntervalTrace` -- terminal energy of a solution
  and traces of interval integrals.
* `EulerDNSelection`, `EulerLagrangian` -- the diagonal selection argument and
  the Lagrangian formulation.
* `EulerVectorCalculus` -- divergence, curl and the identities relating them.
* `EulerGevreyCutoff`, `EulerGevreyFunctions`, `EulerGevreyInverse`,
  `EulerSpatialCutoffs`, `EulerPeriodicProfile` -- the Gevrey cutoff family,
  its inverse estimates, spatial cutoffs and the periodic profile.
* `EulerEnergyBootstrap`, `EulerWeightedConvolution`, `EulerWeightedEnergy`,
  `EulerWeightedPressure` -- weighted convolution of the packet weights and the
  energy and pressure bounds it yields.
* `EulerGraphPullback`, `EulerBreakdownCriterion`, `EulerDeformationVolume`,
  `EulerCylinderGraphTrace` -- pullback along a graph, the breakdown criterion,
  the volume form under a deformation and the graph trace on the cylinder.

This is part 5 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

open Set MeasureTheory

namespace EulerTerminalEnergy

open InnerProductSpace

theorem integral_sq_le_length_mul (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, (g t) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let c := (∫ t in a..b, g t) / (b - a)
  have hgi := hg.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hgs := (hg.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  change IntervalIntegrable (fun t => (g t) ^ 2) volume a b at hgs
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
    (fun t _ => sq_nonneg (g t - c))
  have hex : (fun t => (g t - c) ^ 2) =
      (fun t => (g t) ^ 2 - 2 * c * g t + c ^ 2) := by
    funext t
    ring
  rw [hex, intervalIntegral.integral_add (hgs.sub (hgi.const_mul (2 * c)))
    intervalIntegrable_const, intervalIntegral.integral_sub hgs (hgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hc : c * (b - a) = ∫ t in a..b, g t := div_mul_cancel₀ _ hlen.ne'
  have := mul_nonneg hlen.le hn
  nlinarith [sq_nonneg ((b - a) * c - ∫ t in a..b, g t)]

theorem norm_integral_sq_le_length_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ‖∫ t in a..b, g t‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) hab
  have hq := integral_sq_le_length_mul (fun t => ‖g t‖) hab hg.norm
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hq





end EulerTerminalEnergy

end

section

namespace EulerIntervalTrace

open Set MeasureTheory EulerTerminalEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_sub_sq_le_interval_energy (f v : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ^ 2 ≤ (b - a) * ∫ r in a..b, ‖v r‖ ^ 2 := by
  have hvi : IntervalIntegrable (fun r => ‖v r‖ ^ 2) volume a b :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hab
  have hpos : 0 ≤ ∫ r in a..b, ‖v r‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun r _ => sq_nonneg _)
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (le_of_lt (lt_of_not_ge hst))
    simpa only [norm_sub_rev] using h
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hf r (hsub ((uIcc_of_le hst) ▸ hr)))
    ((hv.mono hsub).intervalIntegrable_of_Icc hst)
  have hq := norm_integral_sq_le_length_mul v hst (hv.mono hsub)
  rw [he] at hq
  have hi := intervalIntegral.integral_mono_interval hs.1 hst ht.2
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖v r‖)) hvi
  exact hq.trans ((mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hst)).trans
    (mul_le_mul_of_nonneg_right (by linarith [hs.1, ht.2] : t - s ≤ b - a) hpos))

/-- Point evaluation on an interval is bounded by the actual zeroth and first derivative energies. -/
theorem pointwise_H1_trace (f v : ℝ → E) (a b : ℝ) (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖f t‖ ^ 2 ≤ 2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2) := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hfi := (hc.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  let V := ∫ s in a..b, ‖v s‖ ^ 2
  have hp (s : ℝ) (hs : s ∈ Icc a b) :
      ‖f t‖ ^ 2 ≤ 2 * ‖f s‖ ^ 2 + 2 * (b - a) * V := by
    have hd := norm_sub_sq_le_interval_energy f v a b hab.le hv hf s t hs ht
    have hn : ‖f t‖ ≤ ‖f t - f s‖ + ‖f s‖ := by
      calc
        _ = ‖(f t - f s) + f s‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    dsimp [V]
    nlinarith [norm_nonneg (f t), norm_nonneg (f s), norm_nonneg (f t - f s),
      sq_nonneg (‖f t - f s‖ - ‖f s‖)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (intervalIntegrable_const (c := ‖f t‖ ^ 2))
    ((hfi.const_mul 2).add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hfi.const_mul 2) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have hlen : 0 < b - a := sub_pos.mpr hab
  apply (mul_le_mul_iff_right₀ hlen).mp
  dsimp [V] at hi ⊢
  have he : (b - a) * (2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) =
      2 * (∫ s in a..b, ‖f s‖ ^ 2) + (b - a) *
        (2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) := by
    field_simp [hlen.ne']
  rw [he]
  exact hi

end EulerIntervalTrace

end

section

/-! Quantitative endpoint selection in the activation step, equations (26)–(27). -/

namespace EulerDNSelection

open InnerProductSpace

theorem positive_cross_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Λ : E →L[ℝ] E) (hΛ : Λ.IsPositive) (p q : E) :
    ⟪Λ p, q⟫_ℝ ^ 2 ≤ ⟪Λ p, p⟫_ℝ * ⟪Λ q, q⟫_ℝ := by
  have hsym : ⟪Λ q, p⟫_ℝ = ⟪Λ p, q⟫_ℝ := by
    rw [hΛ.inner_left_eq_inner_right, real_inner_comm]
  have hquad : ∀ t : ℝ, 0 ≤ ⟪Λ p, p⟫_ℝ * (t * t) +
      (2 * ⟪Λ p, q⟫_ℝ) * t + ⟪Λ q, q⟫_ℝ := by
    intro t
    have ht := hΛ.inner_nonneg_left (t • p + q)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hsym] at ht
    nlinarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith

/-- A positive semidefinite endpoint matrix, perturbed by a unit shear and a small
matrix with negative first diagonal entry, allows the required polarized output. -/
theorem select_endpoint
    (C ε a b d cpp cpq cqp cqq : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (hsmall : 16 * (C + 1) * ε ≤ 1)
    (ha : 0 ≤ a) (had : b ^ 2 ≤ a * d) (hd : 0 ≤ d)
    (haC : a ≤ C) (hbC : |b| ≤ C)
    (hpp : cpp < 0) (hppε : |cpp| ≤ ε)
    (hpq : |cpq| ≤ ε) (hqp : |cqp| ≤ ε) (hqq : |cqq| ≤ ε) :
    ∃ yp yq : ℝ,
      (b - 1 - cqp) * yp + (d - cqq) * yq = 1 ∧
      -8 * (C + 1) ≤ (a - cpp) * yp + (b - cpq) * yq ∧
      (a - cpp) * yp + (b - cpq) * yq ≤ 0 ∧
      |yp| + |yq| ≤ 8 * (C + 1) := by
  have hεsmall : ε ≤ 1 / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ C by linarith) hε]
  have hu : 0 < a - cpp := by linarith
  have huC : a - cpp ≤ C + ε := by
    have := (abs_le.mp hppε).1
    linarith
  rcases le_or_gt b (1 / 2) with hb | hb
  · let D := 1 + cqp - b
    have hD : 1 / 3 ≤ D := by
      have := (abs_le.mp hqp).1
      dsimp [D]
      linarith
    have hDpos : 0 < D := by linarith
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hquot : (a - cpp) / D ≤ 8 * (C + 1) := by
      apply (div_le_iff₀ hDpos).2
      nlinarith [mul_nonneg (show 0 ≤ C + 1 by linarith)
        (show 0 ≤ D - 1 / 3 by linarith)]
    have hinv : 1 / D ≤ 3 := (div_le_iff₀ hDpos).2 (by linarith)
    refine ⟨-1 / D, 0, ?_, ?_, ?_, ?_⟩
    · have heq : b - 1 - cqp = -D := by dsimp [D]; ring
      rw [heq, mul_zero, add_zero]
      field_simp
    · have heq : (a - cpp) * (-1 / D) + (b - cpq) * 0 = -(a - cpp) / D := by ring
      rw [heq, neg_div]
      linarith
    · have heq : (a - cpp) * (-1 / D) + (b - cpq) * 0 = -((a - cpp) / D) := by ring
      rw [heq]
      exact neg_nonpos.mpr (div_nonneg hu.le hDpos.le)
    · simp only [abs_zero, add_zero, abs_div, abs_neg, abs_one, abs_of_pos hDpos]
      linarith
  · let Δ := (a - cpp) * (d - cqq) - (b - 1 - cqp) * (b - cpq)
    have hbpos : 0 ≤ b := by linarith
    have hb_bound : b ≤ C := (abs_le.mp hbC).2
    have hud : b ^ 2 ≤ (a - cpp) * d := by
      nlinarith [mul_nonneg (show 0 ≤ -cpp by linarith) hd]
    have hucqq : (a - cpp) * cqq ≤ (C + ε) * ε :=
      (mul_le_mul_of_nonneg_left (abs_le.mp hqq).2 hu.le).trans
        (mul_le_mul_of_nonneg_right huC hε)
    have hbpq : -(C * ε) ≤ b * cpq := by
      have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hpq).1 hbpos
      have h₂ := mul_le_mul_of_nonneg_right hb_bound hε
      nlinarith
    have hbqp : -(C * ε) ≤ b * cqp := by
      have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hqp).1 hbpos
      have h₂ := mul_le_mul_of_nonneg_right hb_bound hε
      nlinarith
    have hprod : cqp * cpq ≤ ε ^ 2 := by
      calc
        cqp * cpq ≤ |cqp * cpq| := le_abs_self _
        _ = |cqp| * |cpq| := abs_mul _ _
        _ ≤ ε * ε := mul_le_mul hqp hpq (abs_nonneg _) hε
        _ = ε ^ 2 := by ring
    have hΔ : 1 / 4 ≤ Δ := by
      have hpq_upper := (abs_le.mp hpq).2
      have hεsq : ε ^ 2 ≤ ε := by nlinarith
      dsimp [Δ]
      nlinarith
    have hΔpos : 0 < Δ := by linarith
    have hΔne : Δ ≠ 0 := ne_of_gt hΔpos
    have hnum : |b - cpq| ≤ C + ε :=
      (abs_sub b cpq).trans (add_le_add hbC hpq)
    have huabs : |a - cpp| ≤ C + ε := by rwa [abs_of_pos hu]
    have hnorm : |-(b - cpq) / Δ| + |(a - cpp) / Δ| ≤ 8 * (C + 1) := by
      rw [abs_div, abs_div, abs_neg, abs_of_pos hΔpos, ← add_div]
      apply (div_le_iff₀ hΔpos).2
      nlinarith [mul_nonneg (show 0 ≤ C + 1 by linarith)
        (show 0 ≤ Δ - 1 / 4 by linarith)]
    refine ⟨-(b - cpq) / Δ, (a - cpp) / Δ, ?_, ?_, ?_, hnorm⟩
    · field_simp [hΔne]
      dsimp [Δ]
      ring
    · have heq : (a - cpp) * (-(b - cpq) / Δ) +
          (b - cpq) * ((a - cpp) / Δ) = 0 := by ring
      rw [heq]
      linarith
    · have heq : (a - cpp) * (-(b - cpq) / Δ) +
          (b - cpq) * ((a - cpp) / Δ) = 0 := by ring
      rw [heq]

/-- The endpoint choice at an arbitrary positive shear scale `h`. -/
theorem select_endpoint_scaled
    (C ε h a b d cpp cpq cqp cqq : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (hsmall : 16 * (C + 1) * ε ≤ 1)
    (hh : 0 < h) (ha : 0 ≤ a) (had : b ^ 2 ≤ a * d) (hd : 0 ≤ d)
    (haC : a ≤ C * h) (hbC : |b| ≤ C * h)
    (hpp : cpp < 0) (hppε : |cpp| ≤ ε * h)
    (hpq : |cpq| ≤ ε * h) (hqp : |cqp| ≤ ε * h) (hqq : |cqq| ≤ ε * h) :
    ∃ yp yq : ℝ,
      (b - h - cqp) * yp + (d - cqq) * yq = 1 ∧
      -8 * (C + 1) ≤ (a - cpp) * yp + (b - cpq) * yq ∧
      (a - cpp) * yp + (b - cpq) * yq ≤ 0 ∧
      |yp| + |yq| ≤ 8 * (C + 1) / h := by
  have habs (x R : ℝ) (hx : |x| ≤ R * h) : |x / h| ≤ R := by
    rw [abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).2 hx
  have hpsd : (b / h) ^ 2 ≤ (a / h) * (d / h) := by
    rw [div_pow, div_mul_div_comm, ← pow_two]
    exact div_le_div_of_nonneg_right had (sq_nonneg h)
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hnorm⟩ := select_endpoint C ε
    (a / h) (b / h) (d / h) (cpp / h) (cpq / h) (cqp / h) (cqq / h)
    hC hε hsmall (div_nonneg ha hh.le) hpsd (div_nonneg hd hh.le)
    ((div_le_iff₀ hh).2 haC) (habs b C hbC)
    (div_neg_of_neg_of_pos hpp hh) (habs cpp ε hppε)
    (habs cpq ε hpq) (habs cqp ε hqp) (habs cqq ε hqq)
  have heqp : (a - cpp) * (yp / h) + (b - cpq) * (yq / h) =
      (a / h - cpp / h) * yp + (b / h - cpq / h) * yq := by ring
  have heqq : (b - h - cqp) * (yp / h) + (d - cqq) * (yq / h) =
      (b / h - 1 - cqp / h) * yp + (d / h - cqq / h) * yq := by
    field_simp
  refine ⟨yp / h, yq / h, heqq.trans hwq, heqp ▸ hwpl, heqp ▸ hwpu, ?_⟩
  rw [abs_div, abs_div, abs_of_pos hh, ← add_div]
  exact div_le_div_of_nonneg_right hnorm hh.le

theorem select_endpoint_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Λ B : E →L[ℝ] E) (p q : E)
    (C ε h : ℝ) (hΛ : Λ.IsPositive) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : ⟪p, q⟫_ℝ = 0) (hC : 1 ≤ C) (hε : 0 ≤ ε) (hh : 0 < h)
    (hsmall : 16 * (C + 1) * ε ≤ 1) (hΛbound : ‖Λ‖ ≤ C * h)
    (hBbound : ‖B‖ ≤ ε * h) (hBpp : ⟪B p, p⟫_ℝ < 0) :
    ∃ yp yq : ℝ, let Y := yp • p + yq • q
      let w := Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q
      ⟪w, q⟫_ℝ = 1 ∧ -8 * (C + 1) ≤ ⟪w, p⟫_ℝ ∧
        ⟪w, p⟫_ℝ ≤ 0 ∧ ‖Y‖ ≤ 8 * (C + 1) / h := by
  have hbound (T : E →L[ℝ] E) (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      |⟪T v, w⟫_ℝ| ≤ ‖T‖ := by
    calc
      |⟪T v, w⟫_ℝ| ≤ ‖T v‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg w)
      _ = ‖T‖ := by rw [hv, hw, mul_one, mul_one]
  have hsym : ⟪Λ q, p⟫_ℝ = ⟪Λ p, q⟫_ℝ := by
    rw [hΛ.inner_left_eq_inner_right, real_inner_comm]
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hnorm⟩ := select_endpoint_scaled C ε h
    ⟪Λ p, p⟫_ℝ ⟪Λ p, q⟫_ℝ ⟪Λ q, q⟫_ℝ
    ⟪B p, p⟫_ℝ ⟪B q, p⟫_ℝ ⟪B p, q⟫_ℝ ⟪B q, q⟫_ℝ
    hC hε hsmall hh (hΛ.inner_nonneg_left p) (positive_cross_sq_le Λ hΛ p q)
    (hΛ.inner_nonneg_left q)
    ((le_abs_self _).trans ((hbound Λ p p hp hp).trans hΛbound))
    ((hbound Λ p q hp hq).trans hΛbound) hBpp
    ((hbound B p p hp hp).trans hBbound) ((hbound B q p hq hp).trans hBbound)
    ((hbound B p q hp hq).trans hBbound) ((hbound B q q hq hq).trans hBbound)
  have hqp : ⟪q, p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpq
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hqq : ⟪q, q⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hq, one_pow]
  refine ⟨yp, yq, ?_, ?_, ?_, ?_⟩
  · convert hwq using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hpq, hpp, hqq]
    ring
  · convert hwpl using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsym, hpq, hqp, hpp]
    ring
  · convert hwpu using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsym, hpq, hqp, hpp]
    ring
  · calc
      ‖yp • p + yq • q‖ ≤ ‖yp • p‖ + ‖yq • q‖ := norm_add_le _ _
      _ = |yp| + |yq| := by rw [norm_smul, norm_smul, hp, hq]; simp
      _ ≤ 8 * (C + 1) / h := hnorm

end EulerDNSelection

end

section

namespace EulerLagrangian

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unforced Euler momentum residual, with space-time derivative and the
canonical real gradient. -/
def momentumResidual (u : ℝ × E → E) (p : ℝ × E → ℝ) (z : ℝ × E) : E :=
  fderiv ℝ u z (1, u z) + gradient (fun x => p (z.1, x)) z.2

omit [CompleteSpace E] in
theorem material_derivative (w : ℝ × E → E) (X : ℝ → E) (t : ℝ)
    (U : E) (D : (ℝ × E) →L[ℝ] E)
    (hX : HasDerivAt X U t) (hw : HasFDerivAt w D (t, X t)) :
    HasDerivAt (fun s => w (s, X s)) (D (1, U)) t :=
  hw.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)

theorem gradient_add (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  have hs : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  simp only [gradient, hs.fderiv, map_add]

theorem momentum_perturbation (u w : ℝ × E → E) (p q : ℝ × E → ℝ)
    (z : ℝ × E) (Du Dw : (ℝ × E) →L[ℝ] E)
    (hu : HasFDerivAt u Du z) (hw : HasFDerivAt w Dw z)
    (hp : DifferentiableAt ℝ (fun x => p (z.1, x)) z.2)
    (hq : DifferentiableAt ℝ (fun x => q (z.1, x)) z.2) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) z =
      momentumResidual u p z + Dw (1, u z) + Du (0, w z) + Dw (0, w z) +
        gradient (fun x => q (z.1, x)) z.2 := by
  have hsplit : ((1 : ℝ), u z + w z) = (1, u z) + (0, w z) := by simp
  have hs : HasFDerivAt (fun y => u y + w y) (Du + Dw) z := hu.add hw
  simp only [momentumResidual, hs.fderiv, hu.fderiv,
    add_apply, hsplit, map_add,
    gradient_add _ _ _ hp hq]
  abel

theorem euler_perturbation_along_flow (u w : ℝ × E → E)
    (p q : ℝ × E → ℝ) (X : ℝ → E) (t : ℝ)
    (Du Dw : (ℝ × E) →L[ℝ] E) (V : E)
    (hX : HasDerivAt X (u (t, X t)) t)
    (hu : HasFDerivAt u Du (t, X t)) (hw : HasFDerivAt w Dw (t, X t))
    (hW : HasDerivAt (fun s => w (s, X s)) V t)
    (hp : DifferentiableAt ℝ (fun x => p (t, x)) (X t))
    (hq : DifferentiableAt ℝ (fun x => q (t, x)) (X t))
    (hparent : momentumResidual u p (t, X t) = 0) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) (t, X t) =
      V + Du (0, w (t, X t)) + Dw (0, w (t, X t)) +
        gradient (fun x => q (t, x)) (X t) := by
  have hV := hW.unique (material_derivative w X t _ Dw hX hw)
  rw [momentum_perturbation u w p q (t, X t) Du Dw hu hw hp hq, hparent,
    zero_add, ← hV]


omit [CompleteSpace E] in
theorem derivative_pullback_inverse (f X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    fderiv ℝ f (X x) = (fderiv ℝ (f ∘ X) x).comp F.symm.toContinuousLinearMap := by
  rw [(hf.hasFDerivAt.comp x hX).fderiv]
  ext v
  simp

theorem gradient_pullback (f : E → ℝ) (X : E → E) (F : E →L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F x) (hf : DifferentiableAt ℝ f (X x)) :
    gradient (f ∘ X) x = F.adjoint (gradient f (X x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    (hf.hasFDerivAt.comp x hX).fderiv]
  rfl

theorem gradient_pullback_inverse (f : E → ℝ) (X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    gradient f (X x) = F.symm.toContinuousLinearMap.adjoint (gradient (f ∘ X) x) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, gradient_pullback f X _ x hX hf,
    ContinuousLinearMap.adjoint_inner_left]
  simp

end EulerLagrangian

end

section

namespace EulerVectorCalculus

open EulerSmoothLimit
open scoped ContDiff

/-- The ordinary coordinate derivative, evaluated using the Fréchet derivative. -/
def partialDerivative (f : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The three-dimensional curl of a vector potential in standard coordinates. -/
def curl (ψ : Fin 3 → Space → ℝ) (x : Space) : Space :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
    (fun i => partialDerivative (ψ (i + 2)) (i + 1) x -
      partialDerivative (ψ (i + 1)) (i + 2) x)

@[simp] theorem curl_apply (ψ : Fin 3 → Space → ℝ) (x : Space) (i : Fin 3) :
    curl ψ x i = partialDerivative (ψ (i + 2)) (i + 1) x -
      partialDerivative (ψ (i + 1)) (i + 2) x := rfl

theorem contDiff_partialDerivative (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (partialDerivative f i) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_curl (ψ : Fin 3 → Space → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (curl ψ) := by
  apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm.contDiff.comp
  exact contDiff_pi.mpr (fun i =>
    (contDiff_partialDerivative _ (hψ _) _).sub (contDiff_partialDerivative _ (hψ _) _))

theorem partialDerivative_comm (f : Space → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Space) :
    partialDerivative (partialDerivative f i) j x =
      partialDerivative (partialDerivative f j) i x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have he (a b : Fin 3) : partialDerivative (partialDerivative f a) b x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold partialDerivative
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he, he]
  exact (hf.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)).eq _ _

theorem fderiv_coordinate (f : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) (v : Space) :
    fderiv ℝ (fun y => f y i) x v = (fderiv ℝ f x v) i := by
  have he : HasFDerivAt (fun y => f y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ f x)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f x) i).comp x hf.hasFDerivAt
  rw [he.fderiv]
  rfl

theorem divergence_curl (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (x : Space) : divergence (curl ψ) x = 0 := by
  have hc : DifferentiableAt ℝ (curl ψ) x :=
    ((contDiff_curl ψ hψ).differentiable (by simp)).differentiableAt
  have hp (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
      DifferentiableAt ℝ (partialDerivative f i) x :=
    ((contDiff_partialDerivative f hf i).differentiable (by simp)).differentiableAt
  have he (i : Fin 3) : (fderiv ℝ (curl ψ) x (EuclideanSpace.single i 1)) i =
      partialDerivative (partialDerivative (ψ (i + 2)) (i + 1)) i x -
        partialDerivative (partialDerivative (ψ (i + 1)) (i + 2)) i x := by
    rw [← fderiv_coordinate _ _ hc i]
    simp only [curl_apply]
    have hd : HasFDerivAt
        (fun y => partialDerivative (ψ (i + 2)) (i + 1) y -
          partialDerivative (ψ (i + 1)) (i + 2) y)
        (fderiv ℝ (partialDerivative (ψ (i + 2)) (i + 1)) x -
          fderiv ℝ (partialDerivative (ψ (i + 1)) (i + 2)) x) x :=
      (hp _ (hψ _) _).hasFDerivAt.sub (hp _ (hψ _) _).hasFDerivAt
    rw [hd.fderiv]
    rfl
  rw [divergence_eq_coordinate_sum, Fin.sum_univ_three, he, he, he]
  change partialDerivative (partialDerivative (ψ 2) 1) 0 x -
    partialDerivative (partialDerivative (ψ 1) 2) 0 x +
    (partialDerivative (partialDerivative (ψ 0) 2) 1 x -
    partialDerivative (partialDerivative (ψ 2) 0) 1 x) +
    (partialDerivative (partialDerivative (ψ 1) 0) 2 x -
    partialDerivative (partialDerivative (ψ 0) 1) 2 x) = 0
  rw [partialDerivative_comm (ψ 2) ((hψ 2).of_le (by simp)) 1 0 x,
    partialDerivative_comm (ψ 0) ((hψ 0).of_le (by simp)) 2 1 x,
    partialDerivative_comm (ψ 1) ((hψ 1).of_le (by simp)) 0 2 x]
  ring

theorem tsupport_curl_subset (ψ : Fin 3 → Space → ℝ) (K : Set Space)
    (hK : IsClosed K) (hψ : ∀ i, tsupport (ψ i) ⊆ K) :
    tsupport (curl ψ) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  have hzero : curl ψ x = 0 := by
    ext i
    have h₁ : x ∉ tsupport (ψ (i + 2)) := fun h => hnot (hψ _ h)
    have h₂ : x ∉ tsupport (ψ (i + 1)) := fun h => hnot (hψ _ h)
    simp [curl_apply, partialDerivative, fderiv_of_notMem_tsupport ℝ h₁,
      fderiv_of_notMem_tsupport ℝ h₂]
  exact hx hzero

theorem hasCompactSupport_curl (ψ : Fin 3 → Space → ℝ) (K : Set Space)
    (hK : IsCompact K) (hψ : ∀ i, tsupport (ψ i) ⊆ K) :
    HasCompactSupport (curl ψ) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_curl_subset ψ K hK.isClosed hψ)

theorem partialDerivative_odd_of_even (f : Space → ℝ) (hf : Differentiable ℝ f)
    (heven : ∀ x, f (-x) = f x) (i : Fin 3) (x : Space) :
    partialDerivative f i (-x) = -partialDerivative f i x := by
  have he : (fun y => f (-y)) = f := funext heven
  have hd : HasFDerivAt (fun y => f (-y))
      ((fderiv ℝ f (-x)).comp (-ContinuousLinearMap.id ℝ Space)) x :=
    (hf (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  have hv := congrArg (fun A : Space →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd.fderiv
  rw [he] at hv
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg] at hv
  exact neg_eq_iff_eq_neg.mp hv.symm

theorem odd_curl_of_even (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, Differentiable ℝ (ψ i)) (heven : ∀ i x, ψ i (-x) = ψ i x) (x : Space) :
    curl ψ (-x) = -curl ψ x := by
  ext i
  simp only [curl_apply, PiLp.neg_apply,
    partialDerivative_odd_of_even _ (hψ _) (heven _) _ _]
  ring

/-- The vector potential `-x × (L x) / 3` in cyclic coordinates. -/
def linearPotential (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) : ℝ :=
  (-1 / 3 : ℝ) * (x (i + 1) * (L x) (i + 2) - x (i + 2) * (L x) (i + 1))

theorem contDiff_linearPotential (L : Space →L[ℝ] Space) (i : Fin 3) :
    ContDiff ℝ ∞ (linearPotential L i) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff
  have hL (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => L x j) := (hc j).comp L.contDiff
  exact contDiff_const.mul (((hc _).mul (hL _)).sub ((hc _).mul (hL _)))

theorem linearPotential_even (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) :
    linearPotential L i (-x) = linearPotential L i x := by
  simp [linearPotential, map_neg, PiLp.neg_apply]

theorem partialDerivative_linearPotential (L : Space →L[ℝ] Space) (i j : Fin 3)
    (x : Space) :
    partialDerivative (linearPotential L i) j x =
      -((EuclideanSpace.single j (1 : ℝ) : Space) (i + 1) * (L x) (i + 2) +
        x (i + 1) * (L (EuclideanSpace.single j 1)) (i + 2) -
        ((EuclideanSpace.single j (1 : ℝ) : Space) (i + 2) * (L x) (i + 1) +
        x (i + 2) * (L (EuclideanSpace.single j 1)) (i + 1))) / 3 := by
  have hc (a : Fin 3) := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x a
  have hL (a : Fin 3) := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (L x) a).comp x L.hasFDerivAt
  have hd := (((hc (i + 1)).mul (hL (i + 2))).sub
    ((hc (i + 2)).mul (hL (i + 1)))).const_mul (-1 / 3 : ℝ)
  change HasFDerivAt (linearPotential L i) _ x at hd
  unfold partialDerivative
  rw [hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, PiLp.proj_apply, smul_eq_mul]
  ring

theorem curl_linearPotential (L : Space →L[ℝ] Space) (x : Space) :
    curl (linearPotential L) x = L x -
      (LinearMap.trace ℝ Space L.toLinearMap / 3) • x := by
  have hx : (∑ j : Fin 3, x j • (EuclideanSpace.single j 1 : Space)) = x := by
    simpa using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have hL (i : Fin 3) : (L x) i =
      ∑ j : Fin 3, x j * (L (EuclideanSpace.single j 1)) i := by
    nth_rw 1 [← hx]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [← coordinateTrace_eq_linearTrace]
  ext i
  fin_cases i <;>
    simp [curl_apply, partialDerivative_linearPotential, coordinateTrace,
      Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, hL] <;> ring

theorem curl_linearPotential_of_trace_zero (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0) (x : Space) :
    curl (linearPotential L) x = L x := by
  rw [curl_linearPotential, hL, zero_div, zero_smul, sub_zero]

theorem curl_congr_nhds (ψ φ : Fin 3 → Space → ℝ) (x : Space)
    (h : ∀ i, ψ i =ᶠ[nhds x] φ i) : curl ψ x = curl φ x := by
  ext i
  simp only [curl_apply, partialDerivative, (h (i + 2)).fderiv_eq,
    (h (i + 1)).fderiv_eq]


end EulerVectorCalculus

end

section

namespace EulerGevreyCutoff

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- Holomorphic function used to estimate the flat real bump by Cauchy's inequality. -/
def complexFlat (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

theorem real_part_inv_lower_bound (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : ‖z - (x : ℂ)‖ ≤ x / 2) : 1 / (8 * x) ≤ (z⁻¹).re := by
  have hre : x / 2 ≤ z.re := by
    have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans hz
    simp only [sub_re, ofReal_re] at h
    have := (abs_le.mp h).1
    linarith
  have hn : ‖z‖ ≤ 2 * x := by
    calc
      ‖z‖ = ‖(z - (x : ℂ)) + (x : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ x / 2 + x := by simpa [Complex.norm_real, abs_of_pos hx] using add_le_add_right hz x
      _ ≤ 2 * x := by linarith
  have hzn : z ≠ 0 := by intro h; simp [h] at hre; linarith
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzn)
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  apply (div_le_div_iff₀ (by positivity : 0 < 8 * x) hden).2
  have hsq : ‖z‖ ^ 2 ≤ (2 * x) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hn 2
  nlinarith

theorem complexFlat_differentiableAt {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ complexFlat z :=
  Complex.differentiableAt_exp.comp z (differentiableAt_id.inv hz).neg

theorem complexFlat_disc_bound (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : ‖z - (x : ℂ)‖ ≤ x / 2) :
    ‖complexFlat z‖ ≤ Real.exp (-(1 / (8 * x))) := by
  rw [complexFlat, Complex.norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (neg_le_neg (real_part_inv_lower_bound x hx z hz))

theorem factorial_decay (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-t) ≤ n.factorial := by
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp t ht n)
  calc
    t ^ n * Real.exp (-t) ≤ (Real.exp t * n.factorial) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = n.factorial := by rw [Real.exp_neg]; field_simp

theorem complexFlat_gevrey_bound (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤ (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hr : 0 < x / 2 := by positivity
  have hfd : DifferentiableOn ℂ complexFlat (Metric.closedBall (x : ℂ) (x / 2)) := by
    intro z hz
    have hd : ‖z - (x : ℂ)‖ ≤ x / 2 := by simpa [dist_eq_norm] using hz
    have hn : z ≠ 0 := by
      intro h
      simp [h, Complex.norm_real, abs_of_pos hx] at hd
      linarith
    exact (complexFlat_differentiableAt hn).differentiableWithinAt
  have hfc : DiffContOnCl ℂ complexFlat (Metric.ball (x : ℂ) (x / 2)) :=
    (hfd.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hfc
    (fun z hz => complexFlat_disc_bound x hx z (by
      exact le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz)))
  let t : ℝ := 1 / (8 * x)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hi : (x / 2)⁻¹ = 16 * t := by dsimp [t]; field_simp; ring
  have he : (n.factorial : ℝ) * Real.exp (-t) / (x / 2) ^ n =
      (16 : ℝ) ^ n * n.factorial * (t ^ n * Real.exp (-t)) := by
    rw [div_eq_mul_inv, ← inv_pow, hi, mul_pow]
    ring
  change ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤ _
  calc
    ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤
        n.factorial * Real.exp (-t) / (x / 2) ^ n := hc
    _ = (16 : ℝ) ^ n * n.factorial * (t ^ n * Real.exp (-t)) := he
    _ ≤ (16 : ℝ) ^ n * n.factorial * n.factorial :=
      mul_le_mul_of_nonneg_left (factorial_decay n t ht) (by positivity)
    _ = (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by ring

theorem iteratedDeriv_real_restriction (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (n : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ s) :
    iteratedDeriv n (fun t : ℝ => (f (t : ℂ)).re) x =
      (iteratedDeriv n f (x : ℂ)).re := by
  have hc : ContDiffOn ℂ n f s := hf.contDiffOn hs
  have hr : ContDiffOn ℝ n f s := hc.restrict_scalars ℝ
  have hsR : IsOpen (Complex.ofRealCLM ⁻¹' s) := hs.preimage Complex.ofRealCLM.continuous
  have he := Complex.ofRealCLM.iteratedFDerivWithin_comp_right hr hs.uniqueDiffOn
    hsR.uniqueDiffOn hx (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_of_isOpen n hsR hx] at he
  simp only [Complex.ofRealCLM_apply] at he
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hs hx] at he
  have hca : ContDiffAt ℂ n f (x : ℂ) := (hc _ hx).contDiffAt (hs.mem_nhds hx)
  have hra : ContDiffAt ℝ n (f ∘ Complex.ofRealCLM) x :=
    (hca.restrict_scalars ℝ).comp_continuousLinearMap Complex.ofRealCLM
  have hre := Complex.reCLM.iteratedFDeriv_comp_left hra (le_refl (n : ℕ∞ω))
  change (iteratedFDeriv ℝ n (Complex.reCLM ∘ (f ∘ Complex.ofRealCLM)) x)
    (fun _ => 1) = ((iteratedFDeriv ℂ n f (x : ℂ)) (fun _ => 1)).re
  rw [hre, he, ← hca.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp

theorem polynomial_glue_flat (p : Polynomial ℝ) (n : ℕ) (x : ℝ) (hx : x ≤ 0) :
    iteratedDeriv n (fun y => p.eval y⁻¹ * expNegInvGlue y) x = 0 := by
  induction n generalizing p with
  | zero => simp [expNegInvGlue.zero_of_nonpos hx]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y => p.eval y⁻¹ * expNegInvGlue y) =
        fun y => (Polynomial.X ^ 2 * (p - p.derivative)).eval y⁻¹ * expNegInvGlue y :=
      funext (fun y => (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p y).deriv)
    rw [hd]
    exact ih _

theorem expNegInvGlue_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  by_cases hx : x ≤ 0
  · have hz : iteratedDeriv n expNegInvGlue x = 0 := by
      simpa using polynomial_glue_flat 1 n x hx
    rw [hz, abs_zero]
    positivity
  have hx : 0 < x := lt_of_not_ge hx
  have hs : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hd : DifferentiableOn ℂ complexFlat ({0}ᶜ : Set ℂ) :=
    fun z hz => (complexFlat_differentiableAt hz).differentiableWithinAt
  have hr := iteratedDeriv_real_restriction complexFlat _ hs hd n x (by simpa using hx.ne')
  have hg : expNegInvGlue =ᶠ[nhds x] (fun t : ℝ => (complexFlat (t : ℂ)).re) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp [expNegInvGlue, hy.not_ge, complexFlat, ← Complex.ofReal_inv,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hg.iteratedDeriv_eq n, hr]
  exact (Complex.abs_re_le_norm _).trans (complexFlat_gevrey_bound n x hx)

/-- Nonnegative even smooth bump supported on the unit interval. -/
def rawBump (x : ℝ) : ℝ := expNegInvGlue (x + 1) * expNegInvGlue (1 - x)

theorem rawBump_contDiff : ContDiff ℝ ∞ rawBump := by
  exact (expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem rawBump_nonneg (x : ℝ) : 0 ≤ rawBump x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem rawBump_even (x : ℝ) : rawBump (-x) = rawBump x := by
  simp only [rawBump, neg_add_eq_sub, sub_neg_eq_add]
  rw [add_comm (1 : ℝ) x, mul_comm]

theorem rawBump_pos_zero : 0 < rawBump 0 := by
  apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> norm_num

theorem rawBump_support : tsupport rawBump ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    have hz := expNegInvGlue.zero_of_nonpos (show x + 1 ≤ 0 by linarith)
    exact hx (by simp [rawBump, hz])
  · by_contra h
    have hz := expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)
    exact hx (by simp [rawBump, hz])


theorem rawBump_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n rawBump x| ≤ 3 * (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun y => expNegInvGlue (y + 1)
  let g : ℝ → ℝ := fun y => expNegInvGlue (1 - y)
  have hf : ContDiff ℝ ∞ f := expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ g := expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hb₁ (k : ℕ) : |iteratedDeriv k f x| ≤ 1 * EulerGevrey.majorant 16 0 k := by
    simpa [f, EulerGevrey.majorant, iteratedDeriv_comp_add_const] using
      expNegInvGlue_gevrey_bound k (x + 1)
  have hb₂ (k : ℕ) : |iteratedDeriv k g x| ≤ 1 * EulerGevrey.majorant 16 0 k := by
    simpa [g, EulerGevrey.majorant, iteratedDeriv_comp_const_sub, abs_mul, abs_pow] using
      expNegInvGlue_gevrey_bound k (1 - x)
  have hp := EulerGevrey.sequence_product_majorant 16 1 1 (by norm_num) (by norm_num)
    (by norm_num) 0 0 (fun k => iteratedDeriv k f x) (fun k => iteratedDeriv k g x) hb₁ hb₂ n
  have hmul : rawBump = f * g := rfl
  rw [hmul, iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  simpa [EulerGevrey.majorant, mul_assoc] using hp

/-- Positive integral used to normalize the smooth transition. -/
def bumpMass : ℝ := ∫ t in (-1 : ℝ)..1, rawBump t

theorem bumpMass_pos : 0 < bumpMass := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (rawBump_contDiff.continuous.intervalIntegrable _ _)
  · intro x hx
    apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> linarith [hx.1, hx.2]
  · norm_num

/-- Smooth monotone transition from zero to one, with explicit Gevrey bounds. -/
def transition (x : ℝ) : ℝ := (∫ t in (-1 : ℝ)..x, rawBump t) / bumpMass

theorem transition_hasDerivAt (x : ℝ) :
    HasDerivAt transition (rawBump x / bumpMass) x := by
  have hc := rawBump_contDiff.continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).div_const bumpMass

theorem transition_deriv : deriv transition = fun x => rawBump x / bumpMass :=
  funext (fun x => (transition_hasDerivAt x).deriv)

theorem transition_contDiff : ContDiff ℝ ∞ transition := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (transition_hasDerivAt x).differentiableAt,
    transition_deriv ▸ rawBump_contDiff.div_const bumpMass⟩

theorem rawBump_eq_zero_of_le (x : ℝ) (hx : x ≤ -1) : rawBump x = 0 := by
  simp [rawBump, expNegInvGlue.zero_of_nonpos (show x + 1 ≤ 0 by linarith)]

theorem rawBump_eq_zero_of_ge (x : ℝ) (hx : 1 ≤ x) : rawBump x = 0 := by
  simp [rawBump, expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)]

theorem transition_zero_of_le (x : ℝ) (hx : x ≤ -1) : transition x = 0 := by
  have hi : (∫ t in x..(-1 : ℝ), rawBump t) = 0 := by
    calc
      _ = ∫ t in x..(-1 : ℝ), (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        rawBump_eq_zero_of_le t (((uIcc_of_le hx) ▸ ht).2))
      _ = 0 := by simp
  unfold transition
  rw [intervalIntegral.integral_symm, hi]
  simp

theorem transition_one_of_ge (x : ℝ) (hx : 1 ≤ x) : transition x = 1 := by
  have hi : (∫ t in (1 : ℝ)..x, rawBump t) = 0 := by
    calc
      _ = ∫ t in (1 : ℝ)..x, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        rawBump_eq_zero_of_ge t (((uIcc_of_le hx) ▸ ht).1))
      _ = 0 := by simp
  unfold transition
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rawBump_contDiff.continuous.intervalIntegrable (-1) 1)
    (rawBump_contDiff.continuous.intervalIntegrable 1 x), hi, add_zero]
  exact div_self bumpMass_pos.ne'

theorem transition_monotone : Monotone transition := by
  apply monotone_of_deriv_nonneg (fun x => (transition_hasDerivAt x).differentiableAt)
  intro x
  rw [transition_deriv]
  exact div_nonneg (rawBump_nonneg x) bumpMass_pos.le

theorem transition_mem_unitInterval (x : ℝ) : transition x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · by_cases hx : x ≤ -1
    · rw [transition_zero_of_le x hx]
    · have h := transition_monotone (le_of_lt (lt_of_not_ge hx))
      rwa [transition_zero_of_le (-1) le_rfl] at h
  · by_cases hx : 1 ≤ x
    · rw [transition_one_of_ge x hx]
    · have h := transition_monotone (le_of_lt (lt_of_not_ge hx))
      rwa [transition_one_of_ge 1 le_rfl] at h

theorem transition_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n transition x| ≤
      (1 + 3 / bumpMass) * (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hm := bumpMass_pos
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    rw [abs_of_nonneg (transition_mem_unitInterval x).1]
    have h := (transition_mem_unitInterval x).2
    have : 0 < 3 / bumpMass := div_pos (by norm_num) bumpMass_pos
    linarith
  | succ n =>
    rw [iteratedDeriv_succ', transition_deriv]
    have he : (fun x => rawBump x / bumpMass) = fun x => rawBump x * bumpMass⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos bumpMass_pos]
    have hb := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n x) (inv_nonneg.mpr bumpMass_pos.le)
    have hp : (16 : ℝ) ^ n ≤ 16 ^ (n + 1) := by gcongr <;> norm_num
    have hf : (n.factorial : ℝ) ^ 2 ≤ ((n + 1).factorial : ℝ) ^ 2 := by
      gcongr
      omega
    have hA : 3 * bumpMass⁻¹ ≤ 1 + 3 / bumpMass := by rw [div_eq_mul_inv]; linarith
    calc
      _ ≤ (3 * 16 ^ n * (n.factorial : ℝ) ^ 2) * bumpMass⁻¹ := hb
      _ = (3 * bumpMass⁻¹) * 16 ^ n * (n.factorial : ℝ) ^ 2 := by ring
      _ ≤ (1 + 3 / bumpMass) * 16 ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2 := by
        gcongr


end EulerGevreyCutoff

end

section

namespace EulerGevreyFunctions

open EulerGevreyCutoff EulerGevrey
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem product_bound (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb₁ : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R 0 n)
    (hb₂ : ∀ n x, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (3 * A * B) * majorant R 0 n := by
  have hp := sequence_product_majorant R A B hR hA hB 0 0
    (fun k => ‖iteratedFDeriv ℝ k f x‖) (fun k => ‖iteratedFDeriv ℝ k g x‖)
    (fun k => by simpa only [abs_norm] using hb₁ k x)
    (fun k => by simpa only [abs_norm] using hb₂ k x) n
  exact (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
    ((le_abs_self _).trans (by simpa using hp))

theorem linear_composition_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hL : ‖L‖ ≤ C) (hb : ∀ n x, |iteratedDeriv n f x| ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ A * majorant (R * C) 0 n := by
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  have hnorm := (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hnorm
  calc
    _ ≤ |iteratedDeriv n f (L x)| * ‖L‖ ^ n := hnorm
    _ ≤ (A * majorant R 0 n) * C ^ n :=
      mul_le_mul (hb n (L x)) (pow_le_pow_left₀ (norm_nonneg _) hL n)
        (pow_nonneg (norm_nonneg _) n) (mul_nonneg hA (majorant_nonneg R hR 0 n))
    _ = A * majorant (R * C) 0 n := by simp [majorant, mul_pow]; ring

theorem affine_composition_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (a R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hL : ‖L‖ ≤ C) (hb : ∀ n x, |iteratedDeriv n f x| ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f (L y + a)) x‖ ≤ A * majorant (R * C) 0 n := by
  exact linear_composition_bound (fun t => f (t + a))
    (hf.comp (contDiff_id.add contDiff_const)) L R A C hR hA hC hL
    (fun k y => by simpa only [iteratedDeriv_comp_add_const] using hb k (y + a)) n x

theorem finite_product_bound {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ u, ContDiff ℝ ∞ (f i))
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ i ∈ u, ∀ n x, ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∏ i ∈ u, f i y) x‖ ≤
      (3 * A) ^ u.card * majorant R 0 n := by
  induction u using Finset.induction_on generalizing n x with
  | empty =>
    cases n with
    | zero => simp [majorant]
    | succ n => simp [iteratedFDeriv_succ_const, majorant_nonneg R hR]
  | @insert i u hi ih =>
    have hfu : ∀ j ∈ u, ContDiff ℝ ∞ (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hbu : ∀ j ∈ u, ∀ n x, ‖iteratedFDeriv ℝ n (f j) x‖ ≤ A * majorant R 0 n :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have he : (fun y => ∏ j ∈ insert i u, f j y) =
        fun y => f i y * ∏ j ∈ u, f j y := by
      funext y
      rw [Finset.prod_insert hi]
    rw [he, Finset.card_insert_of_notMem hi]
    have hp := product_bound (f i) (fun y => ∏ j ∈ u, f j y)
      (hf i (Finset.mem_insert_self _ _)) (contDiff_prod hfu)
      R A ((3 * A) ^ u.card) hR hA (by positivity)
      (hb i (Finset.mem_insert_self _ _)) (fun k y => ih hfu hbu k y) n x
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hp

end EulerGevreyFunctions

end

section

namespace EulerGevreyInverse

open EulerGevrey Finset
open scoped ContDiff

theorem reciprocal_derivative_recurrence (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x = -(f x)⁻¹ *
      ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv (k + 1) f x * iteratedDeriv (n + 1 - (k + 1)) (fun y => (f y)⁻¹) x := by
  have hi : ContDiff ℝ ∞ (fun y => (f y)⁻¹) := hf.inv hnz
  have he : (fun y => f y * (f y)⁻¹) = fun _ => (1 : ℝ) := by
    funext y
    exact mul_inv_cancel₀ (hnz y)
  have hp := congrArg (fun g : ℝ → ℝ => iteratedDeriv (n + 1) g x) he
  have hmul : (fun y => f y * (f y)⁻¹) = f * (fun y => (f y)⁻¹) := rfl
  rw [hmul] at hp
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hi.contDiffAt.of_le (by simp)),
    sum_range_succ'] at hp
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
    Nat.sub_zero, iteratedDeriv_const, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte] at hp
  have h := congrArg (fun z : ℝ => (f x)⁻¹ * z) hp
  field_simp [hnz x] at h ⊢
  nlinarith

theorem reciprocal_gevrey_shift (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ majorant R 1 n := by
  have hA0 : 0 ≤ A := by linarith
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant A Rc R hA hRc hR 0
    (fun n => if n = 0 then 1 else 0)
    (fun n => |iteratedDeriv n (fun y => (f y)⁻¹) x|) _ _ n
  · intro k
    split_ifs with hk
    · subst k
      simp [majorant]
    · exact majorant_nonneg R hR0 0 k
  · intro k
    cases k with
    | zero => simpa using hb x
    | succ k =>
      rw [reciprocal_derivative_recurrence f hf hnz k x, abs_mul, abs_neg]
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      apply mul_le_mul (hb x) _ (abs_nonneg _) hA0
      calc
        _ ≤ ∑ j ∈ range (k + 1), |((k + 1).choose (j + 1) : ℝ) *
            iteratedDeriv (j + 1) f x *
            iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x| := abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro j _
          have hj : (0 : ℝ) ≤ (k + 1).choose (j + 1) := by positivity
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hc j x) hj)
            (abs_nonneg (iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x))
          simpa only [abs_mul, abs_of_nonneg hj, majorant, Nat.add_zero, mul_assoc] using h

theorem shift_one_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 1 n ≤ R * majorant (4 * R) 0 n := by
  have hnat : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega
  have hn : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hs : ((n : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ n := by
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := by gcongr
      _ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  simp only [majorant, Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_pow, pow_succ]
  have hp := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (pow_nonneg hR n) (mul_nonneg hR (sq_nonneg (n.factorial : ℝ))))
  nlinarith

theorem reciprocal_gevrey (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ R * majorant (4 * R) 0 n := by
  have hR0 : 0 ≤ R := by nlinarith
  exact (reciprocal_gevrey_shift f hf hnz A Rc R hA hRc hR hb hc n x).trans
    (shift_one_bound R hR0 n)

end EulerGevreyInverse

end

section

namespace EulerSpatialCutoffs

open EulerGevrey EulerGevreyCutoff EulerGevreyFunctions EulerSmoothLimit
open scoped ContDiff
open Set

/-- The even one-dimensional bump normalized to have value one at the origin. -/
def normalizedBump (t : ℝ) : ℝ := rawBump t / rawBump 0

theorem normalizedBump_contDiff : ContDiff ℝ ∞ normalizedBump :=
  rawBump_contDiff.div_const _

theorem normalizedBump_zero : normalizedBump 0 = 1 :=
  div_self rawBump_pos_zero.ne'

theorem normalizedBump_even (t : ℝ) : normalizedBump (-t) = normalizedBump t := by
  simp only [normalizedBump, rawBump_even]

theorem normalizedBump_nonneg (t : ℝ) : 0 ≤ normalizedBump t :=
  div_nonneg (rawBump_nonneg t) rawBump_pos_zero.le

theorem normalizedBump_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n normalizedBump t| ≤ (3 / rawBump 0) * majorant 16 0 n := by
  have he : normalizedBump = fun x => rawBump x * (rawBump 0)⁻¹ := by
    funext x
    simp [normalizedBump, div_eq_mul_inv]
  rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos rawBump_pos_zero]
  have h := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n t)
    (inv_nonneg.mpr rawBump_pos_zero.le)
  simpa [majorant, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- A plateau on the unit interval with support inside the interval of radius nine eighths. -/
def outerWindow (t : ℝ) : ℝ := transition (17 + 16 * t) * transition (17 - 16 * t)

theorem outerWindow_contDiff : ContDiff ℝ ∞ outerWindow :=
  (transition_contDiff.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).mul
    (transition_contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem outerWindow_even (t : ℝ) : outerWindow (-t) = outerWindow t := by
  simp [outerWindow, sub_eq_add_neg, mul_comm]

theorem outerWindow_one (t : ℝ) (ht : |t| ≤ 1) : outerWindow t = 1 := by
  have ht' := abs_le.mp ht
  simp [outerWindow, transition_one_of_ge _ (show 1 ≤ 17 + 16 * t by linarith),
    transition_one_of_ge _ (show 1 ≤ 17 - 16 * t by linarith)]

theorem outerWindow_zero (t : ℝ) (ht : 9 / 8 ≤ |t|) : outerWindow t = 0 := by
  rcases le_abs.mp ht with h | h
  · simp [outerWindow, transition_zero_of_le _ (show 17 - 16 * t ≤ -1 by linarith)]
  · simp [outerWindow, transition_zero_of_le _ (show 17 + 16 * t ≤ -1 by linarith)]

theorem outerWindow_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n outerWindow t| ≤
      (3 * (1 + 3 / bumpMass) ^ 2) * majorant 256 0 n := by
  let L : ℝ →L[ℝ] ℝ := (16 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hn : ‖L‖ ≤ 16 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    simp [L, norm_mul]
  have hmass := bumpMass_pos
  have hb : ∀ n t, |iteratedDeriv n transition t| ≤ (1 + 3 / bumpMass) * majorant 16 0 n :=
    fun n t => by simpa [majorant, mul_assoc] using transition_gevrey_bound n t
  have hp := affine_composition_bound transition transition_contDiff L 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num) hn hb
  have hm := affine_composition_bound transition transition_contDiff (-L) 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num)
    (by simpa using hn) hb
  have hf : ContDiff ℝ ∞ (fun y : ℝ => transition (L y + 17)) :=
    transition_contDiff.comp (L.contDiff.add contDiff_const)
  have hg : ContDiff ℝ ∞ (fun y : ℝ => transition ((-L) y + 17)) :=
    transition_contDiff.comp ((-L).contDiff.add contDiff_const)
  have h := product_bound _ _ hf hg 256 (1 + 3 / bumpMass) (1 + 3 / bumpMass)
    (by norm_num) (by positivity) (by positivity) (by norm_num at hp; exact hp)
    (by norm_num at hm; exact hm) n t
  have he : outerWindow = (fun y => transition (L y + 17) * transition ((-L) y + 17)) := by
    funext y
    simp [outerWindow, L, sub_eq_add_neg, add_comm]
  rw [he]
  simpa [L, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, sub_eq_add_neg, add_comm, pow_two, mul_assoc] using h

/-- Product of three copies of a scalar profile at a common coordinate scale. -/
def tensorCutoff (g : ℝ → ℝ) (a : ℝ) (x : Space) : ℝ := ∏ i : Fin 3, g (a * x i)

theorem tensorCutoff_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (tensorCutoff g a) := by
  apply contDiff_prod
  intro i _
  have hc : ContDiff ℝ ∞ (fun y : Space => y i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  exact hg.comp (contDiff_const.mul hc)

theorem tensorCutoff_even (g : ℝ → ℝ) (hg : ∀ t, g (-t) = g t) (a : ℝ) (x : Space) :
    tensorCutoff g a (-x) = tensorCutoff g a x := by
  simp [tensorCutoff, hg]

theorem tensorCutoff_gevrey (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (a R A : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n t, |iteratedDeriv n g t| ≤ A * majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (tensorCutoff g a) x‖ ≤ (3 * A) ^ 3 * majorant (R * a) 0 n := by
  have hL (i : Fin 3) : ‖(a • EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ a := by
    apply (a • EuclideanSpace.proj i : Space →L[ℝ] ℝ).opNorm_le_bound ha
    intro y
    simpa [Real.norm_eq_abs, abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y i) ha
  have hi (i : Fin 3) := linear_composition_bound g hg (a • EuclideanSpace.proj i)
    R A a hR hA ha (hL i) hb
  have h := finite_product_bound (Finset.univ : Finset (Fin 3))
    (fun i (y : Space) => g (a * y i))
    (fun i _ => hg.comp (contDiff_const.mul
      (show ContDiff ℝ ∞ (fun y : Space => y i) from
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff)))
    (R * a) A (mul_nonneg hR ha) hA (fun i _ k y => by
      simpa only [Function.comp_def, smul_apply, smul_eq_mul, PiLp.proj_apply] using hi i k y) n x
  have he : tensorCutoff g a = (fun y : Space => ∏ i : Fin 3, g (a * y i)) := rfl
  rw [he]
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Inner spatial cutoff used to localize the leading oscillatory packet. -/
def innerCutoff : Space → ℝ := tensorCutoff normalizedBump 4

/-- Outer plateau used by the compactly supported mean correction. -/
def outerCutoff : Space → ℝ := tensorCutoff outerWindow 1

theorem innerCutoff_contDiff : ContDiff ℝ ∞ innerCutoff :=
  tensorCutoff_contDiff _ normalizedBump_contDiff _

theorem outerCutoff_contDiff : ContDiff ℝ ∞ outerCutoff :=
  tensorCutoff_contDiff _ outerWindow_contDiff _

theorem innerCutoff_even (x : Space) : innerCutoff (-x) = innerCutoff x :=
  tensorCutoff_even _ normalizedBump_even _ _

theorem outerCutoff_even (x : Space) : outerCutoff (-x) = outerCutoff x :=
  tensorCutoff_even _ outerWindow_even _ _

theorem innerCutoff_nonneg (x : Space) : 0 ≤ innerCutoff x := by
  unfold innerCutoff tensorCutoff
  exact Finset.prod_nonneg (fun i _ => normalizedBump_nonneg _)

theorem innerCutoff_zero : innerCutoff 0 = 1 := by
  simp [innerCutoff, tensorCutoff, normalizedBump_zero]

theorem outerCutoff_one (x : Space) (hx : ‖x‖ ≤ 1) : outerCutoff x = 1 := by
  unfold outerCutoff tensorCutoff
  apply Finset.prod_eq_one
  intro i _
  apply outerWindow_one
  simpa only [one_mul, ← Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx

theorem innerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n innerCutoff x‖ ≤
      (9 / rawBump 0) ^ 3 * majorant 64 0 n := by
  have hpos := rawBump_pos_zero
  have h := tensorCutoff_gevrey _ normalizedBump_contDiff 4 16 (3 / rawBump 0)
    (by norm_num) (by norm_num) (by positivity) normalizedBump_gevrey n x
  simpa only [innerCutoff, show (16 : ℝ) * 4 = 64 by norm_num,
    show (3 : ℝ) * (3 / rawBump 0) = 9 / rawBump 0 by ring] using h

theorem outerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n outerCutoff x‖ ≤
      (9 * (1 + 3 / bumpMass) ^ 2) ^ 3 * majorant 256 0 n := by
  have h := tensorCutoff_gevrey _ outerWindow_contDiff 1 256 (3 * (1 + 3 / bumpMass) ^ 2)
    (by norm_num) (by norm_num) (by positivity) outerWindow_gevrey n x
  simpa only [outerCutoff, mul_one,
    show (3 : ℝ) * (3 * (1 + 3 / bumpMass) ^ 2) = 9 * (1 + 3 / bumpMass) ^ 2 by ring] using h


theorem cube_closed (r : ℝ) : IsClosed (({x : Space | ∀ i, |x i| ≤ r})) := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.abs) continuous_const

theorem norm_sq_le_of_mem_cube (r : ℝ) (hr : 0 ≤ r) (x : Space) (hx : x ∈ ({x : Space | ∀ i, |x i| ≤ r})) :
    ‖x‖ ^ 2 ≤ 3 * r ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 3, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (abs_nonneg (x i)) hr).2 (hx i)
      simpa only [sq_abs] using h
    _ = _ := by simp

theorem tensorCutoff_support (g : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ b) :
    tsupport (tensorCutoff g a) ⊆ ({x : Space | ∀ i, |x i| ≤ b / a}) := by
  apply closure_minimal _ (cube_closed _)
  intro x hx i
  have hgx : g (a * x i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  have h := hg (a * x i) hgx
  rw [abs_mul, abs_of_pos ha] at h
  exact (le_div_iff₀ ha).2 (by nlinarith)

theorem innerCutoff_support : tsupport innerCutoff ⊆ Metric.ball (0 : Space) (1 / 2) := by
  have hs := tensorCutoff_support normalizedBump 4 1 (by norm_num) (fun t ht => by
    have hraw : rawBump t ≠ 0 := fun h => ht (by simp [normalizedBump, h])
    exact abs_le.mpr (rawBump_support (subset_tsupport _ hraw)))
  intro x hx
  have hn := norm_sq_le_of_mem_cube (1 / 4) (by norm_num) x (hs hx)
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem outerCutoff_support : tsupport outerCutoff ⊆ Metric.closedBall (0 : Space) 2 := by
  have hs := tensorCutoff_support outerWindow 1 (9 / 8) (by norm_num) (fun t ht => by
    by_contra h
    exact ht (outerWindow_zero t (le_of_lt (lt_of_not_ge h))))
  intro x hx
  have hc : x ∈ ({x : Space | ∀ i, |x i| ≤ 9 / 8}) := by simpa using hs hx
  have hn := norm_sq_le_of_mem_cube (9 / 8) (by norm_num) x hc
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem innerCutoff_compactSupport : HasCompactSupport innerCutoff := by
  apply (isCompact_closedBall (0 : Space) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
  exact innerCutoff_support.trans Metric.ball_subset_closedBall

theorem outerCutoff_compactSupport : HasCompactSupport outerCutoff :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) outerCutoff_support

end EulerSpatialCutoffs

end

section

namespace EulerPeriodicProfile

open scoped ContDiff
open Real
open EulerGevrey EulerGevreyInverse EulerGevreyFunctions

/-- Explicit smooth periodic profile with a narrow positive derivative peak. -/
def profile (δ t : ℝ) : ℝ := arctan (sin t / (1 + δ - cos t))

/-- Denominator of the derivative of the periodic profile. -/
def denominator (δ t : ℝ) : ℝ := (1 + δ) ^ 2 - 2 * (1 + δ) * cos t + 1

theorem first_denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < 1 + δ - cos t := by
  linarith [cos_le_one t]

theorem denominator_lower (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ) : δ ^ 2 ≤ denominator δ t := by
  have h := mul_nonneg (show 0 ≤ 2 * (1 + δ) by positivity) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  nlinarith

theorem denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < denominator δ t :=
  lt_of_lt_of_le (sq_pos_of_pos hδ) (denominator_lower δ hδ.le t)

theorem profile_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (profile δ) := by
  apply contDiff_arctan.comp
  exact contDiff_sin.div ((contDiff_const.add contDiff_const).sub contDiff_cos)
    (fun t => (first_denominator_pos δ hδ t).ne')

theorem profile_odd (δ t : ℝ) : profile δ (-t) = -profile δ t := by
  simp [profile, neg_div]

theorem profile_periodic (δ : ℝ) : Function.Periodic (profile δ) (2 * π) := by
  intro t
  simp [profile, sin_add_two_pi, cos_add_two_pi]

theorem profile_hasDerivAt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (profile δ) (((1 + δ) * cos t - 1) / denominator δ t) t := by
  have hd := first_denominator_pos δ hδ t
  have he := denominator_pos δ hδ t
  have hs := sin_sq_add_cos_sq t
  have hg : HasDerivAt (fun x => sin x / (1 + δ - cos x))
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) t := by
    have hfun : (sin / ((fun _ : ℝ => 1 + δ) - cos)) =
        (fun x => sin x / (1 + δ - cos x)) := rfl
    have ht := (hasDerivAt_sin t).div
      ((hasDerivAt_const t (1 + δ)).sub (hasDerivAt_cos t)) hd.ne'
    rw [hfun] at ht
    simpa only [sub_neg_eq_add, zero_add, Pi.sub_apply, Pi.div_apply] using
      ht
  have heq : (1 + (sin t / (1 + δ - cos t)) ^ 2)⁻¹ *
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) =
      ((1 + δ) * cos t - 1) / denominator δ t := by
    have hds : (1 + δ - cos t) ^ 2 + sin t ^ 2 = denominator δ t := by
      dsimp [denominator]
      nlinarith
    have hnum : cos t * (1 + δ - cos t) - sin t * sin t = (1 + δ) * cos t - 1 := by
      nlinarith
    rw [hnum]
    field_simp [hd.ne', he.ne']
    rw [hds]
    ring
  exact hg.arctan.congr_deriv (by simpa only [one_div] using heq)

theorem profile_deriv (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (profile δ) t = ((1 + δ) * cos t - 1) / denominator δ t :=
  (profile_hasDerivAt δ hδ t).deriv

theorem profile_deriv_zero (δ : ℝ) (hδ : 0 < δ) : deriv (profile δ) 0 = δ⁻¹ := by
  rw [profile_deriv δ hδ]
  have he : denominator δ 0 = δ ^ 2 := by simp [denominator]; ring
  rw [he, cos_zero, mul_one]
  ring_nf
  field_simp [hδ.ne']

theorem profile_deriv_lower (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : -1 ≤ deriv (profile δ) t := by
  rw [profile_deriv δ hδ, le_div_iff₀ (denominator_pos δ hδ t)]
  have h := mul_pos (show 0 < 1 + δ by linarith) (first_denominator_pos δ hδ t)
  dsimp [denominator]
  nlinarith

theorem profile_deriv_upper (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : deriv (profile δ) t ≤ δ⁻¹ := by
  rw [profile_deriv δ hδ, inv_eq_one_div,
    div_le_div_iff₀ (denominator_pos δ hδ t) hδ]
  have h := mul_nonneg (mul_nonneg (show 0 ≤ 2 + δ by linarith)
    (show 0 ≤ 1 + δ by linarith)) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  nlinarith

theorem profile_mean_zero (δ : ℝ) : ∫ t in (-π)..π, profile δ t = 0 := by
  have he : (fun t => profile δ (-t)) = fun t => -profile δ t := funext (profile_odd δ)
  have hi := intervalIntegral.integral_comp_neg (f := profile δ) (a := -π) (b := π)
  rw [he, intervalIntegral.integral_neg] at hi
  simp only [neg_neg] at hi
  linarith

theorem denominator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (denominator δ) := by
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_cos)).add contDiff_const)

theorem denominator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv (n + 1) (denominator δ) t| ≤ majorant 4 0 (n + 1) := by
  have he : denominator δ = fun t => ((1 + δ) ^ 2 + 1) - (2 * (1 + δ)) * cos t := by
    funext t
    dsimp [denominator]
    ring
  rw [he, iteratedDeriv_const_sub (by omega), iteratedDeriv_neg,
    iteratedDeriv_const_mul_field, abs_neg, abs_mul,
    abs_of_nonneg (show 0 ≤ 2 * (1 + δ) by positivity)]
  have hc := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
    (show 0 ≤ 2 * (1 + δ) by positivity)
  have hp : (4 : ℝ) ≤ 4 ^ (n + 1) := by
    have h : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  have hf : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    nlinarith
  dsimp [majorant]
  nlinarith

theorem denominator_inverse_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (fun t => (denominator δ t)⁻¹) t| ≤
      (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ hδsq).2
    nlinarith
  have hb (t : ℝ) : |(denominator δ t)⁻¹| ≤ (δ ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (denominator_pos δ hδ t))]
    exact inv_anti₀ hδsq (denominator_lower δ hδ.le t)
  have h := reciprocal_gevrey (denominator δ) (denominator_contDiff δ)
    (fun t => (denominator_pos δ hδ t).ne') ((δ ^ 2)⁻¹) 4 (10 * (δ ^ 2)⁻¹)
    hA (by norm_num) (by ring_nf; rfl) hb (denominator_derivative_bound δ hδ.le hδ1) n t
  simpa only [show (4 : ℝ) * (10 * (δ ^ 2)⁻¹) = 40 * (δ ^ 2)⁻¹ by ring] using h

/-- The numerator of the derivative of the explicit periodic profile. -/
def numerator (δ t : ℝ) : ℝ := (1 + δ) * cos t - 1

theorem numerator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (numerator δ) :=
  (contDiff_const.mul contDiff_cos).sub contDiff_const

theorem numerator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv n (numerator δ) t| ≤ 3 := by
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero]
    dsimp [numerator]
    have ht := abs_cos_le_one t
    have h : |(1 + δ) * cos t - 1| ≤ |(1 + δ) * cos t| + |(1 : ℝ)| := abs_sub _ _
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity), abs_one] at h
    nlinarith
  | succ n =>
    have he : numerator δ = fun t => (-1 : ℝ) + (1 + δ) * cos t := by
      funext t
      dsimp [numerator]
      ring
    rw [he, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity)]
    have h := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
      (show 0 ≤ 1 + δ by positivity)
    nlinarith

theorem profile_gevrey (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (profile δ) t| ≤
      (100 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ (sq_pos_of_pos hδ)).2
    nlinarith
  have hB : 1 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hBi : 0 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hAi : 0 ≤ (δ ^ 2)⁻¹ := by positivity
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, majorant, Nat.add_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    have hp := arctan_lt_pi_div_two (sin t / (1 + δ - cos t))
    have hm := neg_pi_div_two_lt_arctan (sin t / (1 + δ - cos t))
    rw [abs_le]
    dsimp [profile]
    constructor <;> nlinarith [pi_le_four]
  | succ n =>
    have hn (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (numerator δ) x‖ ≤
        3 * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      have hp : 1 ≤ (40 * (δ ^ 2)⁻¹) ^ k := one_le_pow₀ hB
      have hf : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by
        have hh : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
        nlinarith
      have hb := numerator_derivative_bound δ hδ.le hδ1 k x
      dsimp [majorant]
      nlinarith
    have hi (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (fun t => (denominator δ t)⁻¹) x‖ ≤
        (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        denominator_inverse_bound δ hδ hδ1 k x
    have hp := product_bound (numerator δ) (fun t => (denominator δ t)⁻¹)
      (numerator_contDiff δ) ((denominator_contDiff δ).inv (fun t => (denominator_pos δ hδ t).ne'))
      (40 * (δ ^ 2)⁻¹) 3 (10 * (δ ^ 2)⁻¹) hBi (by norm_num) (by positivity) hn hi n t
    have he : deriv (profile δ) = fun t => numerator δ t * (denominator δ t)⁻¹ := by
      funext t
      rw [profile_deriv δ hδ]
      rfl
    rw [iteratedDeriv_succ', he]
    have hm : majorant (40 * (δ ^ 2)⁻¹) 0 n ≤ majorant (40 * (δ ^ 2)⁻¹) 0 (n + 1) := by
      unfold majorant
      apply mul_le_mul
      · exact pow_le_pow_right₀ hB (by omega)
      · gcongr; omega
      · positivity
      · positivity
    have hp' : |iteratedDeriv n (fun t => numerator δ t * (denominator δ t)⁻¹) t| ≤
        (90 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        show (3 : ℝ) * 3 * (10 * (δ ^ 2)⁻¹) = 90 * (δ ^ 2)⁻¹ by ring] using hp
    exact hp'.trans (mul_le_mul (by nlinarith) hm (majorant_nonneg _ hBi _ _)
      (by positivity))

end EulerPeriodicProfile

end

section

namespace EulerEnergyBootstrap

open Set Real

theorem radius_bounds (C B Δ ρ₀ S R₀ : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hΔ : 0 ≤ Δ) (hρ : 0 < ρ₀) (_hS : 0 ≤ S) (hR : 0 ≤ R₀)
    (hdecay : 2 * C * (B + Δ) * S ≤ ρ₀ / 2) (hscale : ρ₀ * R₀ ≤ 1)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    ρ₀ / 2 ≤ ρ₀ - 2 * C * (B + Δ) * t ∧
      0 < ρ₀ - 2 * C * (B + Δ) * t ∧
      (ρ₀ - 2 * C * (B + Δ) * t) * R₀ ≤ 1 := by
  have hl := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2 * C * (B + Δ) by positivity)
  have hn := mul_nonneg (show 0 ≤ 2 * C * (B + Δ) by positivity) ht.1
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

theorem shrinking_radius_cancels_loss (C B Δ ρ R₀ X : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) (hρ : 0 < ρ)
    (hR : 0 ≤ R₀) (hscale : ρ * R₀ ≤ 1) (hX : X ≤ Δ) :
    (-2 * C * (B + Δ)) / ρ + C * (ρ⁻¹ + R₀) * (B + X) ≤ 0 := by
  have hinv : R₀ ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hρ).2 (by nlinarith)
  have hp : C * (ρ⁻¹ + R₀) * (B + X) ≤ C * (ρ⁻¹ + R₀) * (B + Δ) := by
    gcongr
  have hq : C * (ρ⁻¹ + R₀) * (B + Δ) ≤ 2 * C * (B + Δ) / ρ := by
    calc
      _ ≤ C * (ρ⁻¹ + ρ⁻¹) * (B + Δ) := by gcongr
      _ = _ := by ring
  have hneg : (-2 * C * (B + Δ)) / ρ = -(2 * C * (B + Δ) / ρ) := by ring
  rw [hneg]
  linarith



end EulerEnergyBootstrap

end

section

namespace EulerWeightedConvolution

open Finset EulerPacketWeights

theorem triangular_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, a (l + 1) * b (n - l)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  let e : (Σ _n : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 + 1, p.1 - p.2)
  have hinj : Set.InjOn e ((range (N + 1)).sigma range) := by
    rintro ⟨n, l⟩ hx ⟨n', l'⟩ hy h
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hl : l < n := mem_range.mp hx'.2
    have hl' : l' < n' := mem_range.mp hy'.2
    have heq : l + 1 = l' + 1 ∧ n - l = n' - l' := Prod.mk.inj h
    have hll : l = l' := by omega
    have hnn : n = n' := by omega
    subst l'
    subst n'
    rfl
  have himg : Finset.image e ((range (N + 1)).sigma range) ⊆
      (range (N + 1)) ×ˢ (range (N + 1)) := by
    intro p hp
    obtain ⟨⟨n, l⟩, hx, rfl⟩ := mem_image.mp hp
    have hx' := mem_sigma.mp hx
    have hn := mem_range.mp hx'.1
    have hl := mem_range.mp hx'.2
    change n < N + 1 at hn
    change l < n at hl
    simp only [e, mem_product, mem_range]
    omega
  calc
    _ = ∑ p ∈ (range (N + 1)).sigma range, a (p.2 + 1) * b (p.1 - p.2) :=
      sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (range (N + 1)) ×ˢ (range (N + 1)), a p.1 * b p.2 :=
      sum_le_sum_of_injOn e hinj himg (fun _ _ => le_rfl)
        (fun p _ _ => mul_nonneg (ha p.1) (hb p.2))
    _ = _ := by rw [sum_product, ← sum_mul_sum]

theorem external_commutator_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ) (hl : 1 ≤ l)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) * a * b ≤
      ρ⁻¹ * (weight ρ l * a) * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * b) := by
  have hden : 0 < weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) := by
    have h1 := weight_pos hρ l
    have h2 := weight_pos hρ (j + 1)
    positivity
  have h := (div_le_iff₀ hden).mp (external_commutator_ratio_le ρ hρ j l hl)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hp

/-- The full truncated external-commutator convolution has a constant independent of the cutoff. -/
theorem external_commutator_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n,
      weight ρ n * (n.choose (l + 1) : ℝ) * a (l + 1) * b (n - l)) ≤
      ρ⁻¹ * (∑ l ∈ range (N + 1), weight ρ l * a l) *
        (∑ j ∈ range (N + 1), (j : ℝ) * weight ρ j * b j) := by
  have hp : ∀ n, 0 ≤ weight ρ n := fun n => (weight_pos hρ n).le
  calc
    _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
        ρ⁻¹ * (weight ρ (l + 1) * a (l + 1)) *
          (((n - l : ℕ) : ℝ) * weight ρ (n - l) * b (n - l)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have hln := mem_range.mp hl
      have h := external_commutator_term ρ hρ (n - (l + 1)) (l + 1) (by omega)
        (a (l + 1)) (b (n - l)) (ha _) (hb _)
      have h1 : n - (l + 1) + (l + 1) = n := by omega
      have h2 : n - (l + 1) + 1 = n - l := by omega
      simpa only [h1, h2] using h
    _ = ρ⁻¹ * (∑ n ∈ range (N + 1), ∑ l ∈ range n,
        (weight ρ (l + 1) * a (l + 1)) *
          (((n - l : ℕ) : ℝ) * weight ρ (n - l) * b (n - l))) := by
      simp only [mul_assoc, mul_sum]
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hρ.le)
      exact triangular_sum_le_product N (fun l => weight ρ l * a l)
        (fun j => (j : ℝ) * weight ρ j * b j)
        (fun l => mul_nonneg (hp l) (ha l))
        (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (hp j)) (hb j))

theorem shifted_triangular_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range N, ∑ l ∈ range (n + 1), a l * b (n - l + 1)) ≤
      2 * (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  have hi (n : ℕ) : (∑ l ∈ range (n + 1), a l * b (n - l + 1)) =
      (∑ l ∈ range n, a (l + 1) * b (n - l)) + a 0 * b (n + 1) := by
    rw [sum_range_succ']
    congr 1
    apply sum_congr rfl
    intro l hl
    have : n - (l + 1) + 1 = n - l := by have := mem_range.mp hl; omega
    rw [this]
  simp_rw [hi]
  rw [sum_add_distrib]
  have hrest : (∑ n ∈ range N, ∑ l ∈ range n, a (l + 1) * b (n - l)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
    apply le_trans _ (triangular_sum_le_product N a b ha hb)
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro n _ _
    exact sum_nonneg (fun l _ => mul_nonneg (ha _) (hb _))
  have ha0 : a 0 ≤ ∑ l ∈ range (N + 1), a l :=
    single_le_sum (fun l _ => ha l) (mem_range.mpr (by omega))
  have hsum : (∑ n ∈ range N, b (n + 1)) ≤ ∑ j ∈ range (N + 1), b j := by
    rw [sum_range_succ']
    linarith [hb 0]
  have hfirst : (∑ n ∈ range N, a 0 * b (n + 1)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
    rw [← mul_sum]
    exact mul_le_mul ha0 hsum (sum_nonneg (fun n _ => hb _))
      (sum_nonneg (fun n _ => ha _))
  nlinarith

theorem shifted_source_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) * a * b ≤
      (weight ρ l * a) * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * b) := by
  have hden : 0 < weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) := by
    have h1 := weight_pos hρ l
    have h2 := weight_pos hρ (j + 1)
    positivity
  have h := (div_le_iff₀ hden).mp (shifted_source_ratio_le_one ρ hρ.ne' j l)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb
  simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using hp

/-- The pressure-source derivative shift sums with a cutoff-independent constant. -/
theorem shifted_source_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range N, ∑ l ∈ range (n + 1),
      ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * (n.choose l : ℝ) * a l * b (n - l + 1)) ≤
      2 * (∑ l ∈ range (N + 1), weight ρ l * a l) *
        (∑ j ∈ range (N + 1), (j : ℝ) * weight ρ j * b j) := by
  have hp : ∀ n, 0 ≤ weight ρ n := fun n => (weight_pos hρ n).le
  calc
    _ ≤ ∑ n ∈ range N, ∑ l ∈ range (n + 1),
        (weight ρ l * a l) * (((n - l + 1 : ℕ) : ℝ) * weight ρ (n - l + 1) * b (n - l + 1)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have hln := mem_range.mp hl
      have h := shifted_source_term ρ hρ (n - l) l (a l) (b (n - l + 1)) (ha _) (hb _)
      have he : n - l + l = n := by omega
      simpa only [he] using h
    _ ≤ _ := shifted_triangular_sum_le_product N (fun l => weight ρ l * a l)
      (fun j => (j : ℝ) * weight ρ j * b j)
      (fun l => mul_nonneg (hp l) (ha l))
      (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (hp j)) (hb j))

end EulerWeightedConvolution

end

section

namespace EulerWeightedEnergy

open Finset EulerPacketWeights

theorem weight_hasDerivAt (ρ : ℝ → ℝ) (ρ' t : ℝ) (hρ : HasDerivAt ρ ρ' t)
    (hpos : 0 < ρ t) (n : ℕ) :
    HasDerivAt (fun s => weight (ρ s) n)
      ((ρ' / ρ t) * (n : ℝ) * weight (ρ t) n) t := by
  have he : ((n : ℝ) * (ρ t) ^ (n - 1) * ρ') / (n.factorial : ℝ) ^ 2 =
      (ρ' / ρ t) * (n : ℝ) * weight (ρ t) n := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [weight, Nat.succ_sub_one, pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp [hpos.ne', factorial_cast_ne_zero]
  exact ((hρ.pow n).div_const ((n.factorial : ℝ) ^ 2)).congr_deriv he


end EulerWeightedEnergy

end

section

namespace EulerGraphPullback

open InnerProductSpace Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The linear graph carrying the oscillating phase. -/
def graphMap (k : ℝ) (m : E) : E →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.id ℝ E).prod (k • toDual ℝ E m)

/-- The constant lifted differential direction associated with a spatial vector. -/
def liftedDirection (κ : ℝ) (m : E) : E →L[ℝ] (E × ℝ) :=
  (κ • ContinuousLinearMap.id ℝ E).prod (toDual ℝ E m)

theorem graphMap_apply (k : ℝ) (m v : E) : graphMap k m v = (v, k * ⟪m, v⟫_ℝ) := rfl

theorem liftedDirection_apply (κ : ℝ) (m v : E) :
    liftedDirection κ m v = (κ • v, ⟪m, v⟫_ℝ) := rfl

theorem graph_direction_identity (k κ : ℝ) (hκ : k * κ = 1) (m v : E) :
    graphMap k m v = k • liftedDirection κ m v := by
  rw [graphMap_apply, liftedDirection_apply]
  ext <;> simp [smul_smul, hκ]

theorem graph_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × ℝ → F) (k κ : ℝ) (hκ : k * κ = 1) (m x v : E)
    (hf : DifferentiableAt ℝ f (graphMap k m x)) :
    fderiv ℝ (fun y => f (graphMap k m y)) x v =
      k • fderiv ℝ f (graphMap k m x) (liftedDirection κ m v) := by
  have h : HasFDerivAt (fun y => f (graphMap k m y))
      ((fderiv ℝ f (graphMap k m x)).comp (graphMap k m)) x :=
    hf.hasFDerivAt.comp x (graphMap k m).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, graph_direction_identity k κ hκ m v, map_smul]

/-- A smooth vector field with symmetric derivative has a genuine smooth scalar potential. -/
theorem smooth_gradient_potential (v : E → E) (hv : ContDiff ℝ ∞ v)
    (hsymm : ∀ x a b, ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ) :
    ∃ p : E → ℝ, ContDiff ℝ ∞ p ∧ ∀ x, gradient p x = v x := by
  let form : E → E →L[ℝ] ℝ := fun x => toDual ℝ E (v x)
  have hω : ContDiff ℝ ∞ form := (toDual ℝ E).toContinuousLinearEquiv.contDiff.comp hv
  have hωd (x : E) : HasFDerivAt form
      ((toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ v x)) x :=
    (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
      ((hv.differentiable (by simp)) x).hasFDerivAt
  obtain ⟨p, hp⟩ := (convex_univ : Convex ℝ (univ : Set E)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hω.differentiable (by simp)).differentiableOn (fun x _ a b => by
      rw [(hωd x).fderiv]
      change ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ
      exact hsymm x a b)
  have hp' (x : E) : HasFDerivAt p (form x) x := hp x (mem_univ _)
  have hpd : Differentiable ℝ p := fun x => (hp' x).differentiableAt
  have hpf : fderiv ℝ p = form := funext (fun x => (hp' x).fderiv)
  refine ⟨p, ?_, ?_⟩
  · rw [contDiff_infty_iff_fderiv]
    exact ⟨hpd, by rwa [hpf]⟩
  · intro x
    rw [gradient, (hp' x).fderiv]
    exact (toDual ℝ E).symm_apply_apply (v x)

/-- Closedness for the lifted derivatives becomes a scalar pressure potential on the graph. -/
theorem lifted_closed_field_has_graph_potential (p : E × ℝ → E)
    (hp : ContDiff ℝ ∞ p) (k κ : ℝ) (hκ : k * κ = 1) (m : E)
    (hclosed : ∀ z a b,
      ⟪fderiv ℝ p z (liftedDirection κ m a), b⟫_ℝ =
        ⟪fderiv ℝ p z (liftedDirection κ m b), a⟫_ℝ) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = κ • p (graphMap k m x) := by
  let v : E → E := fun x => κ • p (graphMap k m x)
  have hv : ContDiff ℝ ∞ v := (hp.comp (graphMap k m).contDiff).const_smul κ
  apply smooth_gradient_potential v hv
  intro x a b
  have hg := (hp.differentiable (by simp)) (graphMap k m x)
  have hd : fderiv ℝ v x = κ • fderiv ℝ (fun y => p (graphMap k m y)) x := by
    exact ((hg.comp x (graphMap k m).differentiableAt).hasFDerivAt.const_smul κ).fderiv
  rw [hd]
  simp only [smul_apply, real_inner_smul_left, graph_fderiv p k κ hκ m x a hg,
    graph_fderiv p k κ hκ m x b hg]
  rw [hclosed]

end EulerGraphPullback

end

section

namespace EulerBreakdownCriterion

open Filter Set EulerSmoothLimit
open scoped Topology

theorem no_escape_near_compact_trajectory
    {E : Type*} [NormedAddCommGroup E]
    (reference : ℝ → E) (samples : ℕ → E) (times errors : ℕ → ℝ) (S : ℝ)
    (hc : ContinuousOn reference (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S)
    (he : Tendsto errors atTop (nhds 0))
    (hd : ∀ᶠ n in atTop, ‖samples n - reference (times n)‖ ≤ errors n) :
    ¬ Tendsto (fun n => ‖samples n‖) atTop atTop := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  intro hg
  have hε : ∀ᶠ n in atTop, errors n < 1 := he.eventually (gt_mem_nhds (by norm_num))
  have hlarge : ∀ᶠ n in atTop, C + 2 ≤ ‖samples n‖ :=
    hg.eventually (eventually_ge_atTop (C + 2))
  obtain ⟨n, hnε, hnlarge, hnd⟩ := (hε.and (hlarge.and hd)).exists
  have hnorm : ‖samples n‖ ≤ ‖samples n - reference (times n)‖ + ‖reference (times n)‖ := by
    calc
      _ = ‖(samples n - reference (times n)) + reference (times n)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have href := hC (times n) (ht n)
  have herr := hnd
  linarith


end EulerBreakdownCriterion

end

section

namespace EulerDeformationVolume

open Matrix Set MeasureTheory

/-- Jacobi's formula along the three-dimensional deformation equation, including
singular matrices; no inverse determinant is used. -/
theorem determinant_hasDerivAt (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (hF : ∀ i j, HasDerivAt (fun s => F s i j) ((M t * F t) i j) t) :
    HasDerivAt (fun s => (F s).det) ((M t).trace * (F t).det) t := by
  have h := (((((hF 0 0).mul (hF 1 1)).mul (hF 2 2)).sub
    (((hF 0 0).mul (hF 1 2)).mul (hF 2 1))).sub
    (((hF 0 1).mul (hF 1 0)).mul (hF 2 2))).add
    (((hF 0 1).mul (hF 1 2)).mul (hF 2 0))
  have h' := (h.add (((hF 0 2).mul (hF 1 0)).mul (hF 2 1))).sub
    (((hF 0 2).mul (hF 1 1)).mul (hF 2 0))
  have hd := h'.congr_deriv (g' := (M t).trace * (F t).det) (by
    simp only [Pi.mul_apply, mul_apply, Fin.sum_univ_three, trace, diag, det_fin_three]
    ring)
  convert hd using 1 <;> first | rfl | (funext s; exact det_fin_three (F s))


section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bijective differentiable map with unit Jacobian preserves Lebesgue measure. -/
theorem measurePreserving_of_det_one (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (F : E → E →L[ℝ] E)
    (hf : ∀ x, HasFDerivAt f (F x) x) (hbij : Function.Bijective f)
    (hdet : ∀ x, (F x).det = 1) : MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable, ?_⟩
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := (univ : Set E)) (f' := F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [hdet, abs_one, ENNReal.ofReal_one, Measure.restrict_univ,
    image_univ, hbij.2.range_eq] at hm
  change Measure.map f (μ.withDensity 1) = μ at hm
  rwa [withDensity_one] at hm

end ChangeOfVariables

end EulerDeformationVolume

end

section

namespace EulerCylinderGraphTrace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open Set
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (0 < period)] [CompleteSpace F] in
theorem angular_hasDerivAt (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : Vector3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x, (s : AddCircle period)))
      (fieldDerivative period (0, 1) f (x, (t : AddCircle period))) t := by
  have hd := ((hf 0).differentiable (by simp) (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have he := fderiv_localFieldLift_cover period f (x, t)
  change fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0 =
    fderiv ℝ (localFieldLift period f 0) (x, t) at he
  change HasDerivAt _ ((fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0) (0, 1)) t
  rw [he]
  simpa [Function.comp_def, localFieldLift] using hd

/-- Point evaluation in the periodic coordinate costs one angular derivative,
with a bound independent of the chosen phase. -/
theorem cylinder_pointwise_trace (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : Vector3) (θ : AddCircle period) :
    ‖f (x, θ)‖ ^ 2 ≤
      (2 / period) * (∫ s : AddCircle period, ‖f (x, s)‖ ^ 2) +
      (2 * period) * (∫ s : AddCircle period,
        ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2) := by
  have hT : 0 < period := Fact.out
  let θ₀ := AddCircle.equivIco period 0 θ
  have hθ : (θ₀ : ℝ) ∈ Icc 0 period := by
    have hh := θ₀.property
    simp only [zero_add] at hh
    exact ⟨hh.1, hh.2.le⟩
  have hcont : Continuous (fun s : ℝ => fieldDerivative period (0, 1) f
      (x, (s : AddCircle period))) := by
    exact (smoothField_continuous period _
      (fieldDerivative_smooth period (0, 1) f hf)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' period))
  have h := EulerIntervalTrace.pointwise_H1_trace
    (fun s : ℝ => f (x, (s : AddCircle period)))
    (fun s : ℝ => fieldDerivative period (0, 1) f (x, (s : AddCircle period)))
    0 period hT hcont.continuousOn (fun s _ => angular_hasDerivAt period f hf x s)
    θ₀ hθ
  have hcoe : ((θ₀ : ℝ) : AddCircle period) = θ := AddCircle.coe_equivIco
  rw [hcoe] at h
  have hfi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖f (x, s)‖ ^ 2)
  have hdi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2)
  simp only [zero_add] at hfi hdi
  simpa only [sub_zero, hfi, hdi] using h

/-- Pullback to any continuous phase graph preserves square integrability.
The estimate has no dependence on the phase frequency. -/
theorem graph_memLp_and_energy_bound (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : MemLp f 2 (liftMeasure period))
    (hdL2 : MemLp (fieldDerivative period (0, 1) f) 2 (liftMeasure period))
    (θ : Vector3 → AddCircle period) (hθ : Continuous θ) :
    MemLp (fun x => f (x, θ x)) 2 volume ∧
      (∫ x : Vector3, ‖f (x, θ x)‖ ^ 2) ≤
        (2 / period) * (∫ z, ‖f z‖ ^ 2 ∂liftMeasure period) +
        (2 * period) * (∫ z, ‖fieldDerivative period (0, 1) f z‖ ^ 2
          ∂liftMeasure period) := by
  have hfc : Continuous (fun x => f (x, θ x)) :=
    (smoothField_continuous period f hf).comp (continuous_id.prodMk hθ)
  have hfint := hfL2.norm.integrable_sq
  have hdint := hdL2.norm.integrable_sq
  have hi := (hfint.integral_prod_left.const_mul (2 / period)).add
    (hdint.integral_prod_left.const_mul (2 * period))
  have hgraph : Integrable (fun x => ‖f (x, θ x)‖ ^ 2) volume := by
    apply hi.mono' (hfc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖f (x, θ x)‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (x, θ x)‖)]
    exact cylinder_pointwise_trace period f hf x (θ x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mpr hgraph, ?_⟩
  have hbound := integral_mono hgraph hi (fun x => cylinder_pointwise_trace period f hf x (θ x))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hfint.integral_prod_left.const_mul (2 / period))
    (hdint.integral_prod_left.const_mul (2 * period)), integral_const_mul, integral_const_mul,
    integral_integral hfint, integral_integral hdint] at hbound
  exact hbound

end EulerCylinderGraphTrace

end

section

namespace EulerWeightedPressure

open Finset EulerPacketWeights EulerWeightedConvolution EulerGevrey

theorem lower_triangle_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, a (l + 1) * b (n - (l + 1))) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  let e : (Σ _n : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 + 1, p.1 - (p.2 + 1))
  have hinj : Set.InjOn e ((range (N + 1)).sigma range) := by
    rintro ⟨n, l⟩ hx ⟨n', l'⟩ hy h
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hl : l < n := mem_range.mp hx'.2
    have hl' : l' < n' := mem_range.mp hy'.2
    have heq : l + 1 = l' + 1 ∧ n - (l + 1) = n' - (l' + 1) := Prod.mk.inj h
    have hll : l = l' := by omega
    have hnn : n = n' := by omega
    subst l'
    subst n'
    rfl
  have himg : Finset.image e ((range (N + 1)).sigma range) ⊆
      (range (N + 1)) ×ˢ (range (N + 1)) := by
    intro p hp
    obtain ⟨⟨n, l⟩, hx, rfl⟩ := mem_image.mp hp
    have hx' := mem_sigma.mp hx
    have hn := mem_range.mp hx'.1
    have hl := mem_range.mp hx'.2
    change n < N + 1 at hn
    change l < n at hl
    simp only [e, mem_product, Finset.mem_range]
    omega
  calc
    _ = ∑ p ∈ (range (N + 1)).sigma range, a (p.2 + 1) * b (p.1 - (p.2 + 1)) :=
      sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (range (N + 1)) ×ˢ (range (N + 1)), a p.1 * b p.2 :=
      sum_le_sum_of_injOn e hinj himg (fun _ _ => le_rfl)
        (fun p _ _ => mul_nonneg (ha p.1) (hb p.2))
    _ = _ := by rw [sum_product, ← sum_mul_sum]

theorem geometric_lower_triangle (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (N : ℕ) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, q ^ (l + 1) * b (n - (l + 1))) ≤
      (2 * q) * ∑ j ∈ range (N + 1), b j := by
  let a : ℕ → ℝ := fun n => if n = 0 then 0 else q ^ n
  have ha : ∀ n, 0 ≤ a n := fun n => by dsimp [a]; split <;> positivity
  have h := lower_triangle_sum_le_product N a b ha hb
  have hsum : (∑ l ∈ range (N + 1), a l) ≤ 2 * q := by
    rw [sum_range_succ']
    simpa [a] using geometric_tail_le_two_mul q hq hhalf N
  simp only [a, Nat.add_one_ne_zero, ↓reduceIte] at h
  exact h.trans (mul_le_mul_of_nonneg_right hsum (sum_nonneg (fun j _ => hb j)))

theorem shifted_weight_kernel (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (j l : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) *
      (Rc ^ l * (l.factorial : ℝ) ^ 2) * Z ≤
    (ρ * Rc) ^ l * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * Z) := by
  have h := shifted_source_term ρ hρ j l (Rc ^ l * (l.factorial : ℝ) ^ 2) Z
    (by positivity) hZ
  have hw : weight ρ l * (Rc ^ l * (l.factorial : ℝ) ^ 2) = (ρ * Rc) ^ l := by
    unfold weight
    rw [mul_pow]
    field_simp [factorial_cast_ne_zero]
  simpa only [hw] using h

/-- A shifted Gevrey inverse estimate whose constant is independent of truncation.
The positive-order coefficient terms are absorbed, rather than accumulated with order. -/
theorem shifted_weighted_inverse (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hM : 1 ≤ M) (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (N : ℕ) (A F Z : ℕ → ℝ) (_hF : ∀ n, 0 ≤ F n) (hZ : ∀ n, 0 ≤ Z n)
    (hA : ∀ l, 1 ≤ l → l ≤ N → A l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hrec : ∀ n ≤ N, Z n ≤ M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)))) :
    (∑ n ∈ range (N + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * Z n) ≤
      2 * M * ∑ n ∈ range (N + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * F n := by
  let v : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1)
  have hv : ∀ n, 0 ≤ v n := fun n => mul_nonneg (Nat.cast_nonneg _) (weight_pos hρ _).le
  have hq : 0 ≤ ρ * Rc := mul_nonneg hρ.le hRc
  have hhalf : ρ * Rc ≤ 1 / 2 := by nlinarith
  have hcomm : (∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) ≤
      (2 * (ρ * Rc)) * ∑ j ∈ range (N + 1), v j * Z j := by
    calc
      _ = ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          v n * (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)) := by
        simp only [mul_sum, mul_assoc]
      _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          (ρ * Rc) ^ (l + 1) * (v (n - (l + 1)) * Z (n - (l + 1))) := by
        apply sum_le_sum
        intro n hn
        apply sum_le_sum
        intro l hl
        have hln := mem_range.mp hl
        have hnN : n ≤ N := by have := mem_range.mp hn; omega
        have hcoeff := hA (l + 1) (by omega) (by omega)
        have h1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff
            (mul_nonneg (hv n) (Nat.cast_nonneg (n.choose (l + 1))))) (hZ (n - (l + 1)))
        have h2 := shifted_weight_kernel ρ Rc hρ hRc (n - (l + 1)) (l + 1)
          (Z (n - (l + 1))) (hZ _)
        have he : n - (l + 1) + (l + 1) = n := by omega
        dsimp [v] at h1 ⊢
        exact h1.trans (by simpa only [he] using h2)
      _ ≤ _ := geometric_lower_triangle (ρ * Rc) hq hhalf N
        (fun j => v j * Z j) (fun j => mul_nonneg (hv j) (hZ j))
  have hs := sum_le_sum (s := range (N + 1)) (fun n hn =>
    mul_le_mul_of_nonneg_left (hrec n (by have := mem_range.mp hn; omega)) (hv n))
  have hsumid : (∑ n ∈ range (N + 1), v n * (M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))))) =
      M * ((∑ n ∈ range (N + 1), v n * F n) +
        ∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
          (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) := by
    simp only [mul_add, sum_add_distrib, mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hsumid] at hs
  have hzsum : 0 ≤ ∑ n ∈ range (N + 1), v n * Z n :=
    sum_nonneg (fun n _ => mul_nonneg (hv n) (hZ n))
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hzsum
  have hcomm' := mul_le_mul_of_nonneg_left hcomm (show 0 ≤ M by linarith)
  change (∑ n ∈ range (N + 1), v n * Z n) ≤ 2 * M * ∑ n ∈ range (N + 1), v n * F n
  nlinarith

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerJetProductBounds


end EulerWeightedPressure

end

end
