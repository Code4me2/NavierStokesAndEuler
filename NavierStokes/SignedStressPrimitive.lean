import NavierStokes.IntegratedMeanBalances
import NavierStokes.WeightedRadialPrimitive
import NavierStokes.RadialPullback

/-!
# The actual compact signed-stress primitive

A positive normalized bump is constructed in a chosen interior slow patch.
Subtracting its exact weighted moment makes the negative radial primitive
compact. The physical construction is normalized by the physical scale.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.SignedStressPrimitive

structure Patch where
  a : ℝ
  b : ℝ
  left : ℝ
  right : ℝ
  a_pos : 0 < a
  a_lt_left : a < left
  left_lt_right : left < right
  right_lt_b : right < b

theorem Patch.a_lt_b (P : Patch) : P.a < P.b :=
  P.a_lt_left.trans (P.left_lt_right.trans P.right_lt_b)

theorem Patch.left_pos (P : Patch) : 0 < P.left := P.a_pos.trans P.a_lt_left

noncomputable def density (P : Patch) : ℝ → ℝ :=
  PressureStream.rho P.left P.right P.left_lt_right

theorem density_contDiff (P : Patch) : ContDiff ℝ ∞ (density P) :=
  PressureStream.rho_contDiff _ _ _

theorem density_support (P : Patch) : support (density P) ⊆ Icc P.left P.right :=
  PressureStream.rho_support _ _ _

theorem density_integral (P : Patch) : (∫ r, density P r) = 1 := PressureStream.rho_integral _ _ _


noncomputable def densityLift (P : Patch) (z : ℝ × ℝ) : ℝ := density P z.1

theorem densityLift_contDiff (P : Patch) : ContDiff ℝ ∞ (densityLift P) :=
  (density_contDiff P).comp contDiff_fst

theorem densityLift_supported (P : Patch) :
    RadialAlias.RadiallySupported P.left P.right (densityLift P) :=
  fun _ h => density_support P h

noncomputable def cutoff (P : Patch) (r : ℝ) : ℝ :=
  TransportPrimitive.pastIntegral 0 (0 : ℝ) (densityLift P) (r, 0)

theorem cutoff_contDiff (P : Patch) : ContDiff ℝ ∞ (cutoff P) :=
  (TransportPrimitive.pastIntegral_contDiff (densityLift_contDiff P) (densityLift_supported P)).comp
    (contDiff_id.prodMk contDiff_const)

theorem cutoff_total (P : Patch) (r : ℝ) :
    TransportPrimitive.totalIntegral 0 (0 : ℝ) (densityLift P) (r, 0) = 1 := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval
    (densityLift_contDiff P).continuous (densityLift_supported P)]
  simp only [densityLift]
  have h := IntegratedMeanBalances.radialMoment_eq_interval
    (densityLift_contDiff P).continuous (densityLift_supported P) 0 0
  simp only [IntegratedMeanBalances.radialMoment, IntegratedMeanBalances.moment,
    densityLift, pow_zero, one_mul, density_integral] at h
  exact h.symm

theorem cutoff_zero (P : Patch) {r : ℝ} (hr : r ≤ P.left) : cutoff P r = 0 :=
  TransportPrimitive.pastIntegral_eq_zero_of_le
    (densityLift_contDiff P).continuous (densityLift_supported P) (r, 0) hr

theorem cutoff_one (P : Patch) {r : ℝ} (hr : P.right ≤ r) : cutoff P r = 1 := by
  change TransportPrimitive.pastIntegral 0 (0 : ℝ) (densityLift P) (r, 0) = 1
  rw [TransportPrimitive.pastIntegral_eq_total_of_ge (densityLift_supported P) (r, 0) hr,
    cutoff_total]

theorem cutoff_hasDerivAt (P : Patch) (r : ℝ) : HasDerivAt (cutoff P) (density P r) r := by
  have hs := TransportPrimitive.pastIntegral_contDiff (M := 0) (v := (0 : ℝ))
    (densityLift_contDiff P) (densityLift_supported P)
  have hd := ((hs.differentiable (by simp)) (r, 0)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r (0 : ℝ)))
  have ht := TransportPrimitive.transport_pastIntegral (M := 0) (v := (0 : ℝ))
    (densityLift_contDiff P) (densityLift_supported P) (r, 0)
  simp only [TransportPrimitive.fixedDeriv, zero_smul, densityLift] at ht
  unfold cutoff
  simpa only [ht, Function.comp_def, id_eq] using hd

theorem cutoff_deriv (P : Patch) (r : ℝ) : deriv (cutoff P) r = density P r :=
  (cutoff_hasDerivAt P r).deriv

noncomputable def inversePower (P : Patch) (e : ℕ) (r : ℝ) : ℝ :=
  ((RadialPullback.positiveRadius (P.a / 4) r) ^ e)⁻¹

theorem inversePower_contDiff (P : Patch) (e : ℕ) : ContDiff ℝ ∞ (inversePower P e) :=
  ((RadialPullback.positiveRadius_contDiff _).pow e).inv
    (fun r => pow_ne_zero _ (RadialPullback.positiveRadius_pos (by linarith [P.a_pos]) r).ne')


theorem inversePower_eq (P : Patch) (e : ℕ) {r : ℝ} (hr : P.a ≤ r) :
    inversePower P e r = (r ^ e)⁻¹ := by
  unfold inversePower
  rw [RadialPullback.positiveRadius_eq_self (by linarith [P.a_pos]) (by linarith [P.a_pos])]

noncomputable def momentDensity (P : Patch) (e : ℕ) (r : ℝ) : ℝ := inversePower P e r * density P r

theorem momentDensity_contDiff (P : Patch) (e : ℕ) : ContDiff ℝ ∞ (momentDensity P e) :=
  (inversePower_contDiff P e).mul (density_contDiff P)


theorem momentDensity_support (P : Patch) (e : ℕ) : support (momentDensity P e) ⊆ Icc P.left P.right :=
  fun _ h => density_support P (right_ne_zero_of_mul h)

theorem weighted_momentDensity (P : Patch) (e : ℕ) (r : ℝ) :
    r ^ e * momentDensity P e r = density P r := by
  by_cases h : density P r = 0
  · simp [momentDensity, h]
  have hr := density_support P h
  have hr0 : 0 < r := P.left_pos.trans_le hr.1
  rw [momentDensity, inversePower_eq P e (P.a_lt_left.le.trans hr.1)]
  field_simp [hr0.ne']




section Primitive

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def weightedSource (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ := z.1 ^ e * F z
noncomputable def mass (e : ℕ) (F : ℝ × E → ℝ) : E → ℝ := IntegratedMeanBalances.radialMoment e F
noncomputable def bumpCorrection (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  momentDensity P e z.1 * mass e F z.2
noncomputable def adjusted (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  F z - bumpCorrection P e F z
noncomputable def primitive (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) : ℝ × E → ℝ :=
  TransportPrimitive.compactIntegral (cutoff P) 0 0 (weightedSource e F)
noncomputable def sigma (P : Patch) (e : ℕ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  -inversePower P e z.1 * primitive P e F z

theorem weightedSource_contDiff (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (weightedSource e F) := (contDiff_fst.pow e).mul hF

omit [NormedSpace ℝ E] in
theorem weightedSource_continuous (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F) :
    Continuous (weightedSource e F) := (continuous_fst.pow e).mul hF

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weightedSource_supported (e : ℕ) {P : Patch} {F : ℝ × E → ℝ}
    (hF : RadialAlias.RadiallySupported P.a P.b F) :
    RadialAlias.RadiallySupported P.a P.b (weightedSource e F) :=
  fun _ h => hF (right_ne_zero_of_mul h)

theorem mass_contDiff {P : Patch} (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (mass e F) :=
  IntegratedMeanBalances.radialMoment_smooth hF hs e





theorem primitive_contDiff (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (primitive P e F) :=
  TransportPrimitive.compactIntegral_contDiff (cutoff_contDiff P)
    (weightedSource_contDiff e hF) (weightedSource_supported e hs)

theorem primitive_supported (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) :
    RadialAlias.RadiallySupported P.a P.b (primitive P e F) :=
  TransportPrimitive.compactIntegral_supported ((continuous_fst.pow e).mul hF)
    (weightedSource_supported e hs)
    (fun _ hr => cutoff_zero P (hr.trans P.a_lt_left.le))
    (fun _ hr => cutoff_one P (P.right_lt_b.le.trans hr))

theorem sigma_contDiff (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) : ContDiff ℝ ∞ (sigma P e F) :=
  (((inversePower_contDiff P e).comp contDiff_fst).neg).mul (primitive_contDiff P e hF hs)


theorem total_weightedSource (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    TransportPrimitive.totalIntegral 0 (0 : E) (weightedSource e F) z = mass e F z.2 := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval
    (weightedSource_continuous e hF) (weightedSource_supported e hs)]
  simp only [zero_mul, zero_smul, add_zero, weightedSource]
  exact (IntegratedMeanBalances.radialMoment_eq_interval hF hs e z.2).symm

theorem past_zero_eq_integral {a b : ℝ} (ha : 0 ≤ a) {F : ℝ × E → ℝ} (hF : Continuous F)
    (hs : RadialAlias.RadiallySupported a b F) (z : ℝ × E) :
    TransportPrimitive.pastIntegral 0 (0 : E) F z = ∫ r in (0 : ℝ)..z.1, F (r, z.2) := by
  have hs0 : RadialAlias.RadiallySupported 0 b F := fun y hy => ⟨ha.trans (hs hy).1, (hs hy).2⟩
  simpa only [zero_mul, zero_smul, add_zero] using
    TransportPrimitive.pastIntegral_eq_radialInterval (M := 0) (v := (0 : E)) hF hs0 z

theorem cutoff_eq_integral (P : Patch) (r : ℝ) : cutoff P r = ∫ s in (0 : ℝ)..r, density P s :=
  past_zero_eq_integral P.left_pos.le (densityLift_contDiff P).continuous (densityLift_supported P) (r, 0)

theorem primitive_eq_integral (P : Patch) (e : ℕ) {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    primitive P e F z = ∫ r in (0 : ℝ)..z.1, r ^ e * adjusted P e F (r, z.2) := by
  have hiF : IntervalIntegrable (fun r => r ^ e * F (r, z.2)) volume 0 z.1 :=
    ((continuous_id.pow e).mul (hF.continuous.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  have hiD : IntervalIntegrable (fun r => density P r * mass e F z.2) volume 0 z.1 :=
    ((density_contDiff P).continuous.mul continuous_const).intervalIntegrable _ _
  have heq : (fun r => r ^ e * adjusted P e F (r, z.2)) =
      fun r => r ^ e * F (r, z.2) - density P r * mass e F z.2 := by
    funext r
    dsimp [adjusted, bumpCorrection]
    rw [mul_sub, ← mul_assoc, weighted_momentDensity]
  rw [heq, intervalIntegral.integral_sub hiF hiD, intervalIntegral.integral_mul_const]
  unfold primitive TransportPrimitive.compactIntegral
  rw [past_zero_eq_integral P.a_pos.le (weightedSource_continuous e hF.continuous)
    (weightedSource_supported e hs), total_weightedSource P e hF.continuous hs, cutoff_eq_integral]
  rfl


theorem sigma_eq_negative_primitive (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (z : ℝ × E) :
    sigma P e F z = -(∫ r in (0 : ℝ)..z.1, r ^ e * adjusted P e F (r, z.2)) / z.1 ^ e := by
  rw [← primitive_eq_integral P e hF hs]
  by_cases h : primitive P e F z = 0
  · simp [sigma, h]
  rw [sigma, inversePower_eq P e (primitive_supported P e hF.continuous hs h).1]
  ring




theorem primitive_hasDerivAt (P : Patch) (e : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : RadialAlias.RadiallySupported P.a P.b F) (p : E) (r : ℝ) :
    HasDerivAt (fun t => primitive P e F (t, p)) (r ^ e * adjusted P e F (r, p)) r := by
  have hp := primitive_contDiff P e hF hs
  have hd := ((hp.differentiable (by simp)) (r, p)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r p))
  have ht := TransportPrimitive.transport_compactIntegral (M := 0) (v := (0 : E))
    (cutoff_contDiff P) (weightedSource_contDiff e hF) (weightedSource_supported e hs) (r, p)
  simp only [TransportPrimitive.fixedDeriv, zero_smul, cutoff_deriv,
    total_weightedSource P e hF.continuous hs, smul_eq_mul] at ht
  have he : weightedSource e F (r, p) - density P r * mass e F p =
      r ^ e * adjusted P e F (r, p) := by
    dsimp [weightedSource, adjusted, bumpCorrection]
    rw [mul_sub, ← mul_assoc, weighted_momentDensity]
  rw [he] at ht
  change fderiv ℝ (primitive P e F) (r, p) (1, 0) = _ at ht
  simpa only [ht, Function.comp_def, id_eq] using hd





/-- All fixed-order constants come from the proved weighted integral estimate
and bounded radial multipliers on a fixed positive annulus. -/
theorem sigma_finiteJets_uniform (P : Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : ℝ × E → ℝ, ContDiff ℝ ∞ F →
      RadialAlias.RadiallySupported P.a P.b F → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ∀ r ∈ Ioo P.a P.b, ∀ y : E,
        ‖iteratedFDeriv ℝ i F (r, y)‖ ≤ A * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r) →
      ∀ z : ℝ × E, z.1 ∈ Ioo P.a P.b → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (sigma P e F) z‖ ≤
          K * A * WeightedRadialPrimitive.logWeight cL cR P.a P.b p z.1 := by
  obtain ⟨K1, hK1, h1⟩ := RadialPullback.radial_multiplier_finiteJets_uniform
    (E := E) (V := ℝ) P.a P.b (contDiff_id.pow e) m
  obtain ⟨K2, hK2, h2⟩ := WeightedRadialPrimitive.transport_compact_finiteJets_uniform
    (E := E) (V := ℝ) P.a_pos P.a_lt_left P.left_lt_right P.right_lt_b hcL hcR p m
    (cutoff P) (cutoff_contDiff P) (fun _ h => cutoff_zero P h) (fun _ h => cutoff_one P h)
  obtain ⟨K3, hK3, h3⟩ := RadialPullback.radial_multiplier_finiteJets_uniform
    (E := E) (V := ℝ) P.a P.b (inversePower_contDiff P e).neg m
  refine ⟨K3 * K2 * K1, by positivity, ?_⟩
  intro F hF hs A hA hFbound z hz j hj
  have hweight (r : ℝ) (hr : r ∈ Ioo P.a P.b) :
      0 ≤ WeightedRadialPrimitive.logWeight cL cR P.a P.b p r :=
    (WeightedRadialPrimitive.weight_pos cL cR p (WeightedRadialPrimitive.logPosition_mem P.a_pos hr)).le
  have hweighted : ∀ i ≤ m, ∀ r ∈ Ioo P.a P.b, ∀ y : E,
      ‖iteratedFDeriv ℝ i (weightedSource e F) (r, y)‖ ≤
        (K1 * A) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r := by
    intro i hi r hr y
    have h := h1 F hF (r, y) ⟨hr.1.le, hr.2.le⟩
      (A * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r) (mul_nonneg hA (hweight r hr))
      (fun k hk => hFbound k hk r hr y) i hi
    simp only [smul_eq_mul, mul_assoc, id_eq] at h ⊢
    exact h
  have hprimitive (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (primitive P e F) z‖ ≤
        (K2 * (K1 * A)) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p z.1 :=
    h2 0 0 (weightedSource e F) (weightedSource_contDiff e hF) (weightedSource_supported e hs)
      (K1 * A) (mul_nonneg hK1 hA) hweighted z hz i hi
  have h := h3 (primitive P e F) (primitive_contDiff P e hF hs) z ⟨hz.1.le, hz.2.le⟩
    ((K2 * (K1 * A)) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p z.1)
    (mul_nonneg (mul_nonneg hK2 (mul_nonneg hK1 hA)) (hweight z.1 hz)) hprimitive j hj
  simp only [smul_eq_mul, mul_assoc] at h ⊢
  exact h

theorem meanClass_sigma (P : Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (F : ℕ → ℝ × E → ℝ) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hs : ∀ n, RadialAlias.RadiallySupported P.a P.b (F n))
    (hclass : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow) α F) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow) α
      (fun n => sigma P e (F n)) := by
  refine ⟨hclass.weight_nonneg, fun n => (sigma_contDiff P e (hF n) (hs n)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hsource⟩ := hclass.bounds m
  obtain ⟨K, hK, hbound⟩ := sigma_finiteJets_uniform (E := E) P e hcL hcR p m
  refine ⟨K * C, mul_nonneg hK hC, p, ?_⟩
  intro n z hz j hj
  change z.1 ∈ Ioo P.a P.b at hz
  have hA : 0 ≤ C * (ε n) ^ α * (slow n) ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hslow n)) p)
  have hinput : ∀ i ≤ m, ∀ r ∈ Ioo P.a P.b, ∀ y : E,
      ‖iteratedFDeriv ℝ i (F n) (r, y)‖ ≤
        (C * (ε n) ^ α * (slow n) ^ p) * WeightedRadialPrimitive.logWeight cL cR P.a P.b p r := by
    intro i hi r hr y
    have h := hsource n (r, y) hr i hi
    rw [WeightedRadialPrimitive.logStrip_majorant_eq P.a_pos hcL hcR ε slow hε hε1 hslow
      α C p n (r, y) hr] at h
    exact h
  have h := hbound (F n) (hF n) (hs n) _ hA hinput z hz j hj
  rw [WeightedRadialPrimitive.logStrip_majorant_eq P.a_pos hcL hcR ε slow hε hε1 hslow
    α (K * C) p n z hz]
  simpa only [mul_assoc] using h

/-- The constructed interior bump carries the full edge weight, because its
support lies in a fixed compact subset of the active annulus. -/
theorem momentDensity_meanClass (P : Patch) (e : ℕ) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε slow : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      0 (fun _ (z : ℝ × E) => momentDensity P e z.1) := by
  let s := WeightedRadialPrimitive.logStripData (E := E) P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow
  have hmem : ∀ r ∈ Icc P.left P.right, (r, (0 : E)) ∈ s.domain := by
    intro r hr
    exact ⟨P.a_lt_left.trans_le hr.1, hr.2.trans_lt P.right_lt_b⟩
  have hc : ContinuousOn (fun r => s.zeta (r, (0 : E))) (Icc P.left P.right) :=
    s.zeta_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hp : ∀ r ∈ Icc P.left P.right, 0 < s.zeta (r, (0 : E)) := by
    intro r hr
    exact WeightedRadialPrimitive.zeta_pos cL cR
      (WeightedRadialPrimitive.logPosition_mem P.a_pos (hmem r hr))
  obtain ⟨D, hD, hDb⟩ := UniformCone.positive_uniform_margin isCompact_Icc hc hp
  have hs : RadialAlias.RadiallySupported P.left P.right (fun z : ℝ × E => momentDensity P e z.1) :=
    fun z hz => momentDensity_support P e hz
  refine ⟨fun _ z hz => s.zeta_nonneg z hz,
    fun _ => ((momentDensity_contDiff P e).comp contDiff_fst).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, hCb⟩ := WeightedRadialPrimitive.cutoff_finiteJet_bound (E := E)
    P.a P.b (momentDensity P e) (momentDensity_contDiff P e) m
  refine ⟨C / D, div_nonneg hC hD.le, 0, ?_⟩
  intro n z hz j hj
  change ‖iteratedFDeriv ℝ j (fun z : ℝ × E => momentDensity P e z.1) z‖ ≤
    WeightedClasses.majorant s (fun _ y => s.zeta y) 0 (C / D) 0 n z
  simp only [WeightedClasses.majorant, Real.rpow_zero, pow_zero, mul_one]
  by_cases hi : z.1 ∈ Icc P.left P.right
  · have hd : D ≤ s.zeta z := hDb z.1 hi
    calc
      _ ≤ C := hCb j hj z ⟨hz.1.le, hz.2.le⟩
      _ = (C / D) * D := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (div_nonneg hC hD.le)
  · have hzj : iteratedFDeriv ℝ j (fun z : ℝ × E => momentDensity P e z.1) z = 0 := by
      by_contra hn
      exact hi (TransportPrimitive.iteratedFDeriv_supported hs j hn)
    rw [hzj, norm_zero]
    exact mul_nonneg (div_nonneg hC hD.le) (s.zeta_nonneg z hz)

theorem fderiv_lift (D : E → ℝ) (hD : ContDiff ℝ ∞ D) (z : ℝ × E) (v : E) :
    fderiv ℝ (fun y : ℝ × E => D y.2) z (0, v) = fderiv ℝ D z.2 v := by
  have h := ((hD.differentiable (by simp)) z.2).hasFDerivAt.comp z hasFDerivAt_snd
  change fderiv ℝ (D ∘ Prod.snd) z (0, v) = _
  rw [h.fderiv]
  simp

/-- The improved bump order follows from a proved residual-moment identity:
one slow derivative comes with one additional factor of epsilon. -/
theorem bump_improvedClass_of_moment_identity (P : Patch) (e : ℕ) {cL cR : ℝ}
    (hcL : 0 < cL) (hcR : 0 < cR) (ε slow : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
    (α : ℝ) (F : ℕ → ℝ × E → ℝ) (D : ℕ → E → ℝ) (v : E)
    (hD : ∀ n, ContDiff ℝ ∞ (D n))
    (hclass : WeightedClasses.UnweightedClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      α (fun n (z : ℝ × E) => D n z.2))
    (hmoment : ∀ n p, mass e (F n) p = ε n * fderiv ℝ (D n) p v) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow)
      (α + 1) (fun n => bumpCorrection P e (F n)) := by
  let s := WeightedRadialPrimitive.logStripData (E := E) P.a P.b cL cR P.a_pos hcL hcR ε slow hε hε1 hslow
  have hd := hclass.directional ((0 : ℝ), v)
  have hb := (momentDensity_meanClass (E := E) P e hcL hcR ε slow hε hε1 hslow).mul hd
  have hmean : WeightedClasses.MeanClass s α (fun n (z : ℝ × E) =>
      momentDensity P e z.1 * fderiv ℝ (D n) z.2 v) := by
    simpa only [WeightedClasses.MeanClass, zero_add, mul_one, fderiv_lift _ (hD _)] using hb
  have hh := hmean.band_smul (WeightedClasses.bandBound_rpow s 1)
  have heq : (fun n (z : ℝ × E) => s.epsilon n ^ (1 : ℝ) •
      (momentDensity P e z.1 * fderiv ℝ (D n) z.2 v)) = fun n => bumpCorrection P e (F n) := by
    funext n z
    simp only [Real.rpow_one, smul_eq_mul, bumpCorrection, hmoment]
    change ε n * (momentDensity P e z.1 * _) = momentDensity P e z.1 * (ε n * _)
    ring
  rwa [heq] at hh

noncomputable def barSigma (P : Patch) (e : ℕ) (F : PressureStream.Lift E → ℝ) : ℝ × E → ℝ :=
  sigma P e (PressureStream.torusAverage F)



/-- Slow coefficients are constant along the ordinary radial integration. -/
theorem sigma_slow_mul (P : Patch) (e : ℕ) (k : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) :
    sigma P e (fun y => k y.2 * F y) z = k z.2 * sigma P e F z := by
  have hp : TransportPrimitive.pastIntegral 0 (0 : E) (weightedSource e (fun y => k y.2 * F y)) z =
      k z.2 * TransportPrimitive.pastIntegral 0 (0 : E) (weightedSource e F) z := by
    unfold TransportPrimitive.pastIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by simp [weightedSource, TransportPrimitive.shift]; ring)
  have ht : TransportPrimitive.totalIntegral 0 (0 : E) (weightedSource e (fun y => k y.2 * F y)) z =
      k z.2 * TransportPrimitive.totalIntegral 0 (0 : E) (weightedSource e F) z := by
    unfold TransportPrimitive.totalIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by simp [weightedSource, TransportPrimitive.shift]; ring)
  unfold sigma primitive TransportPrimitive.compactIntegral
  rw [hp, ht]
  simp only [smul_eq_mul]
  ring



end Primitive

section Physical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The physical radial length is sqrt q, as in the chart R = r / sqrt Q. -/
noncomputable def lengthScale (q : E → ℝ) (p : E) : ℝ := Real.sqrt (q p)
noncomputable def nativeSource (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  F (lengthScale q z.2 * z.1, z.2)
noncomputable def physicalDensity (P : Patch) (e : ℕ) (q : E → ℝ) (z : ℝ × E) : ℝ :=
  momentDensity P e (z.1 / lengthScale q z.2) / lengthScale q z.2 ^ (e + 1)
noncomputable def physicalBump (P : Patch) (e : ℕ) (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  physicalDensity P e q z * mass e F z.2
noncomputable def physicalAdjusted (P : Patch) (e : ℕ) (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  F z - physicalBump P e q F z
noncomputable def physicalSigma (P : Patch) (e : ℕ) (q : E → ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  lengthScale q z.2 * sigma P e (nativeSource q F) (z.1 / lengthScale q z.2, z.2)

/-- Radial support stated directly using the physical q, with no band index. -/
def PhysicalSupport (P : Patch) (q : E → ℝ) (F : ℝ × E → ℝ) : Prop :=
  ∀ z, F z ≠ 0 → z.1 / lengthScale q z.2 ∈ Icc P.a P.b

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lengthScale_pos {q : E → ℝ} (hq : ∀ p, 0 < q p) (p : E) : 0 < lengthScale q p :=
  Real.sqrt_pos.mpr (hq p)

theorem lengthScale_contDiff {q : E → ℝ} (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) :
    ContDiff ℝ ∞ (lengthScale q) := hq.sqrt (fun p => (hpos p).ne')

theorem nativeSource_contDiff {q : E → ℝ} (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p)
    {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (nativeSource q F) :=
  hF.comp ((((lengthScale_contDiff hq hpos).comp contDiff_snd).mul contDiff_fst).prodMk contDiff_snd)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem nativeSource_supported (P : Patch) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    {F : ℝ × E → ℝ} (hs : PhysicalSupport P q F) :
    RadialAlias.RadiallySupported P.a P.b (nativeSource q F) := by
  intro z hz
  have h := hs (lengthScale q z.2 * z.1, z.2) hz
  simp only [mul_div_cancel_left₀ _ (lengthScale_pos hq z.2).ne'] at h
  exact h

theorem integral_dilate_weighted (e : ℕ) (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ r, r ^ e * f (s * r)) = (∫ r, r ^ e * f r) / s ^ (e + 1) := by
  have he : (fun r => r ^ e * f (s * r)) =
      fun r => (s ^ e)⁻¹ * ((s * r) ^ e * f (s * r)) := by
    funext r
    rw [mul_pow]
    field_simp [hs.ne']
  rw [he, integral_const_mul, Measure.integral_comp_mul_left (fun r => r ^ e * f r) s]
  rw [abs_of_pos (inv_pos.mpr hs), smul_eq_mul, pow_succ]
  field_simp [hs.ne']

theorem interval_dilate_weighted (e : ℕ) (f : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ r in (0 : ℝ)..x, r ^ e * f (s * r)) =
      (∫ r in (0 : ℝ)..(s * x), r ^ e * f r) / s ^ (e + 1) := by
  have he : (fun r => r ^ e * f (s * r)) =
      fun r => (s ^ e)⁻¹ * ((s * r) ^ e * f (s * r)) := by
    funext r
    rw [mul_pow]
    field_simp [hs.ne']
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun r => r ^ e * f r) hs.ne']
  rw [mul_zero, smul_eq_mul, pow_succ]
  field_simp [hs.ne']

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem nativeSource_mass (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (F : ℝ × E → ℝ) (p : E) :
    mass e (nativeSource q F) p = mass e F p / lengthScale q p ^ (e + 1) :=
  integral_dilate_weighted e (fun r => F (r, p)) (lengthScale_pos hq p)


theorem physicalDensity_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) : ContDiff ℝ ∞ (physicalDensity P e q) := by
  have hs := (lengthScale_contDiff hq hpos).comp (contDiff_snd (E := ℝ))
  exact ((momentDensity_contDiff P e).comp
    (contDiff_fst.div hs (fun z => (lengthScale_pos hpos z.2).ne'))).div (hs.pow (e + 1))
      (fun z => pow_ne_zero _ (lengthScale_pos hpos z.2).ne')

theorem physical_mass_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : ContDiff ℝ ∞ (mass e F) := by
  have hn := mass_contDiff e (nativeSource_contDiff hq hpos hF) (nativeSource_supported P hpos hs)
  have he : mass e F = fun p => lengthScale q p ^ (e + 1) * mass e (nativeSource q F) p := by
    funext p
    rw [nativeSource_mass e hpos]
    field_simp [(lengthScale_pos hpos p).ne']
  rw [he]
  exact ((lengthScale_contDiff hq hpos).pow (e + 1)).mul hn

theorem physicalBump_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : ContDiff ℝ ∞ (physicalBump P e q F) :=
  (physicalDensity_contDiff P e hq hpos).mul ((physical_mass_contDiff P e hq hpos hF hs).comp contDiff_snd)

theorem physicalSigma_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) : ContDiff ℝ ∞ (physicalSigma P e q F) := by
  have hl : ContDiff ℝ ∞ (fun z : ℝ × E => lengthScale q z.2) :=
    (lengthScale_contDiff hq hpos).comp contDiff_snd
  exact hl.mul ((sigma_contDiff P e (nativeSource_contDiff hq hpos hF)
    (nativeSource_supported P hpos hs)).comp
      ((contDiff_fst.div hl (fun z => (lengthScale_pos hpos z.2).ne')).prodMk contDiff_snd))


omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem native_adjusted_eq (P : Patch) (e : ℕ) {q : E → ℝ} (hq : ∀ p, 0 < q p)
    (F : ℝ × E → ℝ) (z : ℝ × E) :
    adjusted P e (nativeSource q F) z =
      physicalAdjusted P e q F (lengthScale q z.2 * z.1, z.2) := by
  simp only [adjusted, bumpCorrection, nativeSource, physicalAdjusted, physicalBump, physicalDensity,
    nativeSource_mass e hq, mul_div_cancel_left₀ _ (lengthScale_pos hq z.2).ne']
  ring

/-- The physical sigma is exactly the requested negative primitive from zero.
No fixed-Q chart enters this definition or identity. -/
theorem physicalSigma_eq_negative_primitive (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (z : ℝ × E) :
    physicalSigma P e q F z =
      -(∫ r in (0 : ℝ)..z.1, r ^ e * physicalAdjusted P e q F (r, z.2)) / z.1 ^ e := by
  have hl := lengthScale_pos hpos z.2
  unfold physicalSigma
  rw [sigma_eq_negative_primitive P e (nativeSource_contDiff hq hpos hF) (nativeSource_supported P hpos hs)]
  simp_rw [native_adjusted_eq P e hpos]
  rw [interval_dilate_weighted e (fun r => physicalAdjusted P e q F (r, z.2)) hl,
    mul_div_cancel₀ z.1 hl.ne']
  rw [div_pow, pow_succ]
  by_cases hr : z.1 = 0
  · simp [hr]
  · field_simp [hl.ne', hr]






theorem physicalAdjusted_contDiff (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) :
    ContDiff ℝ ∞ (physicalAdjusted P e q F) := hF.sub (physicalBump_contDiff P e hq hpos hF hs)

theorem physical_weighted_sigma_eq (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) (r : ℝ) :
    r ^ e * physicalSigma P e q F (r, p) =
      -(∫ t in (0 : ℝ)..r, t ^ e * physicalAdjusted P e q F (t, p)) := by
  rw [physicalSigma_eq_negative_primitive P e hq hpos hF hs]
  by_cases hr : r = 0
  · subst r
    simp
  · field_simp

theorem physical_weighted_sigma_hasDerivAt (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) (r : ℝ) :
    HasDerivAt (fun t => t ^ e * physicalSigma P e q F (t, p))
      (-r ^ e * physicalAdjusted P e q F (r, p)) r := by
  have hc : Continuous (fun t => t ^ e * physicalAdjusted P e q F (t, p)) :=
    (continuous_id.pow e).mul ((physicalAdjusted_contDiff P e hq hpos hF hs).continuous.comp
      (continuous_id.prodMk continuous_const))
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).neg
  have he : (fun t => t ^ e * physicalSigma P e q F (t, p)) =
      fun t => -(∫ u in (0 : ℝ)..t, u ^ e * physicalAdjusted P e q F (u, p)) :=
    funext (physical_weighted_sigma_eq P e hq hpos hF hs p)
  rw [he]
  convert! hd using 1
  ring

theorem physical_angular_divergence (P : Patch) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 2 (fun t => physicalSigma P 2 q F (t, p)) r =
      -physicalAdjusted P 2 q F (r, p) := by
  have hd := ((IntegratedMeanBalances.radial_slice_smooth (physicalSigma_contDiff P 2 hq hpos hF hs) p).differentiable
    (by simp) r).hasDerivAt
  have he := ((hasDerivAt_pow 2 r).mul hd).unique
    (physical_weighted_sigma_hasDerivAt P 2 hq hpos hF hs p r)
  norm_num at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  dsimp [IntegratedMeanBalances.radialDivergence]
  calc
    _ = 2 * r * physicalSigma P 2 q F (r, p) +
        r ^ 2 * deriv (fun t => physicalSigma P 2 q F (t, p)) r := by field_simp ; ring
    _ = _ := by nlinarith [he]

theorem physical_axial_divergence (P : Patch) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P q F) (p : E) {r : ℝ} (hr : 0 < r) :
    IntegratedMeanBalances.radialDivergence 1 (fun t => physicalSigma P 1 q F (t, p)) r =
      -physicalAdjusted P 1 q F (r, p) := by
  have hd := ((IntegratedMeanBalances.radial_slice_smooth (physicalSigma_contDiff P 1 hq hpos hF hs) p).differentiable
    (by simp) r).hasDerivAt
  have he := ((hasDerivAt_pow 1 r).mul hd).unique
    (physical_weighted_sigma_hasDerivAt P 1 hq hpos hF hs p r)
  norm_num at he
  apply mul_left_cancel₀ hr.ne'
  dsimp [IntegratedMeanBalances.radialDivergence]
  calc
    _ = physicalSigma P 1 q F (r, p) + r * deriv (fun t => physicalSigma P 1 q F (t, p)) r := by
      field_simp ; ring
    _ = _ := by nlinarith [he]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Taking the torus bar preserves support described by the physical q. -/
theorem physical_torusAverage_supported (P : Patch) {q : E → ℝ}
    {F : PressureStream.Lift E → ℝ}
    (hs : PhysicalSupport P (fun p => q p.1) F) :
    PhysicalSupport P q (PressureStream.torusAverage F) := by
  intro z hz
  by_contra hn
  apply hz
  apply PressureStream.torusAverage_zero_of_forall
  intro Y
  by_contra hF
  exact hn (hs (z.1, (z.2, Y)) hF)

noncomputable def physicalBarSigma (P : Patch) (e : ℕ) (q : E → ℝ)
    (F : PressureStream.Lift E → ℝ) : ℝ × E → ℝ :=
  physicalSigma P e q (PressureStream.torusAverage F)


theorem physicalBarSigma_eq_negative_primitive (P : Patch) (e : ℕ) {q : E → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ p, 0 < q p) {F : PressureStream.Lift E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hs : PhysicalSupport P (fun p => q p.1) F) (z : ℝ × E) :
    physicalBarSigma P e q F z = -(∫ r in (0 : ℝ)..z.1,
      r ^ e * physicalAdjusted P e q (PressureStream.torusAverage F) (r, z.2)) / z.1 ^ e :=
  physicalSigma_eq_negative_primitive P e hq hpos (PressureStream.torusAverage_contDiff hF)
    (physical_torusAverage_supported P hs) z

/-- Residual units in the q-chart: q^(2A+1/2) times the physical residual. -/
noncomputable def normalizedResidual (q : E → ℝ) (A : ℝ) (F : ℝ × E → ℝ) (z : ℝ × E) : ℝ :=
  q z.2 ^ (2 * A + 1 / 2) * nativeSource q F z











end Physical

section IntegratedBalances

open IntegratedMeanBalances








end IntegratedBalances

section ChartComparison

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]









end ChartComparison

end NavierStokes.SignedStressPrimitive
