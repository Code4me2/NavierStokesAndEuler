import NavierStokes.CorrectionState
import NavierStokes.CommonCoverClass

/-!
# Naturality of the actual mean operators

Radial endpoints, the normalized density, the compactification cutoff,
frequencies, and amplitudes are transported together.  The identities below
are identities of the defined integral/Fourier/rank operators, not an
assumption that separately chosen chart outputs coincide.
-/

namespace NavierStokes.MeanChartCompatibility

noncomputable section

open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval

section RadialScale

theorem cutoff_scale {l : ℝ} (hl : l ≠ 0) (a b x : ℝ) :
    TransportPrimitive.cutoff (l * a) (l * b) (l * x) = TransportPrimitive.cutoff a b x := by
  unfold TransportPrimitive.cutoff
  congr 1
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hl]

theorem interiorCutoff_scale {l : ℝ} (hl : l ≠ 0) (a b x : ℝ) :
    TransportPrimitive.interiorCutoff (l * a) (l * b) (l * x) =
      TransportPrimitive.interiorCutoff a b x := by
  unfold TransportPrimitive.interiorCutoff
  rw [show (2 * (l * a) + l * b) / 3 = l * ((2 * a + b) / 3) by ring,
    show (l * a + 2 * (l * b)) / 3 = l * ((a + 2 * b) / 3) by ring]
  exact cutoff_scale hl _ _ _

theorem interiorCutoff_power_scale {l a b x : ℝ} (hl : 0 < l)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (d : ℝ) :
    TransportPrimitive.interiorCutoff ((l * a) ^ d) ((l * b) ^ d) ((l * x) ^ d) =
      TransportPrimitive.interiorCutoff (a ^ d) (b ^ d) (x ^ d) := by
  rw [Real.mul_rpow hl.le ha, Real.mul_rpow hl.le hb, Real.mul_rpow hl.le hx]
  exact interiorCutoff_scale (Real.rpow_pos_of_pos hl d).ne' _ _ _

theorem meanBump_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) (x : ℝ) :
    PressureStream.meanBump (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) (l * x) =
      PressureStream.meanBump a b hab x := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  dsimp only [PressureStream.meanBump]
  rw [show l * b - l * a = l * (b - a) by ring,
    show (l * a + l * b) / 2 = l * ((a + b) / 2) by ring]
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  congr 1
  · field_simp [hl.ne', hba]
  · simp only [smul_eq_mul]
    rw [← mul_sub]
    field_simp [hl.ne', hba]

theorem meanBump_integral_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) :
    (∫ x, PressureStream.meanBump (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) x) =
      l * ∫ x, PressureStream.meanBump a b hab x := by
  have he (x : ℝ) :
      PressureStream.meanBump (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) x =
        PressureStream.meanBump a b hab (x / l) := by
    simpa only [mul_div_cancel₀ _ hl.ne'] using meanBump_scale hl hab (x / l)
  simp_rw [he]
  simpa using MeanRankUpdate.integral_scaled hl 1 (PressureStream.meanBump a b hab)

/-- The density transforms with the inverse radial length. -/
theorem rho_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) (x : ℝ) :
    PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) (l * x) =
      l⁻¹ * PressureStream.rho a b hab x := by
  unfold PressureStream.rho
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, meanBump_scale hl hab,
    meanBump_integral_scale hl hab]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end RadialScale

section Pullback

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def chartLinear (l : ℝ) (C : E →L[ℝ] F) : ℝ × E →L[ℝ] ℝ × F :=
  (l • ContinuousLinearMap.id ℝ ℝ).prodMap C

@[simp] theorem chartLinear_apply (l : ℝ) (C : E →L[ℝ] F) (z : ℝ × E) :
    chartLinear l C z = (l * z.1, C z.2) := rfl

noncomputable def pull (l : ℝ) (C : E →L[ℝ] F) (u : ℝ) (f : ℝ × F → ℝ) (z : ℝ × E) : ℝ :=
  u * f (chartLinear l C z)

theorem pull_smooth (l : ℝ) (C : E →L[ℝ] F) (u : ℝ) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pull l C u f) :=
  contDiff_const.mul (hf.comp (chartLinear l C).contDiff)

theorem pull_supported {l a b : ℝ} (hl : 0 < l) (C : E →L[ℝ] F) (u : ℝ)
    {f : ℝ × F → ℝ} (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) :
    RadialAlias.RadiallySupported a b (pull l C u f) := by
  intro z hz
  have hne : f (chartLinear l C z) ≠ 0 := by
    intro he
    apply hz
    change u * f (chartLinear l C z) = 0
    rw [he, mul_zero]
  have hp := hs hne
  change l * a ≤ l * z.1 ∧ l * z.1 ≤ l * b at hp
  exact ⟨(mul_le_mul_iff_right₀ hl).mp hp.1, (mul_le_mul_iff_right₀ hl).mp hp.2⟩

theorem shifted_chart {l : ℝ} (hl : 0 < l) (C : E →L[ℝ] F)
    (d M N : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (Y : E) :
    C (Y + (M * (s ^ d - r ^ d)) • v) =
      C Y + (N * ((l * s) ^ d - (l * r) ^ d)) • w := by
  rw [map_add, map_smul]
  calc
    _ = C Y + (s ^ d - r ^ d) • (M • C v) := by
      rw [smul_smul]
      congr 2
      ring
    _ = _ := by
      rw [hshift, smul_smul, Real.mul_rpow hl.le hs, Real.mul_rpow hl.le hr]
      congr 2
      ring

theorem shifted_integral_scale {l a t r : ℝ} (hl : 0 < l) (ha : 0 ≤ a)
    (hat : a ≤ t) (hr : 0 ≤ r) (C : E →L[ℝ] F)
    (d M N u : ℝ) (v : E) (w : F) (f : ℝ × F → ℝ) (Y : E)
    (hshift : M • C v = (N * l ^ d) • w) :
    (∫ s in a..t, pull l C u f (s, Y + (M * (s ^ d - r ^ d)) • v)) =
      (u / l) * ∫ x in (l * a)..(l * t),
        f (x, C Y + (N * (x ^ d - (l * r) ^ d)) • w) := by
  have he : (∫ s in a..t, pull l C u f (s, Y + (M * (s ^ d - r ^ d)) • v)) =
      ∫ s in a..t, u * f (l * s, C Y + (N * ((l * s) ^ d - (l * r) ^ d)) • w) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsa : a ≤ s := (show s ∈ Icc a t by simpa only [uIcc_of_le hat] using hs).1
    simp only [pull, chartLinear_apply]
    rw [shifted_chart hl C d M N v w hshift hr (ha.trans hsa) Y]
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left
      (fun x => f (x, C Y + (N * (x ^ d - (l * r) ^ d)) • w)) hl.ne']
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]

/-- Scaling of the actual compact radial integral, with transformed
endpoints and the exact transformed transport direction. -/
theorem physicalCompact_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : ℝ × E) :
    RadialPullback.physicalCompact d a b M v (pull l C u f) z =
      (u / l) * RadialPullback.physicalCompact d (l * a) (l * b) N w f (chartLinear l C z) := by
  have hp := pull_smooth l C u hf
  have hsp := pull_supported hl C u hs
  have hla : 0 < l * a := mul_pos hl ha
  have hlab : l * a < l * b := mul_lt_mul_of_pos_left hab hl
  by_cases hz : a ≤ z.1
  · rw [RadialPullback.physicalCompact_eq_radialIntegral ha hab hd hp hsp M v z hz,
      RadialPullback.physicalCompact_eq_radialIntegral hla hlab hd hf hs N w
        (chartLinear l C z) (mul_le_mul_of_nonneg_left hz hl.le)]
    simp only [chartLinear_apply]
    rw [shifted_integral_scale hl ha.le hz (ha.le.trans hz) C d M N u v w f z.2 hshift,
      shifted_integral_scale hl ha.le hab.le (ha.le.trans hz) C d M N u v w f z.2 hshift,
      interiorCutoff_power_scale hl ha.le (ha.le.trans hab.le) (ha.le.trans hz) d]
    simp only [smul_eq_mul]
    ring
  · have hz' : z.1 < a := lt_of_not_ge hz
    have hleft : RadialPullback.physicalCompact d a b M v (pull l C u f) z = 0 := by
      by_contra hn
      exact hz (RadialPullback.physicalCompact_supported ha hab hd hp hsp M v hn).1
    have hright : RadialPullback.physicalCompact d (l * a) (l * b) N w f (chartLinear l C z) = 0 := by
      by_contra hn
      have ht := (RadialPullback.physicalCompact_supported hla hlab hd hf hs N w hn).1
      exact (not_le_of_gt (mul_lt_mul_of_pos_left hz' hl)) ht
    rw [hleft, hright, mul_zero]

theorem weightedSource_pull {l : ℝ} (hl : l ≠ 0) (C : E →L[ℝ] F)
    (u : ℝ) (f : ℝ × F → ℝ) :
    PressureStream.weightedSource (pull l C u f) =
      pull l C (u / l) (PressureStream.weightedSource f) := by
  funext z
  change z.1 * (u * f (chartLinear l C z)) =
    (u / l) * ((l * z.1) * f (chartLinear l C z))
  field_simp

/-- The stream potential has one less velocity length factor. -/
theorem streamPotential_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) :
    PressureStream.streamPotential d a b M v (pull l C u f) =
      pull l C (u / l) (PressureStream.streamPotential d (l * a) (l * b) N w f) := by
  funext z
  change RadialPullback.physicalCompact d a b M v
      (PressureStream.weightedSource (pull l C u f)) z / z.1 = _
  rw [weightedSource_pull hl.ne', physicalCompact_pull hl ha hab hd C M N (u / l) v w hshift
    (PressureStream.weightedSource_contDiff hf) (PressureStream.weightedSource_supported hs)]
  change (u / l / l * RadialPullback.physicalCompact d (l * a) (l * b) N w
    (PressureStream.weightedSource f) (chartLinear l C z)) / z.1 =
      (u / l) * (RadialPullback.physicalCompact d (l * a) (l * b) N w
        (PressureStream.weightedSource f) (chartLinear l C z) / (l * z.1))
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem fderiv_pull_apply (l : ℝ) (C : E →L[ℝ] F) (u : ℝ) {f : ℝ × F → ℝ}
    {z : ℝ × E} (hf : DifferentiableAt ℝ f (chartLinear l C z)) (v : ℝ × E) :
    fderiv ℝ (pull l C u f) z v = u * fderiv ℝ f (chartLinear l C z) (chartLinear l C v) := by
  have hd := (hf.hasFDerivAt.comp z (chartLinear l C).hasFDerivAt).const_mul u
  simp only [Function.comp_def] at hd
  rw [show pull l C u f = fun x => u * f (chartLinear l C x) from rfl, hd.fderiv]
  rfl


theorem graphDr_pull (l : ℝ) (C : E →L[ℝ] F) (u : ℝ)
    (knew kold : ℝ → ℝ) (v : E) (w : F) {f : ℝ × F → ℝ} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f (chartLinear l C z))
    (hvector : C (knew z.1 • v) = l • (kold (l * z.1) • w)) :
    PressureStream.graphDr knew v (pull l C u f) z =
      (u * l) * PressureStream.graphDr kold w f (chartLinear l C z) := by
  rw [PressureStream.graphDr, fderiv_pull_apply l C u hf]
  have he : chartLinear l C (PressureStream.radialVector knew v z) =
      l • PressureStream.radialVector kold w (chartLinear l C z) := by
    apply Prod.ext
    · simp [chartLinear_apply, PressureStream.radialVector]
    · exact hvector
  rw [he, map_smul]
  simp only [smul_eq_mul, PressureStream.graphDr]
  ring


theorem physicalSpeed_vector {l R : ℝ} (hl : 0 < l) (hR : 0 ≤ R)
    (C : E →L[ℝ] F) (d M N : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) :
    C (PressureStream.physicalSpeed d M R • v) =
      l • (PressureStream.physicalSpeed d N (l * R) • w) := by
  have hpow : l * l ^ (d - 1) = l ^ d := by
    conv_lhs => lhs; rw [← Real.rpow_one l]
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc
    _ = (d * R ^ (d - 1)) • (M • C v) := by
      simp only [PressureStream.physicalSpeed, RadialPullback.radialJacobian, map_smul, smul_smul]
    _ = (d * R ^ (d - 1)) • ((N * l ^ d) • w) := by rw [hshift]
    _ = _ := by
      simp only [PressureStream.physicalSpeed, RadialPullback.radialJacobian, smul_smul,
        Real.mul_rpow hl.le hR]
      congr 1
      rw [show l * (d * (l ^ (d - 1) * R ^ (d - 1)) * N) =
        d * R ^ (d - 1) * N * (l * l ^ (d - 1)) by ring, hpow]
      ring



end Pullback

section TorusPullback

open TorusInverse

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

noncomputable def parameterPull (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) : PressureStream.Lift S → ℝ :=
  pull l (P.prodMap (ContinuousLinearMap.id ℝ Plane)) u f

noncomputable def coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) : PressureStream.Lift S → ℝ :=
  pull l (P.prodMap (TemporalMeanUpdate.coverMap k)) u f

theorem coverPull_eq (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) :
    coverPull l P k u f = TemporalMeanUpdate.pullbackCover k (parameterPull l P u f) := rfl

theorem parameterPull_smooth (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterPull l P u f) := pull_smooth _ _ _ hf

theorem parameterPull_periodic (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.TorusPeriodicLift (parameterPull l P u f) := by
  intro r s Y k
  change u * f (l * r, (P s, Y + ((k.1 : ℝ), (k.2 : ℝ)))) = u * f (l * r, (P s, Y))
  exact congrArg (fun q : ℝ => u * q) (hp (l * r) (P s) Y k)

theorem coverPull_smooth (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coverPull l P k u f) := pull_smooth _ _ _ hf


theorem torusAverage_parameterPull (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) (p : ℝ × S) :
    PressureStream.torusAverage (parameterPull l P u f) p =
      u * PressureStream.torusAverage f (l * p.1, P p.2) := by
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, u * f (l * p.1, (P p.2, (x, y)))) =
    u * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (l * p.1, (P p.2, (x, y))))
  simp only [intervalIntegral.integral_const_mul]

theorem torusAverage_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (coverPull l P k u f) p =
      u * PressureStream.torusAverage f (l * p.1, P p.2) := by
  rw [coverPull_eq, TemporalMeanUpdate.torusAverage_pullbackCover k
    (parameterPull_smooth l P u hf) (parameterPull_periodic l P u hp), torusAverage_parameterPull]

theorem pressureMass_coverPull {l : ℝ} (hl : 0 < l) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (s : S) :
    PressureStream.pressureMass (coverPull l P k u f) s =
      (u / l) * PressureStream.pressureMass f (P s) := by
  unfold PressureStream.pressureMass
  simp_rw [torusAverage_coverPull l P k u hf hp]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun r => PressureStream.torusAverage f (r, P s)) l,
    abs_of_pos (inv_pos.mpr hl)]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]

theorem pressureSource_coverPull {l a b : ℝ} (hl : 0 < l) (hab : a < b)
    (P : S →L[ℝ] T) (k : ℕ) (u : ℝ) {f : PressureStream.Lift T → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.pressureSource a b hab (coverPull l P k u f) =
      coverPull l P k u (PressureStream.pressureSource (l * a) (l * b)
        (mul_lt_mul_of_pos_left hab hl) f) := by
  funext z
  change u * f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.rho a b hab z.1 * PressureStream.pressureMass (coverPull l P k u f) z.2.1 =
    u * (f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) (l * z.1) *
        PressureStream.pressureMass f (P z.2.1))
  rw [pressureMass_coverPull hl P k u hf hp, rho_scale hl hab]
  simp only [div_eq_mul_inv]
  ring

theorem centered_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) :
    TemporalMeanUpdate.centered (coverPull l P k u f) =
      coverPull l P k u (TemporalMeanUpdate.centered f) := by
  funext z
  change u * f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.torusAverage (coverPull l P k u f) (z.1, z.2.1) =
    u * (f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.torusAverage f (l * z.1, P z.2.1))
  rw [torusAverage_coverPull l P k u hf hp]
  ring

/-- Naturality of the actual pressure formula, including its normalized
mass correction and compactification, on a common covering. -/
theorem meanPressure_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) (z : PressureStream.Lift S) :
    PressureStream.meanPressure d a b M hab v (coverPull l P k u f) z =
      coverPull l P k (u / l)
        (PressureStream.meanPressure d (l * a) (l * b) N (mul_lt_mul_of_pos_left hab hl) w f) z := by
  have hvector : M • (P.prodMap (TemporalMeanUpdate.coverMap k)) ((0 : S), v) =
      (N * l ^ d) • ((0 : T), w) := by
    apply Prod.ext
    · simp
    · exact hshift
  unfold PressureStream.meanPressure
  rw [pressureSource_coverPull hl hab P k u hf hp]
  exact physicalCompact_pull hl ha hab hd _ M N u _ _ hvector
    (PressureStream.pressureSource_contDiff (mul_lt_mul_of_pos_left hab hl) hf hs)
    (PressureStream.pressureSource_supported (mul_lt_mul_of_pos_left hab hl) hs) z

theorem absoluteInverse_const_mul (c : ℂ) (f : Plane → ℂ) (Y : Plane) :
    TemporalMeanUpdate.absoluteInverse (fun z => c * f z) Y =
      c * TemporalMeanUpdate.absoluteInverse f Y := by
  unfold TemporalMeanUpdate.absoluteInverse TorusInverse.directionalInverse TorusInverse.series
  simp only [TorusInverse.inverseCoeff, TemporalMeanUpdate.coefficient_const_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

theorem temporalInverse_parameterPull (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) (z : PressureStream.Lift S) :
    TemporalMeanUpdate.temporalInverse (parameterPull l P u f) z =
      parameterPull l P u (TemporalMeanUpdate.temporalInverse f) z := by
  change (TemporalMeanUpdate.absoluteInverse
    (fun Y => Complex.ofReal (u * f (l * z.1, (P z.2.1, Y)))) z.2.2).re =
      u * (TemporalMeanUpdate.absoluteInverse
        (fun Y => (f (l * z.1, (P z.2.1, Y)) : ℂ)) z.2.2).re
  simp_rw [Complex.ofReal_mul]
  rw [absoluteInverse_const_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem temporalInverse_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hm : ∀ p, PressureStream.torusAverage f p = 0) (z : PressureStream.Lift S) :
    TemporalMeanUpdate.temporalInverse (coverPull l P k u f) z =
      (ChartScales.Tg ^ k)⁻¹ * coverPull l P k u (TemporalMeanUpdate.temporalInverse f) z := by
  have hmean : ∀ p, PressureStream.torusAverage (parameterPull l P u f) p = 0 := by
    intro p
    rw [torusAverage_parameterPull, hm, mul_zero]
  have he := TemporalMeanUpdate.temporalInverse_coverMap
    (parameterPull_smooth l P u hf) (parameterPull_periodic l P u hp) hmean k z
  rw [temporalInverse_parameterPull] at he
  exact he

theorem temporalInverse_centered_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered (coverPull l P k u f)) z =
      (ChartScales.Tg ^ k)⁻¹ * coverPull l P k u
        (TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)) z := by
  rw [centered_coverPull l P k u hf hp]
  exact temporalInverse_coverPull l P k u (TemporalMeanUpdate.centered_smooth hf)
    (TemporalMeanUpdate.centered_periodic hp) (TemporalMeanUpdate.centered_zeroMean hf) z


/-- The common-index form of the actual temporal update. A common index
is independent of the dyadic band; the native recipe is its specialization. -/
noncomputable def temporalAtIndex (h : ℝ) (n i : ℕ)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  -((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h))⁻¹) *
    TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f) z




end TorusPullback

section RankScaling

theorem normalizeDebt_scale {l u ell U : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (hell : ell ≠ 0) (hU : U ≠ 0) (d : MeanRankUpdate.Debt) :
    MeanRankUpdate.normalizeDebt (l * ell) (u * U) (MeanRankUpdate.scaleDebt l u d) =
      MeanRankUpdate.normalizeDebt ell U d := by
  ext i
  fin_cases i <;> simp [MeanRankUpdate.normalizeDebt, MeanRankUpdate.scaleDebt] <;>
    field_simp [hl, hu, hell, hU]

/-- Naturality of the constructed five-row inverse, not just of its rows. -/
theorem rankAngular_scale {l u ell U : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (hell : ell ≠ 0) (hU : U ≠ 0) (lam C a b : ℝ) (d : MeanRankUpdate.Debt) (r : ℝ) :
    MeanRankUpdate.angularIncrement lam C a b (l * ell) (u * U)
      (MeanRankUpdate.scaleDebt l u d) (l * r) =
        u * MeanRankUpdate.angularIncrement lam C a b ell U d r := by
  unfold MeanRankUpdate.angularIncrement
  rw [normalizeDebt_scale hl hu hell hU]
  simp only [MeanRankUpdate.scaleField, mul_div_mul_left _ _ hl]
  ring

theorem rankDesiredAxial_scale {l u ell U : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (hell : ell ≠ 0) (hU : U ≠ 0) (lam C a b : ℝ) (d : MeanRankUpdate.Debt) (r : ℝ) :
    MeanRankUpdate.desiredAxialIncrement lam C a b (l * ell) (u * U)
      (MeanRankUpdate.scaleDebt l u d) (l * r) =
        u * MeanRankUpdate.desiredAxialIncrement lam C a b ell U d r := by
  unfold MeanRankUpdate.desiredAxialIncrement
  rw [normalizeDebt_scale hl hu hell hU]
  simp only [MeanRankUpdate.scaleField, mul_div_mul_left _ _ hl]
  ring


end RankScaling

section CommonTemporalBounds

open TorusInverse

noncomputable def commonRatio (h : ℝ) (n i : ℕ) : ℝ :=
  ChartScales.Tg ^ ChartScales.nativeIndex h n / ChartScales.Tg ^ i

theorem commonRatio_pos (h : ℝ) (n i : ℕ) : 0 < commonRatio h n i :=
  div_pos (pow_pos ChartScales.Tg_pos _) (pow_pos ChartScales.Tg_pos _)

theorem commonRatio_le {h : ℝ} {n i D : ℕ}
    (hgap : ChartScales.nativeIndex h n ≤ i + D) : commonRatio h n i ≤ ChartScales.Tg ^ D := by
  apply (div_le_iff₀ (pow_pos ChartScales.Tg_pos i)).mpr
  simpa only [pow_add, mul_comm] using pow_le_pow_right₀ ChartScales.Tg_one_lt.le hgap

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_eq_native (h : ℝ) (n i : ℕ) (f : PressureStream.Lift S → ℝ) :
    temporalAtIndex h n i f = fun z => commonRatio h n i * TemporalMeanUpdate.desiredIncrement h n f z := by
  funext z
  unfold temporalAtIndex commonRatio TemporalMeanUpdate.desiredIncrement
    TemporalMeanUpdate.chartPrefactor ChartScales.timeCoefficient
  field_simp [pow_ne_zero _ ChartScales.Tg_pos.ne',
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (1 + h)).ne']

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_periodic (h : ℝ) (n i : ℕ) (f : PressureStream.Lift S → ℝ) :
    PressureStream.TorusPeriodicLift (temporalAtIndex h n i f) := by
  intro r s Y k
  exact congrArg (-((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h))⁻¹) * ·)
    (TemporalMeanUpdate.temporalInverse_periodic (TemporalMeanUpdate.centered f) r s Y k)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_supported (h : ℝ) (n i : ℕ) {a b : ℝ}
    {f : PressureStream.Lift S → ℝ} (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (temporalAtIndex h n i f) := by
  intro z hz
  apply TemporalMeanUpdate.temporalInverse_supported (TemporalMeanUpdate.centered_supported hs)
  intro hi
  exact hz (by simp only [temporalAtIndex, hi, mul_zero])

theorem meanClass_temporalAtIndex_of_native (s : WeightedClasses.StripData (PressureStream.Lift S))
    {h α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ} (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (hf : WeightedClasses.MeanClass s α (fun n => TemporalMeanUpdate.desiredIncrement h n (f n))) :
    WeightedClasses.MeanClass s α (fun n => temporalAtIndex h n (index n) (f n)) := by
  have hb : WeightedClasses.BandBound s 0 (fun n => commonRatio h n (index n)) := by
    refine ⟨ChartScales.Tg ^ D, (pow_pos ChartScales.Tg_pos D).le, 0, ?_⟩
    intro n
    simp only [Real.norm_eq_abs, abs_of_pos (commonRatio_pos h n (index n)), Real.rpow_zero,
      pow_zero, mul_one]
    exact commonRatio_le (hgap n)
  have hout := hf.band_smul hb
  simpa only [add_zero, temporalAtIndex_eq_native, smul_eq_mul] using hout

noncomputable def fastAtIndex (h : ℝ) (n i : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  (ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)) *
    PressureStream.graphDz ((0 : S), vector .temporal) f z

variable [FiniteDimensional ℝ S]

theorem temporalAtIndex_smooth (h : ℝ) (n i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    ContDiff ℝ ∞ (temporalAtIndex h n i f) :=
  contDiff_const.mul (TemporalMeanUpdate.temporalInverse_smooth
    (TemporalMeanUpdate.centered_smooth hf) (TemporalMeanUpdate.centered_periodic hp))

theorem temporalAtIndex_fast_cancellation (h : ℝ) (n i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    fastAtIndex h n i (temporalAtIndex h n i f) z = -TemporalMeanUpdate.centered f z := by
  let c := ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)
  have hc : c ≠ 0 := (mul_pos (pow_pos ChartScales.Tg_pos _)
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)).ne'
  have hi := TemporalMeanUpdate.temporalInverse_smooth
    (TemporalMeanUpdate.centered_smooth hf) (TemporalMeanUpdate.centered_periodic hp)
  have hd := (((hi.differentiable (by simp)) z).hasFDerivAt).const_smul (-c⁻¹)
  change HasFDerivAt (temporalAtIndex h n i f) _ z at hd
  rw [fastAtIndex, PressureStream.graphDz, hd.fderiv]
  change c * (-c⁻¹ * PressureStream.graphDz ((0 : S), vector .temporal)
    (TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)) z) = _
  rw [TemporalMeanUpdate.temporalInverse_solves (TemporalMeanUpdate.centered_smooth hf)
    (TemporalMeanUpdate.centered_periodic hp) (TemporalMeanUpdate.centered_zeroMean hf)]
  field_simp

end CommonTemporalBounds

section PhysicalFamilies

open TorusInverse

theorem coverMap_eq_coverPower (i : ℕ) (Y : Plane) :
    TemporalMeanUpdate.coverMap i Y = CommonCoverSolve.coverPower i Y := by
  induction i with
  | zero => rfl
  | succ i hi =>
      change TemporalMeanUpdate.coverLinear (TemporalMeanUpdate.coverMap i Y) =
        CommonCoverSolve.coverEquiv (CommonCoverSolve.coverPower i Y)
      rw [hi, TemporalMeanUpdate.coverLinear_apply, CommonCoverSolve.coverEquiv_apply,
        SlotGeometry.cover_apply]
      rfl

theorem coverMap_radial (i : ℕ) :
    TemporalMeanUpdate.coverMap i (vector .radial) = ChartScales.Lambda ^ i • vector .radial := by
  rw [coverMap_eq_coverPower, CommonCoverSolve.coverPower_apply]
  exact PhysicalGraphBounds.cover_pow_radialDirection i

noncomputable def chartScale (n : ℕ) : ℝ := ChartScales.Q n ^ (-(1 / 2 : ℝ))

theorem chartScale_pos (n : ℕ) : 0 < chartScale n :=
  Real.rpow_pos_of_pos (ChartScales.Q_pos n) _

noncomputable def radialFrequency (_h : ℝ) (n i : ℕ) (d M : ℝ) : ℝ :=
  M * ChartScales.Lambda ^ i * ChartScales.Q n ^ (d / 2)

theorem radialFrequency_scale (h : ℝ) (n i : ℕ) (d M : ℝ) :
    radialFrequency h n i d M * chartScale n ^ d = M * ChartScales.Lambda ^ i := by
  have hs : chartScale n ^ d = ChartScales.Q n ^ (-(d / 2)) := by
    unfold chartScale
    rw [← Real.rpow_mul (ChartScales.Q_pos n).le]
    congr 1
    ring
  rw [hs, radialFrequency, mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n)]
  simp


theorem radialFrequency_shift (h : ℝ) (n i : ℕ) (d M : ℝ) :
    M • TemporalMeanUpdate.coverMap i (vector .radial) =
      (radialFrequency h n i d M * chartScale n ^ d) • vector .radial := by
  rw [coverMap_radial, smul_smul, radialFrequency_scale]

/-- The physical slow variables are `(z,τ)` with `τ=1-t`. -/
noncomputable def slowToChart (h : ℝ) (n : ℕ) : Plane →L[ℝ] Plane :=
  (ChartScales.Q n ^ (-CoordinateAlgebra.D h) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ChartScales.Q n ^ (-1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

noncomputable def physicalToChart (h : ℝ) (n i : ℕ) :
    PressureStream.Lift Plane →L[ℝ] PressureStream.Lift Plane :=
  chartLinear (chartScale n) ((slowToChart h n).prodMap (TemporalMeanUpdate.coverMap i))

@[simp] theorem physicalToChart_apply (h : ℝ) (n i : ℕ) (z : PressureStream.Lift Plane) :
    physicalToChart h n i z = (chartScale n * z.1,
      ((ChartScales.Q n ^ (-CoordinateAlgebra.D h) * z.2.1.1,
        ChartScales.Q n ^ (-1 : ℝ) * z.2.1.2), TemporalMeanUpdate.coverMap i z.2.2)) := rfl

/-- Normalize a chart field of scaling degree `a` on the actual physical
slow variables and absolute auxiliary lift. -/
noncomputable def fieldOnPhysical (h : ℝ) (n i : ℕ) (a : ℝ)
    (f : PressureStream.Lift Plane → ℝ) : PressureStream.Lift Plane → ℝ :=
  coverPull (chartScale n) (slowToChart h n) i (ChartScales.Q n ^ (-a)) f


theorem pressure_unit_factor (h : ℝ) (n : ℕ) :
    ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) / chartScale n =
      ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) := by
  unfold chartScale
  rw [← Real.rpow_sub (ChartScales.Q_pos n)]
  congr 1
  ring



noncomputable def reconstructPressureFamily (r : ℕ → CorrectionState.ReconstructionData)
    (c : CorrectionState.Context (PressureStream.Lift Plane))
    (u : CorrectionState.State (PressureStream.Lift Plane)) :
    CorrectionState.State (PressureStream.Lift Plane) :=
  { u with pressure := fun n => (CorrectionState.reconstructPressure (r n) c u).pressure n }



end PhysicalFamilies

section ReconstructedStream

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




end ReconstructedStream

section PressureAlias

open TorusInverse

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem pressureAlias_eq_source_sub_derivative {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (z : PressureStream.Lift S) :
    PressureStream.pressureAlias d a b M hab v f z =
      PressureStream.pressureSource a b hab f z -
        PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : S), v)
          (PressureStream.meanPressure d a b M hab v f) z := by
  have he := PressureStream.meanPressure_radial_residual_global (M := M) ha hab hd v hf hs z
  unfold PressureStream.pressureSource
  linarith

theorem pressureAlias_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : PressureStream.Lift S) (hz : 0 ≤ z.1) :
    PressureStream.pressureAlias d a b M hab v (coverPull l P k u f) z =
      coverPull l P k u
        (PressureStream.pressureAlias d (l * a) (l * b) N (mul_lt_mul_of_pos_left hab hl) w f) z := by
  let C := P.prodMap (TemporalMeanUpdate.coverMap k)
  have hvector : M • C ((0 : S), v) = (N * l ^ d) • ((0 : T), w) := by
    apply Prod.ext
    · simp [C]
    · exact hshift
  have hpressure : PressureStream.meanPressure d a b M hab v (coverPull l P k u f) =
      pull l C (u / l) (PressureStream.meanPressure d (l * a) (l * b) N
        (mul_lt_mul_of_pos_left hab hl) w f) := by
    funext x
    exact meanPressure_coverPull hl ha hab hd P k M N u v w hshift hf hp hs x
  have hps := PressureStream.meanPressure_contDiff (M := N) (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd w hf hs
  rw [pressureAlias_eq_source_sub_derivative ha hab hd v (coverPull_smooth l P k u hf)
    (pull_supported hl C u hs), pressureSource_coverPull hl hab P k u hf hp, hpressure,
    graphDr_pull l C (u / l) _ _ ((0 : S), v) ((0 : T), w)
      ((hps.differentiable (by simp)) _)
      (physicalSpeed_vector hl hz C d M N ((0 : S), v) ((0 : T), w) hvector),
    div_mul_cancel₀ _ hl.ne']
  change u * PressureStream.pressureSource (l * a) (l * b) _ f (chartLinear l C z) -
      u * PressureStream.graphDr _ _ _ (chartLinear l C z) =
    u * PressureStream.pressureAlias d (l * a) (l * b) N _ w f (chartLinear l C z)
  rw [pressureAlias_eq_source_sub_derivative (mul_pos hl ha) (mul_lt_mul_of_pos_left hab hl) hd w hf hs]
  ring

end PressureAlias

section CommonTemporalReconstruction

open TorusInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]





variable [FiniteDimensional ℝ S]







end CommonTemporalReconstruction

section PhysicalTemporalFields

open TorusInverse











end PhysicalTemporalFields

section DebtTransport

open TorusInverse

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

noncomputable def sourceMoment (m : ℕ) (f : PressureStream.Lift S → ℝ) (s : S) : ℝ :=
  PressureStream.pressureMass (fun z => z.1 ^ m * f z) s

noncomputable def sourceDebt (g qθ qz : PressureStream.Lift S → ℝ) (s : S) : MeanRankUpdate.Debt :=
  ![sourceMoment 0 g s, sourceMoment 2 qθ s, sourceMoment 1 qz s - (1 / 2 : ℝ) * sourceMoment 2 g s]

theorem sourceMoment_coverPull {l : ℝ} (hl : 0 < l) (P : S →L[ℝ] T)
    (k m : ℕ) (u : ℝ) {f : PressureStream.Lift T → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (s : S) :
    sourceMoment m (coverPull l P k u f) s =
      (u / l ^ (m + 1)) * sourceMoment m f (P s) := by
  have he : (fun z : PressureStream.Lift S => z.1 ^ m * coverPull l P k u f z) =
      coverPull l P k (u / l ^ m) (fun z => z.1 ^ m * f z) := by
    funext z
    change z.1 ^ m * (u * f (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z)) =
      (u / l ^ m) * ((l * z.1) ^ m * f (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z))
    rw [mul_pow]
    field_simp
  have hfp : PressureStream.TorusPeriodicLift (fun z : PressureStream.Lift T => z.1 ^ m * f z) := by
    intro r t Y j
    exact congrArg (r ^ m * ·) (hp r t Y j)
  unfold sourceMoment
  rw [he, pressureMass_coverPull hl P k (u / l ^ m) ((contDiff_fst.pow m).mul hf) hfp]
  rw [pow_succ]
  field_simp


omit [NormedAddCommGroup T] [NormedSpace ℝ T] in
theorem stateDebt_eq_sourceDebt (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ) (s : S) :
    CorrectionState.debt c u n s =
      sourceDebt (u.gr c n)
        ((MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1) n)
        ((MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2) n) s := rfl

end DebtTransport

section RankFamilies

variable {S T : Type}



end RankFamilies

section PhysicalProfile

open TorusInverse

noncomputable def slowProjection (z : PressureStream.Lift Plane) : SimilarityHomogeneity.ChartPoint :=
  (z.1, z.2.1)





end PhysicalProfile

end

end NavierStokes.MeanChartCompatibility
