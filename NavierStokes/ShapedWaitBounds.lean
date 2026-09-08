import NavierStokes.OutgoingEntranceCone

/-!
# Actual shaped-hold errors with constants uniform in the small slope

The angular lag is solved exactly from its incoming value at `holdStart`.
The two decaying modes are kept separate, so no inverse small-slope constant
appears in the error estimate.
-/

noncomputable section

namespace NavierStokes.ShapedWaitBounds

open Set Filter MeasureTheory
open scoped Topology ContDiff
open OutgoingSchedule OutgoingTail NaturalAxisData OutgoingEntranceCone

theorem linearLag_neg (r b : ℝ → ℝ) (q₀ y : ℝ) :
    linearLag r (fun t => -b t) (-q₀) y = -linearLag r b q₀ y := by
  unfold linearLag OutgoingSchedule.primitive
  simp only [mul_neg, intervalIntegral.integral_neg]
  ring

theorem linearLag_le_constant {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {q₀ B y : ℝ} (hy : 0 ≤ y) (hq : q₀ ≤ B)
    (hs : ∀ t ∈ Icc (0 : ℝ) y, b t ≤ r t * B) : linearLag r b q₀ y ≤ B := by
  have h := linearLag_lower_barrier hr hb.fun_neg (q₀ := -q₀) (β := -B) (κ := 0) hy
    (by linarith) (fun t ht => by have := hs t ht; nlinarith)
  rw [linearLag_neg] at h
  linarith

theorem linearLag_abs_le {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {q₀ B y : ℝ} (hy : 0 ≤ y) (hq : |q₀| ≤ B)
    (hs : ∀ t ∈ Icc (0 : ℝ) y, |b t| ≤ r t * B) : |linearLag r b q₀ y| ≤ B := by
  apply abs_le.mpr
  refine ⟨?_, linearLag_le_constant hr hb hy ((le_abs_self _).trans hq)
    (fun t ht => (le_abs_self _).trans (hs t ht))⟩
  have h := linearLag_lower_barrier hr hb (β := -B) (κ := 0) hy
    (by have := (abs_le.mp hq).1; linarith) (fun t ht => by
      have := (abs_le.mp (hs t ht)).1
      nlinarith)
  linarith

theorem angularSource_abs_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    |angularSource c h η y| ≤ 8 := by
  have hr := angularRate_bounds c y
  have hl : |slope c.dropLength c.lam y| ≤ 1 := by
    unfold angularRate at hr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hW : |transportW c h y η| ≤ 3 :=
    abs_le.mpr ⟨(transportW_bounds c hh hh1 hy hη).1,
      (transportW_bounds c hh hh1 hy hη).2.trans (by norm_num)⟩
  have hk := dropCoefficient_bounds c.m y
  have hsq := parameter_square_le_one hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by unfold d; constructor <;> nlinarith [sq_nonneg η]
  have hD : 0 ≤ D h ∧ D h ≤ 1 / 2 := by unfold D; constructor <;> linarith
  have hJ := eta_shapeGradient_bounds hη
  have hcoef : |1 - 2 * dropCoefficient c.m y * η ^ 2| ≤ 9 := by
    have hp := mul_le_mul hk.2 hsq (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 4)
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hk.1 (sq_nonneg η)]
  have hfirst : |-slope c.dropLength c.lam y * transportW c h y η| ≤ 3 := by
    rw [abs_mul, abs_neg]
    exact (mul_le_mul hl hW (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hsecond : |h * (1 - 2 * dropCoefficient c.m y * η ^ 2)| ≤ 9 / 100 := by
    rw [abs_mul, abs_of_nonneg hh]
    have hb := mul_le_mul hh1 hcoef (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    nlinarith
  have hbase : 0 ≤ D h + d η * dropCoefficient c.m y ∧ D h + d η * dropCoefficient c.m y ≤ 9 / 2 := by
    have hb := mul_le_mul hd.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)
    constructor <;> nlinarith [mul_nonneg hd.1 hk.1]
  have hthird : |(D h + d η * dropCoefficient c.m y) * η * shapeGradient η| ≤ 9 / 2 := by
    rw [mul_assoc, abs_mul, abs_of_nonneg hbase.1, abs_of_nonneg (by nlinarith [sq_nonneg η] : 0 ≤ η * shapeGradient η)]
    exact (mul_le_mul hbase.2 hJ.2 (by nlinarith [sq_nonneg η]) (by norm_num : (0 : ℝ) ≤ 9 / 2)).trans_eq (by ring)
  unfold angularSource
  have hs : |-slope c.dropLength c.lam y * transportW c h y η -
      h * (1 - 2 * dropCoefficient c.m y * η ^ 2) +
        (D h + d η * dropCoefficient c.m y) * η * shapeGradient η| ≤
      |-slope c.dropLength c.lam y * transportW c h y η| +
        |h * (1 - 2 * dropCoefficient c.m y * η ^ 2)| +
          |(D h + d η * dropCoefficient c.m y) * η * shapeGradient η| :=
    (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
  linarith

theorem angularLag_abs_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    |angularLag c h η y| ≤ 10 := by
  have hi := angularSource_abs_bound c hh hh1 (show (0 : ℝ) ≤ 0 by rfl) hη
  rw [angularSource_ideal c h η le_rfl] at hi
  have hinit : |idealAngularLag h η| ≤ 10 := by
    unfold idealAngularLag
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8 / 5)).mpr
    linarith
  apply linearLag_abs_le (angularRate_contDiff c).continuous
    (angularSource_contDiff c h η).continuous hy hinit
  intro t ht
  have hs := angularSource_abs_bound c hh hh1 ht.1 hη
  have hr := (angularRate_bounds c t).1
  linarith

noncomputable def equilibrium (c : Parameters) (h η : ℝ) : ℝ :=
  (c.lam - h + D h * η * shapeGradient η) / (1 - c.lam)

noncomputable def holdCoefficient (c : Parameters) (h η : ℝ) : ℝ :=
  L h η * averagedDrop c c.holdStart

noncomputable def holdSource (c : Parameters) (h η t : ℝ) : ℝ :=
  c.lam - h + D h * η * shapeGradient η - c.lam * holdCoefficient c h η * Real.exp (-t)

noncomputable def holdFormula (c : Parameters) (h η t : ℝ) : ℝ :=
  equilibrium c h η +
    (angularLag c h η c.holdStart - equilibrium c h η - holdCoefficient c h η) *
      Real.exp (-(1 - c.lam) * t) + holdCoefficient c h η * Real.exp (-t)

theorem hold_rate_pos (c : Parameters) : 0 < 1 - c.lam := by linarith [c.lam_lt]

theorem dropCoefficient_hold (c : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    dropCoefficient c.m (c.holdStart + t) = 0 := by
  apply dropCoefficient_late c.m_pos
  dsimp [Parameters.holdStart, Parameters.dropLength]
  linarith

theorem averagedDrop_hold (c : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    averagedDrop c (c.holdStart + t) = Real.exp (-t) * averagedDrop c c.holdStart := by
  have hl := historyAverage_late (dropCoefficient_contDiff c.m_pos).continuous
    (b₀ := (4 : ℝ)) (a := c.holdStart) (y := c.holdStart + t) (by linarith)
    (fun u hu => by
      apply dropCoefficient_late c.m_pos
      dsimp [Parameters.holdStart, Parameters.dropLength] at hu
      linarith)
  simpa only [averagedDrop, add_sub_cancel_left] using hl

theorem angularRate_hold (c : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    angularRate c (c.holdStart + t) = 1 - c.lam := by
  unfold angularRate
  rw [slope_hold c.dropLength_pos.le (by dsimp [Parameters.holdStart]; linarith)]
  ring

theorem angularSource_hold (c : Parameters) (h η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    angularSource c h η (c.holdStart + t) = holdSource c h η t := by
  unfold angularSource transportW holdSource holdCoefficient
  rw [dropCoefficient_hold c ht, averagedDrop_hold c ht,
    slope_hold c.dropLength_pos.le (by dsimp [Parameters.holdStart]; linarith)]
  ring

theorem decay_hasDerivAt (r t : ℝ) : HasDerivAt (fun t => Real.exp (-r * t))
    (-r * Real.exp (-r * t)) t := by
  convert! ((hasDerivAt_id t).const_mul (-r)).exp using 1
  simp only [id_eq]
  ring

theorem holdFormula_hasDerivAt (c : Parameters) (h η t : ℝ) :
    HasDerivAt (holdFormula c h η)
      (holdSource c h η t - (1 - c.lam) * holdFormula c h η t) t := by
  have hd := ((decay_hasDerivAt (1 - c.lam) t).const_mul
    (angularLag c h η c.holdStart - equilibrium c h η - holdCoefficient c h η)).const_add
      (equilibrium c h η)
  have hd' := hd.fun_add (((hasDerivAt_id t).fun_neg.exp).const_mul (holdCoefficient c h η))
  convert! hd' using 1
  unfold holdSource holdFormula equilibrium
  simp only [id_eq]
  field_simp [(hold_rate_pos c).ne'] ; ring

/-- Exact integration of the shaped-hold equation, with no division by `λ`. -/
theorem angularLag_hold_formula (c : Parameters) (h η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    angularLag c h η (c.holdStart + t) = holdFormula c h η t := by
  have hb : Continuous (holdSource c h η) :=
    continuous_const.sub (continuous_const.mul (Real.continuous_exp.comp continuous_neg))
  have ha := linearLag_eq_of_solution (r := fun _ => 1 - c.lam) (b := holdSource c h η)
    (f := fun u => angularLag c h η (c.holdStart + u)) continuous_const hb
    (by simp : angularLag c h η (c.holdStart + 0) = angularLag c h η c.holdStart) (fun u hu => by
      have hu0 := (uIcc_of_le ht ▸ hu).1
      have hd := (angularLag_hasDerivAt c h η (c.holdStart + u)).comp u ((hasDerivAt_id u).const_add c.holdStart)
      simp only [Function.comp_def, mul_one, angularSource_hold c h η hu0,
        angularRate_hold c hu0] at hd
      exact hd)
  have hf := linearLag_eq_of_solution (r := fun _ => 1 - c.lam) (b := holdSource c h η)
    (f := holdFormula c h η) continuous_const hb
    (show holdFormula c h η 0 = angularLag c h η c.holdStart by
      simp only [holdFormula, mul_zero, neg_zero, Real.exp_zero, mul_one]
      ring)
    (fun u _ => holdFormula_hasDerivAt c h η u) (y := t)
  exact ha.trans hf.symm

theorem equilibrium_bounds (v : TailData) {η : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) :
    0 ≤ equilibrium v.core v.h η ∧ equilibrium v.core v.h η ≤ 1 := by
  have hr := hold_rate_pos v.core
  have hj := eta_shapeGradient_bounds hη
  have hD : 0 ≤ D v.h ∧ D v.h ≤ 1 / 2 := by unfold D; constructor <;> linarith [v.h_pos]
  have hprod := mul_le_mul hD.2 hj.2 (by nlinarith [sq_nonneg η]) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hprod0 := mul_nonneg hD.1 (show 0 ≤ η * shapeGradient η by nlinarith [sq_nonneg η])
  unfold equilibrium
  constructor
  · exact div_nonneg (by nlinarith [v.h_small, v.h_pos]) hr.le
  · apply (div_le_iff₀ hr).mpr
    nlinarith [v.core.lam_lt, v.h_pos]

theorem holdCoefficient_bounds (c : Parameters) {h η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hη : |η| ≤ 1) : 0 ≤ holdCoefficient c h η ∧ holdCoefficient c h η ≤ 4 := by
  have hL := natural_L_bounds hh hh1 hη
  have hk := averagedDrop_bounds c c.holdStart_pos.le
  unfold holdCoefficient
  refine ⟨mul_nonneg (by linarith) hk.1, ?_⟩
  exact (mul_le_mul hL.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)

theorem angularLag_hold_error (v : TailData) {η t : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    |angularLag v.core v.h η (v.core.holdStart + t) - equilibrium v.core v.h η| ≤
      19 * Real.exp (-(1 - v.core.lam) * t) := by
  have hq := angularLag_abs_bound v.core v.h_pos.le hh1 v.core.holdStart_pos.le hη
  have heq := equilibrium_bounds v hh1 hη
  have hc := holdCoefficient_bounds v.core v.h_pos.le hh1 hη
  have hcabs : |holdCoefficient v.core v.h η| ≤ 4 := by simpa only [abs_of_nonneg hc.1] using hc.2
  have heqabs : |equilibrium v.core v.h η| ≤ 1 := by simpa only [abs_of_nonneg heq.1] using heq.2
  have hcoef : |angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η -
      holdCoefficient v.core v.h η| ≤ 15 := by
    have hb := (abs_sub (angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η)
      (holdCoefficient v.core v.h η)).trans (add_le_add_left (abs_sub _ _) _)
    linarith
  have hex : Real.exp (-t) ≤ Real.exp (-(1 - v.core.lam) * t) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg v.core.lam_pos.le ht])
  rw [angularLag_hold_formula v.core v.h η ht]
  have hf : holdFormula v.core v.h η t - equilibrium v.core v.h η =
      (angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η - holdCoefficient v.core v.h η) *
        Real.exp (-(1 - v.core.lam) * t) + holdCoefficient v.core v.h η * Real.exp (-t) := by
    unfold holdFormula
    ring
  rw [hf]
  calc
    _ ≤ |(angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η - holdCoefficient v.core v.h η) *
        Real.exp (-(1 - v.core.lam) * t)| + |holdCoefficient v.core v.h η * Real.exp (-t)| := abs_add_le _ _
    _ ≤ 15 * Real.exp (-(1 - v.core.lam) * t) + 4 * Real.exp (-(1 - v.core.lam) * t) := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
        (mul_le_mul hcabs hex (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 4))
    _ = _ := by ring

theorem canonical_Qs_pulseStart_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hh1 : v.h ≤ 1 / 100) {η : ℝ} (hη : |η| ≤ 1) :
    |OutgoingHistories.Qs w Amp (v.core.pulseStart, η) - equilibrium v.core v.h η| ≤
      19 * Real.exp (-(1 - v.core.lam) * v.core.wait) := by
  rw [canonical_Qs_before w ha v.core.pulseStart_pos.le le_rfl]
  exact angularLag_hold_error v hh1 hη (by linarith [v.core.wait_gt])

noncomputable def waitForPower (c : Parameters) (n : ℕ) : ℝ :=
  -(n : ℝ) * Real.log c.lam / (1 - c.lam)

theorem decay_le_power (c : Parameters) (n : ℕ) (ht : waitForPower c n ≤ c.wait) :
    Real.exp (-(1 - c.lam) * c.wait) ≤ c.lam ^ n := by
  have hmul := (div_le_iff₀ (hold_rate_pos c)).mp ht
  calc
    _ ≤ Real.exp ((n : ℝ) * Real.log c.lam) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log c.lam_pos]

theorem canonical_Qs_pulseStart_power_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hh1 : v.h ≤ 1 / 100) {η : ℝ} (hη : |η| ≤ 1) (n : ℕ)
    (hwait : waitForPower v.core n ≤ v.core.wait) :
    |OutgoingHistories.Qs w Amp (v.core.pulseStart, η) - equilibrium v.core v.h η| ≤
      19 * v.core.lam ^ n :=
  (canonical_Qs_pulseStart_error w ha hh1 hη).trans
    (mul_le_mul_of_nonneg_left (decay_le_power v.core n hwait) (by norm_num))

/-! ## The positive shaped-hold floor -/

noncomputable def holdFloor (m : ℝ) : ℝ :=
  min (coneFloor * Real.exp (-entranceTime m) / 4) (1 / 16)

theorem holdFloor_pos (m : ℝ) : 0 < holdFloor m := by
  unfold holdFloor
  exact lt_min (by have := coneFloor_pos; positivity) (by norm_num)

theorem holdFloor_bounds (m : ℝ) : holdFloor m ≤ coneFloor ∧ holdFloor m ≤ 1 / 16 ∧
    4 * holdFloor m ≤ coneFloor * Real.exp (-entranceTime m) := by
  have hb : holdFloor m ≤ coneFloor * Real.exp (-entranceTime m) / 4 := min_le_left _ _
  have he : Real.exp (-entranceTime m) ≤ 1 := Real.exp_le_one_iff.mpr (by
    unfold entranceTime
    have := Real.exp_pos m
    linarith)
  have hc := coneFloor_pos
  refine ⟨?_, min_le_right _ _, by linarith⟩
  nlinarith [mul_le_mul_of_nonneg_left he hc.le]

theorem holdSource_lower (v : TailData) {η t : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hhlam : v.h ≤ v.core.lam / 4) (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    v.core.lam / 4 + (49 / 100) * η ^ 2 ≤ holdSource v.core v.h η t := by
  have hy : v.core.dropLength + 2 ≤ v.core.holdStart + t := by
    dsimp [Parameters.holdStart]
    linarith
  have hW := transportW_second_ramp v.core v.h_pos.le hh1 (y := v.core.holdStart + t) (by linarith) hη
  have hD : 49 / 100 ≤ D v.h := by unfold D; linarith
  have hJ := (eta_shapeGradient_bounds hη).1
  have hprod := mul_le_mul hD hJ (sq_nonneg η) (by linarith : 0 ≤ D v.h)
  rw [← angularSource_hold v.core v.h η ht, angularSource,
    slope_hold v.core.dropLength_pos.le hy, dropCoefficient_hold v.core ht]
  simp only [mul_zero, add_zero, neg_neg]
  nlinarith [mul_le_mul_of_nonneg_left hW v.core.lam_pos.le]

theorem holdFormula_eq_linearLag (c : Parameters) (h η t : ℝ) :
    holdFormula c h η t =
      linearLag (fun _ => 1 - c.lam) (holdSource c h η) (angularLag c h η c.holdStart) t := by
  apply linearLag_eq_of_solution continuous_const
    (continuous_const.sub (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))
  · simp only [holdFormula, mul_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  · intro u _
    exact holdFormula_hasDerivAt c h η u

theorem angularLag_hold_lower (v : TailData) {η t : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hhlam : v.h ≤ v.core.lam / 4)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    holdFloor v.core.m * (η ^ 2 + v.core.lam + Real.exp (-(1 - v.core.lam) * t)) ≤
      angularLag v.core v.h η (v.core.holdStart + t) := by
  have hc := holdFloor_pos v.core.m
  have hb := holdFloor_bounds v.core.m
  have hi := angularLag_lower v.core v.h_pos.le hh1 v.core.holdStart_pos.le le_rfl hη hhT
  have htime : 4 * holdFloor v.core.m ≤ coneFloor * Real.exp (-v.core.holdStart) := by
    simpa only [holdStart_eq_entranceTime] using hb.2.2
  have hinit : holdFloor v.core.m * (η ^ 2 + v.core.lam) + holdFloor v.core.m ≤
      angularLag v.core v.h η v.core.holdStart := by
    have hs := mul_le_mul_of_nonneg_right hb.1 (sq_nonneg η)
    have hl := mul_le_mul_of_nonneg_left v.core.lam_lt.le hc.le
    nlinarith
  have hsource : ∀ u ∈ Icc (0 : ℝ) t,
      (1 - v.core.lam) * (holdFloor v.core.m * (η ^ 2 + v.core.lam)) ≤ holdSource v.core v.h η u := by
    intro u hu
    have hs := holdSource_lower v hh1 hhlam hη hu.1
    have hbase : holdFloor v.core.m * (η ^ 2 + v.core.lam) ≤
        v.core.lam / 4 + (49 / 100) * η ^ 2 := by
      have hbη := mul_le_mul_of_nonneg_right hb.2.1 (sq_nonneg η)
      have hbLam := mul_le_mul_of_nonneg_right hb.2.1 v.core.lam_pos.le
      nlinarith [sq_nonneg η, v.core.lam_pos]
    have hn : 0 ≤ holdFloor v.core.m * (η ^ 2 + v.core.lam) :=
      mul_nonneg hc.le (add_nonneg (sq_nonneg η) v.core.lam_pos.le)
    nlinarith [mul_nonneg v.core.lam_pos.le hn]
  have hlo := linearLag_lower_barrier continuous_const
    (continuous_const.sub (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))
    ht hinit hsource
  rw [angularLag_hold_formula v.core v.h η ht, holdFormula_eq_linearLag]
  have hp : -OutgoingSchedule.primitive (fun _ : ℝ => 1 - v.core.lam) t = -(1 - v.core.lam) * t := by
    simp only [OutgoingSchedule.primitive, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hp] at hlo
  convert! hlo using 1
  ring

/-! ## The axial source and its actual convolution on the hold -/

theorem pressureClock_contDiff (c : Parameters) : ContDiff ℝ ∞ (pressureClock c) :=
  contDiff_const.add (contDiff_const.mul (primitive_contDiff (clockEnergy_contDiff c)))

theorem entrancePressure_contDiff (v : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => entrancePressure v p.1 p.2) := by
  exact ((SchedulePressure.axisPressure_contDiff v).comp contDiff_snd).add
    (((shape_contDiff.comp contDiff_snd).pow 2).mul ((pressureClock_contDiff v.core).comp contDiff_fst))

theorem pressureGradient_contDiff (v : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureGradient v p.1 p.2) := by
  exact ((contDiff_infty_iff_deriv.mp (SchedulePressure.axisPressure_contDiff v)).2.comp contDiff_snd).sub
    (((contDiff_const.mul (shapeGradient_contDiff.comp contDiff_snd)).mul
      ((shape_contDiff.comp contDiff_snd).pow 2)).mul ((pressureClock_contDiff v.core).comp contDiff_fst))

theorem pressureAxialSource_contDiff (v : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureAxialSource v p.1 p.2) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => d p.2) := contDiff_const.sub (contDiff_snd.pow 2)
  exact ((hd.neg.mul (pressureGradient_contDiff v)).add
    (((contDiff_const.mul contDiff_snd).mul (entrancePressure_contDiff v)))).add
      (contDiff_snd.mul ((angular_contDiff v.core.P v.core.dropLength v.core.lam).pow 2))

theorem geometricAxialSource_hold (c : Parameters) (h η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    geometricAxialSource c h (c.holdStart + t) η = 0 := by
  have hl : Real.exp c.m < c.holdStart + t := by
    dsimp [Parameters.holdStart, Parameters.dropLength]
    linarith
  simp [geometricAxialSource, dropCoefficient_hold c ht, dropCoefficient_deriv_late c.m_pos hl]

theorem axialLag_hold_history (v : TailData) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    axialLag v (v.core.holdStart + t) η =
      historyAverage (fun u => pressureAxialSource v (v.core.holdStart + u) η)
        (axialLag v v.core.holdStart η) t := by
  unfold historyAverage
  apply linearLag_eq_of_solution (r := fun _ => 1)
    (f := fun u => axialLag v (v.core.holdStart + u) η) continuous_const
    ((pressureAxialSource_contDiff v).continuous.comp
      ((continuous_const.add continuous_id).prodMk continuous_const))
  · simp
  · intro u hu
    have hu0 := (uIcc_of_le ht ▸ hu).1
    have hd := (axialLag_hasDerivAt v (v.core.holdStart + u) η).comp u
      ((hasDerivAt_id u).const_add v.core.holdStart)
    simp only [Function.comp_def, mul_one, one_mul, axialSource,
      geometricAxialSource_hold v.core v.h η hu0, zero_add] at hd ⊢
    exact hd

theorem historyAverage_abs_bound {b : ℝ → ℝ} {b₀ A B t : ℝ} (ht : 0 ≤ t)
    (hb₀ : |b₀| ≤ A) (hb : ∀ u ∈ Icc (0 : ℝ) t, |Real.exp u * b u| ≤ B) :
    |historyAverage b b₀ t| ≤ Real.exp (-t) * (A + t * B) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (f := fun u => Real.exp u * b u) (C := B) (fun u hu => by
      rw [Real.norm_eq_abs]
      have hu' : u ∈ Icc (0 : ℝ) t := ⟨(show 0 < u from (uIoc_of_le ht ▸ hu).1).le,
        (uIoc_of_le ht ▸ hu).2⟩
      exact hb u hu')
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at hi
  rw [historyAverage_formula, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact (abs_add_le _ _).trans (by linarith)

theorem angular_hold (c : Parameters) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    angular c.P c.dropLength c.lam (c.holdStart + t, η) =
      angular c.P c.dropLength c.lam (c.holdStart, η) * Real.exp (-(1 / 2 + c.lam) * t) := by
  unfold angular
  rw [radialAmplitude_hold c.dropLength_pos.le (show c.dropLength + 2 ≤ c.holdStart by rfl)
    (show c.holdStart ≤ c.holdStart + t by linarith)]
  simp only [add_sub_cancel_left]
  ring

theorem weighted_angular_square_hold (c : Parameters) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t * angular c.P c.dropLength c.lam (c.holdStart + t, η) ^ 2 =
      angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2 * Real.exp (-2 * c.lam * t) := by
  rw [angular_hold c η ht, mul_pow, ← Real.exp_nat_mul]
  have he : -2 * c.lam * t = t + 2 * (-(1 / 2 + c.lam) * t) := by ring
  rw [he, Real.exp_add]
  norm_num
  ring

noncomputable def initialEnergyLower (P m : ℝ) : ℝ := P * Real.exp (-entranceTime m) / 2
noncomputable def initialEnergyUpper (P m : ℝ) : ℝ := P * Real.exp (entranceTime m)
noncomputable def initialAxialBound (P m : ℝ) : ℝ :=
  64 + (3 + 4 * pressureBound) * energyEnvelope P (entranceTime m)
noncomputable def axialWaitConstant (P m : ℝ) : ℝ :=
  initialAxialBound P m / initialEnergyLower P m + pressureSourceBound * initialEnergyUpper P m

theorem initialEnergyLower_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < initialEnergyLower P m := by
  unfold initialEnergyLower
  positivity

theorem initialEnergyUpper_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < initialEnergyUpper P m := by
  unfold initialEnergyUpper
  positivity

theorem initialAxialBound_pos (P m : ℝ) : 0 < initialAxialBound P m := by
  unfold initialAxialBound energyEnvelope
  have := pressureBound_pos
  positivity

theorem axialWaitConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < axialWaitConstant P m := by
  unfold axialWaitConstant
  exact add_pos (div_pos (initialAxialBound_pos _ _) (initialEnergyLower_pos hP _))
    (mul_pos pressureSourceBound_pos (initialEnergyUpper_pos hP _))

theorem angular_hold_start_bounds (c : Parameters) {η : ℝ} (hη : |η| ≤ 1) :
    initialEnergyLower c.P c.m ≤ angular c.P c.dropLength c.lam (c.holdStart, η) ∧
      angular c.P c.dropLength c.lam (c.holdStart, η) ≤ initialEnergyUpper c.P c.m := by
  have hlo := angular_lower_envelope c c.holdStart_pos.le le_rfl hη
  refine ⟨?_, ?_⟩
  · simpa only [initialEnergyLower, holdStart_eq_entranceTime] using hlo
  · have hi := (OutgoingPulseBounds.radialAmplitude_bounds c c.holdStart_pos.le).2
    have hs := (shape_interval hη).2
    have hp := mul_le_mul hi hs (shape_pos η).le (mul_pos c.P_pos (Real.exp_pos _)).le
    simpa only [angular, initialEnergyUpper, holdStart_eq_entranceTime, mul_one] using hp

theorem axialLag_hold_start_bound (v : TailData) {η : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) :
    |axialLag v v.core.holdStart η| ≤ initialAxialBound v.core.P v.core.m * |η| := by
  have hend : v.core.holdStart ≤ v.core.endpoint := by
    have := v.core.pulseStart_ge_hold
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  have hg := geometricAxialLag_bound v.core v.h_pos.le hh1 v.core.holdStart_pos.le hη
  have hp := pressureAxialLag_le_envelope v hh1 v.core.holdStart_pos.le le_rfl hend hη
  unfold axialLag
  have hs := (abs_add_le (geometricAxialLag v.core v.h v.core.holdStart η)
    (pressureAxialLag v v.core.holdStart η)).trans (add_le_add hg hp)
  convert! hs using 1
  unfold initialAxialBound
  rw [holdStart_eq_entranceTime]
  ring

theorem weighted_pressure_source_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |Real.exp t * pressureAxialSource v (v.core.holdStart + t) η| ≤
      pressureSourceBound * |η| * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η) ^ 2 := by
  have hy : 0 ≤ v.core.holdStart + t := by linarith [v.core.holdStart_pos]
  have hend : v.core.holdStart + t ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint, Parameters.pulseStart]
    linarith [v.core.pulseLength_pos]
  have hb := pressureAxialSource_bound v hh1 hy hend hη
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp t * (pressureSourceBound * |η| *
        angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η) ^ 2) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (pressureSourceBound * |η|) *
        (Real.exp t * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η) ^ 2) := by ring
    _ = _ * (angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η) ^ 2 *
        Real.exp (-2 * v.core.lam * t)) := by rw [weighted_angular_square_hold v.core η ht]
    _ ≤ _ := by
      have he : Real.exp (-2 * v.core.lam * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg v.core.lam_pos.le ht])
      have hp := mul_le_mul_of_nonneg_left he
        (show 0 ≤ pressureSourceBound * |η| * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η) ^ 2 by
          have := pressureSourceBound_pos
          positivity)
      nlinarith

theorem axialLag_hold_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |axialLag v (v.core.holdStart + t) η| ≤ Real.exp (-t) *
      (initialAxialBound v.core.P v.core.m * |η| + t *
        (pressureSourceBound * |η| * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η) ^ 2)) := by
  rw [axialLag_hold_history v η ht]
  apply historyAverage_abs_bound ht (axialLag_hold_start_bound v hh1 hη)
  intro u hu
  exact weighted_pressure_source_bound v hh1 hη hu.1 (hu.2.trans htw)

theorem axialLag_hold_ratio_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |axialLag v (v.core.holdStart + t) η /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η)| ≤
      axialWaitConstant v.core.P v.core.m * |η| * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) := by
  let E₀ := angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η)
  have hE₀ : 0 < E₀ := angular_pos v.core.P_pos _ _ _
  have hE := angular_hold_start_bounds v.core hη
  have hEmin := initialEnergyLower_pos v.core.P_pos v.core.m
  have hA := initialAxialBound_pos v.core.P v.core.m
  have hC := pressureSourceBound_pos
  have hCb := axialWaitConstant_pos v.core.P_pos v.core.m
  have hfirst : initialAxialBound v.core.P v.core.m ≤
      (initialAxialBound v.core.P v.core.m / initialEnergyLower v.core.P v.core.m) * E₀ := by
    have hp := mul_le_mul_of_nonneg_left hE.1 (div_pos hA hEmin).le
    simpa only [div_mul_cancel₀ _ hEmin.ne'] using hp
  have hsecond : pressureSourceBound * E₀ ^ 2 ≤
      (pressureSourceBound * initialEnergyUpper v.core.P v.core.m) * E₀ := by
    have hp := mul_le_mul_of_nonneg_right hE.2 (mul_pos hC hE₀).le
    nlinarith
  have hinside : initialAxialBound v.core.P v.core.m + t * (pressureSourceBound * E₀ ^ 2) ≤
      axialWaitConstant v.core.P v.core.m * (1 + t) * E₀ := by
    have hm := mul_le_mul_of_nonneg_left hsecond ht
    have hc1 := div_pos hA hEmin
    have hc2 := mul_pos hC (initialEnergyUpper_pos v.core.P_pos v.core.m)
    unfold axialWaitConstant
    nlinarith [mul_nonneg ht hc1.le, mul_nonneg ht hc2.le, mul_pos hc2 hE₀]
  have hN := axialLag_hold_bound v hh1 hη ht htw
  have hex : Real.exp (-(1 / 2 - v.core.lam) * t) * Real.exp (-(1 / 2 + v.core.lam) * t) =
      Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring
  rw [abs_div, abs_of_pos (angular_pos v.core.P_pos _ _ _)]
  apply (div_le_iff₀ (angular_pos v.core.P_pos _ _ _)).mpr
  apply hN.trans
  rw [angular_hold v.core η ht]
  change Real.exp (-t) * (_ + _) ≤
    axialWaitConstant v.core.P v.core.m * |η| * (1 + t) *
      Real.exp (-(1 / 2 - v.core.lam) * t) * (E₀ * Real.exp (-(1 / 2 + v.core.lam) * t))
  have hm := mul_le_mul_of_nonneg_left hinside (mul_nonneg (Real.exp_pos (-t)).le (abs_nonneg η))
  calc
    _ ≤ Real.exp (-t) * |η| * (axialWaitConstant v.core.P v.core.m * (1 + t) * E₀) := by
      convert! hm using 1
      ring
    _ = _ := by rw [← hex]; ring

theorem canonical_Ns_hold_ratio_bound {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |OutgoingHistories.Ns w Amp (v.core.holdStart + t, η) /
      OutgoingHistories.E w (v.core.holdStart + t, η)| ≤
      axialWaitConstant v.core.P v.core.m * |η| * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) := by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  have hend : v.core.holdStart + t ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  rw [canonical_Ns_before w ha hpulse, OutgoingHistories.E_before w η hend]
  exact axialLag_hold_ratio_bound v hh1 hη ht htw

/-! ## Differentiating the genuine parameter-dependent histories -/

















/-! ## The axial parameter derivative at the beginning of the hold -/


















/-! ## Canonical combined statements and pulse-entry powers -/

theorem canonical_Qs_hold_lower {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hhlam : v.h ≤ v.core.lam / 4)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    holdFloor v.core.m * (η ^ 2 + v.core.lam + Real.exp (-(1 - v.core.lam) * t)) ≤
      OutgoingHistories.Qs w Amp (v.core.holdStart + t, η) := by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  rw [canonical_Qs_before w ha (by linarith [v.core.holdStart_pos]) hpulse]
  exact angularLag_hold_lower v hh1 hhlam hhT hη ht









end NavierStokes.ShapedWaitBounds
