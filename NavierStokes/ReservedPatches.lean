import NavierStokes.HeatedOutgoing
import NavierStokes.FiveProfileMoments

/-!
# Four disjoint reservations on the actual outgoing shaped wait

The log intervals are the four examples in the manuscript: (-25,-20),
(-20,-15), (-14,-9), and (-8,-3), relative to the pulse entrance.
The first is the five-row repair after radial modulation. The second is the
existing heat-compensation patch. The last two remain pure powers after that
heat correction. All fields below use the same outgoing profile.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators
open NavierStokes.OutgoingProfile (Profile)

namespace NavierStokes.ReservedPatches

inductive Slot where
  | modulation
  | heat
  | positive
  | mean
  deriving DecidableEq

noncomputable def leftOffset : Slot → ℝ
  | .modulation => -25
  | .heat => -20
  | .positive => -14
  | .mean => -8

noncomputable def rightOffset : Slot → ℝ
  | .modulation => -20
  | .heat => -15
  | .positive => -9
  | .mean => -3

theorem offset_width (s : Slot) : rightOffset s = leftOffset s + 5 := by
  cases s <;> norm_num [leftOffset, rightOffset]

theorem offset_bounds (s : Slot) :
    -25 ≤ leftOffset s ∧ leftOffset s < rightOffset s ∧ rightOffset s ≤ -3 := by
  cases s <;> norm_num [leftOffset, rightOffset]

theorem offsets_separated {s t : Slot} (hst : s ≠ t) :
    rightOffset s ≤ leftOffset t ∨ rightOffset t ≤ leftOffset s := by
  cases s <;> cases t <;> simp_all [leftOffset, rightOffset] <;> norm_num

noncomputable def leftClock (F : Profile) (s : Slot) : ℝ :=
  F.data.core.pulseStart + leftOffset s

noncomputable def rightClock (F : Profile) (s : Slot) : ℝ :=
  F.data.core.pulseStart + rightOffset s

noncomputable def left (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  OutgoingDilation.radius XR (leftClock F s)

noncomputable def right (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  OutgoingDilation.radius XR (rightClock F s)

noncomputable def window (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Ioo (left F XR s) (right F XR s)

theorem radius_strictMono (XR : ℝ) (hXR : 0 < XR) :
    StrictMono (OutgoingDilation.radius XR) := by
  intro a b hab
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hab) hXR

theorem left_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < left F XR s := OutgoingDilation.radius_pos XR _ hXR

theorem left_lt_right (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    left F XR s < right F XR s := by
  apply radius_strictMono XR hXR
  exact add_lt_add_right (offset_bounds s).2.1 _

theorem right_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < right F XR s := (left_pos F XR hXR s).trans (left_lt_right F XR hXR s)

theorem mem_window_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (s : Slot) {X : ℝ} (hX : X ∈ window F XR s) : 0 < X :=
  (left_pos F XR hXR s).trans hX.1



theorem clock_bounds (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    {X : ℝ} (hX : X ∈ window F XR s) :
    leftClock F s < OutgoingDilation.clock XR X ∧
      OutgoingDilation.clock XR X < rightClock F s := by
  have hp := mem_window_pos F XR hXR s hX
  constructor
  · exact (OutgoingDilation.radius_lt_iff XR X _ hXR hp).mp hX.1
  · by_contra hn
    have hr := (OutgoingDilation.radius_le_iff XR X (rightClock F s) hXR hp).mpr
      (le_of_not_gt hn)
    exact (not_le_of_gt hX.2) hr

theorem clock_inside_wait (F : Profile) (s : Slot) :
    F.data.core.holdStart < leftClock F s ∧ rightClock F s < F.data.core.pulseStart := by
  obtain ⟨hlo, _, hhi⟩ := offset_bounds s
  dsimp only [leftClock, rightClock, OutgoingSchedule.Parameters.pulseStart]
  constructor <;> linarith [F.data.core.wait_gt]

theorem window_inside_wait (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (s : Slot) {X : ℝ} (hX : X ∈ window F XR s) :
    F.data.core.holdStart < OutgoingDilation.clock XR X ∧
      OutgoingDilation.clock XR X < F.data.core.pulseStart := by
  obtain ⟨hl, hr⟩ := clock_bounds F XR hXR s hX
  obtain ⟨hwl, hwr⟩ := clock_inside_wait F s
  exact ⟨hwl.trans hl, hr.trans hwr⟩



theorem pulse_before_switch (F : Profile) :
    F.data.core.pulseStart < HeatTailEdit.switchStart F.data := by
  have hp := F.data.core.pulseLength_pos
  have hf := OutgoingTail.flattenEnd_gt_core F.data
  have hr := OutgoingTail.releaseStart_gt_flattenEnd F.data
  have ht := OutgoingTail.tailStart_gt_release F.data
  dsimp only [OutgoingSchedule.Parameters.endpoint] at hf
  dsimp only [HeatTailEdit.switchStart]
  linarith

theorem right_before_switch (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    right F XR s < OutgoingDilation.switchRadius F XR := by
  apply radius_strictMono XR hXR
  exact (clock_inside_wait F s).2.trans (pulse_before_switch F)

theorem heat_left (F : Profile) (XR : ℝ) :
    left F XR .heat = OutgoingDilation.patchRadius F XR := by
  simp only [left, leftClock, leftOffset, OutgoingDilation.patchRadius,
    OutgoingDilation.patchClock, sub_eq_add_neg]

theorem right_eq_left_mul_exp (F : Profile) (XR : ℝ) (s : Slot) :
    right F XR s = left F XR s * Real.exp 5 := by
  unfold right left OutgoingDilation.radius rightClock leftClock
  rw [offset_width, ← add_assoc, Real.exp_add]
  ring

theorem heat_right (F : Profile) (XR : ℝ) :
    right F XR .heat = OutgoingDilation.patchRadius F XR *
      OutgoingDilation.compensationPatch.right := by
  rw [right_eq_left_mul_exp, heat_left]
  rfl

/-! ## Closed support regions with strict margins in the four windows -/

noncomputable def innerLower : Slot → ℝ
  | .heat => TerminalCompensation.lower OutgoingDilation.compensationPatch 0
  | _ => Real.exp 1

noncomputable def innerUpper : Slot → ℝ
  | .heat => TerminalCompensation.upper OutgoingDilation.compensationPatch 2
  | _ => Real.exp 4

theorem inner_bounds (s : Slot) :
    1 < innerLower s ∧ innerLower s < innerUpper s ∧ innerUpper s < Real.exp 5 := by
  cases s with
  | heat =>
    refine ⟨TerminalCompensation.lower_gt_left OutgoingDilation.compensationPatch 0, ?_,
      TerminalCompensation.upper_lt_right OutgoingDilation.compensationPatch 2⟩
    have h := OutgoingDilation.compensationPatch.ordered
    norm_num [innerLower, innerUpper, TerminalCompensation.lower, TerminalCompensation.upper] at *
    linarith
  | modulation | positive | mean =>
    simp only [innerLower, innerUpper]
    exact ⟨by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num),
      Real.exp_lt_exp.mpr (by norm_num), Real.exp_lt_exp.mpr (by norm_num)⟩

noncomputable def supportLeft (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  left F XR s * innerLower s

noncomputable def supportRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  left F XR s * innerUpper s

noncomputable def closedPatch (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Icc (supportLeft F XR s) (supportRight F XR s)



theorem support_margins (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    left F XR s < supportLeft F XR s ∧
      supportLeft F XR s < supportRight F XR s ∧
      supportRight F XR s < right F XR s := by
  obtain ⟨hl, hm, hr⟩ := inner_bounds s
  have hp := left_pos F XR hXR s
  refine ⟨?_, mul_lt_mul_of_pos_left hm hp, ?_⟩
  · unfold supportLeft
    simpa only [mul_one] using mul_lt_mul_of_pos_left hl hp
  · rw [right_eq_left_mul_exp]
    exact mul_lt_mul_of_pos_left hr hp

theorem supportLeft_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < supportLeft F XR s :=
  (left_pos F XR hXR s).trans (support_margins F XR hXR s).1

theorem closedPatch_subset (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    closedPatch F XR s ⊆ window F XR s := by
  intro X hX
  obtain ⟨hl, _, hr⟩ := support_margins F XR hXR s
  exact ⟨hl.trans_le hX.1, hX.2.trans_lt hr⟩



noncomputable def momentPatch (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (s : Slot) : FiveProfileMoments.Patch where
  left := supportLeft F XR s
  right := supportRight F XR s
  left_pos := supportLeft_pos F XR hXR s
  ordered := (support_margins F XR hXR s).2.1

/-! ## Exact fields on the actual, common outgoing profile -/

noncomputable def xAmplitude (F : Profile) (XR eta : ℝ) : ℝ :=
  OutgoingSchedule.radialAmplitude F.data.core.P F.data.core.dropLength F.data.core.lam
    F.data.core.holdStart * OutgoingSchedule.shape eta *
      Real.exp ((1 / 2 + F.data.core.lam) * (Real.log XR + F.data.core.holdStart))

theorem xAmplitude_pos (F : Profile) (XR eta : ℝ) : 0 < xAmplitude F XR eta := by
  apply mul_pos
  · exact mul_pos (mul_pos F.data.core.P_pos (Real.exp_pos _)) (OutgoingSchedule.shape_pos eta)
  · exact Real.exp_pos _

theorem xAmplitude_contDiff (F : Profile) (XR : ℝ) : ContDiff ℝ ∞ (xAmplitude F XR) :=
  (contDiff_const.mul OutgoingSchedule.shape_contDiff).mul contDiff_const

theorem xAmplitude_shape (F : Profile) (XR eta : ℝ) :
    xAmplitude F XR eta = xAmplitude F XR 0 / (1 + eta ^ 2) := by
  simp only [xAmplitude, OutgoingSchedule.shape, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, inv_one, mul_one, div_eq_mul_inv]
  ring

theorem clean_E_shaped (F : Profile) (XR eta X : ℝ) (hXR : 0 < XR) (hX : 0 < X)
    (hlo : F.data.core.holdStart ≤ OutgoingDilation.clock XR X)
    (hhi : OutgoingDilation.clock XR X ≤ F.data.core.pulseStart) :
    OutgoingDilation.E F XR (X, eta) =
      xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  have he : OutgoingDilation.clock XR X ≤ F.data.core.endpoint := by
    dsimp only [OutgoingSchedule.Parameters.endpoint]
    linarith [F.data.core.pulseLength_pos]
  change F.logE (OutgoingDilation.clock XR X, eta) = _
  rw [F.logE_before eta he, OutgoingSchedule.angular_shaped_wait F.data.core eta hlo]
  unfold xAmplitude
  rw [Real.rpow_def_of_pos hX]
  have hex :
      -(1 / 2 + F.data.core.lam) * (OutgoingDilation.clock XR X - F.data.core.holdStart) =
      (1 / 2 + F.data.core.lam) * (Real.log XR + F.data.core.holdStart) +
        Real.log X * -(1 / 2 + F.data.core.lam) := by
    rw [OutgoingDilation.clock, Real.log_div hX.ne' hXR.ne']
    ring
  rw [hex, Real.exp_add]
  ring

theorem clean_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    OutgoingDilation.U F XR (X, eta) = 0 ∧
      OutgoingDilation.E F XR (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  obtain ⟨hlo, hhi⟩ := window_inside_wait F XR hXR s hX
  refine ⟨?_, clean_E_shaped F XR eta X hXR (mem_window_pos F XR hXR s hX) hlo.le hhi.le⟩
  exact OutgoingSchedule.axial_shaped_wait F.data.core F.amp eta hlo.le hhi.le

theorem heated_E_eq_clean (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    HeatedOutgoing.E F XR c (X, eta) = OutgoingDilation.E F XR (X, eta) := by
  have hp := mem_window_pos F XR hXR s hX
  rcases offsets_separated hs with h | h
  · apply HeatedOutgoing.E_before_patch F XR c eta X hXR hp
    rw [← heat_left]
    exact hX.2.le.trans ((radius_strictMono XR hXR).monotone (add_le_add_right h _))
  · apply HeatedOutgoing.E_between_patch_and_switch F XR c eta X hXR hp
    · rw [← heat_right]
      exact ((radius_strictMono XR hXR).monotone (add_le_add_right h _)).trans hX.1.le
    · exact hX.2.le.trans (right_before_switch F XR hXR s).le

/-- The heat slot is deliberately excluded: its additive correction is real. -/
theorem heated_fields (F : Profile) (XR : ℝ) (hXR : 0 < XR)
    (c : ℝ → HeatedOutgoing.Coeff) {s : Slot} (hs : s ≠ .heat)
    (eta : ℝ) {X : ℝ} (hX : X ∈ window F XR s) :
    HeatedOutgoing.U F XR (X, eta) = 0 ∧
      HeatedOutgoing.E F XR c (X, eta) =
        xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam)) := by
  rw [heated_E_eq_clean F XR hXR c hs eta hX]
  exact clean_fields F XR hXR s eta hX




/-! ## The heat correction lies in its own closed interior support region -/






/-! ## Conversion to the similarity radius R, where X = R squared / 2 -/

noncomputable def radialLeft (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * left F XR s)

noncomputable def radialRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * right F XR s)

noncomputable def radialSupportLeft (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * supportLeft F XR s)

noncomputable def radialSupportRight (F : Profile) (XR : ℝ) (s : Slot) : ℝ :=
  Real.sqrt (2 * supportRight F XR s)

noncomputable def radialWindow (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Ioo (radialLeft F XR s) (radialRight F XR s)

noncomputable def radialClosedPatch (F : Profile) (XR : ℝ) (s : Slot) : Set ℝ :=
  Icc (radialSupportLeft F XR s) (radialSupportRight F XR s)

theorem radialLeft_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < radialLeft F XR s :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (left_pos F XR hXR s))

theorem radial_left_lt_right (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    radialLeft F XR s < radialRight F XR s :=
  Real.sqrt_lt_sqrt (mul_nonneg (by norm_num) (left_pos F XR hXR s).le)
    (mul_lt_mul_of_pos_left (left_lt_right F XR hXR s) (by norm_num))

theorem radial_support_margins (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    radialLeft F XR s < radialSupportLeft F XR s ∧
      radialSupportLeft F XR s < radialSupportRight F XR s ∧
      radialSupportRight F XR s < radialRight F XR s := by
  obtain ⟨hl, hm, hr⟩ := support_margins F XR hXR s
  have ha := left_pos F XR hXR s
  have hb := ha.trans hl
  have hc := hb.trans hm
  exact ⟨Real.sqrt_lt_sqrt (by positivity) (by nlinarith),
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith),
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith)⟩

theorem radialSupportLeft_pos (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    0 < radialSupportLeft F XR s :=
  (radialLeft_pos F XR hXR s).trans (radial_support_margins F XR hXR s).1

theorem square_half_mem_Ioo {a b R : ℝ} (ha : 0 < a)
    (hR : R ∈ Ioo (Real.sqrt (2 * a)) (Real.sqrt (2 * b))) :
    R ^ 2 / 2 ∈ Ioo a b := by
  have hRp : 0 < R := (Real.sqrt_pos.mpr (mul_pos (by norm_num) ha)).trans hR.1
  have hb : 0 < b := by
    have hsb : 0 < Real.sqrt (2 * b) := hRp.trans hR.2
    have h2b := Real.sqrt_pos.mp hsb
    linarith
  have hl := (sq_lt_sq₀ (Real.sqrt_nonneg (2 * a)) hRp.le).mpr hR.1
  have hr := (sq_lt_sq₀ hRp.le (Real.sqrt_nonneg (2 * b))).mpr hR.2
  rw [Real.sq_sqrt (by positivity)] at hl
  rw [Real.sq_sqrt (by positivity)] at hr
  constructor <;> nlinarith


theorem radial_mem_window (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot)
    {R : ℝ} (hR : R ∈ radialWindow F XR s) : R ^ 2 / 2 ∈ window F XR s :=
  square_half_mem_Ioo (left_pos F XR hXR s) hR


theorem radial_closedPatch_subset (F : Profile) (XR : ℝ) (hXR : 0 < XR) (s : Slot) :
    radialClosedPatch F XR s ⊆ radialWindow F XR s := by
  intro R hR
  obtain ⟨hl, _, hr⟩ := radial_support_margins F XR hXR s
  exact ⟨hl.trans_le hR.1, hR.2.trans_lt hr⟩



noncomputable def radialAmplitude (F : Profile) (XR eta : ℝ) : ℝ :=
  xAmplitude F XR eta * (2 : ℝ) ^ (1 / 2 + F.data.core.lam)

theorem radialAmplitude_pos (F : Profile) (XR eta : ℝ) :
    0 < radialAmplitude F XR eta :=
  mul_pos (xAmplitude_pos F XR eta) (Real.rpow_pos_of_pos (by norm_num) _)

theorem radialAmplitude_contDiff (F : Profile) (XR : ℝ) :
    ContDiff ℝ ∞ (radialAmplitude F XR) :=
  (xAmplitude_contDiff F XR).mul contDiff_const

theorem radialAmplitude_shape (F : Profile) (XR eta : ℝ) :
    radialAmplitude F XR eta = radialAmplitude F XR 0 / (1 + eta ^ 2) := by
  simp only [radialAmplitude]
  rw [xAmplitude_shape F XR eta]
  ring

theorem square_half_power (lam R : ℝ) (hR : 0 < R) :
    (R ^ 2 / 2) ^ (-(1 / 2 + lam)) =
      (2 : ℝ) ^ (1 / 2 + lam) * R ^ (-1 - 2 * lam) := by
  have hX : 0 < R ^ 2 / 2 := by positivity
  rw [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hR, ← Real.exp_add,
    Real.log_div (pow_ne_zero 2 hR.ne') (by norm_num), Real.log_pow]
  congr 1
  ring




/-! ## Supported perturbations preserve the other complete open windows -/

def Supported (F : Profile) (XR : ℝ) (s : Slot) (v : ℝ × ℝ → ℝ) : Prop :=
  ∀ eta, support (fun X => v (X, eta)) ⊆ closedPatch F XR s














end NavierStokes.ReservedPatches
