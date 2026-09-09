import NavierStokes.ExponentLedger
import NavierStokes.PhysicalStageBounds

/-!
# The arithmetic ledger for actual correction stages

The input of cycle `n` has accuracy `sigma n`.  Its physical increment has
index `n+1`, while a finite prefix after `J` cycles has accuracy `sigma J`.
The gain and all physical offsets below are fixed before the stage index.
This module does not assert the existence of correction cycles or their
native class estimates.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.ActualIterationLedger

/-- Accuracy of the state after this many correction cycles. -/
noncomputable def sigma (J : ℕ) : ℝ := ExponentLedger.stageParameter J

/-- The input accuracy used to construct a positive physical increment.
The value at zero is unused by the positive-stage estimates. -/
noncomputable def inputSigma (j : ℕ) : ℝ := sigma (j - 1)

/-- One common physical gain for all increment types and finite residuals. -/
noncomputable def gain (h : ℝ) (j : ℕ) : ℝ := h * (j : ℝ) / 10


@[simp] theorem sigma_zero : sigma 0 = 1 / 5 := ExponentLedger.stage_parameter_zero

theorem sigma_formula (J : ℕ) : sigma J = 1 / 5 + (J : ℝ) / 10 := rfl

theorem sigma_succ (J : ℕ) : sigma (J + 1) = sigma J + 1 / 10 :=
  ExponentLedger.stage_parameter_succ J

theorem sigma_admissible (J : ℕ) : 1 / 5 ≤ sigma J :=
  ExponentLedger.stage_parameter_admissible J


@[simp] theorem inputSigma_succ (j : ℕ) : inputSigma (j + 1) = sigma j := by
  simp [inputSigma]

theorem inputSigma_formula {j : ℕ} (hj : 1 ≤ j) :
    inputSigma j = 1 / 10 + (j : ℝ) / 10 := by
  simp only [inputSigma, sigma_formula, Nat.cast_sub hj, Nat.cast_one]
  ring



@[simp] theorem gain_zero (h : ℝ) : gain h 0 = 0 := by simp [gain]



theorem gain_nonneg {h : ℝ} (hh : 0 ≤ h) (j : ℕ) : 0 ≤ gain h j := by
  unfold gain
  positivity

theorem gain_pos {h : ℝ} (hh : 0 < h) {j : ℕ} (hj : 1 ≤ j) : 0 < gain h j := by
  have hn : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  unfold gain
  positivity

theorem gain_monotone {h : ℝ} (hh : 0 ≤ h) : Monotone (gain h) := by
  intro j k hjk
  have hk : (j : ℝ) ≤ k := by exact_mod_cast hjk
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hh) (by norm_num)


theorem gain_add_tendsto_atTop {h : ℝ} (hh : 0 < h) (a : ℝ) :
    Tendsto (fun j => gain h j + a) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt (10 * (b - a) / h)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hn : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hp := (div_lt_iff₀ hh).mp hN
  have hm := mul_le_mul_of_nonneg_left hn hh.le
  unfold gain
  nlinarith

theorem gain_tendsto_atTop {h : ℝ} (hh : 0 < h) : Tendsto (gain h) atTop atTop := by
  simpa only [add_zero] using gain_add_tendsto_atTop hh 0





/-! ## The native increment exponents and their physical comparison -/

/-- Conservative class for the actual wave potential.  The local inverse
frequency can give an additional half power, which is not needed here. -/
noncomputable def waveNative (κ : ℝ) (j : ℕ) : ℝ :=
  ExponentLedger.waveExponent (inputSigma j) - κ

noncomputable def wavePressureNative (κ : ℝ) (j : ℕ) : ℝ := waveNative κ j + 1 / 2

noncomputable def meanNative (κ : ℝ) (j : ℕ) : ℝ :=
  ExponentLedger.meanUpdateExponent (inputSigma j) κ


theorem waveNative_formula (κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    waveNative κ j = (j : ℝ) / 10 + (3 / 5 - κ) := by
  rw [waveNative, ExponentLedger.waveExponent, inputSigma_formula hj]
  ring

theorem wavePressureNative_formula (κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    wavePressureNative κ j = (j : ℝ) / 10 + (11 / 10 - κ) := by
  rw [wavePressureNative, waveNative_formula κ hj]
  ring

theorem meanNative_formula (κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    meanNative κ j = (j : ℝ) / 10 + (11 / 10 - 2 * κ) := by
  rw [meanNative, ExponentLedger.meanUpdateExponent, ExponentLedger.meanExponent, inputSigma_formula hj]
  ring


theorem wave_physical_gap (h κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    h * waveNative κ j = gain h j + h * (3 / 5 - κ) := by
  rw [waveNative_formula κ hj]
  unfold gain
  ring

theorem pressure_physical_gap (h κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    h * wavePressureNative κ j = gain h j + h * (11 / 10 - κ) := by
  rw [wavePressureNative_formula κ hj]
  unfold gain
  ring

theorem mean_physical_gap (h κ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    h * meanNative κ j = gain h j + h * (11 / 10 - 2 * κ) := by
  rw [meanNative_formula κ hj]
  unfold gain
  ring

theorem gain_le_wave {h κ : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) {j : ℕ} (hj : 1 ≤ j) :
    gain h j ≤ h * waveNative κ j := by
  rw [wave_physical_gap h κ hj]
  exact le_add_of_nonneg_right (mul_nonneg hh (by linarith))

theorem gain_le_wavePressure {h κ : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) {j : ℕ} (hj : 1 ≤ j) :
    gain h j ≤ h * wavePressureNative κ j := by
  rw [pressure_physical_gap h κ hj]
  exact le_add_of_nonneg_right (mul_nonneg hh (by linarith))

theorem gain_le_mean {h κ : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000) {j : ℕ} (hj : 1 ≤ j) :
    gain h j ≤ h * meanNative κ j := by
  rw [mean_physical_gap h κ hj]
  exact le_add_of_nonneg_right (mul_nonneg hh (by linarith))


structure Offsets where
  wavePotential : ℝ
  meanStream : ℝ
  directAngular : ℝ
  wavePressure : ℝ
  meanPressure : ℝ



/-! ## Residual indexing after a finite number of cycles -/

noncomputable def residualWave (J : ℕ) : ℝ := ExponentLedger.waveExponent (sigma J)

theorem residualWave_formula (J : ℕ) : residualWave J = (J : ℝ) / 10 + 7 / 10 := by
  rw [residualWave, ExponentLedger.waveExponent, sigma_formula]
  ring





theorem residual_physical_gap (h : ℝ) (J : ℕ) :
    h * residualWave J = gain h J + 7 * h / 10 := by
  rw [residualWave_formula]
  unfold gain
  ring


theorem gain_le_residualWave {h : ℝ} (hh : 0 ≤ h) (J : ℕ) :
    gain h J ≤ h * residualWave J := by
  rw [residual_physical_gap]
  linarith











/-! ## Binding the ledger to the actual physical-stage interface -/

section StageInputs

open PhysicalStageBounds ProblemStatement

variable {h κ qbig : ℝ}
  {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- Only native exponent metadata occur here.  The physical fields, charts,
regularity and local class estimates are those in the supplied `WaveData`
and `MeanData`.  The sharper potential class may be weakened to `B−κ`. -/
structure StageMetadata
    (WA : ℕ → WaveData h DA IA KA (Fin 3))
    (MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (MB : ℕ → MeanData h (CoordinateAlgebra.A h))
    (WP : ℕ → WaveData h DP IP KP Unit)
    (MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h)) (κ : ℝ) : Prop where
  wavePotential : ∀ j, 1 ≤ j → waveNative κ j ≤ (WA j).alpha
  wavePotentialShift : ∀ j, 1 ≤ j → -h ≤ (WA j).shift
  meanStream : ∀ j, 1 ≤ j → meanNative κ j ≤ (MA j).alpha
  directAngular : ∀ j, 1 ≤ j → meanNative κ j ≤ (MB j).alpha
  wavePressure : ∀ j, 1 ≤ j → wavePressureNative κ j ≤ (WP j).alpha
  wavePressureShift : ∀ j, 1 ≤ j → -(2 * CoordinateAlgebra.A h) ≤ (WP j).shift
  meanPressure : ∀ j, 1 ≤ j → meanNative κ j ≤ (MP j).alpha

variable {WA : ℕ → WaveData h DA IA KA (Fin 3)}
  {MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2)}
  {MB : ℕ → MeanData h (CoordinateAlgebra.A h)}
  {WP : ℕ → WaveData h DP IP KP Unit}
  {MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h)}



end StageInputs


end NavierStokes.ActualIterationLedger
