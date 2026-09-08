import NavierStokes.LoopMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Smooth periodic tilt functions and their actual integral moments

This file advances the finite moment calculations in `LoopMoments` to genuine
smooth functions on the real line, with period `2π` and actual interval
integrals. The cosine construction realizes all nonnegative variances. A
separate, explicit amplitude bound is required to preserve the stress
projection. Smoothness in parameters is stated using the amplitude, avoiding
an incorrect claim of smoothness of the square root at zero variance.

The positive exponential tilt used by the manuscript is also treated below.
Neither a smooth variance-inversion theorem nor a full true-cone result is
assumed or asserted.
-/

namespace NavierStokes.SmoothLoop

noncomputable section

open MeasureTheory
open scoped Interval ContDiff

/-- Angular average over one full turn. -/
def angularMean (f : ℝ → ℝ) : ℝ := (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) / (2 * Real.pi)

theorem period_pos : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos

theorem period_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt period_pos

theorem angularMean_const (c : ℝ) : angularMean (fun _ => c) = c := by
  simp only [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [period_ne_zero]

theorem angularMean_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun θ => f θ + g θ) = angularMean f + angularMean g := by
  unfold angularMean
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem angularMean_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun θ => f θ - g θ) = angularMean f - angularMean g := by
  unfold angularMean
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem angularMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularMean (fun θ => c * f θ) = c * angularMean f := by
  unfold angularMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem angularMean_div_const (f : ℝ → ℝ) (c : ℝ) :
    angularMean (fun θ => f θ / c) = angularMean f / c := by
  simp only [div_eq_mul_inv, mul_comm _ c⁻¹, angularMean_const_mul]


theorem angularMean_pos (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ θ, 0 < f θ) :
    0 < angularMean f := by
  exact div_pos (intervalIntegral.intervalIntegral_pos_of_pos
    (hf.intervalIntegrable _ _) hpos period_pos) period_pos

theorem angularMean_cos : angularMean Real.cos = 0 := by
  simp [angularMean, Real.sin_two_pi]

theorem angularMean_cos_sq : angularMean (fun θ => Real.cos θ ^ 2) = 1 / 2 := by
  simp only [angularMean, integral_cos_sq, Real.sin_two_pi, Real.sin_zero,
    mul_zero, sub_zero, zero_add]
  field_simp [Real.pi_ne_zero]

/-- A smooth tilt parametrized by its mean and its (signed) amplitude. -/
def cosineTilt (m amplitude θ : ℝ) : ℝ := m + amplitude * Real.cos θ

theorem cosineTilt_periodic (m amplitude : ℝ) :
    Function.Periodic (cosineTilt m amplitude) (2 * Real.pi) := by
  intro θ
  simp only [cosineTilt, Real.cos_periodic θ]

theorem cosineTilt_contDiff (m amplitude : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (cosineTilt m amplitude) := by
  exact contDiff_const.add (contDiff_const.mul Real.contDiff_cos)


theorem cosineTilt_mean (m amplitude : ℝ) : angularMean (cosineTilt m amplitude) = m := by
  unfold cosineTilt
  rw [angularMean_add _ _ continuous_const (continuous_const.fun_mul Real.continuous_cos),
    angularMean_const, angularMean_const_mul, angularMean_cos]
  ring

theorem cosineTilt_variance (m amplitude : ℝ) :
    angularMean (fun θ => (cosineTilt m amplitude θ - m) ^ 2) = amplitude ^ 2 / 2 := by
  have heq : (fun θ => (cosineTilt m amplitude θ - m) ^ 2) =
      fun θ => amplitude ^ 2 * Real.cos θ ^ 2 := by
    funext θ
    dsimp [cosineTilt]
    ring
  rw [heq, angularMean_const_mul, angularMean_cos_sq]
  ring






/-- Variance expansion for actual angular integrals. -/
theorem angular_variance_identity (t : ℝ → ℝ) (m : ℝ)
    (ht : Continuous t) (hmean : angularMean t = m) :
    angularMean (fun θ => (t θ - m) ^ 2) = angularMean (fun θ => t θ ^ 2) - m ^ 2 := by
  have heq : (fun θ => (t θ - m) ^ 2) =
      (fun θ => (t θ ^ 2 - (2 * m) * t θ) + m ^ 2) := by
    funext θ
    ring
  rw [heq, angularMean_add _ _ ((ht.fun_pow 2).fun_sub (continuous_const.fun_mul ht)) continuous_const,
    angularMean_sub _ _ (ht.fun_pow 2) (continuous_const.fun_mul ht), angularMean_const_mul,
    angularMean_const, hmean]
  ring

theorem angular_energy_moment (t : ℝ → ℝ) (a m ρ : ℝ) (ha : a ≠ 0)
    (ht : Continuous t) (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a) :
    a * angularMean (fun θ => 1 + t θ ^ 2) = a * (1 + m ^ 2) + ρ := by
  have hv := angular_variance_identity t m ht hmean
  have hsecond : angularMean (fun θ => t θ ^ 2) = m ^ 2 + ρ / a := by linarith
  rw [angularMean_add _ _ continuous_const (ht.fun_pow 2), angularMean_const, hsecond]
  field_simp; ring

open LoopMoments in
theorem angular_rephasing_moments (t : ℝ → ℝ) (a m ρ v : ℝ)
    (ha : a ≠ 0) (hv : v ≠ 0) (ht : Continuous t) (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) :
    angularMean (fun θ => phaseDensity a v (t θ)) = 1 ∧
      angularMean (fun θ => phaseDensity a v (t θ) * loopA v (t θ)) = a ∧
      angularMean (fun θ => phaseDensity a v (t θ) * loopC v (t θ)) = a * m := by
  constructor
  · have he := angular_energy_moment t a m ρ ha ht hmean hvar
    rw [← hspeed] at he
    simp only [phaseDensity, angularMean_div_const, angularMean_const_mul, he, div_self hv]
  constructor
  · simp_rw [density_times_loopA a v _ hv]
    exact angularMean_const a
  · simp_rw [density_times_loopC a v _ hv]
    rw [angularMean_const_mul, hmean]

open LoopMoments in
theorem smooth_loop_shears (t : ℝ → ℝ) (v : ℝ)
    (ht : ContDiff ℝ (∞ : WithTop ℕ∞) t) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun θ => loopA v (t θ)) ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) (fun θ => loopC v (t θ)) := by
  have hden : ContDiff ℝ (∞ : WithTop ℕ∞) (fun θ => 1 + t θ ^ 2) :=
    contDiff_const.add (ht.pow 2)
  have hnz : ∀ θ, 1 + t θ ^ 2 ≠ 0 := fun θ => ne_of_gt (one_add_sq_pos (t θ))
  exact ⟨contDiff_const.div hden hnz, (contDiff_const.mul ht).div hden hnz⟩

open LoopMoments in
theorem periodic_loop_shears (t : ℝ → ℝ) (v : ℝ)
    (ht : Function.Periodic t (2 * Real.pi)) :
    Function.Periodic (fun θ => loopA v (t θ)) (2 * Real.pi) ∧
      Function.Periodic (fun θ => loopC v (t θ)) (2 * Real.pi) := by
  constructor <;> intro θ <;> dsimp only <;> rw [ht θ]

/-- The normalizing angular mean in the manuscript's exponential family,
using cosine instead of sine (a translation of the angular origin). -/
def expNormalizer (s : ℝ) : ℝ := angularMean (fun θ => Real.exp (s * Real.cos θ))

theorem expNormalizer_pos (s : ℝ) : 0 < expNormalizer s := by
  apply angularMean_pos
  · exact Real.continuous_exp.comp (continuous_const.fun_mul Real.continuous_cos)
  · intro θ
    exact Real.exp_pos _

theorem expNormalizer_zero : expNormalizer 0 = 1 := by
  simp only [expNormalizer, zero_mul, Real.exp_zero, angularMean_const]

def normalizedExp (s θ : ℝ) : ℝ := Real.exp (s * Real.cos θ) / expNormalizer s

theorem normalizedExp_pos (s θ : ℝ) : 0 < normalizedExp s θ :=
  div_pos (Real.exp_pos _) (expNormalizer_pos s)

theorem normalizedExp_contDiff (s : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (normalizedExp s) := by
  exact (Real.contDiff_exp.comp (contDiff_const.mul Real.contDiff_cos)).div_const _

theorem normalizedExp_periodic (s : ℝ) :
    Function.Periodic (normalizedExp s) (2 * Real.pi) := by
  intro θ
  simp only [normalizedExp, Real.cos_periodic θ]

theorem normalizedExp_mean (s : ℝ) : angularMean (normalizedExp s) = 1 := by
  unfold normalizedExp
  rw [angularMean_div_const]
  exact div_self (ne_of_gt (expNormalizer_pos s))

theorem normalizedExp_second_moment (s : ℝ) :
    angularMean (fun θ => normalizedExp s θ ^ 2) =
      expNormalizer (2 * s) / expNormalizer s ^ 2 := by
  have heq : (fun θ => normalizedExp s θ ^ 2) =
      (fun θ => Real.exp ((2 * s) * Real.cos θ) / expNormalizer s ^ 2) := by
    funext θ
    dsimp [normalizedExp]
    rw [div_pow, show (2 * s) * Real.cos θ = s * Real.cos θ + s * Real.cos θ by ring,
      Real.exp_add, pow_two]
  rw [heq, angularMean_div_const]
  rfl

theorem normalizedExp_variance (s : ℝ) :
    angularMean (fun θ => (normalizedExp s θ - 1) ^ 2) =
      expNormalizer (2 * s) / expNormalizer s ^ 2 - 1 := by
  rw [angular_variance_identity _ 1 (normalizedExp_contDiff s).continuous (normalizedExp_mean s),
    normalizedExp_second_moment]
  norm_num

/-- The divided exponential tilt. Its smooth extension at `p=0` is handled
separately below; this expression by itself is not that extension. -/
def expTilt (m d μ p θ : ℝ) : ℝ := m + (d / p) * (normalizedExp (μ * p) θ - 1)

theorem expTilt_contDiff (m d μ p : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (expTilt m d μ p) := by
  exact contDiff_const.add (contDiff_const.mul ((normalizedExp_contDiff _).sub contDiff_const))

theorem expTilt_periodic (m d μ p : ℝ) :
    Function.Periodic (expTilt m d μ p) (2 * Real.pi) := by
  intro θ
  simp only [expTilt, normalizedExp_periodic (μ * p) θ]

theorem expTilt_mean (m d μ p : ℝ) : angularMean (expTilt m d μ p) = m := by
  unfold expTilt
  rw [angularMean_add _ _ continuous_const
      (continuous_const.fun_mul ((normalizedExp_contDiff _).continuous.fun_sub continuous_const)),
    angularMean_const, angularMean_const_mul,
    angularMean_sub _ _ (normalizedExp_contDiff _).continuous continuous_const,
    normalizedExp_mean, angularMean_const]
  ring

theorem expTilt_variance (m d μ p : ℝ) :
    angularMean (fun θ => (expTilt m d μ p θ - m) ^ 2) =
      (d / p) ^ 2 * (expNormalizer (2 * (μ * p)) / expNormalizer (μ * p) ^ 2 - 1) := by
  have heq : (fun θ => (expTilt m d μ p θ - m) ^ 2) =
      fun θ => (d / p) ^ 2 * (normalizedExp (μ * p) θ - 1) ^ 2 := by
    funext θ
    dsimp [expTilt]
    ring
  rw [heq, angularMean_const_mul, normalizedExp_variance]

theorem expTilt_projection (p₁ p₂ m d μ θ : ℝ) (hp : p₂ ≠ 0) :
    p₁ + p₂ * expTilt m d μ p₂ θ =
      (p₁ + p₂ * m - d) + d * normalizedExp (μ * p₂) θ := by
  unfold expTilt
  field_simp; ring

theorem expTilt_projection_lower (p₁ p₂ m d μ : ℝ) (hp : p₂ ≠ 0) (hd : 0 < d) :
    ∀ θ, p₁ + p₂ * m - d < p₁ + p₂ * expTilt m d μ p₂ θ := by
  intro θ
  rw [expTilt_projection p₁ p₂ m d μ θ hp]
  exact lt_add_of_pos_right _ (mul_pos hd (normalizedExp_pos _ _))

/-- Correct value at vanishing transverse stress. Smooth dependence across
`p=0` is a separate analytic obligation; only angular smoothness is proved. -/
def extendedExpTilt (m d μ p : ℝ) : ℝ → ℝ :=
  if p = 0 then cosineTilt m (d * μ) else expTilt m d μ p

theorem extendedExpTilt_contDiff (m d μ p : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (extendedExpTilt m d μ p) := by
  by_cases hp : p = 0
  · simpa only [extendedExpTilt, ite_eq_left hp] using cosineTilt_contDiff m (d * μ)
  · simpa only [extendedExpTilt, ite_eq_right hp] using expTilt_contDiff m d μ p

theorem extendedExpTilt_periodic (m d μ p : ℝ) :
    Function.Periodic (extendedExpTilt m d μ p) (2 * Real.pi) := by
  by_cases hp : p = 0
  · simpa only [extendedExpTilt, ite_eq_left hp] using cosineTilt_periodic m (d * μ)
  · simpa only [extendedExpTilt, ite_eq_right hp] using expTilt_periodic m d μ p

theorem extendedExpTilt_mean (m d μ p : ℝ) :
    angularMean (extendedExpTilt m d μ p) = m := by
  by_cases hp : p = 0
  · simpa only [extendedExpTilt, ite_eq_left hp] using cosineTilt_mean m (d * μ)
  · simpa only [extendedExpTilt, ite_eq_right hp] using expTilt_mean m d μ p

theorem extendedExpTilt_variance_zero (m d μ : ℝ) :
    angularMean (fun θ => (extendedExpTilt m d μ 0 θ - m) ^ 2) = d ^ 2 * μ ^ 2 / 2 := by
  simp [extendedExpTilt, cosineTilt_variance, mul_pow]

theorem extendedExpTilt_projection_positive (p₁ p₂ m d μ : ℝ)
    (hd : 0 < d) (hmargin : 2 ≤ p₁ + p₂ * m - d) :
    ∀ θ, 2 < p₁ + p₂ * extendedExpTilt m d μ p₂ θ := by
  intro θ
  by_cases hp : p₂ = 0
  · simp only [hp, zero_mul, add_zero] at hmargin ⊢
    linarith
  · simp only [extendedExpTilt, ite_eq_right hp]
    exact lt_of_le_of_lt hmargin (expTilt_projection_lower p₁ p₂ m d μ hp hd θ)

/-- A positive normalized density on a circle, given as a smooth periodic
function on its universal covering line. The construction `densityOfTilt`
below supplies these data from the already proved moment identity. -/
structure CircleDensity where
  rate : ℝ → ℝ
  smooth : ContDiff ℝ (∞ : WithTop ℕ∞) rate
  positive : ∀ θ, 0 < rate θ
  periodic : Function.Periodic rate (2 * Real.pi)
  integral_one : (∫ θ in (0 : ℝ)..(2 * Real.pi), rate θ) = 1

def phaseMap (d : CircleDensity) (θ : ℝ) : ℝ := ∫ x in (0 : ℝ)..θ, d.rate x

theorem phaseMap_hasDerivAt (d : CircleDensity) (θ : ℝ) :
    HasDerivAt (phaseMap d) (d.rate θ) θ := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact d.smooth.continuous.intervalIntegrable _ _
  · exact d.smooth.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact d.smooth.continuous.continuousAt

theorem phaseMap_contDiff (d : CircleDensity) : ContDiff ℝ (∞ : WithTop ℕ∞) (phaseMap d) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun θ => (phaseMap_hasDerivAt d θ).differentiableAt, ?_⟩
  have heq : deriv (phaseMap d) = d.rate := funext (fun θ => (phaseMap_hasDerivAt d θ).deriv)
  rw [heq]
  exact d.smooth

theorem phaseMap_strictMono (d : CircleDensity) : StrictMono (phaseMap d) :=
  strictMono_of_hasDerivAt_pos (phaseMap_hasDerivAt d) d.positive

theorem phaseMap_zero (d : CircleDensity) : phaseMap d 0 = 0 := by simp [phaseMap]

theorem phaseMap_fullTurn (d : CircleDensity) : phaseMap d (2 * Real.pi) = 1 := d.integral_one

theorem phaseMap_add_fullTurn (d : CircleDensity) (θ : ℝ) :
    phaseMap d (θ + 2 * Real.pi) = phaseMap d θ + 1 := by
  have h := d.periodic.intervalIntegral_add_eq_add 0 θ
    (fun a b => d.smooth.continuous.intervalIntegrable a b)
  simpa only [phaseMap, zero_add, d.integral_one] using h

theorem phaseMap_int_fullTurn (d : CircleDensity) (n : ℤ) :
    phaseMap d ((n : ℝ) * (2 * Real.pi)) = (n : ℝ) := by
  have h := d.periodic.intervalIntegral_add_zsmul_eq n 0
    (fun a b => d.smooth.continuous.intervalIntegrable a b)
  simpa only [phaseMap, zero_add, d.integral_one, zsmul_eq_mul, mul_one] using h

theorem phaseMap_surjective (d : CircleDensity) : Function.Surjective (phaseMap d) := by
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt |y|
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy : -(n : ℝ) ≤ y ∧ y ≤ (n : ℝ) := by
    have h₁ := neg_abs_le y
    have h₂ := le_abs_self y
    constructor <;> linarith
  have hlo : phaseMap d (-(n : ℝ) * (2 * Real.pi)) = -(n : ℝ) := by
    simpa only [Int.cast_neg, Int.cast_natCast] using phaseMap_int_fullTurn d (-(n : ℤ))
  have hhi : phaseMap d ((n : ℝ) * (2 * Real.pi)) = (n : ℝ) := by
    simpa only [Int.cast_natCast] using phaseMap_int_fullTurn d (n : ℤ)
  have hab : -(n : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right (by linarith) (le_of_lt period_pos)
  have hmem : y ∈ Set.Icc (phaseMap d (-(n : ℝ) * (2 * Real.pi)))
      (phaseMap d ((n : ℝ) * (2 * Real.pi))) := by
    simpa only [hlo, hhi, Set.mem_Icc] using hy
  obtain ⟨θ, _, heq⟩ :=
    intermediate_value_Icc hab (phaseMap_contDiff d).continuous.continuousOn hmem
  exact ⟨θ, heq⟩

/-- The phase map is an actual global homeomorphism, not an assumed inverse. -/
def phaseHomeomorph (d : CircleDensity) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (phaseMap d) (phaseMap_strictMono d)
    (phaseMap_surjective d)).toHomeomorph

theorem phaseHomeomorph_apply (d : CircleDensity) (θ : ℝ) :
    phaseHomeomorph d θ = phaseMap d θ := rfl


theorem phaseInverse_add_one (d : CircleDensity) (φ : ℝ) :
    (phaseHomeomorph d).symm (φ + 1) = (phaseHomeomorph d).symm φ + 2 * Real.pi := by
  apply (phaseHomeomorph d).injective
  rw [(phaseHomeomorph d).apply_symm_apply, phaseHomeomorph_apply, phaseMap_add_fullTurn]
  change φ + 1 = phaseHomeomorph d ((phaseHomeomorph d).symm φ) + 1
  rw [(phaseHomeomorph d).apply_symm_apply]

def rephase (d : CircleDensity) (f : ℝ → ℝ) (φ : ℝ) : ℝ :=
  f ((phaseHomeomorph d).symm φ)


theorem rephase_periodic (d : CircleDensity) (f : ℝ → ℝ)
    (hf : Function.Periodic f (2 * Real.pi)) : Function.Periodic (rephase d f) 1 := by
  intro φ
  dsimp [rephase]
  rw [phaseInverse_add_one]
  exact hf _

theorem rephase_phaseMap (d : CircleDensity) (f : ℝ → ℝ) (θ : ℝ) :
    rephase d f (phaseMap d θ) = f θ := by
  change f ((phaseHomeomorph d).symm (phaseHomeomorph d θ)) = f θ
  rw [(phaseHomeomorph d).symm_apply_apply]

/-- The actual change of variables for the constructed smooth inverse. -/
theorem integral_rephase (d : CircleDensity) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ φ in (0 : ℝ)..1, rephase d f φ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * d.rate θ := by
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 2 * Real.pi) (f := phaseMap d) (f' := d.rate)
    (g := rephase d f) (fun θ _ => phaseMap_hasDerivAt d θ)
    d.smooth.continuous.continuousOn (hf.comp (phaseHomeomorph d).symm.continuous)
  simpa only [Function.comp_apply, rephase_phaseMap, phaseMap_zero, phaseMap_fullTurn] using hsub.symm

open LoopMoments in
def densityOfTilt (t : ℝ → ℝ) (a m ρ v : ℝ)
    (ha : 0 < a) (hv : 0 < v) (ht : ContDiff ℝ (∞ : WithTop ℕ∞) t)
    (hperiodic : Function.Periodic t (2 * Real.pi))
    (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) : CircleDensity where
  rate θ := phaseDensity a v (t θ) / (2 * Real.pi)
  smooth := ((contDiff_const.mul (contDiff_const.add (ht.pow 2))).div_const v).div_const _
  positive θ := div_pos (phaseDensity_pos a v (t θ) ha hv) period_pos
  periodic := by intro θ; dsimp only; rw [hperiodic θ]
  integral_one := by
    rw [intervalIntegral.integral_div]
    exact (angular_rephasing_moments t a m ρ v (ne_of_gt ha) (ne_of_gt hv)
      ht.continuous hmean hvar hspeed).1








end

end NavierStokes.SmoothLoop
