import NavierStokes.SmoothFourierData
import NavierStokes.TransportPrimitive
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The actual smooth torus inverse with an external real parameter

The coefficients are the integrals of the given function. Local uniform
decay is obtained from genuine derivatives on compact parameter intervals.
-/

noncomputable section

namespace NavierStokes.ParametricTorusInverse

open Set Filter MeasureTheory
open TorusInverse
open scoped Topology ContDiff BigOperators

abbrev Point := ℝ × Plane
abbrev Source := Point → ℂ

noncomputable def slice (f : Source) (p : ℝ) : Plane → ℂ := fun Y => f (p, Y)


noncomputable def parameterPartial (f : Source) (z : Point) : ℂ :=
  fderiv ℝ f z (1, 0)


noncomputable def parameterJet (n : ℕ) (f : Source) : Source := parameterPartial^[n] f



noncomputable def coefficient (f : Source) (p : ℝ) (k : Frequency) : ℂ :=
  SmoothFourierData.coefficient (slice f p) k

noncomputable def mean (f : Source) (p : ℝ) : ℂ := coefficient f p 0


noncomputable def inverse (d : Direction) (f : Source) (z : Point) : ℂ :=
  directionalInverse d (coefficient f z.1) z.2

noncomputable def iterateInverse (d : Direction) (n : ℕ) (f : Source) : Source :=
  (inverse d)^[n] f

theorem mean_eq_integral (f : Source) (p : ℝ) :
    mean f p = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (p, (x, y)) :=
  SmoothFourierData.coefficient_zero_eq_integral _












theorem parameter_slice_hasDerivAt {f : Source} (hf : ContDiff ℝ ∞ f)
    (p : ℝ) (Y : Plane) :
    HasDerivAt (fun q => f (q, Y)) (parameterPartial f (p, Y)) p := by
  exact ((hf.differentiable (by simp)) (p, Y)).hasFDerivAt.comp_hasDerivAt p
    ((hasDerivAt_id p).prodMk (hasDerivAt_const p Y))




theorem kernel_eq_mode (k : Frequency) (Y : Plane) :
    SmoothFourierData.kernel k Y = mode (-k) Y := by
  rw [mode_eq_torusMode]
  rfl

theorem mode_smooth (k : Frequency) : ContDiff ℝ ∞ (mode k) :=
  Complex.contDiff_exp.comp (phase k).contDiff

theorem kernel_smooth (k : Frequency) : ContDiff ℝ ∞ (SmoothFourierData.kernel k) := by
  simpa only [funext (kernel_eq_mode k)] using mode_smooth (-k)

/-- Differentiation of an actual fixed-interval integral. -/
theorem integral_hasDerivAt {g g' : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hd : ∀ p u, HasDerivAt (fun q => g (q, u)) (g' (p, u)) p)
    (a b p : ℝ) :
    HasDerivAt (fun q => ∫ u in a..b, g (q, u)) (∫ u in a..b, g' (p, u)) p := by
  have hh := (TransportPrimitive.parameterIntegral_hasFDerivAt hg a b p).hasDerivAt
  have hi : IntervalIntegrable (fun u => TransportPrimitive.parameterDerivative g (p, u))
      volume a b :=
    ((TransportPrimitive.parameterDerivative_contDiff hg).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  rw [ContinuousLinearMap.intervalIntegral_apply hi (1 : ℝ)] at hh
  convert! hh using 1
  apply intervalIntegral.integral_congr
  intro u hu
  exact ((TransportPrimitive.parameter_hasFDerivAt hg p u).hasDerivAt.unique (hd p u)).symm

noncomputable def weightedSource (k : Frequency) (f : Source) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  SmoothFourierData.kernel k (q.2, q.1.2) * f (q.1.1, (q.2, q.1.2))

theorem weightedSource_smooth {f : Source} (hf : ContDiff ℝ ∞ f) (k : Frequency) :
    ContDiff ℝ ∞ (weightedSource k f) :=
  ((kernel_smooth k).comp (contDiff_snd.prodMk contDiff_fst.snd)).mul
    (hf.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)))


theorem coefficient_hasDerivAt {f : Source} (hf : ContDiff ℝ ∞ f)
    (k : Frequency) (p : ℝ) :
    HasDerivAt (fun q => coefficient f q k) (coefficient (parameterPartial f) p k) p := by
  let inner : ℝ × ℝ → ℂ := fun q => ∫ x in (0 : ℝ)..1, weightedSource k f (q, x)
  let innerD : ℝ × ℝ → ℂ := fun q => ∫ x in (0 : ℝ)..1,
    weightedSource k (parameterPartial f) (q, x)
  have hi : ContDiff ℝ ∞ inner :=
    TransportPrimitive.parameterIntegral_contDiff (weightedSource_smooth hf k) 0 1
  have hd : ∀ q y, HasDerivAt (fun u => inner (u, y)) (innerD (q, y)) q := by
    intro q y
    have hy : ContDiff ℝ ∞ (fun z : ℝ × ℝ => weightedSource k f ((z.1, y), z.2)) :=
      ((weightedSource_smooth hf k).comp
        ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    exact integral_hasDerivAt
      (g' := fun z : ℝ × ℝ => weightedSource k (parameterPartial f) ((z.1, y), z.2))
      hy (fun u x => by
        simpa only [weightedSource] using
          (parameter_slice_hasDerivAt hf u (x, y)).const_mul
            (SmoothFourierData.kernel k (x, y))) 0 1 q
  have ho := integral_hasDerivAt hi hd 0 1 p
  simpa only [coefficient, SmoothFourierData.coefficient_eq_doubleIntegral, slice,
    inner, innerD, weightedSource] using ho



def PolynomialGrowth (m : Frequency → ℂ) : Prop :=
  ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖m k‖ ≤ C * weight k ^ s

noncomputable def multiplierX (m : Frequency → ℂ) (k : Frequency) : ℂ := freqX k * m k
noncomputable def multiplierY (m : Frequency → ℂ) (k : Frequency) : ℂ := freqY k * m k

theorem PolynomialGrowth.mulX {m : Frequency → ℂ} (hm : PolynomialGrowth m) :
    PolynomialGrowth (multiplierX m) := by
  obtain ⟨s, C, hC, hm⟩ := hm
  refine ⟨s + 1, ‖omega‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro k
  have hw := (weight_pos k).le
  calc
    ‖multiplierX m k‖ = ‖freqX k‖ * ‖m k‖ := norm_mul _ _
    _ ≤ (‖omega‖ * weight k) * (C * weight k ^ s) :=
      mul_le_mul (norm_freqX_le k) (hm k) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem PolynomialGrowth.mulY {m : Frequency → ℂ} (hm : PolynomialGrowth m) :
    PolynomialGrowth (multiplierY m) := by
  obtain ⟨s, C, hC, hm⟩ := hm
  refine ⟨s + 1, ‖omega‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro k
  have hw := (weight_pos k).le
  calc
    ‖multiplierY m k‖ = ‖freqY k‖ * ‖m k‖ := norm_mul _ _
    _ ≤ (‖omega‖ * weight k) * (C * weight k ^ s) :=
      mul_le_mul (norm_freqY_le k) (hm k) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem inverseMultiplier_growth (d : Direction) : PolynomialGrowth (multiplier d) :=
  ⟨1, 6 * ‖omega⁻¹‖, by positivity, fun k => by simpa using norm_multiplier_le d k⟩

theorem PolynomialGrowth.rapid_mul {m a : Frequency → ℂ} (hm : PolynomialGrowth m)
    (ha : Rapid a) : Rapid (fun k => m k * a k) := by
  obtain ⟨s, C, hC, hm⟩ := hm
  intro n
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le n) (norm_nonneg _))
    _ ((ha (n + s)).mul_left C)
  intro k
  have hw := (weight_pos k).le
  calc
    weight k ^ n * ‖m k * a k‖ = weight k ^ n * (‖m k‖ * ‖a k‖) := by rw [norm_mul]
    _ ≤ weight k ^ n * ((C * weight k ^ s) * ‖a k‖) := by
      gcongr
      exact hm k
    _ = _ := by rw [pow_add]; ring

theorem multiplied_coeff_bound {m a : Frequency → ℂ} {s : ℕ} {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ k, ‖m k‖ ≤ C * weight k ^ s)
    (ha : ∀ k, weight k ^ (s + 4) * ‖a k‖ ≤ B) (k : Frequency) :
    ‖m k * a k‖ ≤ (C * B) * (weight k ^ 4)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
  calc
    ‖m k * a k‖ * weight k ^ 4 ≤
        ((C * weight k ^ s) * ‖a k‖) * weight k ^ 4 := by
      rw [norm_mul]
      gcongr
      exact hm k
    _ = C * (weight k ^ (s + 4) * ‖a k‖) := by rw [pow_add]; ring
    _ ≤ C * B := mul_le_mul_of_nonneg_left (ha k) hC





noncomputable def jointDP : Point →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Plane
noncomputable def jointDX : Point →L[ℝ] ℝ :=
  TorusInverse.dx.comp (ContinuousLinearMap.snd ℝ ℝ Plane)
noncomputable def jointDY : Point →L[ℝ] ℝ :=
  TorusInverse.dy.comp (ContinuousLinearMap.snd ℝ ℝ Plane)

noncomputable def jointLiftP : ℂ →L[ℝ] (Point →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Point ℂ jointDP
noncomputable def jointLiftX : ℂ →L[ℝ] (Point →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Point ℂ jointDX
noncomputable def jointLiftY : ℂ →L[ℝ] (Point →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Point ℂ jointDY


noncomputable def multiplierTermDerivative (m : Frequency → ℂ) (f : Source)
    (k : Frequency) (z : Point) : Point →L[ℝ] ℂ :=
  jointLiftP (m k * coefficient (parameterPartial f) z.1 k * mode k z.2) +
  jointLiftX (multiplierX m k * coefficient f z.1 k * mode k z.2) +
  jointLiftY (multiplierY m k * coefficient f z.1 k * mode k z.2)
















@[simp] theorem parameterJet_zero (f : Source) : parameterJet 0 f = f := rfl

theorem parameterJet_succ (n : ℕ) (f : Source) :
    parameterJet (n + 1) f = parameterPartial (parameterJet n f) :=
  Function.iterate_succ_apply' _ _ _




theorem iterateInverse_succ (d : Direction) (n : ℕ) (f : Source) :
    iterateInverse d (n + 1) f = inverse d (iterateInverse d n f) :=
  Function.iterate_succ_apply' _ _ _












end NavierStokes.ParametricTorusInverse
