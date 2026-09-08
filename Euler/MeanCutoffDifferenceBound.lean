import Euler.MeanBoundaryDifference
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Uniform bounds for actual cutoff difference quotients from classical derivative bounds. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanCutoffCurl
open scoped ContDiff ENNReal

/-- A support-volume bound, derived from the genuine Lp seminorm. -/
theorem lpNorm_le_bound_volume {E : Type*} [NormedAddCommGroup E]
    (f : Space → E) (hf : AEStronglyMeasurable f volume) (K : Set Space)
    (hK : volume K ≠ (∞ : ℝ≥0∞)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) (hzero : ∀ x ∉ K, f x = 0) (p : ℝ≥0∞) :
    lpNorm f p volume ≤ C * (volume K).toReal ^ (1 / p.toReal) := by
  have he : eLpNorm f p volume ≤ ENNReal.ofReal C * volume K ^ (1 / p.toReal) := by
    calc
      _ ≤ eLpNorm (K.indicator (fun _ : Space => C)) p volume := by
        apply eLpNorm_mono
        intro x
        by_cases hx : x ∈ K
        · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hC] using hbound x
        · simp only [Set.indicator_of_notMem hx, hzero x hx, norm_zero, le_refl]
      _ ≤ _ := by
        simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC] using
          (eLpNorm_indicator_const_le (μ := (volume : Measure Space)) (s := K) C p)
  have hfinite : ENNReal.ofReal C * volume K ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK)
  have H := ENNReal.toReal_mono hfinite he
  simpa only [toReal_eLpNorm hf, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_rpow] using H

/-- The classical mean value inequality bounds a directional difference quotient uniformly. -/
theorem norm_differenceQuotient_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) (hf : Differentiable ℝ f) (M : ℝ) (hM : 0 ≤ M)
    (hDf : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (a : Space) (h : ℝ) (x : Space) :
    ‖h⁻¹ • (f (x + h • a) - f x)‖ ≤ M * ‖a‖ := by
  by_cases hh : h = 0
  · simp only [hh, inv_zero, zero_smul, norm_zero]
    exact mul_nonneg hM (norm_nonneg a)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := f) (s := Set.univ) (C := M) (x := x) (y := x+h•a)
    (fun y _ => hf y) (fun y _ => hDf y) (convex_univ : Convex ℝ (Set.univ : Set Space))
    (Set.mem_univ x) (Set.mem_univ (x+h•a))
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    _ ≤ |h|⁻¹ * (M * (|h| * ‖a‖)) := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (abs_nonneg h))
    _ = M * ‖a‖ := by
      field_simp [abs_ne_zero.mpr hh]

theorem differenceQuotient_fderiv (χ : Cutoff) (a : Space) (h : ℝ) (x : Space) :
    fderiv ℝ (χ.differenceQuotient a h).field x =
      h⁻¹ • (fderiv ℝ χ.field (x+h•a) - fderiv ℝ χ.field x) := by
  change fderiv ℝ (h⁻¹ • ((χ.translate (h•a)).field - χ.field)) x = _
  rw [fderiv_const_smul (f := (χ.translate (h•a)).field - χ.field)
      (((χ.translate (h•a)).smooth.sub χ.smooth).differentiable (by simp) x) h⁻¹,
    fderiv_sub (f := (χ.translate (h•a)).field) (g := χ.field)
      ((χ.translate (h•a)).smooth.differentiable (by simp) x)
      (χ.smooth.differentiable (by simp) x)]
  change h⁻¹ • (fderiv ℝ (fun y => χ.field (y+h•a)) x - fderiv ℝ χ.field x) = _
  rw [fderiv_comp_add_right]

theorem differenceQuotient_support (χ : Cutoff) (R : ℝ)
    (hsupport : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (a : Space) (h : ℝ) (hstep : ‖h • a‖ ≤ 1) :
    tsupport (χ.differenceQuotient a h).field ⊆ Metric.closedBall (0 : Space) (R+1) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have hxlarge : R+1 < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  have hxout : x ∉ tsupport χ.field := by
    intro ht
    have ht' := hsupport ht
    simp only [Metric.mem_closedBall, dist_zero_right] at ht'
    linarith
  have hyout : x+h•a ∉ tsupport χ.field := by
    intro ht
    have ht' := hsupport ht
    simp only [Metric.mem_closedBall, dist_zero_right] at ht'
    have htriangle := norm_sub_le (x+h•a) (h•a)
    rw [add_sub_cancel_right] at htriangle
    linarith
  have hzero : (χ.differenceQuotient a h).field x = 0 := by
    rw [Cutoff.differenceQuotient_field, image_eq_zero_of_notMem_tsupport hxout,
      image_eq_zero_of_notMem_tsupport hyout, sub_self, mul_zero]
  exact hx hzero

def cutoffDifferenceConstant (R M₁ M₂ : ℝ) : ℝ :=
  3 * cutoffCurlConstant *
    (M₁ + M₂ * (volume (Metric.closedBall (0 : Space) (R+1))).toReal ^ (1/3 : ℝ))



end EulerMeanBoundary
