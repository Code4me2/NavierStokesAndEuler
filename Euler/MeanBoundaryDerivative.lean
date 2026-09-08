import Euler.MeanCutoffTaylor
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Genuine directional derivatives of the localized Newtonian operator family in operator norm. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  Filter
open scoped ContDiff Topology

private local instance : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance

@[simp] theorem Cutoff.translate_zero (χ : Cutoff) : χ.translate 0 = χ := by
  exact Cutoff.ext (funext fun x => congrArg χ.field (add_zero x))

theorem cutoffCurl_differenceError (χ : Cutoff) (a : Space) (h : ℝ) :
    cutoffCurl (χ.differenceError a h) =
      h⁻¹ • (cutoffCurl (χ.translate (h • a)) - cutoffCurl χ) - cutoffCurl (χ.directional a) := by
  rw [Cutoff.differenceError, cutoffCurl_sub, Cutoff.differenceQuotient,
    cutoffCurl_scale, cutoffCurl_sub]

theorem Cutoff.exists_taylor_controls (χ : Cutoff) :
    ∃ R M₂ M₃ : ℝ, 0 ≤ M₂ ∧ 0 ≤ M₃ ∧
      tsupport χ.field ⊆ Metric.closedBall (0 : Space) R ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ χ.field) x‖ ≤ M₂) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field)) x‖ ≤ M₃) := by
  obtain ⟨R, hR⟩ := χ.compact.isBounded.subset_closedBall (0 : Space)
  have hs₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ χ.field)) :=
    (χ.smooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hs₃ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ χ.field))) :=
    hs₂.fderiv_right (m := ∞) (by simp)
  obtain ⟨M₂, h₂⟩ := ((χ.compact.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hs₂.continuous
  obtain ⟨M₃, h₃⟩ := (((χ.compact.fderiv ℝ).fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hs₃.continuous
  exact ⟨R, M₂, M₃, (norm_nonneg _).trans (h₂ 0), (norm_nonneg _).trans (h₃ 0), hR, h₂, h₃⟩



theorem weakPotential_operatorNorm_le (χ : Cutoff) : ‖weakPotential χ‖ ≤ cutoffBound χ := by
  change ‖(cutoffCurl χ).adjoint‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact cutoffCurl_norm_le χ




end EulerMeanBoundary
