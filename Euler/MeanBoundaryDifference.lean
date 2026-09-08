import Euler.MeanBoundaryTranslation

/-! Exact spatial difference-quotient commutators with the actual mixed boundary operator. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl
open scoped ENNReal

theorem lpNorm_translated {E : Type*} [NormedAddCommGroup E]
    (f : Space → E) (hf : Continuous f) (a : Space) (p : ℝ≥0∞) :
    lpNorm (fun x => f (x+a)) p volume = lpNorm f p volume := by
  have hm := measurePreserving_add_right (volume : Measure Space) a
  have hfc : AEStronglyMeasurable (fun x => f (x+a)) volume :=
    hf.aestronglyMeasurable.comp_measurePreserving hm
  rw [← toReal_eLpNorm hfc, ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hm)

theorem cutoffBound_translate (χ : Cutoff) (a : Space) :
    cutoffBound (χ.translate a) = cutoffBound χ := by
  have hgrad : gradient (χ.translate a).field = fun x => gradient χ.field (x+a) :=
    funext fun x => gradient_translated a χ.field x
  unfold cutoffBound
  rw [hgrad]
  change 3 * cutoffCurlConstant *
    (lpNorm (fun x => χ.field (x+a)) ∞ volume + lpNorm (fun x => gradient χ.field (x+a)) 3 volume) = _
  rw [lpNorm_translated χ.field χ.smooth.continuous,
    lpNorm_translated (gradient χ.field) (contDiff_gradient χ.smooth).continuous]

/-- The genuine directional spatial difference quotient, defined also at h = 0. -/
def spatialDifference (a : Space) (h : ℝ) : L2 →L[ℝ] L2 :=
  h⁻¹ • ((translation (h • a)).toContinuousLinearMap - ContinuousLinearMap.id ℝ L2)


def Cutoff.differenceQuotient (χ : Cutoff) (a : Space) (h : ℝ) : Cutoff :=
  ((χ.translate (h • a)).sub χ).scale h⁻¹

theorem Cutoff.differenceQuotient_field (χ : Cutoff) (a : Space) (h : ℝ) (x : Space) :
    (χ.differenceQuotient a h).field x = h⁻¹ * (χ.field (x + h • a) - χ.field x) := rfl





end EulerMeanBoundary
