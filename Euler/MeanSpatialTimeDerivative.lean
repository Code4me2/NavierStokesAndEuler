import Euler.MeanSpatialEvaluation

/-! Genuine time derivatives pass through the reconstructed ordinary spatial representatives. -/

noncomputable section


namespace EulerMeanSmoothRepresentative

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPointEvaluation
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


theorem hasDerivWithinAt_submodule_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (f : ℝ → S) (v : S) (U : Set ℝ) (t : ℝ) :
    HasDerivWithinAt f v U t ↔ HasDerivWithinAt (fun s => (f s : E)) (v : E) U t := by
  rw [hasDerivWithinAt_iff_tendsto, hasDerivWithinAt_iff_tendsto]
  rfl





end EulerMeanSmoothRepresentative
