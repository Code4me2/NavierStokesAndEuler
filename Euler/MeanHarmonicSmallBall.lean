import Euler.MeanHarmonicInterior
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! A dimensional r³ localization estimate, derived from the interior bound. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit
open scoped ContDiff



theorem volume_ball_toReal (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : Space) r)).toReal = r ^ 3 * (Real.pi * 4 / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]


end EulerMeanHarmonic
