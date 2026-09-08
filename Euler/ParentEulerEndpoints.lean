import Euler.ParentEulerSobolev

/-! The physical gradient is continuous up to the endpoints in the
actual Sobolev class. Incompressibility therefore holds at time zero
and the final time as well as in the open Euler interval. -/

noncomputable section

namespace EulerParentPacketFrames.SobolevData

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField EulerMeanCoefficients
open scoped Topology

variable {A : Parent} {E : Evolution A} (S : SobolevData E)

include S

theorem spatial_derivative_continuous (x : Space) :
    Continuous (fun t : Icc (0 : ℝ) A.T => fderiv ℝ (fun y => E.velocity (t,y)) x) := by
  let D := coefficientPath (fun t => (S.velocity t).derivative)
    (continuous_jetLp_derivative S.velocity S.velocity_continuous)
  have hc : Continuous (fun t => D.field t x) :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp D.field.continuous
  apply hc.congr
  intro t
  rw [show D.field t x=fderiv ℝ (S.velocity t).field x from
    coefficientPath_apply _ _ t x]
  rw [funext (S.velocity_match t)]


end EulerParentPacketFrames.SobolevData
