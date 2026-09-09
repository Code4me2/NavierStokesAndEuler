import Euler.MeanSpatialEvaluation
import Euler.MeanTimeContinuousTranslation

/-! Jointly continuous ordinary spatial representatives of continuous L² paths with smooth spatial orbits. -/

noncomputable section


namespace EulerMeanSmoothRepresentative

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPointEvaluation
  EulerMeanTimeContinuousTranslation
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Evaluation at time commutes with every actual spatial derivative tensor. -/
theorem path_orbit_tensor_evaluation (T : ℝ) (p : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (p t)) 0 =
      (ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0) :=
  (ContinuousMap.evalCLM ℝ t).iteratedFDeriv_comp_left hp.contDiffAt (by simp)





end EulerMeanSmoothRepresentative
