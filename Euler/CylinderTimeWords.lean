import Euler.CylinderTimeRegularity
import Euler.CylinderClassicalWordBounds
import Euler.SobolevWordBlocks

/-! Every actual classical spatial/angular word differentiates in time on the closed interval. -/

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerSobolevWordBlocks
  EulerLpCylinderTranslation EulerVolterraConvolution
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem pointField_word_eq_evaluation (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (n : ℕ) (w : Fin n → Fin 4) (t : K) (x : LiftDomain P) :
    iteratedFieldDerivative P w (pointField P p hp t) x =
      EulerSobolevPointEvaluation.pointEvaluation P x
        (wordBlock P 3 n w (sobolevPath P (3+n) p hp t)) := by
  symm
  apply EulerSobolevPointEvaluation.pointEvaluation_eq
  · exact smoothField_continuous P _ (iteratedFieldDerivative_smooth P w _ (pointField_smooth P p hp t))
  · have he : value P (wordBlock P 3 n w (sobolevPath P (3+n) p hp t)) = strongWord P (p t) w := by
      rw [wordBlock_value]
      exact sobolev_coordinate P (3+n) (p t) (path_evaluation_smooth P p hp t)
        ⟨⟨n,by omega⟩,w⟩
    rw [he, pointField_eq_representative]
    exact strongWord_ae P (p t) (path_evaluation_smooth P p hp t) w

theorem pointField_word_joint_continuous (p : C(K,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (n : ℕ) (w : Fin n → Fin 4) :
    Continuous (fun z : K × LiftDomain P => iteratedFieldDerivative P w (pointField P p hp z.1) z.2) := by
  let v : C(K,SobolevSpace P 3) := (wordBlock P 3 n w).compLeftContinuous ℝ K (sobolevPath P (3+n) p hp)
  have h := EulerSobolevJointEvaluation.path_representative_joint_continuous P v
  change Continuous (fun z : K × LiftDomain P => EulerSobolevPointEvaluation.pointEvaluation P z.2
    (wordBlock P 3 n w (sobolevPath P (3+n) p hp z.1))) at h
  simpa only [pointField_word_eq_evaluation] using h

variable (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)


end EulerCylinderSmoothOrbit
