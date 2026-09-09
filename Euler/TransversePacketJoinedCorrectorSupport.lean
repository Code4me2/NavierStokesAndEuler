import Euler.TransversePacketJoinedCorrector
import Euler.CylinderLocalSupport
import Euler.CylinderCorrectorMeanZero

/-! Support and zero angular mean of the literal joined corrector and its actual time derivative. -/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderLocalSupport
  EulerCylinderAngleAverage EulerCylinderCorrectorMeanZero EulerPacketProfileRecursion
  EulerTransversePacketProvider EulerElapsedTimePathGluing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)


theorem potentialPath_supported (t : Icc (0 : ℝ) D.T) :
    potentialPath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable :=
  EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
    (velocityPath τ hτ hτT B G) D.potentialCoefficientPath (velocityPath_supported τ hτ hτT B G) t


theorem correctorPath_supported (t : Icc (0 : ℝ) D.T) :
    correctorPath τ hτ hτT B G t ∈ Supported P Space D.support D.support_measurable :=
  slowCurlPath_supported P D.support D.support_measurable (potentialPath τ hτ hτT B G)
    (potentialPath_orbit τ hτ hτT B G) D.FInv.field D.support_compact.isClosed
    (potentialPath_supported τ hτ hτT B G) t






theorem corrector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    corrector τ hτ hτT B G (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (correctorPath τ hτ hτT B G)
    (correctorPath_orbit τ hτ hτT B G) D.support_compact.isClosed
    (correctorPath_supported τ hτ hτT B G) (D.clamp t) (x,(θ : AddCircle P)) hx



end EulerTransversePacketJoin
