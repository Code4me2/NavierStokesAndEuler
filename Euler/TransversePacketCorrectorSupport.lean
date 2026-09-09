import Euler.TransversePacketCorrector
import Euler.CylinderLocalSupport

/-! Compact support of the actual transverse potential, corrector, and their time derivatives. -/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerCylinderLocalSupport EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem potentialPath_supported (t : Icc (0 : ℝ) D.T) :
    G.potentialPath I t ∈ Supported P Space D.support D.support_measurable :=
  EulerCylinderLocalSupport.potentialPath_supported P D.support D.support_measurable
    (G.fullVelocityPath I) D.potentialCoefficientPath (fun s => (G.velocityPath I s).property) t


theorem correctorPath_supported (t : Icc (0 : ℝ) D.T) :
    G.correctorPath I t ∈ Supported P Space D.support D.support_measurable :=
  slowCurlPath_supported P D.support D.support_measurable (G.potentialPath I)
    (G.potentialPath_orbit I) D.FInv.field D.support_compact.isClosed (G.potentialPath_supported I) t


theorem corrector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.corrector I (t,(x,θ)) = 0 :=
  pointField_zero_outside P D.support D.support_measurable (G.correctorPath I) (G.correctorPath_orbit I)
    D.support_compact.isClosed (G.correctorPath_supported I) (D.clamp t) (x,(θ : AddCircle P)) hx




end EulerTransversePacketProvider.Forcing
