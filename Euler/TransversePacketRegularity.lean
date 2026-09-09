import Euler.TransversePacketProvider

/-! Joint continuity and actual spatial support of the concrete forward packet fields. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerCylinderSmoothOrbit EulerSourceCylinderClassical
  EulerPacketProfileRecursion EulerMetricTransport

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace Forcing

variable {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

omit [Fact (0 < P)] [CompleteSpace U] in
private theorem continuous_cover :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => (z.1,(z.2.1,(z.2.2 : AddCircle P)))) :=
  continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
    ((AddCircle.continuous_mk' P).comp (continuous_snd.comp continuous_snd)))









end Forcing

end EulerTransversePacketProvider
