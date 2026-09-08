import Euler.TransversePacketPressureGradient
import Euler.PacketCylinderScalarGradientWeight
import Euler.SourceCylinderPressureWeight

/-! Bounds for the actual high-pressure gradient from the normalized forcing and solved velocity. -/

noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketCylinderField EulerLpCylinderPaths EulerLpCylinderTranslation
  EulerCylinderSobolev EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
  EulerSourceNormalResidualBounds EulerCylinderPotential EulerTimeLpGramGevrey

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem pressurePath_normalized_eq_source (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t) :
    normalize g hg (G.pressurePath I) =
      sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
        (normalize g hg (includePath P D.support D.support_measurable G.path))
        (normalize g hg (includePath P D.support D.support_measurable (G.velocityPath I))) :=
  (sourcePressure_weight P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (reciprocal g hg) (includePath P D.support D.support_measurable G.path)
    (includePath P D.support D.support_measurable (G.velocityPath I))).symm

theorem scalarGradientField_normalized_bound (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.pressurePath I))) n 0 ≤
        A*majorant R d n) (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (G.scalarGradientField I).path)) n 0 ≤
        (3*A)*majorant R (d+1) n :=
  scalarGradientPath_normalized_majorant (G.pressurePath I) (G.pressurePath_orbit I) g hg q R A d hb n


end EulerTransversePacketProvider.Forcing
