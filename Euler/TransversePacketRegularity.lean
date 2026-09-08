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

theorem vector_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => G.vector I (z.1,z.2)) := by
  have h := (field_joint_continuous P D.support D.support_measurable D.support_compact
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.path_orbit I.orbit).comp (continuous_cover (P := P) (D := D))
  simpa only [vector,Data.clamp_coe,Function.comp_def] using h



theorem vectorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.vectorDerivative I (t,(x,θ)) = 0 := by
  change pointField P (includePath P D.support D.support_measurable (G.derivativePath I))
    (G.derivativePath_orbit I) (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (G.derivativePath I (D.clamp t)).property (x,(θ : AddCircle P)) hx





end Forcing

end EulerTransversePacketProvider
