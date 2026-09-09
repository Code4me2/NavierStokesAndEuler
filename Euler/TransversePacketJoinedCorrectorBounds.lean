import Euler.TransversePacketJoinedCorrector
import Euler.TransversePacketPathBounds

/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile.

The four bounds are the generic `EulerTransversePacketPaths` estimates instantiated at the
joined solution's own velocity path and its time derivative. -/

noncomputable section

namespace EulerTransversePacketJoin

open Set EulerTransversePacketProvider EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients EulerGevrey
  EulerPacketProfileRecursion EulerCylinderSobolev EulerParameterWordGevrey
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)
  (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (velocityPath τ hτ hτT B G))) n 0 ≤
      A*majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivativePath τ hτ hτT B G))) n 0 ≤
      A*majorant R d n)
  (hbK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
    C*majorant Rc 0 n)
  (hbKt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
    C*majorant Rc 0 n)
  (hbI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C*majorant Rc 0 n)
  (hbIt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
    C*majorant Rc 0 n)

include hRc hC hA hR hbA hbK in
theorem potentialPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialPath τ hτ hτT B G))) n 0 ≤
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerTransversePacketPaths.potential_block_bound (velocityPath τ hτ hτT B G)
    (velocityPath_orbit τ hτ hτT B G) g hg q Rc C R A hRc hC hA hR d hbA hbK n

include hRc hC hA hR hbA hbAt hbK hbKt in
theorem potentialTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialTimePath τ hτ hτT B G))) n 0 ≤
      (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerTransversePacketPaths.potentialTime_block_bound (velocityPath τ hτ hτT B G)
    (derivativePath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (derivativePath_orbit τ hτ hτT B G) g hg q Rc C R A hRc hC hA hR d hbA hbAt hbK hbKt n

include hRc hC hA hR hbA hbK hbI in
theorem correctorPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorPath τ hτ hτT B G))) n 0 ≤
      (27*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n :=
  EulerTransversePacketPaths.slowCurl_block_bound (velocityPath τ hτ hτT B G)
    (velocityPath_orbit τ hτ hτT B G) g hg q Rc C R A hRc hC hA hR d hbA hbK hbI n

include hRc hC hA hR hbA hbAt hbK hbKt hbI hbIt in
theorem correctorTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorTimePath τ hτ hτT B G))) n 0 ≤
      (108*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n :=
  EulerTransversePacketPaths.slowCurlTime_block_bound (velocityPath τ hτ hτT B G)
    (derivativePath τ hτ hτT B G) (velocityPath_orbit τ hτ hτT B G)
    (derivativePath_orbit τ hτ hτT B G) g hg q Rc C R A hRc hC hA hR d
    hbA hbAt hbK hbKt hbI hbIt n

end EulerTransversePacketJoin
