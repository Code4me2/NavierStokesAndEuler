import Euler.StandardDirectionBounds
import Euler.TransversePacketCorrector
import Euler.CylinderSlowCurlWeight
import Euler.CylinderPotentialTimeWeight

/-! # Same-radius corrector estimates for an arbitrary velocity/derivative pair

Every transverse provider builds its potential `Q`, its time derivative `Q_t` and the slow
curl `C`, `C_t` by the *same* recipe from a velocity path `u` and its time derivative `ut`:
`EulerCylinderPotential.potentialPath`/`potentialDerivative` followed by
`EulerCylinderSlowCurl.path`/`derivative`, all divided by the prescribed positive time
profile.  The four block-Sobolev bounds below are therefore proved once, for an arbitrary
smooth-orbit pair `u`, `ut`; the forward, joined and primary providers each instantiate them
at their own paths, whose constructions are definitionally the ones named here.
-/

noncomputable section

namespace EulerTransversePacketPaths

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients EulerGevrey
  EulerPacketProfileRecursion EulerCylinderSobolev EulerParameterWordGevrey
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerContinuousTimeWeight
  EulerTransversePacketProvider
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} (u ut : C(Icc (0 : ℝ) D.T,LiftL2 P))

/-- The potential the providers build from a velocity path. -/
abbrev potential : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialPath P D.potentialCoefficientPath u

/-- The time derivative of `potential`, built from the velocity path and its derivative. -/
abbrev potentialTime : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderPotential.potentialDerivative P D.T D.potentialCoefficientPath
    D.potentialDerivative u ut

/-- The slow curl of `potential`. -/
abbrev slowCurl : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.path P D.FInv.field (potential u)

/-- The time derivative of `slowCurl`. -/
abbrev slowCurlTime : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  EulerCylinderSlowCurl.derivative P D.T D.FInv.field D.inverseDerivative
    (potential u) (potentialTime u ut)

variable (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a u))
  (hut : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a ut))

include hu in
theorem potential_orbit : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potential u)) :=
  EulerCylinderPotential.potentialPath_orbit P D.potentialCoefficientPath
    D.potentialCoefficientPath_orbit u hu

include hu hut in
theorem potentialTime_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potentialTime u ut)) :=
  EulerCylinderPotential.potentialDerivative_orbit P D.T D.potentialCoefficientPath
    D.potentialDerivative D.potentialCoefficientPath_orbit D.potentialDerivative_orbit u ut hu hut

variable (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg u)) n 0 ≤ A*majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg ut)) n 0 ≤ A*majorant R d n)
  (hbK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
    C*majorant Rc 0 n)
  (hbKt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
    C*majorant Rc 0 n)
  (hbI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C*majorant Rc 0 n)
  (hbIt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
    C*majorant Rc 0 n)

include hu hRc hC hA hR hbA hbK in
/-- The normalized potential keeps the input radius, at three times the coefficient cost. -/
theorem potential_block_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potential u))) n 0 ≤
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialPath_block_bound P g u
    D.potentialCoefficientPath hg D.potentialCoefficientPath_orbit
    (EulerCylinderPotential.weighted_orbit P (reciprocal g hg) u hu)
    standardDirection standardDirection_norm_le_one q Rc C R A hRc hC hA hR hbK d hbA n

include hu hut hRc hC hA hR hbA hbAt hbK hbKt in
/-- The normalized potential derivative, without differentiating the profile. -/
theorem potentialTime_block_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialTime u ut))) n 0 ≤
      (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d n :=
  EulerCylinderPotential.normalized_potentialDerivative_block_bound P D.T
    D.potentialCoefficientPath D.potentialDerivative D.potentialCoefficientPath_orbit
    D.potentialDerivative_orbit u ut hu hut g hg standardDirection standardDirection_norm_le_one
    q Rc C R A hRc hC hA hR hbK hbKt d hbA hbAt n

include hu hRc hC hA hR hbA hbK hbI in
/-- The normalized slow curl, at the cost of one derivative shift. -/
theorem slowCurl_block_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (slowCurl u))) n 0 ≤
      (27*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have h := EulerCylinderSlowCurl.normalized_path_block_bound P g D.FInv.field
    (potential u) (potential_orbit u hu) hg D.FInv.translation_contDiff
    q Rc C R (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR hbI d
    (potential_block_bound u hu g hg q Rc C R A hRc hC hA hR d hbA hbK) n
  exact h.trans_eq (by ring)

include hu hut hRc hC hA hR hbA hbAt hbK hbKt hbI hbIt in
/-- The normalized time derivative of the slow curl, at the cost of one derivative shift. -/
theorem slowCurlTime_block_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (slowCurlTime u ut))) n 0 ≤
      (108*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n := by
  have hp : 0 ≤ P := (Fact.out : 0 < P).le
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  have hRn : 0 ≤ R := (sobolevCoefficientRadius_nonneg (ι := Fin 4) Rc hRc).trans hR
  have hQ (j : ℕ) : block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (potential u))) j 0 ≤
        (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A))*majorant R d j := by
    apply (potential_block_bound u hu g hg q Rc C R A hRc hC hA hR d hbA hbK j).trans
    have hn := mul_nonneg
      (show 0 ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A) by positivity)
      (majorant_nonneg R hRn d j)
    nlinarith
  have h := EulerCylinderSlowCurl.normalized_derivative_block_bound P D.T g hg
    D.FInv.field D.inverseDerivative (potential u) (potentialTime u ut)
    (potential_orbit u hu) (potentialTime_orbit u ut hu hut)
    D.FInv.translation_contDiff D.inverseDerivative_orbit
    q Rc C R (6*sobolevCoefficientAmplitude (Fin 4) q Rc C*(P*A)) hRc hC (by positivity) hR
    hbI hbIt d hQ
    (potentialTime_block_bound u ut hu hut g hg q Rc C R A hRc hC hA hR d hbA hbAt hbK hbKt) n
  exact h.trans_eq (by ring)

end EulerTransversePacketPaths
