import Euler.TransversePacketPrimaryCorrector
import Euler.TransversePacketPrimaryBounds
import Euler.TransversePacketNormalBudget
import Euler.SourceCylinderPressureWeight
import Euler.PacketCylinderScalarGradientWeight
import Euler.TransversePacketPathBounds

/-! Same-radius estimates for the actual corrector, divided by the prescribed time profile.

The four corrector bounds are the generic `EulerTransversePacketPaths` estimates instantiated
at the primary solution's own velocity path and its time derivative. -/

noncomputable section

namespace EulerTransversePacketPrimary

open Set EulerTransversePacketProvider EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients EulerGevrey
  EulerPacketProfileRecursion EulerCylinderSobolev EulerParameterWordGevrey
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
  (q : ℕ) (Rc C R A : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
  (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R) (d : ℕ)
  (hbA : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (velocityPath τ hτ hτT B Y))) n 0 ≤
      A*majorant R d n)
  (hbAt : ∀ n, block standardDirection q
    (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivativePath τ hτ hτT B Y))) n 0 ≤
      A*majorant R d n)
  (hbK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
    C*majorant Rc 0 n)
  (hbKt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
    C*majorant Rc 0 n)
  (hbI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ C*majorant Rc 0 n)
  (hbIt : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
    C*majorant Rc 0 n)



include hRc hC hA hR hbA hbK hbI in
theorem correctorPath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorPath τ hτ hτT B Y))) n 0 ≤
      (27*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n :=
  EulerTransversePacketPaths.slowCurl_block_bound (velocityPath τ hτ hτT B Y)
    (velocityPath_orbit τ hτ hτT B Y) g hg q Rc C R A hRc hC hA hR d hbA hbK hbI n

include hRc hC hA hR hbA hbAt hbK hbKt hbI hbIt in
theorem correctorTimePath_normalized_bound (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (correctorTimePath τ hτ hτT B Y))) n 0 ≤
      (108*(sobolevCoefficientAmplitude (Fin 4) q Rc C)^2*(P*A))*majorant R (d+1) n :=
  EulerTransversePacketPaths.slowCurlTime_block_bound (velocityPath τ hτ hτT B Y)
    (derivativePath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)
    (derivativePath_orbit τ hτ hτT B Y) g hg q Rc C R A hRc hC hA hR d
    hbA hbAt hbK hbKt hbI hbIt n

end EulerTransversePacketPrimary

namespace EulerTransversePacketPrimary.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderSobolev
  EulerSourceNormalResidualBounds EulerMeanCoefficients EulerTimeLpGramGevrey
  EulerSourceCylinderTimeBounds EulerCylinderDirichlet.Coefficients EulerTransverseForwardCoefficientGevrey
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {q : ℕ}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) q}
  (H : Budget L) (N : EulerTransversePacketJoin.NormalBudget D q L.R)

theorem derivativeCost_nonneg : 0 ≤ H.derivativeCost := by
  have hi := (inverseRadius_bounds (D.tail τ hτ.le hτT).frameLower L.C₀ L.Rc L.Ri
    (D.tail τ hτ.le hτT).frameLower_pos L.Rc_nonneg L.forward_inverse).1
  have h0 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg
  have h1 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q L.Rc L.C₁ L.Rc_nonneg L.C₁_nonneg
  have hb0 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) L.C₀ (by positivity) L.C₀_nonneg
  have hb1 := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) L.C₁ (by positivity) L.C₁_nonneg
  have hc0 := L.C₀_nonneg
  have hc1 := L.C₁_nonneg
  have hbb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)
    (by positivity) (by positivity)
  have hbf := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*L.Ri) (3*L.Ri*L.C₀)
    (by positivity) (by positivity)
  have ht := H.endpointBudget.coordinateCost_nonneg
  unfold derivativeCost EndpointBudget.derivativeCost physicalCost coordinateCost
  change 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) q L.Rc L.C₁*H.endpointBudget.coordinateCost+
    3*sobolevCoefficientAmplitude (Fin 4) q L.Rc L.C₀+
      (3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) L.C₁*1+
        3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) L.C₀*
          (3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)*1+
            3*sobolevCoefficientAmplitude (Fin 4) q (4*L.Ri) (3*L.Ri*L.C₀)*0))
  positivity

def commonCost : ℝ := H.velocityCost+H.derivativeCost
def pressureAmplitude : ℝ := P*pressureCost (Fin 4) q N.Ri N.C N.C 0 H.commonCost
def correctorAmplitude : ℝ := 27*N.blockAmplitude^2*(P*H.commonCost)
def correctorTimeAmplitude : ℝ := 108*N.blockAmplitude^2*(P*H.commonCost)

theorem commonCost_nonneg : 0 ≤ H.commonCost := add_nonneg H.velocityCost_nonneg H.derivativeCost_nonneg
theorem velocityCost_le_common : H.velocityCost ≤ H.commonCost := le_add_of_nonneg_right H.derivativeCost_nonneg
theorem derivativeCost_le_common : H.derivativeCost ≤ H.commonCost := le_add_of_nonneg_left H.velocityCost_nonneg

theorem pressureAmplitude_nonneg : 0 ≤ H.pressureAmplitude (P := P) N := by
  have hRi := N.Ri_nonneg
  have hC := N.C_nonneg
  have hH := H.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  have hm := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*N.Ri) (3*N.Ri*N.C)
    (by positivity) (by positivity)
  have hM := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q (4*N.Ri) N.C (by positivity) hC
  unfold pressureAmplitude pressureCost
  positivity

theorem correctorAmplitude_nonneg : 0 ≤ H.correctorAmplitude (P := P) N := by
  have hH := H.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorAmplitude
  positivity

theorem correctorTimeAmplitude_nonneg : 0 ≤ H.correctorTimeAmplitude (P := P) N := by
  have hH := H.commonCost_nonneg
  have hP := (Fact.out : 0 < P).le
  unfold correctorTimeAmplitude
  positivity

variable (Y : InitialData P D) (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hYb : ∀ n, block standardDirection q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    A*majorant L.R d n)

include hA hYb

theorem velocity_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))) n 0 ≤
        (H.commonCost*A)*majorant L.R (d+3) n :=
  (H.velocity_bound Y standardDirection standardDirection_norm_le_one A hA d hYb n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.velocityCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))

theorem derivative_common_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B Y))) n 0 ≤
        (H.commonCost*A)*majorant L.R (d+3) n :=
  (H.derivative_bound Y standardDirection standardDirection_norm_le_one A hA d hYb n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.derivativeCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_bounds.1) (d+3) n))

theorem pressure_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (pressurePath τ hτ hτT B Y))) n 0 ≤
        (H.pressureAmplitude (P := P) N*A)*majorant L.R (d+3) n := by
  have he : normalize L.fullProfile L.fullProfile_pos (pressurePath τ hτ hτT B Y) =
      sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower 0
        (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y)) := by
    simpa only [EulerTransversePacketPrimary.pressurePath,EulerContinuousTimeWeight.normalize,map_zero] using
      (sourcePressure_weight P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
        (reciprocal L.fullProfile L.fullProfile_pos) 0 (velocityPath τ hτ hτT B Y)).symm
  rw [he]
  have hzero : ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate P a (0 : C(Icc (0 : ℝ) D.T,LiftL2 P))) := by
    simpa only [map_zero] using (contDiff_const : ContDiff ℝ ∞
      (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P))))
  have h := sourcePressure_block_bound P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))
    standardDirection standardDirection_norm_le_one q hzero
    (normalize_orbit_contDiff P L.fullProfile L.fullProfile_pos _ (velocityPath_orbit τ hτ hτT B Y))
    N.Rc N.C N.C N.Ri L.R 0 (H.commonCost*A) N.Rc_nonneg N.C_nonneg N.C_nonneg le_rfl
    (mul_nonneg H.commonCost_nonneg hA) N.inverse_radius N.pressure_radius N.normal_bound N.strain_bound
    (d+3) (fun j => by simp only [map_zero,block_zero_function,zero_mul,le_refl])
    (H.velocity_common_bound Y A hA d hYb) n
  exact h.trans_eq (by unfold pressureAmplitude pressureCost; ring)

theorem pressure_gradient_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (scalarGradientField τ hτ hτT B Y).path)) n 0 ≤
        (3*H.pressureAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  change block standardDirection q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos
      (EulerPacketCylinderField.scalarGradientPath (pressurePath τ hτ hτT B Y)))) n 0 ≤ _
  have h := EulerPacketCylinderField.scalarGradientPath_normalized_majorant
    (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
    L.fullProfile L.fullProfile_pos q L.R (H.pressureAmplitude (P := P) N*A) (d+3)
    (H.pressure_bound N Y A hA d hYb) n
  simpa only [show d+3+1=d+4 by omega,mul_assoc] using h



theorem corrector_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorPath τ hτ hτT B Y))) n 0 ≤
        (H.correctorAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorPath_normalized_bound τ hτ hτT B Y L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (H.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg H.commonCost_nonneg hA) N.radius (d+3)
    (H.velocity_common_bound Y A hA d hYb)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by unfold correctorAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

theorem corrector_time_bound (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (correctorTimePath τ hτ hτT B Y))) n 0 ≤
        (H.correctorTimeAmplitude (P := P) N*A)*majorant L.R (d+4) n := by
  have hc := N.coefficient_bounds
  have h := correctorTimePath_normalized_bound τ hτ hτT B Y L.fullProfile L.fullProfile_pos
    q N.coefficientRadius N.coefficientAmplitude L.R (H.commonCost*A)
    hc.1 hc.2.1 (mul_nonneg H.commonCost_nonneg hA) N.radius (d+3)
    (H.velocity_common_bound Y A hA d hYb) (H.derivative_common_bound Y A hA d hYb)
    (fun j a => (hc.2.2 j a).2.2.1) (fun j a => (hc.2.2 j a).2.2.2)
    (fun j a => (hc.2.2 j a).1) (fun j a => (hc.2.2 j a).2.1) n
  rw [show d+3+1=d+4 by omega] at h
  exact h.trans_eq (by unfold correctorTimeAmplitude EulerTransversePacketJoin.NormalBudget.blockAmplitude; ring)

end EulerTransversePacketPrimary.Budget
