import Euler.ParentGeometryChoiceCenter
import Euler.ParentTargetRenewal

/-! Frame renewal for the correction and flow chosen by the geometric packet
factories: each choice's renewed frame at its target time, matched exactly to
its `lowGeometry` (`renewal_matches`), from which the successor assembly reads
the new shear, coupling, tilt and compression. Center source matching is derived. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit EulerVolterraConvolution

variable {A : Parent} (E : Evolution A)

theorem centerStrain_bound (CM : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (t : ℝ) : ‖A.centerStrain t‖ ≤ CM := by
  change ‖A.strain.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CM
  rw [E.strain_eq]
  exact hCM _ _

theorem centerCurvature_bound (CH : ℝ)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (t : ℝ) : ‖A.centerCurvature t‖ ≤ CH := by
  change ‖A.curvature.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CH
  rw [E.curvature_eq]
  exact hCH _ _

end EulerParentPacketFrames.Evolution

namespace EulerParentPacketFrames.GeometryForwardChoice

open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖=1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.forwardTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.geometry I.halfBall CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)

theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall)
    (F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport) := by
  unfold renewal
  apply SmoothState.forwardTargetRenewal_matches

end EulerParentPacketFrames.GeometryForwardChoice

namespace EulerParentPacketFrames.GeometryJoinedChoice

open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖=1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.joinedTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.historyTime I.history_pos I.history_lt I.history I.geometry I.halfBall
    I.cutoff_support CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)

theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall)
    (F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport) := by
  unfold renewal
  apply SmoothState.joinedTargetRenewal_matches

end EulerParentPacketFrames.GeometryJoinedChoice
