import Euler.ParentRenewalParameters
import Euler.PacketForwardGeometryLowBounds

/-! The geometric target of the actual forward or joined primary is the
activation time of the next parent frame. These factories are the checked
`SmoothState` renewals with the source-selected amplitude and primary;
all target matching is proved from their definitions. -/

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerSpatialCutoffs EulerPeriodicProfile
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {A N : Parent} (S : SmoothState A) (T : SmoothState N) (hTime : N.T=A.T)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNext : Space) (hmNext : ‖mNext‖=1) (JNext : V ≃ₗᵢ[ℝ] referencePlane mNext)
  (supportNext : Set Space) (hSupportNext : IsCompact supportNext)

local notation "D" => A.transverseData m hm J support hSupport
local notation "DNext" => N.transverseData mNext hmNext JNext supportNext hSupportNext

section Forward

variable {P : ParentFrame (A.transverseData m hm J support hSupport) 0} (G : ForwardGuards P) (hball : (1/2 : ℝ) ≤ G.radius)

local notation "Geo" => ForwardGuards.lowGeometry G hball
local notation "tNext" => PhysicalGeometryData.targetTime (ForwardGuards.lowGeometry G hball)

variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0-
      (G.primaryAmplitude hball*deriv (profile G.δ)
        (k*⟪m,S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
          (A.transverseData m hm J support hSupport) G.initialCoordinate t (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t (S.evolution.inverse.normalized t 0))‖ ≤ error)

/-- The next actual frame, using exactly the forward source primary and
its target-normalized amplitude. -/
def forwardTargetRenewal : ParentFrame DNext tNext :=
  S.forwardRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext ((G.lowGeometry hball).target_time_mem).1 CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    G.initialCoordinate G.initialCoordinate_ne_zero hsource

local notation "Q" => forwardTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource

/-- In particular, the new ray and primary are the old source's actual
physical ray and primary at the target, not freely chosen frame vectors. -/
theorem forwardTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T := ⟨tNext,(G.lowGeometry hball).target_time_mem⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl







end Forward

section Joined

variable (s : ℝ) (hs : 0 < s) (hsT : s < A.T)
  (H : HistoryData ((A.transverseData m hm J support hSupport).initial s hs hsT.le))
  {P : ParentFrame (A.transverseData m hm J support hSupport) s}
  (G : Guards hs hsT P H) (hball : (1/2 : ℝ) ≤ G.radius)
  (hcut : tsupport innerCutoff ⊆ support)

local notation "Geo" => Guards.lowGeometry G hball
local notation "tNext" => PhysicalGeometryData.targetTime (Guards.lowGeometry G hball)

variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0-
      (G.primaryAmplitude hball*deriv (profile G.δ)
        (k*⟪m,S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity
          s hs hsT H G.terminal hcut t (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t (S.evolution.inverse.normalized t 0))‖ ≤ error)

/-- The joined renewal retains the activation-selected endpoint and
its actual stationary-history initial trace. -/
def joinedTargetRenewal : ParentFrame DNext tNext :=
  S.joinedRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext (hs.le.trans ((G.lowGeometry hball).target_time_mem).1) CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    s hs hsT H G.terminal G.terminal_properties.1 hcut hsource

local notation "Q" => joinedTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource

theorem joinedTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T :=
    ⟨tNext,hs.le.trans ((G.lowGeometry hball).target_time_mem).1,
      ((G.lowGeometry hball).target_time_mem).2⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl







end Joined
end EulerParentPacketFrames.SmoothState
