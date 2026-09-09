import Euler.ParentGeometryJoinedChoice
import Euler.ParentGeometryForwardChoice
import Euler.ParentPacketStateGeometry

/-! The increment between a packet child and its parent state is the
normalized packet velocity, whichever source pipeline supplied the packet
(`child_increment_fderiv`, `child_initial_increment`). The center errors of
the two geometric choices, which the frame renewal reads, are instances. -/

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketTerminalDatum EulerPacketSourceFrequency EulerPacketPhysicalLowBounds
  EulerPhysicalL2Scaling EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCorrectionCoefficients EulerGraphInvariantFlow EulerCorrectionAssembly
open scoped ContDiff

namespace SmoothState

variable {A : Parent} (S : SmoothState A)

/-- A state whose time-zero increment over `S` is `w` starts from `S`'s
initial velocity plus `w`. -/
theorem velocity_initial_of_increment {N : Parent} (T : SmoothState N) (w : Space → Space)
    (h : S.velocityIncrement T 0=w) :
    (fun x => T.evolution.velocity (0,x))=(fun x => S.evolution.velocity (0,x))+w := by
  funext x
  have he := congrFun h x
  change T.evolution.velocity (0,x)-S.evolution.velocity (0,x)=w x at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  {V : EulerPacketCylinderField.Field P A.T raw} (hV : Z=V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A=B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k*κ=1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q)=0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (T : SmoothState (A.child G k m hgraph nextEll hnext hnext1))
  (hT : T.evolution=S.evolution.child m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1)

local notation "W" => A.normalizedPacketVelocity m hm J support hSupport B residual k S.evolution.inverse

include hT in
/-- The velocity gradient of a packet child's increment is the gradient of the
normalized packet velocity at the rescaled point. -/
theorem child_increment_fderiv (t : Icc (0 : ℝ) A.T) (x : Space) :
    fderiv ℝ (S.velocityIncrement T t) x = fderiv ℝ (W t) (A.ell⁻¹ • x) := by
  have hnew := (T.evolution.velocity_smooth t).differentiable (by simp) x
  have hold := (S.evolution.velocity_smooth t).differentiable (by simp) x
  change fderiv ℝ (fun y => T.evolution.velocity (t,y)-S.evolution.velocity (t,y)) x = _
  rw [fderiv_fun_sub hnew hold]
  have he : fderiv ℝ (fun y => T.evolution.velocity (t,y)) x =
      fderiv ℝ (fun y => S.evolution.velocity (t,y)) x+fderiv ℝ (W t) (A.ell⁻¹ • x) := by
    rw [hT]
    exact A.exactPacketVelocity_fderiv m hm J support hSupport B residual k S.evolution.inverse
      S.evolution.velocity t x hold
  rw [he,add_sub_cancel_left]

include hT in
/-- A bound on the normalized packet velocity's gradient at the origin is a
bound on the child's increment there: the input of the target renewal. -/
theorem child_center_error (t : Icc (0 : ℝ) A.T) (c : Space →L[ℝ] Space) (e : ℝ)
    (h : ‖fderiv ℝ (W t) 0-c‖ ≤ e) : ‖fderiv ℝ (S.velocityIncrement T t) 0-c‖ ≤ e := by
  rw [S.child_increment_fderiv m hm J support hSupport B residual hV G hG k hk hgraph
    nextEll hnext hnext1 T hT t 0,smul_zero]
  exact h

include hT in
/-- The time-zero increment of a packet child is the rescaled normalized
packet velocity at time zero. -/
theorem child_initial_increment : S.velocityIncrement T 0 = scale A.ell (W A.zeroTime) := by
  funext x
  have he : T.evolution.velocity (0,x) =
      addVelocity A.ell (fun y => S.evolution.velocity (0,y)) (W A.zeroTime) x := by
    rw [hT]
    exact A.exactPacketVelocity_eq_addVelocity m hm J support hSupport B residual k
      S.evolution.inverse S.evolution.velocity A.zeroTime x
  change T.evolution.velocity (0,x)-S.evolution.velocity (0,x)=_
  rw [he]
  simp only [addVelocity,add_sub_cancel_left,scale]

end SmoothState

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace GeometryJoinedChoice

variable (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

abbrev residual := initializedApproximationResidual I.meanData I.data rfl
  I.historyTime I.history_pos I.history_lt I.history I.geometry.δ I.delta_pos
  I.terminal I.cutoff_support I.alpha I.agreement (truncation k) F.hn k hk.four

local notation "T" => state I S k hk nextEll hnext hnext1 F hSym

theorem center_error (t : Icc (0 : ℝ) I.parent.T) :
    ‖fderiv ℝ (S.velocityIncrement T t) 0-
      shearTerm (I.geometry.primaryAmplitude I.halfBall)
        (deriv (EulerPeriodicProfile.profile I.geometry.δ)
          (k*⟪I.normal,S.evolution.inverse.normalized t 0⟫_ℝ))
        (I.data.normal.field t (S.evolution.inverse.normalized t 0))
        (EulerPacketPrimaryFactorization.canonicalVelocity I.historyTime I.history_pos I.history_lt
          I.history I.geometry.terminal I.cutoff_support t (S.evolution.inverse.normalized t 0))‖ ≤
      k^(-(1/4 : ℝ)) :=
  S.child_center_error I.normal I.normal_unit I.coordinates I.support I.support_compact F.Q
    (residual I S k hk nextEll hnext hnext1 F) rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne')
    F.graph nextEll hnext hnext1 T rfl t _ _ (F.errors t 0).1

end GeometryJoinedChoice

namespace GeometryForwardChoice

variable (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)

abbrev residual := forwardInitializedApproximationResidual I.meanData I.data rfl
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha
  I.agreement (truncation k) F.hn k hk.four

local notation "T" => state I S k hk nextEll hnext hnext1 F hSym

theorem center_error (t : Icc (0 : ℝ) I.parent.T) :
    ‖fderiv ℝ (S.velocityIncrement T t) 0-
      shearTerm (I.geometry.primaryAmplitude I.halfBall)
        (deriv (EulerPeriodicProfile.profile I.geometry.δ)
          (k*⟪I.normal,S.evolution.inverse.normalized t 0⟫_ℝ))
        (I.data.normal.field t (S.evolution.inverse.normalized t 0))
        (EulerPacketForwardFactorization.canonicalVelocity I.data
          I.geometry.initialCoordinate t (S.evolution.inverse.normalized t 0))‖ ≤
      k^(-(1/4 : ℝ)) :=
  S.child_center_error I.normal I.normal_unit I.coordinates I.support I.support_compact F.Q
    (residual I S k hk nextEll hnext hnext1 F) rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne')
    F.graph nextEll hnext hnext1 T rfl t _ _ (F.errors t 0).1

end GeometryForwardChoice
end EulerParentPacketFrames
