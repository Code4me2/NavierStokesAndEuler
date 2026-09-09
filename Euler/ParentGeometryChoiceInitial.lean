import Euler.ParentGeometryChoiceCenter
import Euler.ParentForwardInitialSupport

/-! The initial traces of the chosen Euler states are the compact high and
mean increments used in the initial-data convergence proof: the packet
child's time-zero increment is the rescaled normalized packet velocity
(`child_initial_increment`), which each source pipeline identifies with its
exact physical velocity at time zero and splits into `high k + mean k`. -/

noncomputable section

namespace EulerParentPacketFrames

open Set EulerSmoothLimit EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerAllOrderDriftCorrection EulerPacketPhysicalLowBounds EulerPhysicalL2Scaling

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace GeometryJoinedChoice

variable (I : EulerPacketInitial.Input U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)

local notation "res" => residual I S k hk nextEll hnext hnext1 F

theorem normalized_initial :
    I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates I.support I.support_compact
      F.Q res k S.evolution.inverse I.parent.zeroTime =
    initializedExactPhysicalVelocity I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime id := by
  change initializedExactPhysicalVelocity I.meanData I.data rfl I.historyTime I.history_pos I.history_lt
      I.history I.geometry.δ I.delta_pos I.terminal I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime
      (S.evolution.inverse.normalized I.parent.zeroTime) = _
  rw [show S.evolution.inverse.normalized I.parent.zeroTime=id from
    funext S.evolution.inverse.normalized_initial]

variable (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
local notation "T" => state I S k hk nextEll hnext hnext1 F hSym

theorem initial_increment_eq : S.velocityIncrement T 0 = I.high k+I.mean k := by
  refine (S.child_initial_increment I.normal I.normal_unit I.coordinates I.support I.support_compact
    F.Q res rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1 T rfl).trans ?_
  rw [normalized_initial I S k hk nextEll hnext hnext1 F]
  exact I.exactInitial_eq k hk.four F.hn F.Q

theorem state_velocity_initial :
    (fun x => (T).evolution.velocity (0,x)) =
      (fun x => S.evolution.velocity (0,x))+(I.high k+I.mean k) :=
  S.velocity_initial_of_increment T _ (initial_increment_eq I S k hk nextEll hnext hnext1 F hSym)

end GeometryJoinedChoice

namespace GeometryForwardInput

variable (I : GeometryForwardInput U)

def high (k : ℝ) : Space → Space := forwardInitializedInitialHigh I.meanData I.data
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k

def mean (k : ℝ) : Space → Space := forwardInitializedInitialMean I.meanData I.data
  I.geometry.δ I.delta_pos I.geometry.initialCoordinate I.cutoff_support I.alpha (truncation k) k

def exactInitial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : I.correctionBudget k hk hn) :
    Space → Space := scale I.parent.ell
  (forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
    (truncation k) hn k hk Q I.parent.zeroTime id)

theorem exactInitial_eq (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : I.correctionBudget k hk hn) :
    I.exactInitial k hk hn Q=I.high k+I.mean k :=
  forwardInitializedExactPhysicalVelocity_initial_split I.meanData I.data rfl I.geometry.δ I.delta_pos
    I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement (truncation k) hn k hk Q

end GeometryForwardInput

namespace GeometryForwardChoice

variable (I : GeometryForwardInput U) (S : SmoothState I.parent)
  (k : ℝ) (hk : UniversalFrequency k)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)

local notation "res" => residual I S k hk nextEll hnext hnext1 F

theorem normalized_initial :
    I.parent.normalizedPacketVelocity I.normal I.normal_unit I.coordinates I.support I.support_compact
      F.Q res k S.evolution.inverse I.parent.zeroTime =
    forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime id := by
  change forwardInitializedExactPhysicalVelocity I.meanData I.data rfl I.geometry.δ I.delta_pos
      I.geometry.initialCoordinate I.cutoff_support I.alpha I.agreement
      (truncation k) F.hn k hk.four F.Q I.parent.zeroTime
      (S.evolution.inverse.normalized I.parent.zeroTime) = _
  rw [show S.evolution.inverse.normalized I.parent.zeroTime=id from
    funext S.evolution.inverse.normalized_initial]

variable (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
local notation "T" => state I S k hk nextEll hnext hnext1 F hSym

theorem initial_increment_eq : S.velocityIncrement T 0 = I.high k+I.mean k := by
  refine (S.child_initial_increment I.normal I.normal_unit I.coordinates I.support I.support_compact
    F.Q res rfl F.flow F.coefficient k (mul_inv_cancel₀ hk.pos.ne') F.graph nextEll hnext hnext1 T rfl).trans ?_
  rw [normalized_initial I S k hk nextEll hnext hnext1 F]
  exact I.exactInitial_eq k hk.four F.hn F.Q

theorem state_velocity_initial :
    (fun x => (T).evolution.velocity (0,x)) =
      (fun x => S.evolution.velocity (0,x))+(I.high k+I.mean k) :=
  S.velocity_initial_of_increment T _ (initial_increment_eq I S k hk nextEll hnext hnext1 F hSym)

end GeometryForwardChoice
end EulerParentPacketFrames
