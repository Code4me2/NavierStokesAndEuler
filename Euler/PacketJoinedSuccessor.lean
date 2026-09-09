import Euler.PacketStageSuccessor
import Euler.PacketStageInputs
import Euler.PacketStageEstimates
import Euler.ParentGeometryChoiceLow
import Euler.ParentGeometryChoiceRenewal
import Euler.ParentGeometryChoiceInitial

/-! The positive-history step. After the first packet the joined packet
choice, with its guards' `badRatio`, is packaged as a `Step` and assembled by
`next`; its exact initial increment is the high and mean field of the input. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerBaseDatum EulerPacketSupport
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleSequence
  EulerParentNeighborThreshold EulerPacketGeometryLowBounds

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)
  (hn : n ≠ 0) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "I" => P.joinedInput hn hq hB
local notation "G" => P.joinedGuards hn hq hB
local notation "k" => frequency S.J S.X n
local notation "hk" => S.normal_frequency n
local notation "ell" => supportScale S.J S.X (n+1)

abbrev JoinedChoice :=
  GeometryJoinedChoice I P.restrictedState k hk ell (S.support_pos (n+1)) (S.support_one (n+1))

def chooseJoined : P.JoinedChoice hn hq hB := by
  have hsec := S.secondary_frequency n P.restrictedState.labels.K P.label_eq.le
  exact Classical.choice (exists_geometryJoinedChoice I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) rfl (P.joinedInput_frequency hn hq hB) hsec.1
    (by rw [P.joinedInput_scale hn hq hB]; exact hsec.2))

local notation "F" => P.chooseJoined hn hq hB

/-- The joined child state, named so the shared successor record does not have
to unfold the geometry choice while checking later fields. -/
def joinedState : SmoothState (F).parent :=
  GeometryJoinedChoice.state I P.restrictedState k hk ell (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric

/-- Whole-horizon physical bounds for the joined child, kept as one named proof
to avoid elaborating the packet estimate twice inside `Step`. -/
theorem joinedPhysicalBounds (t : Icc (0 : ℝ) (F).parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (P.joinedState hn hq hB).evolution.velocity (t,y)) x‖ ≤
        gradientConstant*previousShear S.J S.X n+(G).hchild*(goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)) ∧
      ‖fderiv ℝ ((P.joinedState hn hq hB).evolution.force t) x‖ ≤
        hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n+
          2*(gradientConstant*previousShear S.J S.X n)*(G).hchild*(goodRatio+(G).badRatio)+k^(-(1/4 : ℝ)) :=
  (F).physical_bounds symmetric _ _ P.restricted_gradient_bound P.restricted_hessian_bound t x

/-- The joined choice's parent, state, low bounds, physical bounds and renewed
frame, with the guards' shear, spike and `badRatio`. -/
def joinedStep : P.Step where
  parent := (F).parent
  state := P.joinedState hn hq hB
  hchild := (G).hchild
  δ := (G).δ
  ratio := (G).badRatio
  ratio_nonneg := (G).badRatio_nonneg
  hchild_eq := P.joinedGuards_shear hn hq hB
  delta_eq := P.joinedGuards_delta hn hq hB
  parent_horizon := rfl
  parent_scale := rfl
  label_eq := (F).label_constant
  low := (F).lowBounds (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    P.restricted_gradient_bound P.restricted_hessian_bound
    (P.smallness (G).hchild (G).δ (G).badRatio (G).child_nonneg (G).delta_nonneg (G).badRatio_nonneg
      (initial_cost_of_bad_cost _ _ (G).child_nonneg (G).badRatio_nonneg (P.joined_bad_cost hn hq hB))
      (P.joined_pressure_cost hn hq hB))
  low_exterior := rfl
  low_core := rfl
  low_pressure := rfl
  low_boundary := rfl
  low_radius := rfl
  physical_bounds := P.joinedPhysicalBounds hn hq hB
  bad_cost := P.joined_bad_cost hn hq hB
  pressure_cost := P.joined_pressure_cost hn hq hB
  geometry := P.joinedGeometry hn hq hB
  geometry_targetTime := P.joinedGeometry_targetTime hn hq hB
  geometry_coupling := P.joinedFrame_a hn
  geometry_y := rfl
  geometry_delta_pos := (I).delta_pos
  geometry_shear := rfl
  renewal_errors := P.joined_renewal_errors hn hq hB
  renewal := (F).renewal symmetric (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    (frameConstant*(1+previousShear S.J S.X n))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one n)))
    (next_frame_bounds (S := S) (n := n)).1 (next_frame_bounds (S := S) (n := n)).2.1
    (next_frame_bounds (S := S) (n := n)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact
  renewal_matches := (F).renewal_matches symmetric (gradientConstant*previousShear S.J S.X n)
    (hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n)
    (frameConstant*(1+previousShear S.J S.X n))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one n)))
    (next_frame_bounds (S := S) (n := n)).1 (next_frame_bounds (S := S) (n := n)).2.1
    (next_frame_bounds (S := S) (n := n)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact
  renewal_G := rfl
  renewal_error := rfl

def joinedNext : Stage S (n+1) := P.next (P.joinedStep hn hq hB)

theorem joinedNext_time : (P.joinedNext hn hq hB).time=P.nextTime := rfl

theorem joinedNext_initial_velocity :
    (fun x => (P.joinedNext hn hq hB).state.evolution.velocity (0,x)) =
      (fun x => P.state.evolution.velocity (0,x))+((I).high k+(I).mean k) :=
  GeometryJoinedChoice.state_velocity_initial I P.restrictedState k hk ell
    (S.support_pos (n+1)) (S.support_one (n+1)) F symmetric

end EulerPacketInduction.Stage
