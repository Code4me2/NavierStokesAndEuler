import Euler.PacketStageSuccessor
import Euler.PacketStageInputs
import Euler.PacketStageEstimates
import Euler.ParentGeometryChoiceLow
import Euler.ParentGeometryChoiceRenewal

/-! The time-zero step. At the base stage the forward packet choice, with its
guards' `earlyRatio`, is packaged as a `Step` and assembled by `next`. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerBaseDatum EulerPacketSupport
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleSequence
  EulerParentNeighborThreshold EulerPacketGeometryLowBounds

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} (P : Stage S 0)
  (hq : requiredExponent ≤ q) (hB : commonThreshold gradientConstant hessianConstant ≤ B)

local notation "I" => P.forwardInput hq hB
local notation "G" => P.forwardGuards hq hB
local notation "k" => frequency S.J S.X 0
local notation "hk" => S.normal_frequency 0
local notation "ell" => supportScale S.J S.X 1

abbrev ForwardChoice := GeometryForwardChoice I P.restrictedState k hk ell (S.support_pos 1) (S.support_one 1)

def chooseForward : P.ForwardChoice hq hB := by
  have hsec := S.secondary_frequency 0 P.restrictedState.labels.K P.label_eq.le
  exact Classical.choice (exists_geometryForwardChoice I P.restrictedState k hk ell
    (S.support_pos 1) (S.support_one 1) (P.forwardInput_frequency hq hB) hsec.1
    (by rw [P.forwardInput_scale]; exact hsec.2))

local notation "F" => P.chooseForward hq hB

/-- The forward child state, named so the shared successor record does not have
to unfold the geometry choice while checking later fields. -/
def forwardState : SmoothState (F).parent :=
  GeometryForwardChoice.state I P.restrictedState k hk ell (S.support_pos 1) (S.support_one 1) F symmetric

/-- Whole-horizon physical bounds for the forward child, kept as one named
proof to avoid elaborating the packet estimate twice inside `Step`. -/
theorem forwardPhysicalBounds (t : Icc (0 : ℝ) (F).parent.T) (x : Space) :
    ‖fderiv ℝ (fun y => (P.forwardState hq hB).evolution.velocity (t,y)) x‖ ≤
        gradientConstant*previousShear S.J S.X 0+(G).hchild*(goodRatio+(G).earlyRatio)+k^(-(1/4 : ℝ)) ∧
      ‖fderiv ℝ ((P.forwardState hq hB).evolution.force t) x‖ ≤
        hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0+
          2*(gradientConstant*previousShear S.J S.X 0)*(G).hchild*(goodRatio+(G).earlyRatio)+k^(-(1/4 : ℝ)) :=
  (F).physical_bounds symmetric _ _ P.restricted_gradient_bound P.restricted_hessian_bound t x

/-- The forward choice's parent, state, low bounds, physical bounds and renewed
frame, with the guards' shear, spike and `earlyRatio`. -/
def forwardStep : P.Step where
  parent := (F).parent
  state := P.forwardState hq hB
  hchild := (G).hchild
  δ := (G).δ
  ratio := (G).earlyRatio
  ratio_nonneg := (G).earlyRatio_nonneg
  hchild_eq := P.forwardGuards_shear hq hB
  delta_eq := P.forwardGuards_delta hq hB
  parent_horizon := rfl
  parent_scale := rfl
  label_eq := (F).label_constant
  low := (F).lowBounds (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    P.restricted_gradient_bound P.restricted_hessian_bound
    (P.smallness (G).hchild (G).δ (G).earlyRatio (G).child_nonneg (G).delta_nonneg (G).earlyRatio_nonneg
      (initial_cost_of_bad_cost _ _ (G).child_nonneg (G).earlyRatio_nonneg (P.forward_bad_cost hq hB))
      (P.forward_pressure_cost hq hB))
  low_exterior := rfl
  low_core := rfl
  low_pressure := rfl
  low_boundary := rfl
  low_radius := rfl
  physical_bounds := P.forwardPhysicalBounds hq hB
  bad_cost := P.forward_bad_cost hq hB
  pressure_cost := P.forward_pressure_cost hq hB
  geometry := P.forwardGeometry hq hB
  geometry_targetTime := P.forwardGeometry_targetTime hq hB
  geometry_coupling := P.forwardFrame_a
  geometry_y := rfl
  geometry_delta_pos := (I).delta_pos
  geometry_shear := rfl
  renewal_errors := P.forward_renewal_errors hq hB
  renewal := (F).renewal symmetric (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    (frameConstant*(1+previousShear S.J S.X 0))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one 0)))
    (next_frame_bounds (S := S) (n := 0)).1 (next_frame_bounds (S := S) (n := 0)).2.1
    (next_frame_bounds (S := S) (n := 0)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact
  renewal_matches := (F).renewal_matches symmetric (gradientConstant*previousShear S.J S.X 0)
    (hessianConstant*previousShear S.J S.X 0*olderShear S.J S.X 0)
    (frameConstant*(1+previousShear S.J S.X 0))
    (mul_nonneg gradient_nonneg (zero_le_one.trans (S.previousShear_one 0)))
    (next_frame_bounds (S := S) (n := 0)).1 (next_frame_bounds (S := S) (n := 0)).2.1
    (next_frame_bounds (S := S) (n := 0)).2.2
    P.restricted_gradient_bound P.restricted_hessian_bound
    firstNormal firstNormal_unit firstFrame support compact
  renewal_G := rfl
  renewal_error := rfl

def forwardNext : Stage S 1 := P.next (P.forwardStep hq hB)

theorem forwardNext_time : (P.forwardNext hq hB).time=P.nextTime := rfl

end EulerPacketInduction.Stage
