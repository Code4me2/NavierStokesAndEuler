import Euler.PacketInductionStage
import Euler.BaseLiteralFirstPacket

/-! The first stage of the actual induction is constructed from the
literal compact base solution and the first same-Q packet choice. -/

noncomputable section

namespace EulerPacketInductionScales.Scales

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerBaseDatum EulerPacketSupport EulerPacketSourceGeometry EulerPacketNormalizedPrimary
  EulerPacketLowConstants EulerPacketInduction EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketBaseGuardScales
  EulerParentRenewalScale EulerMeanHarmonic

-- Limit elaboration of the concrete flow only within this namespace scope.
attribute [local irreducible] initialParent

variable {c B : ℝ} (S : Scales c B)

def firstStage : Stage S 0 := by
  let F := S.first.packet S.j_one
  let P := F.initialFrame firstNormal firstNormal_unit firstFrame support compact
  have hparam := F.initialFrame_parameters firstNormal firstNormal_unit firstFrame support compact
  have hcost := F.initialFrame_costs firstNormal firstNormal_unit firstFrame support compact
  have hlow := S.first.lowBounds_values S.j_one
  have hbounds := initial_bounds (S.X^1000) (literalInitialError S.D S.X)
    (one_le_pow₀ S.x_one) S.first.error_small
  have htilt : P.sigma^2*S.X^2=1 := by
    rw [show P.sigma=sqrt (S.X^(-2 : ℝ)) from hparam.2.1,
      sq_sqrt (rpow_nonneg S.x_pos.le _),rpow_neg S.x_pos.le]
    norm_num only [rpow_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero _ S.x_pos.ne')
  refine {
    parent := S.first.parent S.j_one
    state := S.first.state S.j_one
    low := S.first.lowBounds S.j_one
    time := 0
    time_nonneg := le_rfl
    time_zero := fun _ => rfl
    time_lower := fun h => (h rfl).elim
    horizon_eq := ?horizon_eq
    horizon_le := le_rfl
    scale_eq := rfl
    label_eq := S.first.state_label S.j_one
    gradient_bound := ?gradient_bound
    hessian_bound := ?hessian_bound
    exterior_bound := ?exterior_bound
    core_bound := ?core_bound
    pressure_bound := ?pressure_bound
    boundary_eq := rfl
    radius_eq := hlow.2.2.1
    frame := P
    frame_shear := hparam.2.2
    frame_bound := ?frame_bound
    frame_error := ?frame_error
    coupling_error := ?coupling_error
    tilt_lower := ?tilt_lower
    tilt_upper := ?tilt_upper
    compression := fun h => (h rfl).elim }
  case horizon_eq =>
    change baseHorizon S.J S.X=0+2*timeWidth S.J S.X 0
    rw [zero_add,baseHorizon_eq_timeWidth S.J S.x_pos]
  case gradient_bound =>
    intro t x
    have h := (F.physical_bounds S.first.spike_one S.first.shear_pos.le t x).1
    dsimp only [FirstScaleGuards.state, previousShear]
    exact h.trans hbounds.1
  case hessian_bound =>
    intro t x
    have h := (F.physical_bounds S.first.spike_one S.first.shear_pos.le t x).2
    dsimp only [FirstScaleGuards.state, previousShear, olderShear]
    simpa only [mul_one] using h.trans hbounds.2
  case exterior_bound =>
    rw [hlow.1]
    simp only [sum_range_zero,add_zero,le_refl]
  case core_bound =>
    rw [hlow.2.1]
    simpa only [sum_range_zero,add_zero] using hbounds.1
  case pressure_bound =>
    rw [hlow.2.2.2]
    simp only [sum_range_zero,add_zero,le_refl]
  case frame_bound =>
    change P.G ≤ frameConstant*(1+1)
    rw [show P.G=1+initialCoefficientCost from hcost.1]
    have hf := EulerPacketFirstLowBounds.firstRatio_pos
    have hm := gradient_properties.2.1
    have hc := frame_properties.2.1
    have h0 := frame_properties.1
    linarith only [hf,hm,hc,h0]
  case frame_error =>
    exact le_of_eq hcost.2
  case coupling_error =>
    change |P.a-1| ≤ 2*∑ i ∈ range 0, renewalCost S.J S.D 4 c frameConstant S.X i
    rw [show P.a=1 from hparam.1]
    simp only [sub_self,abs_zero,sum_range_zero,mul_zero,le_refl]
  case tilt_lower =>
    change 1/2 ≤ P.sigma^2*S.X^2
    rw [htilt]
    norm_num
  case tilt_upper =>
    change P.sigma^2*S.X^2 ≤ 2
    rw [htilt]
    norm_num




end EulerPacketInductionScales.Scales
