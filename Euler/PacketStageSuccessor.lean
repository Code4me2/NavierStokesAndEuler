import Euler.PacketStageGeometry
import Euler.PacketStageLowPropagation
import Euler.PacketStagePhysicalBounds
import Euler.ParentRenewalScaleApplication

/-! # The successor step, written once

The forward step (stage `0`, no history) and the joined step (positive
history) build stage `n+1` from stage `n` by the same assembly. They differ in
the analytic pipeline that constructs the packet and in the ratio, `earlyRatio`
or `badRatio`, by which its guards measure the source error. `Step` records
what either pipeline delivers, phrased against the scale sequences, and `next`
is the one assembly of the `Stage` invariant from it. `PacketForwardSuccessor`
and `PacketJoinedSuccessor` instantiate `Step`; nothing below reads a guard. -/

noncomputable section

namespace EulerPacketInduction.Stage

open Set Finset Real InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerPacketSourceGeometry EulerPacketNormalizedPrimary EulerPacketMovingFrame
  EulerPacketInductionScales EulerPacketLowConstants EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketPressureScale
  EulerParentRenewalScale EulerPacketGeometryLowBounds EulerMeanHarmonic

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B} {n : ℕ} (P : Stage S n)

local notation "k" => frequency S.J S.X n

/-- The coercivity guard of the next parent's low bounds, from the packet's
budgets: `h` is the packet's target shear, `d` its spike and `r` its error
ratio. The parent's cumulative bounds absorb the increments (`next_localized`). -/
theorem smallness (h d r : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hinit : h*r+k^(-(1/4 : ℝ)) ≤ initialIncrement S.J S.X n)
    (hpress : 2*(gradientConstant*previousShear S.J S.X n)*h*(d*goodRatio+r)+k^(-(1/4 : ℝ)) ≤
      pressureIncrement S.J S.X n) :
    (P.restrictedLow.K+2*(gradientConstant*previousShear S.J S.X n)*h*(d*goodRatio+r)+
          k^(-(1/4 : ℝ)))*(P.nextHorizon^2/2)+
        (P.restrictedLow.Be+(h*r+k^(-(1/4 : ℝ))))*P.nextHorizon+
        boundaryLocalizationC2*(P.restrictedLow.Bc+(h*r+k^(-(1/4 : ℝ))))*
          P.restrictedLow.r^3*P.nextHorizon ≤ 1/2 := by
  have he : 0 ≤ k^(-(1/4 : ℝ)) := rpow_nonneg (S.normal_frequency n).pos.le _
  have hc := P.next_localized P.nextHorizon (h*r+k^(-(1/4 : ℝ)))
    (2*(gradientConstant*previousShear S.J S.X n)*h*(d*goodRatio+r)+k^(-(1/4 : ℝ)))
    P.nextHorizon_pos.le P.nextHorizon_le_base (by positivity [hh,hr])
    (by positivity [gradient_nonneg,S.previousShear_one n,hh,hd,goodRatio_pos,hr]) hinit hpress
  rw [restrictedLow_pressure,restrictedLow_exterior,restrictedLow_core,restrictedLow_radius]
  convert hc using 1; ring

/-- What one chosen packet delivers to the successor assembly at stage `n`.

The scalars `hchild`, `δ`, `ratio` are the packet's target shear, spike and
error ratio as its guards name them; `hchild_eq` and `delta_eq` identify the
first two with the scale sequences, and the ratio is `earlyRatio` in the forward
step and `badRatio` in the joined step. The rest is what the packet choice
produces on the restricted parent: the new parent and state (`parent_horizon`,
`parent_scale`, `label_eq`), the parent's low bounds updated by the packet's
error terms (`low_*`), the whole-horizon physical bounds, the pressure
budgets that the scale choice makes summable, and the renewed frame matched
to the packet's `lowGeometry` at its target time `nextTime`. -/
structure Step where
  parent : Parent
  state : SmoothState parent
  hchild : ℝ
  δ : ℝ
  ratio : ℝ
  ratio_nonneg : 0 ≤ ratio
  hchild_eq : hchild=shear S.J S.X n
  delta_eq : δ=spike S.J S.X n
  parent_horizon : parent.T=P.nextHorizon
  parent_scale : parent.ell=supportScale S.J S.X (n+1)
  label_eq : state.labels.K=k^80
  low : LowBounds parent
  low_exterior : low.Be=P.low.Be+(hchild*ratio+k^(-(1/4 : ℝ)))
  low_core : low.Bc=P.low.Bc+(hchild*ratio+k^(-(1/4 : ℝ)))
  low_pressure : low.K=P.low.K+2*(gradientConstant*previousShear S.J S.X n)*hchild*
    (δ*goodRatio+ratio)+k^(-(1/4 : ℝ))
  low_boundary : low.L=boundaryLocalizationC1*low.Bc+1
  low_radius : low.r=P.low.r
  physical_bounds : ∀ (t : Icc (0 : ℝ) parent.T) x,
    ‖fderiv ℝ (fun y => state.evolution.velocity (t,y)) x‖ ≤
        gradientConstant*previousShear S.J S.X n+hchild*(goodRatio+ratio)+k^(-(1/4 : ℝ)) ∧
      ‖fderiv ℝ (state.evolution.force t) x‖ ≤
        hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n+
          2*(gradientConstant*previousShear S.J S.X n)*hchild*(goodRatio+ratio)+k^(-(1/4 : ℝ))
  bad_cost : 2*(gradientConstant*previousShear S.J S.X n)*hchild*ratio ≤
    badCost S.J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence S.J S.X) n
  pressure_cost : 2*(gradientConstant*previousShear S.J S.X n)*hchild*(δ*goodRatio+ratio)+
    k^(-(1/4 : ℝ)) ≤ pressureIncrement S.J S.X n
  geometry : PhysicalGeometryData {x : Space // ‖x‖ ≤ (1/2 : ℝ)}
  geometry_targetTime : geometry.targetTime=P.nextTime
  geometry_coupling : geometry.a=P.frame.a
  geometry_y : geometry.y=(scaleSequence S.J S.X (n+1))⁻¹
  geometry_delta_pos : 0 < geometry.δ
  geometry_shear : geometry.hchild=hchild
  renewal_errors : geometry.couplingError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n ∧
    geometry.tiltError ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n
  renewal : ParentFrame (frameData parent) geometry.targetTime
  renewal_matches : RenewalAtTarget geometry renewal
  renewal_G : renewal.G=frameConstant*(1+previousShear S.J S.X n)
  renewal_error : renewal.error=k^(-(1/4 : ℝ))

/-- Stage `n+1` from a `Step`: the packet's error ratio is absorbed into the
next shear level (`ratio_absorption`), its budgets extend the cumulative
bounds by one term, and the renewed frame, re-indexed to `nextTime`, carries
the new shear, coupling, tilt and compression (`literal_step`). -/
def next (D : P.Step) : Stage S (n+1) := by
  have habsorb := ratio_absorption (S := S) (n := n) D.ratio D.ratio_nonneg (by
    have h := D.bad_cost
    rw [D.hchild_eq] at h
    nlinarith only [h])
  have hparams := literal_step D.renewal_matches S.J S.X n S.renewal_series (by norm_num)
    D.renewal_errors D.geometry_y
  have hcoupling : |D.renewal.a/P.frame.a-1| ≤ renewalCost S.J S.D 4 (q : ℝ) frameConstant S.X n := by
    have h := hparams.1
    rwa [D.geometry_coupling] at h
  have hinit := initial_cost_of_bad_cost D.hchild D.ratio
    (by rw [D.hchild_eq]; exact zero_le_one.trans (S.shear_one n)) D.ratio_nonneg D.bad_cost
  refine {
    parent := D.parent
    state := D.state
    low := D.low
    time := P.nextTime
    time_nonneg := P.nextTime_pos.le
    time_zero := fun h => by omega
    time_lower := fun _ => P.nextTime_lower
    horizon_eq := D.parent_horizon
    horizon_le := ?horizon_le
    scale_eq := D.parent_scale
    label_eq := D.label_eq
    gradient_bound := ?gradient_bound
    hessian_bound := ?hessian_bound
    exterior_bound := ?exterior_bound
    core_bound := ?core_bound
    pressure_bound := ?pressure_bound
    boundary_eq := D.low_boundary
    radius_eq := D.low_radius.trans P.radius_eq
    frame := D.renewal.changeActivation D.geometry_targetTime
    frame_shear := ?frame_shear
    frame_bound := ?frame_bound
    frame_error := ?frame_error
    coupling_error := ?coupling_error
    tilt_lower := ?tilt_lower
    tilt_upper := ?tilt_upper
    compression := ?compression }
  case horizon_le =>
    rw [D.parent_horizon]
    exact P.nextHorizon_le_base
  case gradient_bound =>
    intro t x
    refine (D.physical_bounds t x).1.trans ?_
    rw [D.hchild_eq]
    exact habsorb.1
  case hessian_bound =>
    intro t x
    refine (D.physical_bounds t x).2.trans ?_
    rw [D.hchild_eq]
    change hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n+
      2*(gradientConstant*previousShear S.J S.X n)*shear S.J S.X n*(goodRatio+D.ratio)+
        k^(-(1/4 : ℝ)) ≤ hessianConstant*shear S.J S.X n*previousShear S.J S.X n
    nlinarith only [habsorb.2]
  case exterior_bound =>
    rw [D.low_exterior]
    exact (P.initial_step_bound _ hinit).1
  case core_bound =>
    rw [D.low_core]
    exact (P.initial_step_bound _ hinit).2
  case pressure_bound =>
    rw [D.low_pressure,add_assoc]
    exact P.pressure_step_bound _ D.pressure_cost
  case frame_shear =>
    rw [ParentFrame.changeActivation_shear,D.renewal_matches.shear_eq D.geometry_delta_pos,
      D.geometry_shear]
    exact D.hchild_eq
  case frame_bound =>
    rw [ParentFrame.changeActivation_G,D.renewal_G]
    exact le_rfl
  case frame_error =>
    rw [ParentFrame.changeActivation_error,D.renewal_error]
    exact le_rfl
  case coupling_error =>
    rw [ParentFrame.changeActivation_a]
    exact P.coupling_step _ hcoupling
  case tilt_lower =>
    rw [ParentFrame.changeActivation_sigma]
    exact hparams.2.1
  case tilt_upper =>
    rw [ParentFrame.changeActivation_sigma]
    exact hparams.2.2
  case compression =>
    intro _
    have hc := D.renewal_matches.background_compression_of_error_le_one
      (priorError S.J S.D S.X (n+1)) (S.priorError_one (n+1))
    rw [ParentFrame.changeActivation_B,ParentFrame.changeActivation_m]
    simpa only [← D.geometry_targetTime] using hc

theorem next_time (D : P.Step) : (P.next D).time=P.nextTime := rfl

end EulerPacketInduction.Stage
