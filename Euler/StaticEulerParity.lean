import Euler.StaticEulerSolution
import Euler.SmallCorrectionParity
import Euler.AllOrderDriftFieldDecomposition

/-! Odd initial velocity produces the actual odd local Euler velocity
and odd pressure force. The scalar pressure, normalized at the origin,
is even. These are consequences of correction uniqueness. -/

noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCylinderField EulerCorrectionAssembly EulerMetricTransport
  EulerCanonicalGraphPotential EulerGraphPressurePotential

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x=0)
  (hodd : ∀ x, u.field (-x)= -u.field x)

include hodd

theorem symmetry : ParityData P (inputData P u C R hC hR) :=
  EulerSmallCorrection.parityData (EulerStaticCylinder.field P 1 u)
    (fun _ x _ => hodd x) (amplitude P C R hC hR)

theorem exactPacket_odd (t : Icc (0 : ℝ) 1) :
    -EulerCylinderReflection.reflection P ((exactPacket P u C R hC hR hu hdiv).velocity.field t) =
      (exactPacket P u C R hC hR hu hdiv).velocity.field t :=
  exactPacketOfResidual_velocity_odd P (correctionBudget P u C R hC hR hu hdiv)
    _ (symmetry P u C R hC hR hodd) t

theorem unit_velocity_odd (t : ℝ) (x : Space) :
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      -EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  let s := projIcc 0 1 zero_le_one t
  have h := continuous_representative_odd P
    ((exactPacket P u C R hC hR hu hdiv).velocity.field s)
    ((exactPacket P u C R hC hR hu hdiv).velocity.pointField s)
    (exactPacket_odd P u C R hC hR hu hdiv hodd s)
    (smoothField_continuous P _ ((exactPacket P u C R hC hR hu hdiv).velocity.pointField_smooth s))
    ((exactPacket P u C R hC hR hu hdiv).velocity.pointField_ae s) (x,(0 : AddCircle P))
  simpa only [Prod.neg_mk,neg_zero,EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,
    FieldTower.rawField,coveringMap,AddCircle.coe_zero] using h

omit hodd in
theorem unit_pressure_point (t : Icc (0 : ℝ) 1) (x : LiftDomain P) :
    (exactPacket P u C R hC hR hu hdiv).pressure.pointField t x =
      (correctionBudget P u C R hC hR hu hdiv).pointPressure P t x := by
  erw [exactPacket,exactPacketOfResidual_pressure_pointField]
  have hz : (Field.zero P 1).toFieldTower.pointField t x=0 := by
    change EulerSobolevPointEvaluation.pointEvaluation P x
      ((Field.zero P 1).toFieldTower.realization 3 t)=0
    rw [EulerSmallCorrection.zero_tower,map_zero]
  change (Field.zero P 1).toFieldTower.pointField t x+_=_
  rw [hz,zero_add]



theorem localVelocity_odd (t : ℝ) (x : Space) :
    localVelocity P u C R hC hR hu hdiv (t,-x)= -localVelocity P u C R hC hR hu hdiv (t,x) := by
  unfold localVelocity EulerTimeRescaling.velocity
  rw [EulerTimeRescaling.coordinates_apply,EulerTimeRescaling.coordinates_apply,
    unit_velocity_odd P u C R hC hR hu hdiv hodd,smul_neg]


end EulerStaticEuler
