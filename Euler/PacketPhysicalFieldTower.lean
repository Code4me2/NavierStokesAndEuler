import Euler.FieldTowerAlgebra
import Euler.FlowL2Transport
import Euler.PacketSourceCorrectionCoefficients

/-! Reconstruction W=κFz is a genuine all-order field tower. Its graph
restriction and its actual inverse-flow pullback are continuous spatial L²
paths, with no independent integrability assumption on the perturbation. -/

noncomputable section

namespace EulerPacketPhysicalField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerPacketCorrectionCoefficients
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerFlowL2Transport

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)

def reconstructedTower : FieldTower P D.T :=
  (Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul κ

theorem reconstructedTower_pointField (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (reconstructedTower D P κ Z).pointField t x =
      κ • D.F.field t x.1 (Z.pointField t x) := by
  rw [reconstructedTower,FieldTower.smul_pointField,FieldTower.multiply_pointField]
  rfl





variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (D.F.field t x).det=1)




end EulerPacketPhysicalField
