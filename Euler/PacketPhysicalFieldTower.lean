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

def graphPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).canonicalGraphWordPath
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0

theorem graphPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (graphPath D P κ Z k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) := by
  have h := (reconstructedTower D P κ Z).canonicalGraphWordPath_ae
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0 t
  simpa only [graphPath,EulerCylinderSobolev.iteratedFieldDerivative_zero,
    reconstructedTower_pointField,physicalPhase,cylinderGraph] using h

def graphTensorPath (k : ℝ) (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n


variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (D.F.field t x).det=1)

def eulerianPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k)



end EulerPacketPhysicalField
