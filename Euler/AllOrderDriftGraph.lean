import Euler.FieldTowerCanonicalGraph
import Euler.CorrectionAssemblySourceTower

/-! Actual spatial L² paths of the constructed correction and its pressure
on every fixed continuous phase graph, including every cylinder word and
the genuine time derivative. -/

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev
  EulerMetricTransport EulerVolterraConvolution EulerAllOrderCorrectionData

variable (P : ℝ) [Fact (0 < P)]
  {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

def Budget.graphCorrectionWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  (B.fieldTower P).canonicalGraphWordPath θ hθ n w

def Budget.graphTimeDerivativeWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  (B.timeDerivativeTower P).canonicalGraphWordPath θ hθ n w

def Budget.graphPressureWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  (B.pressureTower P).canonicalGraphWordPath θ hθ n w

theorem Budget.correctionTower_pointField (t : Icc (0 : ℝ) T) :
    (B.fieldTower P).pointField t = B.pointField P t :=
  (B.fieldTower P).pointField_unique t (B.pointField P t)
    (Continuous.uncurry_left t (B.pointField_joint_continuous P)) (B.pointField_ae P t)

theorem Budget.pressureTower_pointField (t : Icc (0 : ℝ) T) :
    (B.pressureTower P).pointField t = B.pointPressure P t :=
  (B.pressureTower P).pointField_unique t (B.pointPressure P t)
    (Continuous.uncurry_left t (B.pointPressure_joint_continuous P)) (B.pointPressure_ae P t)





end EulerAllOrderDriftCorrection
