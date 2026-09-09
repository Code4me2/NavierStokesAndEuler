import Euler.VolumeSobolevPath

/-! Actual all-order field towers retain their spatial Sobolev regularity
after a smooth volume-preserving change of coordinates. -/

noncomputable section

namespace EulerVolumeSobolevPath

open MeasureTheory EulerMetricTransport EulerLiftedGradientSpace
open scoped ContDiff

variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (Y : C(K,C(Vector3,Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K,Lp (Tensor i) 2 (volume : Measure Vector3))) {n : ℕ}
  (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D^i)


end EulerVolumeSobolevPath

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerMetricTransport EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerLiftedGradientSpace
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)
  (k : ℝ) (m : Vector3)
  (Y : C(Icc (0 : ℝ) T,C(Vector3,Vector3)))
  (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : Icc (0 : ℝ) T × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D^i)

def volumePointField (t : Icc (0 : ℝ) T) : Vector3 → Vector3 :=
  A.physicalPointField k m t ∘ Y t

def volumeTensorPath : C(Icc (0 : ℝ) T,
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3)) :=
  EulerVolumeSobolevPath.tensorPath Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB


theorem volumeTensorPath_ae (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    (A.volumeTensorPath k m Y hmp n D hD hJ hB t : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (A.volumePointField k m Y t) :=
  EulerVolumeSobolevPath.tensorPath_ae Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB
    (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t


end EulerAllOrderCorrectionData.FieldTower
