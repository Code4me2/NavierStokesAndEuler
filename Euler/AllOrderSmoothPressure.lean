import Euler.AllOrderPressureCoherence
import Euler.GraphPressurePotential

/-! Smooth actual pressure and graph potentials of the constructed common inviscid correction. -/

noncomputable section

namespace EulerAllOrderSmoothPressure

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerAllOrderCorrectionData
  EulerAllOrderCorrectionBudget EulerAllOrderCorrectionFamily EulerAllOrderLiftedCorrection
  EulerAllOrderPressureCoherence EulerVolterraConvolution EulerMetricTransport
  EulerSmoothPressureRepresentative EulerGraphPressurePotential
open scoped Topology ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Every strong derivative order of the common actual signed pressure is supplied by a constructed finite Sobolev realization. -/
def pressureJet {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (n : ℕ) (t : Icc (0 : ℝ) T) : SpatialJet period standardDirection n (commonPressure period hT A B t) := by
  rw [← signedPressurePath_value_common period hT A B (n+6) (by omega) t]
  exact EulerH6Pressure.SpatialJet.restrict
    (toJet period (signedPressurePath period hT A B (n+6) (by omega) t)) n (by omega)

/-- The common nonlinear correction satisfies its actual signed-pressure equation in L². -/
theorem commonPath_pressure_equation {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (commonPath period hT A B))
      (-value period (rawSourcePath period hT A B 6 le_rfl ⟨t,ht.1.le,ht.2.le⟩)-
        (A.metric.coefficient ⟨t,ht.1.le,ht.2.le⟩).operator
          (commonPressure period hT A B ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have h := commonPath_hasDerivAt period hT A B t ht
  rw [(A.atOrder period 6).source_value period le_rfl] at h
  exact h



end EulerAllOrderSmoothPressure
