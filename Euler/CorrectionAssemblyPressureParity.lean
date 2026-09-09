import Euler.CorrectionAssemblyParity
import Euler.CorrectionAssemblyReconstruction

/-! Pointwise parity and canonical normalization of the assembled actual pressure. -/

noncomputable section

namespace EulerGraphPressurePotential

open EulerLiftedGradientSpace


end EulerGraphPressurePotential

namespace EulerCanonicalGraphPotential

open EulerLiftedGradientSpace


end EulerCanonicalGraphPotential

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerAllOrderCorrectionData
  EulerGraphPressurePotential EulerCanonicalGraphPotential
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}




/-- Any smooth potential of the same graph field agrees with the canonical
radial potential after subtracting its value at the origin. -/
theorem FiniteFamily.normalizedGraphPotential_eq_sub (F : FiniteFamily period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (q : Vector3 → ℝ)
    (hq : ContDiff ℝ ∞ q)
    (hgrad : ∀ x, gradient q x = F.graphPressure period k t x) (x : Vector3) :
    F.normalizedGraphPotential period k t x = q x - q 0 :=
  radialPotential_eq_sub _
    (Continuous.uncurry_left t (F.graphPressure_joint_continuous period k)) q hq hgrad x


end EulerCorrectionAssembly
