import Euler.OrdinaryEulerVorticity
import Euler.OrdinaryEulerContinuation
import Euler.OrdinaryEulerMaximal

/-! Actual vorticity supremum norms and their partial integrals on a
half-open maximal Euler interval. All quantities agree exactly with
the genuine smooth solutions on every shorter closed interval. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVectorCalculus EulerMeanCutoffCurl
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff Topology

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)



def maximalVorticityNorm (t : L.Time) : ℝ := vorticityNorm (L.maximalField t)

theorem maximalVorticityNorm_nonneg (t : L.Time) : 0 ≤ L.maximalVorticityNorm t :=
  vorticityNorm_nonneg _



theorem maximalVorticityNorm_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityNorm (L.shorterTime S hSL t)=(L.evolution S hS hSL).vorticityNormPath t := by
  change vorticityNorm (L.maximalField (L.shorterTime S hSL t))=_
  rw [L.maximalField_eq_evolution S hS hSL t]
  rfl









end EulerOrdinarySobolev.FiniteLifespan
