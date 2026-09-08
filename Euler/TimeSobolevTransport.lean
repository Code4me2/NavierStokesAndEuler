import Euler.AsymmetricTransport
import Euler.TimeLpMultiplier
import Euler.SobolevTimeRegularization

/-! Actual derivative-losing transport on continuous coefficients and square-integrable higher Sobolev states. -/

noncomputable section

namespace EulerTimeSobolevTransport

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAsymmetricTransport
  EulerTimeLp EulerVolterraConvolution EulerSobolevTimeRegularization EulerHeatRegularizedPaths
  EulerSobolevHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A named local normed-group instance for the actual Sobolev scale. -/
local instance transportTimeGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

/-- A named local real normed-space instance for the actual Sobolev scale. -/
local instance transportTimeSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- A continuous actual velocity path gives a continuous path of asymmetric transport operators. -/
def transportPath {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s)) :
    C(Icc (0 : ℝ) T, SobolevSpace period (s+1) →L[ℝ] SobolevSpace period s) :=
  (asymmetricTransport period hs L hL).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Actual nonlinear transport of a higher Sobolev time field belongs to the full energy-order Bochner space. -/
def transportTime {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s+1))) : TimeLp T (SobolevSpace period s) :=
  timeMultiplier T hT (transportPath period hs L hL T u) v

/-- The actual Bochner transport is literal asymmetric Sobolev transport almost everywhere in time. -/
theorem transportTime_ae {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (v : TimeLp T (SobolevSpace period (s+1))) :
    (transportTime period hs L hL T hT u v : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => asymmetricTransport period hs L hL (extendPath T hT u t) (v t) :=
  timeMultiplier_ae T hT (transportPath period hs L hL T u) v


end EulerTimeSobolevTransport
