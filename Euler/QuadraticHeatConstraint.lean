import Euler.QuadraticHeatLocal
import Euler.DivergenceFreeHeat

/-! The local quadratic heat construction preserves the actual lifted divergence constraint. -/

noncomputable section

namespace EulerQuadraticSource

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerDivergenceFreeHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance constraintSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
local instance constraintSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance


end EulerQuadraticSource
