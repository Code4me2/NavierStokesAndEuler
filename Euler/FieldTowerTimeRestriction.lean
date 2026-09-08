import Euler.FieldTowerRepresentative

/-! A genuine derivative at one Sobolev order gives the same derivative at
all lower orders of the coherent towers. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set EulerCylinderSobolevSpace EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)]
  (A B : EulerAllOrderCorrectionData.FieldTower P T)

local instance restrictionGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace P q) := inferInstance
local instance restrictionSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace P q) := inferInstance
local instance restrictionTopology (q : ℕ) : TopologicalSpace (SobolevSpace P q) :=
  (inferInstance : PseudoMetricSpace (SobolevSpace P q)).toUniformSpace.toTopologicalSpace



end EulerAllOrderCorrectionData.FieldTower
