import Euler.CylinderSlowCurl
import Euler.CylinderPotentialPath
import Euler.CylinderAngleAverageTime

/-! The actual potential and slow curl preserve the zero angular mean required by the packet recursion. -/

noncomputable section

namespace EulerCylinderCorrectorMeanZero

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderAngleAverage
  EulerCylinderAnglePrimitive EulerCylinderPotential EulerCylinderSlowCurl
  EulerParameterWordGevrey EulerCylinderSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]


variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ (LiftL2 P) := inferInstance
private local instance : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ C(K,LiftL2 P) := inferInstance



variable (p : C(K,LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))






end EulerCylinderCorrectorMeanZero
