import Euler.SourcePotentialTimeCoefficient
import Euler.CylinderPotentialTime

/-! The source vector potential has its genuine, explicitly constructed time derivative. -/

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCrossProduct
  EulerVolterraConvolution EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderPotential
open scoped ContDiff BoundedContinuousFunction

variable (T : ℝ) (hT : 0 ≤ T)
  (m m₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖^2)

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable (hmt : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : Space,
  HasDerivWithinAt (fun r => extendPath T hT m.field r y)
    (extendPath T hT m₁.field t y) (Icc (0 : ℝ) T) t)


variable (P : ℝ) [Fact (0 < P)]
  (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)


end EulerSourcePotentialCoefficient
