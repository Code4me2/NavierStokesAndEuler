import Euler.CylinderPotentialPath
import Euler.LpCylinderFullTime
import Euler.PacketCurlTime

/-! Genuine time derivatives of the constructed vector potential and its slow curl. -/

noncomputable section

namespace EulerCylinderPotential

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedWeakDerivative EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderAnglePrimitive
  EulerMeanCoefficients EulerVolterraConvolution EulerMeanBoundary EulerPacketPiola
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (T : ℝ) (hT : 0 ≤ T)
  (B B₁ : C(Icc (0 : ℝ) T,Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (hB₁ : ContDiff ℝ ∞ (translateCoefficientPath B₁))
  (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))

def potentialDerivative : C(Icc (0 : ℝ) T,LiftL2 P) :=
  potentialPath P B₁ p + potentialPath P B f

include hB hB₁ hp hf in
theorem potentialDerivative_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potentialDerivative P T B B₁ p f)) := by
  simp only [potentialDerivative, map_add]
  exact (potentialPath_orbit P B₁ hB₁ p hp).add (potentialPath_orbit P B hB f hf)

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable
  (hBt : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath T hT B s x)
      (extendPath T hT B₁ t x) (Icc (0 : ℝ) T) t)
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hBt hd

theorem potentialPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (potentialPath P B p))
      (potentialDerivative P T B B₁ p f t) (Icc (0 : ℝ) T) t :=
  fullProduct_hasDerivWithinAt P T hT B B₁ hBt (pathPrimitive P p) (pathPrimitive P f)
    (pathPrimitive_time_derivative P T hT p f hd) t



end EulerCylinderPotential
