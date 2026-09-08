import Euler.CylinderPathAdvection
import Euler.LpCylinderPaths

/-! Genuine nonlinear cylinder products preserve support of their multiplying factor. -/

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpSupportedSubspace EulerMetricTransport EulerLiftedWeakDerivative
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (S : Set Space) (hS : MeasurableSet S)

/-- Retain the actual values of a continuous path that already has the stated support. -/
def supportedPath (p : C(K,LiftL2 P)) (h : ∀ t, p t ∈ Supported P Space S hS) :
    C(K,Supported P Space S hS) :=
  ⟨fun t => ⟨p t,h t⟩, p.continuous.subtype_mk h⟩

omit [CompactSpace K] in
@[simp] theorem include_supportedPath (p : C(K,LiftL2 P))
    (h : ∀ t, p t ∈ Supported P Space S hS) :
    includePath P S hS (supportedPath P S hS p h) = p := by
  apply ContinuousMap.ext
  intro t
  rfl

variable (p q : C(K,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))






end EulerCylinderPathProduct
