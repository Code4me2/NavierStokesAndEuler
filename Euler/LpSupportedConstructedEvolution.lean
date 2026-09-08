import Euler.LpSupportedEvolution
import Euler.LinearFundamentalPath

/-!
# Constructed spatial L² evolution from the coefficient field alone

The bounded-field Banach algebra supplies actual fundamental fields by the
proved Picard construction. Their multiplication operators give an actual
evolution on supported spatial L². The localized H3 estimate is imposed only
on this genuine homogeneous propagator and is then inherited with constant
one by the spatial L² evolution.
-/

noncomputable section

namespace EulerLpSupportedConstructedEvolution

open Set MeasureTheory ContinuousLinearMap EulerVolterraConvolution
  EulerLpSupportedSubspace EulerLpSupportedMultiplier EulerLpSupportedEvolution
  EulerLinearDuhamel EulerLinearFundamentalExistence
open scoped BoundedContinuousFunction

variable {α V : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

private local instance : NormedRing (V →L[ℝ] V) := inferInstance
private local instance : NormedAlgebra ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedRing (Field (α := α) (V := V)) := inferInstance
private local instance : NormedAlgebra ℝ (Field (α := α) (V := V)) := inferInstance

variable (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T,Field (α := α) (V := V)))

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- The constructed fields satisfy the literal pointwise homogeneous ODE. -/
theorem fundamental_pointwise_derivative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : α) :
    HasDerivWithinAt
      (fun s => extendPath (Y := Field (α := α) (V := V)) T hT (fundamentalPath T hT B).forward s x)
      ((extendPath (Y := Field (α := α) (V := V)) T hT B t x).comp
        (extendPath (Y := Field (α := α) (V := V)) T hT (fundamentalPath T hT B).forward t x))
      (Icc (0 : ℝ) T) t := by
  let ev : Field (α := α) (V := V) →L[ℝ] (V →L[ℝ] V) := BoundedContinuousFunction.evalCLM ℝ x
  have hd := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := Field (α := α) (V := V)) (F := V →L[ℝ] V) ev).comp_hasDerivWithinAt t
      ((fundamentalPath T hT B).derivative ⟨t,ht⟩)
  simp only [extendPath, projIcc_of_mem hT ht]
  convert hd using 1
  all_goals rfl

/-- A genuine supported-L² evolution constructed from the original bounded coefficient. -/
def constructedSupportedEvolution (μ : Measure α) (S : Set α) (hS : MeasurableSet S) :
    Evolution T hT (operatorPath μ S hS T B) :=
  liftEvolution μ S hS T hT B (fundamentalPath T hT B).forward (fundamentalPath T hT B).backward
    (fun t x _ => congrArg (fun A : Field (α := α) (V := V) => A x)
      ((fundamentalPath T hT B).forward_backward t))
    (fun t x _ => congrArg (fun A : Field (α := α) (V := V) => A x)
      ((fundamentalPath T hT B).backward_forward t))
    (fundamental_pointwise_derivative T hT B)


end EulerLpSupportedConstructedEvolution
