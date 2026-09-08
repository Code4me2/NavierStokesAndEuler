import Euler.ShortTimeLinearGrowth
import Euler.PacketSourcePropagator
import Euler.PacketParentForwardBudget

/-! The first-packet homogeneous estimate follows from the actual constructed
coordinate evolution. Its coefficient is bounded by the source deformation
and its first time derivative; determinant one supplies the inverse bound.
The resulting forward budget has constant profile one and propagator cost two. -/

noncomputable section

namespace EulerPacketSourcePropagator

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerSourceForwardCoefficient EulerVolterraConvolution
  EulerTransverseGramInverse EulerPacketPiola EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

private local instance : NormedRing (U →L[ℝ] U) := inferInstance
private local instance : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

def shortTimeRate (C C₁ : ℝ) : ℝ := 2*(1+3*C^2)^2*C*C₁


variable (D : Data U)





end EulerPacketSourcePropagator
