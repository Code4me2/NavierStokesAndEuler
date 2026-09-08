import Euler.PacketPiolaAlgebra
import Euler.TransverseGramInverse

/-!
The actual curl Piola identity for a determinant-one coordinate map.
The derivative of the Jacobian cancels by symmetry of the genuine second
Fréchet derivative.  No curl identity or commutation relation is assumed.
-/

noncomputable section


namespace EulerPacketPiola

open EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl EulerVectorCalculus
  InnerProductSpace ContinuousLinearMap EulerTransverseGramInverse
open scoped ContDiff

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

theorem adjoint_apply_coordinate (A : Space →L[ℝ] Space) (q : Space) (i : Fin 3) :
    (A.adjoint q) i = ⟪A (EuclideanSpace.single i 1), q⟫_ℝ := by
  simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
    A.adjoint_inner_right (EuclideanSpace.single i 1) q

/-- Pull back a Euclidean covector field by the actual derivative of the coordinate map. -/
def pullbackCovector (Ξ Q : Space → Space) (x : Space) : Space :=
  (fderiv ℝ Ξ x).adjoint (Q x)






end EulerPacketPiola
