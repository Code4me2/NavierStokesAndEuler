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

/-- Symmetric second derivatives remove the entire derivative-of-Jacobian term from curl. -/
theorem curl_pullbackCovector (Ξ Q : Space → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (x : Space) (hQ : DifferentiableAt ℝ Q x) :
    vectorCurl (pullbackCovector Ξ Q) x =
      curlMatrix ((fderiv ℝ Ξ x).adjoint.comp (fderiv ℝ Q x)) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Ξ) x :=
    ((hΞ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have hA : HasFDerivAt (fun y => (fderiv ℝ Ξ y).adjoint)
      ((realAdjoint (U := Space) (E := Space)).comp (fderiv ℝ (fderiv ℝ Ξ) x)) x :=
    (realAdjoint (U := Space) (E := Space)).hasFDerivAt.comp x hD.hasFDerivAt
  have hp := hA.clm_apply hQ.hasFDerivAt
  have hzero : curlMatrix
      (((realAdjoint (U := Space) (E := Space)).comp
        (fderiv ℝ (fderiv ℝ Ξ) x)).flip (Q x)) = 0 := by
    ext i
    change ((fderiv ℝ (fderiv ℝ Ξ) x (EuclideanSpace.single (i + 1) 1)).adjoint (Q x)) (i + 2) -
      ((fderiv ℝ (fderiv ℝ Ξ) x (EuclideanSpace.single (i + 2) 1)).adjoint (Q x)) (i + 1) = 0
    rw [adjoint_apply_coordinate, adjoint_apply_coordinate]
    have hs := ((hΞ.contDiffAt (x := x)).isSymmSndFDerivAt (n := 2) (by simp)).eq
      (EuclideanSpace.single (i + 1) 1) (EuclideanSpace.single (i + 2) 1)
    rw [hs, sub_self]
  change vectorCurl (fun y => (fderiv ℝ Ξ y).adjoint (Q y)) x = _
  rw [vectorCurl_eq_matrix _ x hp.differentiableAt, hp.fderiv, curlMatrix_add, hzero, add_zero]





end EulerPacketPiola
