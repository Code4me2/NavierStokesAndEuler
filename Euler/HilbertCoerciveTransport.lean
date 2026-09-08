import Euler.TransverseVariationalOperator

/-!
# Coercive operator transport between Hilbert models

This elementary operator lemma applies equally to mean and transverse
displacement spaces, including forms with nonlocal initial-trace terms.
-/

noncomputable section

namespace EulerHilbertCoerciveTransport

open InnerProductSpace ContinuousLinearMap

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- Pull a genuine bounded operator back along a bounded linear coordinate map. -/
def transportedOperator (D : V →L[ℝ] W) (A : W →L[ℝ] W) : V →L[ℝ] V :=
  D.adjoint.comp (A.comp D)

/-- The transported bilinear form is exactly the original form on the image. -/
theorem transportedOperator_inner (D : V →L[ℝ] W) (A : W →L[ℝ] W) (u v : V) :
    ⟪transportedOperator D A u, v⟫_ℝ = ⟪A (D u), D v⟫_ℝ := adjoint_inner_left D v (A (D u))



end EulerHilbertCoerciveTransport
