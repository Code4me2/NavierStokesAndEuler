import Euler.EulerProof.CylinderSobolev

/-! # The coordinate directions are unit vectors

`standardDirection` picks out the four coordinate directions of the cylinder tangent space,
so each of them has norm exactly one.  Every block-Sobolev estimate feeds the resulting
inequality to a lemma quantified over an arbitrary family of directions bounded by one, so
the bound is stated here once, in a leaf module beside the definition, rather than being
reproved in each provider.
-/

namespace EulerCylinderSobolev

/-- Each of the four coordinate directions has norm at most one. -/
theorem standardDirection_norm_le_one (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

end EulerCylinderSobolev
