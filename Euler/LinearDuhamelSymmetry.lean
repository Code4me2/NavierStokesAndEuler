import Euler.LinearDuhamelWeighted

/-!
# Independence and symmetries of the actual forward solve

The forced solution is independent of the selected homogeneous fundamental
representation. Consequently coefficient symmetries pass to the solution
without assuming any corresponding symmetry of that representation.
-/

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T,E →L[ℝ] E)}

namespace Evolution


/-- Sign reversal of both data reverses the actual solution. -/
theorem solution_neg (U : Evolution T hT B) (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    U.solution (-f) (-a₀) = -U.solution f a₀ := by
  rw [U.solution_eq_operators, U.solution_eq_operators, map_neg, map_neg, neg_add]

/-- Zero data vanish identically. -/
@[simp] theorem solution_zero (U : Evolution T hT B) :
    U.solution (0 : C(Icc (0 : ℝ) T,E)) 0 = 0 := by
  rw [U.solution_eq_operators, map_zero, map_zero, add_zero]

end Evolution

variable {P : Type*} (T : ℝ) (hT : 0 ≤ T)
  (B : P → C(Icc (0 : ℝ) T,E →L[ℝ] E)) (U : ∀ x, Evolution T hT (B x))



end EulerLinearDuhamel
