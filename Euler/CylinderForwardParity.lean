import Euler.CylinderFieldReflection
import Euler.LpCylinderCoefficientTime
import Euler.LinearDuhamelNaturality
import Euler.LinearDuhamelWeighted

/-! Actual supported forward evolution preserves joint odd parity for even coefficients.

Merged in from the former module `Euler.LinearDuhamelSymmetry`: `solution_neg`.
-/

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
end

noncomputable section

namespace EulerCylinderForwardParity

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerLpCylinderCoefficients EulerCylinderFieldReflection EulerLinearDuhamel
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
  (hB : ∀ t x, B t (-x) = B t x)
  (U : Evolution T hT (liftedOperatorPath P S hS T B))

include hB in
theorem solution_reflection (f : C(Icc (0 : ℝ) T,Supported P V S hS)) (a₀ : Supported P V S hS) :
    supportedPathReflection P S hS hSym (U.solution f a₀) =
      U.solution (supportedPathReflection P S hS hSym f) (supportedReflection P S hS hSym a₀) := by
  apply (U.solution_map U (supportedReflection P S hS hSym) _ f a₀).symm
  intro t u
  change liftedOperator P S hS (B t) (supportedReflection P S hS hSym u) =
    supportedReflection P S hS hSym (liftedOperator P S hS (B t) u)
  rw [← supportedOperator_eq_square]
  exact (supportedReflection_operator P S hS hSym (B t) (hB t) u).symm

include hB in
theorem solution_reflection_neg (f : C(Icc (0 : ℝ) T,Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, supportedReflection P S hS hSym (f t) = -f t)
    (ha₀ : supportedReflection P S hS hSym a₀ = -a₀) (t : Icc (0 : ℝ) T) :
    supportedReflection P S hS hSym (U.solution f a₀ t) = -U.solution f a₀ t := by
  have hfp : supportedPathReflection P S hS hSym f = -f := ContinuousMap.ext (hf)
  have he := solution_reflection P S hS hSym T hT B hB U f a₀
  rw [hfp,ha₀,U.solution_neg] at he
  exact congrArg (fun p : C(Icc (0 : ℝ) T,Supported P V S hS) => p t) he

include hB hSym in
theorem solution_full_reflection_neg (f : C(Icc (0 : ℝ) T,Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, reflection P (f t : CylinderL2 P V) = -(f t : CylinderL2 P V))
    (ha₀ : reflection P (a₀ : CylinderL2 P V) = -(a₀ : CylinderL2 P V)) (t : Icc (0 : ℝ) T) :
    reflection P (U.solution f a₀ t : CylinderL2 P V) = -(U.solution f a₀ t : CylinderL2 P V) := by
  have h := solution_reflection_neg P S hS hSym T hT B hB U f a₀
    (fun r => Subtype.ext (hf r)) (Subtype.ext ha₀) t
  exact congrArg (fun u : Supported P V S hS => (u : CylinderL2 P V)) h

end EulerCylinderForwardParity
