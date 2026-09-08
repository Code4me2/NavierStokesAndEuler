import Euler.LinearDuhamelParameter
import Euler.LinearDuhamelWeighted
import Euler.FrozenEvolutionGevrey

/-!
# Actual all-order profile estimates for the forward initial value problem

Qualitative smoothness comes from the actual fixed-space Volterra inverse.
Quantitative differentiation instead freezes the evolution and uses its
profile-normalized Green operator, whose norm is bounded by `C*T` directly.
The profile's extrema never enter the factorial radius or amplitude.
-/

noncomputable section


namespace EulerLinearDuhamel

open Set Finset ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerContinuousPathCalculus EulerGevrey
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T,E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
  (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E)

private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) := inferInstance
private local instance : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) := inferInstance

/-- Normalization by a fixed profile preserves actual parameter regularity. -/
theorem weightedSolution_contDiff {n : ℕ∞ω} (hB : ContDiff ℝ n B)
    (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => (U x).weightedSolution g hg (f x) (a₀ x)) := by
  have hw : ContDiff ℝ n (fun x => weight g (f x)) := by
    change ContDiff ℝ n ((weight (E := E) g) ∘ f)
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(Icc (0 : ℝ) T,E)) (F := C(Icc (0 : ℝ) T,E)) (weight g)).comp hf
  have hs := solution_contDiff T hT B U (fun x => weight g (f x)) a₀ hB hw ha₀
  change ContDiff ℝ n ((normalize (E := E) g hg) ∘
    (fun x => (U x).solution (weight g (f x)) (a₀ x)))
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
    (E := C(Icc (0 : ℝ) T,E)) (F := C(Icc (0 : ℝ) T,E)) (normalize g hg)).comp hs


/-- The fixed polynomial amplitude controlling the differentiated forward solve. -/
def forwardCost (T C A D CB : ℝ) : ℝ := 1 + C*A + C*T*(D+CB)


end EulerLinearDuhamel
