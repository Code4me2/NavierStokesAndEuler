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

/-- The exact differentiated ODE yields a triangular estimate in the fixed
profile norm, with the same homogeneous and Green operators at every order. -/
theorem weightedSolution_derivative_recurrence
    (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀)
    (hg₀ : g ⟨0,le_rfl,hT⟩ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ x (t s : Icc (0 : ℝ) T), s ≤ t → ‖(U x).propagator t s‖ ≤ C*g t/g s)
    (x : P) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) x‖ ≤
      C*‖iteratedFDeriv ℝ n a₀ x‖ + (C*T)*
        (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
          (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) (fun y => multiplier (B y)) x‖ *
            ‖iteratedFDeriv ℝ (n-(j+1))
              (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) x‖) := by
  let u := fun y => (U y).weightedSolution g hg (f y) (a₀ y)
  have hu := weightedSolution_contDiff T hT B U g hg f a₀ hB hf ha₀
  have hfreeze : ∀ y, u y = (U x).weightedInitial g hg (a₀ y) +
      (U x).weightedForcing g hg (f y + (multiplier (B y)-multiplier (B x)) (u y)) := by
    intro y
    have hd : multiplier (B y-B x) = multiplier (B y)-multiplier (B x) := by
      ext p t
      rfl
    simpa only [hd] using (U x).weighted_frozen_solution g hg (U y) (f y) (a₀ y)
  have hr := EulerFrozenEvolutionGevrey.derivative_recurrence
    (fun y => multiplier (B y)) u f a₀ (contDiff_multiplier B hB) hu hf ha₀ x
    ((U x).weightedInitial g hg) ((U x).weightedForcing g hg) hfreeze n
  exact hr.trans (add_le_add
    (mul_le_mul_of_nonneg_right ((U x).weightedInitial_norm g hg hg₀ C hC (hU x)) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right ((U x).weightedForcing_norm g hg hg₀ C hC (hU x)) (by positivity)))

/-- The fixed polynomial amplitude controlling the differentiated forward solve. -/
def forwardCost (T C A D CB : ℝ) : ℝ := 1 + C*A + C*T*(D+CB)


end EulerLinearDuhamel
