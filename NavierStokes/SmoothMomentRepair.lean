import NavierStokes.MomentRepair
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Smooth dependence of quadratic moment repair

The coefficients of a quadratic moment map are included among the variables
of a universal polynomial map. Its derivative at zero correction is a proved
product equivalence. The smooth inverse-function theorem constructs a local
solver; no solution branch or its regularity is assumed.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace NavierStokes.SmoothMomentRepair

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev QuadraticCoefficients := (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E)
abbrev RepairData := QuadraticCoefficients E × E

variable {E}

/-- The same type holds an unknown correction on input and a moment debt on output. -/
def forward (z : RepairData E) : RepairData E :=
  (z.1, z.1.1 z.2 + z.1.2 z.2 z.2)

def base (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) : RepairData E :=
  ((B.toContinuousLinearMap, A), 0)


/-- This universal coefficient map is polynomial, hence analytic. -/
theorem forward_contDiff : ContDiff ℝ ⊤ (forward : RepairData E → RepairData E) :=
  contDiff_fst.prodMk ((contDiff_fst.fst.clm_apply contDiff_snd).add
    ((contDiff_fst.snd.clm_apply contDiff_snd).clm_apply contDiff_snd))






/-- The quadratic growth constant is the actual norm of the bilinear coefficient. -/
theorem quadratic_norm_le (A : E →L[ℝ] E →L[ℝ] E) (c : E) :
    ‖A c c‖ ≤ ‖A‖ * ‖c‖ ^ 2 := by
  calc
    _ ≤ ‖A‖ * ‖c‖ * ‖c‖ := A.le_opNorm₂ c c
    _ = _ := by ring

/-- The two-point quadratic estimate follows from bilinearity. -/
theorem quadratic_sub_le (A : E →L[ℝ] E →L[ℝ] E) (c e : E) :
    ‖A c c - A e e‖ ≤ ‖A‖ * (‖c‖ + ‖e‖) * ‖c - e‖ := by
  have hid : A c c - A e e = A (c - e) c + A e (c - e) := by
    simp only [map_sub, sub_apply]
    abel
  rw [hid]
  calc
    _ ≤ ‖A (c - e) c‖ + ‖A e (c - e)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖c - e‖ * ‖c‖ + ‖A‖ * ‖e‖ * ‖c - e‖ :=
      add_le_add (A.le_opNorm₂ (c - e) c) (A.le_opNorm₂ e (c - e))
    _ = _ := by ring


/-- Compactness supplies genuine uniform bounds on the inverse linear part and
the quadratic coefficient; these bounds are not additional hypotheses. -/
theorem compact_inverse_quadratic_bounds [CompleteSpace E]
    {P : Type*} [TopologicalSpace P] (S : Set P) (hS : IsCompact S)
    (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E)
    (hB : ContinuousOn B S) (hA : ContinuousOn A S)
    (hinv : ∀ p ∈ S, (B p).IsInvertible) :
    ∃ β K : ℝ, 0 < β ∧ 0 < K ∧
      ∀ p ∈ S, ‖(B p).inverse‖ ≤ β ∧ ‖A p‖ ≤ K := by
  have hcontinuous : ContinuousOn (fun p => (B p).inverse) S := by
    intro p hp
    have hi : ContinuousAt
        (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)) (B p) :=
      ((hinv p hp).contDiffAt_map_inverse (𝕜 := ℝ) (n := 0)).continuousAt
    exact hi.comp_continuousWithinAt (hB p hp)
  obtain ⟨β₀, hβ₀⟩ := hS.exists_bound_of_continuousOn hcontinuous
  obtain ⟨K₀, hK₀⟩ := hS.exists_bound_of_continuousOn (E := E →L[ℝ] E →L[ℝ] E) (f := A) hA
  refine ⟨max β₀ 1, max K₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp
  exact ⟨(hβ₀ p hp).trans (le_max_left _ _), (hK₀ p hp).trans (le_max_left _ _)⟩


end NavierStokes.SmoothMomentRepair
