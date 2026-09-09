import Euler.ComparatorLocalEvolution
import Euler.ScalarEulerVorticity
import Euler.OrdinaryEulerBKM

/-!
# Step 3: agreement on a compact set contradicts blowup

The last step of the top of the Euler argument. If the vorticity of the
canonical maximal solution stays in one compact set `K` and agrees on `K`
with a field that is jointly continuous on `[0,T*] × K`, then it is
uniformly bounded on the lifespan, which contradicts the proved
Beale--Kato--Majda criterion. A global Comparator solution supplies such a
field by step 2 (`comparator_agrees_with_canonical`) and joint smoothness.
-/

noncomputable section

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanCutoffCurl

namespace EulerOrdinarySobolev.FiniteLifespan

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Agreement on a compact set contradicts blowup. The Euler instance of the
common final step of both developments: a compact `K` that carries all the
vorticity, and a comparison field continuous on `[0,T*] × K`, bound the
vorticity supremum uniformly below the maximal time. -/
theorem false_of_vorticity_agree_on_compact (w : ℝ → Space → Space)
    (K : Set Space) (hK : IsCompact K)
    (hw : ContinuousOn (fun z : ℝ × Space => w z.1 z.2) (Icc 0 L.duration ×ˢ K))
    (hagree : ∀ (t : L.Time), ∀ x ∈ K, vectorCurl (L.maximalVelocity t) x = w t x)
    (hconf : ∀ t : L.Time, tsupport (vectorCurl (L.maximalVelocity t)) ⊆ K) : False := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hw
  have hcurl : ∀ (t : L.Time) x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ max M 0 := by
    intro t x
    by_cases hx : x ∈ K
    · rw [hagree t x hx]
      exact (hM ((t : ℝ), x) ⟨⟨t.property.1, t.property.2.le⟩, hx⟩).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hconf t hm)), norm_zero]
      exact le_max_right _ _
  obtain ⟨S, hS, hSL, t, hlarge⟩ := L.vorticityIntegral_unbounded (max M 0 * L.duration)
  have hbound : ∀ s x, ‖vectorCurl ((L.evolution S hS hSL).velocity s).field x‖ ≤ max M 0 := by
    intro s x
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcurl _ x
  have hupper := (L.evolution S hS hSL).vorticityIntegral_le_const (max M 0) hbound t
  have ht : (t : ℝ) ≤ L.duration := t.property.2.trans hSL.le
  exact (not_lt_of_ge (hupper.trans (mul_le_mul_of_nonneg_left ht (le_max_right _ _)))) hlarge

end EulerOrdinarySobolev.FiniteLifespan

namespace Euler.ComparatorBridge

/-- Step 3 of the top of the Euler argument: no global Comparator solution
starts from the datum of a finite lifespan whose canonical vorticity is
confined to one compact set. Steps 2 and 3 are composed here. -/
theorem no_global_solution_of_confined_vorticity {A : SmoothL2Field Space}
    (L : FiniteLifespan A) (K : Set Space) (hK : IsCompact K)
    (hconf : ∀ t : L.Time, tsupport (vectorCurl (L.maximalVelocity t)) ⊆ K) :
    ¬ ∃ v p, EulerExistenceAndSmoothnessR3 A.field v p := by
  rintro ⟨v, p, h⟩
  have hcompact (t : L.Time) : HasCompactSupport (vectorCurl (L.maximalVelocity t)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hconf t)
  have hmatch := comparator_agrees_with_canonical L h hcompact
  refine L.false_of_vorticity_agree_on_compact (fun t x => vectorCurl (v · t) x) K hK
    (h.vorticity_continuousOn.mono (fun z hz => ⟨hz.1.1, mem_univ _⟩)) ?_ hconf
  intro t x _
  rw [hmatch t]

end Euler.ComparatorBridge
