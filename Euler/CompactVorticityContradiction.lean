import Euler.CompactSmoothBounds
import Euler.CurlTimeDerivative
import Euler.OrdinaryEulerBKM

/-! A classical comparison field with uniformly confined vorticity cannot
agree with the maximal ordinary solution throughout a finite lifespan.
The contradiction uses the proved Beale--Kato--Majda integral criterion.

Merged in from the former module `Euler.CompactCurlBounds`: `vorticity_bounded_on_compact`.
-/

/-! Joint smoothness bounds the actual spatial vorticity on every fixed
compact spatial set and every closed finite time interval. -/

noncomputable section


open Set EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

theorem vorticity_bounded_on_compact (K : Set Space) (hK : IsCompact K) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ‖vectorCurl (v · t) x‖ ≤ M := by
  obtain ⟨C, hC⟩ := h.spatial_fderiv_bounded_on_compact K hK T
  refine ⟨‖ComparatorBridge.curlMatrixCLM‖ * max C 0,
    mul_nonneg (norm_nonneg ComparatorBridge.curlMatrixCLM) (le_max_right _ _), ?_⟩
  intro t ht x hx
  rw [vectorCurl_eq_matrix _ x ((h.velocity_contDiff t ht.1).differentiable (by simp) x)]
  change ‖ComparatorBridge.curlMatrixCLM (fderiv ℝ (v · t) x)‖ ≤ _
  exact (ComparatorBridge.curlMatrixCLM.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((hC x hx t ht).trans (le_max_left _ _))
      (norm_nonneg ComparatorBridge.curlMatrixCLM))

end Euler.EulerExistenceAndSmoothnessR3
end

noncomputable section

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerVectorCalculus EulerMeanBoundary EulerMeanCutoffCurl

namespace Euler.ComparatorBridge

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)
  {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

theorem finiteLifespan_contradiction_of_compact_vorticity
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (K : Set Space) (hK : IsCompact K)
    (hmatch : ∀ t : L.Time, L.maximalVelocity t = (v · (t : ℝ)))
    (hsupport : ∀ (t : L.Time) x, x ∉ K →
      vectorCurl (L.maximalVelocity t) x = 0) : False := by
  obtain ⟨M, hM, hbound⟩ := h.vorticity_bounded_on_compact K hK L.duration
  have hcurl : ∀ (t : L.Time) x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ M := by
    intro t x
    by_cases hx : x ∈ K
    · rw [hmatch t]
      exact hbound t ⟨t.property.1, t.property.2.le⟩ x hx
    · rw [hsupport t x hx, norm_zero]
      exact hM
  obtain ⟨S, hS, hSL, t, hlarge⟩ := L.vorticityIntegral_unbounded (M * L.duration)
  have hbound : ∀ s x, ‖vectorCurl ((L.evolution S hS hSL).velocity s).field x‖ ≤ M := by
    intro s x
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcurl _ x
  have hupper := (L.evolution S hS hSL).vorticityIntegral_le_const M hbound t
  have ht : (t : ℝ) ≤ L.duration := t.property.2.trans hSL.le
  exact (not_lt_of_ge (hupper.trans (mul_le_mul_of_nonneg_left ht hM))) hlarge

end Euler.ComparatorBridge
