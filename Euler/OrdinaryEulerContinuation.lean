import Euler.OrdinaryEulerLocalExistence
import Euler.OrdinaryEulerConcatenation

/-! Genuine continuation of every closed smooth Euler evolution, and
the resulting gradient blowup criterion at a finite maximal horizon. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVolterraConvolution
  EulerContinuousTimeIntegral
open scoped Topology

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)

theorem exists_extension (hTpos : 0 < T) :
    ∃ (S : ℝ) (hS : 0 < S) (hTS : T < S), ∃ V : Evolution S hS.le,
      V.velocity ⟨0,le_rfl,hS.le⟩=U.velocity ⟨0,le_rfl,hT⟩ ∧
      ∀ t : Icc (0 : ℝ) T,
        V.velocity ⟨t,t.property.1,t.property.2.trans hTS.le⟩=U.velocity t := by
  let A := U.velocity ⟨T,hT,le_rfl⟩
  let V := localEvolution A (U.solenoidal ⟨T,hT,le_rfl⟩)
  have hmatch : U.velocity ⟨T,hT,le_rfl⟩=V.velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩ :=
    (localEvolution_initial A (U.solenoidal ⟨T,hT,le_rfl⟩)).symm
  have hST : T < T+regularizedTime A := lt_add_of_pos_right T (regularizedTime_pos A)
  refine ⟨T+regularizedTime A,add_pos hTpos (regularizedTime_pos A),hST,
    U.concatenate V hTpos (regularizedTime_pos A) hmatch,?_,?_⟩
  · exact U.concatenate_initial V hTpos (regularizedTime_pos A) hmatch
  · exact U.concatenate_left V hTpos (regularizedTime_pos A) hmatch


end Evolution

theorem HasEulerEvolution.extend {A : SmoothL2Field Space} {T : ℝ}
    (h : HasEulerEvolution A T) : ∃ S, T < S ∧ HasEulerEvolution A S := by
  obtain ⟨hT,U,hU⟩ := h
  obtain ⟨S,hS,hST,V,hV,_hagree⟩ := U.exists_extension hT
  exact ⟨S,hST,hS,V,hV.trans hU⟩

namespace FiniteLifespan

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

theorem no_endpoint : ¬ HasEulerEvolution A L.duration := by
  intro h
  obtain ⟨S,hS,hE⟩ := h.extend
  exact L.maximal S hS hE


theorem gradient_unbounded (K : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S) (x : Space),
      K < ‖fderiv ℝ ((L.evolution S hS hSL).velocity t).field x‖ := by
  by_contra hn
  push Not at hn
  apply L.no_endpoint
  apply L.endpoint_of_bounded_gradient ((max K 0)*L.duration)
  intro S hS hSL t
  apply ((L.evolution S hS hSL).gradientIntegral_le_const (max K 0)
    (fun r x => (hn S hS hSL r x).trans (le_max_left K 0)) t).trans
  exact mul_le_mul_of_nonneg_left (t.property.2.trans hSL.le) (le_max_right K 0)

theorem evolution_agrees_at (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (t : ℝ)
    (ht0 : 0 ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
    (L.evolution S hS hSL).velocity ⟨t,ht0,htS⟩=
      (L.evolution T hT hTL).velocity ⟨t,ht0,htT⟩ := by
  rcases le_total S T with hST | hTS
  · exact (L.evolution_agrees S T hS hT hSL hTL hST ⟨t,ht0,htS⟩).1.symm
  · exact (L.evolution_agrees T S hT hS hTL hSL hTS ⟨t,ht0,htT⟩).1

theorem gradient_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S) (x : Space),
      τ < t ∧ K < ‖fderiv ℝ ((L.evolution S hS hSL).velocity t).field x‖ := by
  by_contra hn
  push Not at hn
  let R := (max τ 0+L.duration)/2
  have hm : max τ 0 < L.duration := max_lt hτ L.duration_pos
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right τ 0,L.duration_pos]
  have hRL : R < L.duration := by dsimp [R]; linarith
  have hτR : τ < R := by dsimp [R]; linarith [le_max_left τ 0]
  let C := ‖(L.evolution R hR hRL).gradientNormPath‖
  obtain ⟨S,hS,hSL,t,x,hx⟩ := L.gradient_unbounded (max C K)
  apply (not_lt_of_ge (show ‖fderiv ℝ ((L.evolution S hS hSL).velocity t).field x‖ ≤ max C K from ?_)) hx
  by_cases ht : (t : ℝ) ≤ R
  · have he := L.evolution_agrees_at S R hS hR hSL hRL t t.property.1 t.property.2 ht
    rw [he]
    apply ((L.evolution R hR hRL).pointwise_gradient_le ⟨t,t.property.1,ht⟩ x).trans
    apply le_trans _ (le_max_left C K)
    exact le_trans (le_abs_self _) ((L.evolution R hR hRL).gradientNormPath.norm_coe_le_norm _)
  · exact (hn S hS hSL t x (hτR.trans (lt_of_not_ge ht))).trans (le_max_right C K)



end FiniteLifespan
end EulerOrdinarySobolev
