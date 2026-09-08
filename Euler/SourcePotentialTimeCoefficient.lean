import Euler.SourcePotentialCoefficient
import Euler.PacketNormalTimeMap

/-! The actual time coefficient of the vector potential, with uniform factorial bounds. -/

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerPacketCrossProduct EulerSourceNormalCoefficient EulerBoundedFieldCalculus
  EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup NormalField := inferInstance
private local instance : NormedSpace ℝ NormalField := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup C(K,NormalField) := inferInstance
private local instance : NormedSpace ℝ C(K,NormalField) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup PotentialField := inferInstance
private local instance : NormedSpace ℝ PotentialField := inferInstance
private local instance : NormedAddCommGroup C(K,PotentialField) := inferInstance
private local instance : NormedSpace ℝ C(K,PotentialField) := inferInstance

def timeNormalPath (N : C(K,NormalField)) (Q₁ : C(K,Space →ᵇ ℝ →L[ℝ] Space)) : C(K,NormalField) :=
  pathCompositionMap (pathCompositionMap N (pathAdjointMap N)) (pathAdjointMap Q₁) -
    (2 : ℝ) • pathCompositionMap (pathCompositionMap N Q₁) N



section Families

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (N : X → C(K,NormalField)) (Q₁ : X → C(K,Space →ᵇ ℝ →L[ℝ] Space))
  (hN : ContDiff ℝ ∞ N) (hQ₁ : ContDiff ℝ ∞ Q₁)

include hN hQ₁ in
theorem timeNormalPath_contDiff : ContDiff ℝ ∞ (fun a => timeNormalPath (N a) (Q₁ a)) := by
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N (fun x => pathAdjointMap (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA := pathComposition_contDiff
    (fun x => pathCompositionMap (N x) (pathAdjointMap (N x)))
    (fun x => pathAdjointMap (Q₁ x)) hNN hQa
  have hB := pathComposition_contDiff (fun x => pathCompositionMap (N x) (Q₁ x)) N hNQ hN
  exact hA.sub (hB.const_smul 2)

include hN hQ₁ in
theorem timeNormalPath_bound (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n N a‖ ≤ C*majorant R 0 n)
    (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n Q₁ a‖ ≤ D*majorant R 0 n)
    (n : ℕ) (a : X) :
    ‖iteratedFDeriv ℝ n (fun x => timeNormalPath (N x) (Q₁ x)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  let A := fun x => pathCompositionMap (pathCompositionMap (N x) (pathAdjointMap (N x)))
    (pathAdjointMap (Q₁ x))
  let B := fun x => pathCompositionMap (pathCompositionMap (N x) (Q₁ x)) (N x)
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N (fun x => pathAdjointMap (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA : ContDiff ℝ ∞ A := pathComposition_contDiff _ _ hNN hQa
  have hB : ContDiff ℝ ∞ B := pathComposition_contDiff _ _ hNQ hN
  have hbNa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ))
    pathAdjointMap_norm N hN R C hR hC 0 hbN
  have hbQa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space))
    pathAdjointMap_norm Q₁ hQ₁ R D hR hD 0 hbQ₁
  have hbNN := pathComposition_bound N (fun x => pathAdjointMap (N x)) hN hNa
    R C C hR hC hC 0 0 hbN hbNa
  have hbNQ := pathComposition_bound N Q₁ hN hQ₁ R C D hR hC hD 0 0 hbN hbQ₁
  have hbA : ∀ j x, ‖iteratedFDeriv ℝ j A x‖ ≤ (3*(3*C*C)*D)*majorant R 0 j :=
    pathComposition_bound _ _ hNN hQa R (3*C*C) D hR (by positivity) hD 0 0 hbNN hbQa
  have hbB : ∀ j x, ‖iteratedFDeriv ℝ j B x‖ ≤ (3*(3*C*D)*C)*majorant R 0 j :=
    pathComposition_bound _ _ hNQ hN R (3*C*D) C hR (by positivity) hC 0 0 hbNQ hbN
  have hb₂B (j : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ j (fun y => (2 : ℝ) • B y) x‖ ≤
        (2*(3*(3*C*D)*C))*majorant R 0 j := by
    rw [iteratedFDeriv_const_smul_apply' (hB.contDiffAt.of_le (by simp)), norm_smul]
    norm_num only [Real.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (hbB j x) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have h := sub_bound A (fun y => (2 : ℝ) • B y) hA (hB.const_smul 2)
    R (3*(3*C*C)*D) (2*(3*(3*C*D)*C)) 0 hbA hb₂B n a
  exact h.trans_eq (by ring)

end Families

variable (m m₁ : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t y, c ≤ ‖m.field t y‖^2)

def potentialTimeCoefficient : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (normalColumn m₁).field)





end EulerSourcePotentialCoefficient
