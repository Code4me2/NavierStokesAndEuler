import Euler.MeanCoefficientPathJets
import Euler.TransverseSourceFrame
import Euler.OperatorGevreyCalculus

/-!
# Actual source coefficient paths for the transverse inverse

Evaluation of the uniformly smooth spatial coefficient path gives a genuine
smooth map from position to time paths. Restriction to the fixed orthonormal
reference plane is a linear contraction. The pointwise source derivative
bounds therefore imply exactly the time-path coefficient bounds required by
the constructed transverse inverse.
-/

noncomputable section

open scoped ContDiff BoundedContinuousFunction


namespace EulerTransverseSourceCoefficientPath

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseSourceFrame
  EulerOperatorGevreyCalculus EulerGevrey

section Evaluation

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance

/-- Actual spatial evaluation, performed uniformly along the time path. -/
def pathEvaluation (x : Space) : C(K,Space →ᵇ V) →L[ℝ] C(K,V) :=
  (BoundedContinuousFunction.evalCLM ℝ x).compLeftContinuous ℝ K

/-- Evaluation is a contraction in the genuine uniform path norm. -/
theorem pathEvaluation_norm (x : Space) : ‖pathEvaluation (K := K) (V := V) x‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)

/-- The source coefficient viewed as a time path at a spatial position. -/
def pointPath (A : SmoothCoefficientPath K V) (x : Space) : C(K,V) :=
  pathEvaluation 0 (translateCoefficientPath A.field x)

/-- The coefficient path has the literal prescribed pointwise values. -/
theorem pointPath_apply (A : SmoothCoefficientPath K V) (x : Space) (t : K) :
    pointPath A x t = A.field t x := by
  change A.field t (0+x) = A.field t x
  rw [zero_add]

/-- Genuine smooth position dependence, in the uniform time-path norm. -/
theorem pointPath_contDiff (A : SmoothCoefficientPath K V) : ContDiff ℝ ∞ (pointPath A) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,Space →ᵇ V)) (F := C(K,V)) (pathEvaluation 0)).comp A.translation_contDiff

/-- Source pointwise derivative bounds give actual operator-norm derivatives of the time path. -/
theorem pointPath_derivative_bound (A : SmoothCoefficientPath K V)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (x : Space) :
    ‖iteratedFDeriv ℝ n (pointPath A) x‖ ≤ C := by
  have h := (pathEvaluation (K := K) (V := V) 0).norm_iteratedFDeriv_comp_left
    (A.translation_contDiff.contDiffAt (x := x)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (pathEvaluation_norm (K := K) (V := V) 0)
    (norm_nonneg _)).trans (by simpa only [one_mul] using A.norm_iteratedFDeriv_translation_le n C hC hb x))


variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]




end Evaluation

section Frame

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

private local instance : NormedAddCommGroup (U →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,U →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →L[ℝ] Space) := inferInstance

variable (m₀ : Space) (Rperp : U ≃ₗᵢ[ℝ] referencePlane m₀)

/-- The fixed orthonormal reference embedding is a contraction, including a trivial plane. -/
theorem referenceEmbedding_norm : ‖referenceEmbedding m₀ Rperp‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖Rperp v‖ ≤ 1*‖v‖
  rw [one_mul, Rperp.norm_map]

/-- Restrict an actual coefficient operator to the reference plane. -/
def referenceRestriction : (Space →L[ℝ] Space) →L[ℝ] (U →L[ℝ] Space) :=
  (compL ℝ U Space Space).flip (referenceEmbedding m₀ Rperp)






variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]



end Frame

end EulerTransverseSourceCoefficientPath
