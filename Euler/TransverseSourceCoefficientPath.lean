import Euler.MeanCoefficientPathJets
import Euler.TransverseStrongEquation
import Euler.OperatorGevreyCalculus

/-!
# Actual source coefficient paths for the transverse inverse

Evaluation of the uniformly smooth spatial coefficient path gives a genuine
smooth map from position to time paths. Restriction to the fixed orthonormal
reference plane is a linear contraction. The pointwise source derivative
bounds therefore imply exactly the time-path coefficient bounds required by
the constructed transverse inverse.

Merged in from the former module `Euler.TransverseSourceFrame`: `referenceEmbedding`.
-/

/-!
# The source frame `Q = F R⊥`

These coefficient lemmas discharge the moving-plane range and lower-frame
hypotheses using the prescribed invertible deformation and orthonormal reference
plane. No inverse solution or acceleration is supplied as input.
-/

noncomputable section

namespace EulerTransverseSourceFrame

open Set InnerProductSpace ContinuousLinearMap MeasureTheory
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTransverseFrameCoordinates EulerTransverseVariationalInverse
  EulerTransverseCoordinateRegularity EulerTransverseStrongEquation
  EulerTransverseGramInverse

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)

/-- The fixed orthonormal reference-plane embedding. -/
def referenceEmbedding : U →L[ℝ] E :=
  (referencePlane m₀).subtypeL.comp R.toContinuousLinearEquiv.toContinuousLinearMap









end EulerTransverseSourceFrame
end

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


/-- The source coefficient viewed as a time path at a spatial position. -/
def pointPath (A : SmoothCoefficientPath K V) (x : Space) : C(K,V) :=
  pathEvaluation 0 (translateCoefficientPath A.field x)

/-- The coefficient path has the literal prescribed pointwise values. -/
theorem pointPath_apply (A : SmoothCoefficientPath K V) (x : Space) (t : K) :
    pointPath A x t = A.field t x := by
  change A.field t (0+x) = A.field t x
  rw [zero_add]




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
