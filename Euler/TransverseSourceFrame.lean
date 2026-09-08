import Euler.TransverseStrongEquation

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

/-- Applying the source deformation to the fixed orthonormal reference plane. -/
def framePath (T : ℝ) (F : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => (F t).comp (referenceEmbedding m₀ R), F.continuous.clm_comp continuous_const⟩








end EulerTransverseSourceFrame
