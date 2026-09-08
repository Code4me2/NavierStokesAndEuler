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

omit [CompleteSpace U] [CompleteSpace E] in
/-- The frame is literally the source expression `F R⊥`. -/
theorem framePath_apply (T : ℝ) (F : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (t : Icc (0 : ℝ) T) (x : U) :
    framePath m₀ R T F t x = F t (R x : E) := rfl

omit [CompleteSpace U] in
/-- The source frame maps into the moving tangent plane. -/
theorem framePath_tangent (T : ℝ) (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (t : Icc (0 : ℝ) T) (x : U) :
    ⟪movingNormal (F t) m₀, framePath m₀ R T A t x⟫_ℝ = 0 := by
  apply (tangent_iff (F t) m₀ _).2
  rw [framePath_apply, hA]
  change (F t).symm (F t (R x : E)) ∈ referencePlane m₀
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact (R x).property

omit [CompleteSpace U] in
/-- Every moving tangent vector is in the range of the actual source frame. -/
theorem framePath_range (T : ℝ) (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (t : Icc (0 : ℝ) T) (η : E) (hη : ⟪movingNormal (F t) m₀, η⟫_ℝ = 0) :
    ∃ x : U, framePath m₀ R T A t x = η := by
  refine ⟨frameCoordinates (F t) m₀ R η, ?_⟩
  rw [framePath_apply, hA]
  exact frame_reconstruct (F t) m₀ η R hη

omit [CompleteSpace U] [CompleteSpace E] in
/-- A bound on `F⁻¹` gives a quantitative lower frame bound, because `R⊥` is isometric. -/
theorem framePath_lower_bound (T : ℝ) (F : Icc (0 : ℝ) T → E ≃L[ℝ] E)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).toContinuousLinearMap)
    (B : ℝ) (hB : 0 < B) (hinv : ∀ t, ‖(F t).symm.toContinuousLinearMap‖ ≤ B)
    (t : Icc (0 : ℝ) T) (x : U) :
    (B⁻¹)^2 * ‖x‖^2 ≤ ‖framePath m₀ R T A t x‖^2 := by
  have hn : ‖x‖ ≤ B * ‖framePath m₀ R T A t x‖ := by
    calc
      ‖x‖ = ‖(F t).symm (framePath m₀ R T A t x)‖ := by
        rw [framePath_apply, hA]
        change ‖x‖ = ‖(F t).symm (F t (R x : E))‖
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact (R.norm_map x).symm
      _ ≤ ‖(F t).symm.toContinuousLinearMap‖ * ‖framePath m₀ R T A t x‖ :=
        (F t).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B * ‖framePath m₀ R T A t x‖ :=
        mul_le_mul_of_nonneg_right (hinv t) (norm_nonneg _)
  have hdiv : ‖x‖ / B ≤ ‖framePath m₀ R T A t x‖ :=
    (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hn)
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg x) hB.le) (norm_nonneg _)).2 hdiv
  simpa only [div_eq_mul_inv, mul_pow, mul_comm] using hs

omit [CompleteSpace U] [CompleteSpace E] in
/-- The actual within-interval derivative commutes with a fixed reference frame. -/
theorem framePath_hasDerivWithinAt (T : ℝ) (hT : 0 ≤ T)
    (A A₁ : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (framePath m₀ R T A))
      (framePath m₀ R T A₁ t) (Icc (0 : ℝ) T) t := by
  have h := (hd t).clm_comp (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (referenceEmbedding m₀ R))
  convert h using 1
  · rfl
  · simp only [comp_zero, add_zero]
    rfl

omit [CompleteSpace U] [CompleteSpace E] in
/-- The source equation `F_tt = -H F` gives the precise frame equation used in (10). -/
theorem framePath_second_equation (T : ℝ)
    (A A₂ H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hframe : ∀ t, A₂ t = -((H t).comp (A t))) (t : Icc (0 : ℝ) T) :
    framePath m₀ R T A₂ t = -((H t).comp (framePath m₀ R T A t)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [framePath_apply, hframe, neg_apply, comp_apply]


end EulerTransverseSourceFrame
