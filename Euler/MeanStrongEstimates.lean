import Euler.MeanVelocityPressure
import Euler.TransverseStrongEstimates
import Euler.TimeH1PointwiseBounds

/-!
# Quantitative time estimates for the genuine mean inverse

The constants depend explicitly and polynomially on the time interval,
coefficient bounds, and the inverse-frame bound. The only square roots are the
proved finite-time trace/Poincaré factors. These are estimates of the actual
Bochner fields and continuous representatives constructed by the inverse.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution
  EulerTimeH1FieldProduct EulerTimeH1PointwiseBounds EulerTransverseGramInverse
  EulerTransverseStrongEstimates

-- Cache the inherited structures before forming norms of nested operator paths.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance

/-- Restricting F to the actual solenoidal subspace does not increase its norm. -/
theorem solenoidalFrame_norm_le (T : ℝ) (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    ‖solenoidalFrame T F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).2
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro z
  exact ((F t).le_opNorm (z : L2)).trans
    (mul_le_mul_of_nonneg_right (F.norm_coe_le_norm t) (norm_nonneg z))

/-- The ordinary projection equation is exactly the Gram equation on L²σ. -/
theorem gram_equation_of_ordinary (F F₁ : L2 →L[ℝ] L2) (f : L2) (a v : solenoidalSpace)
    (h : solenoidalProjection (F.adjoint (F (a : L2))) =
      solenoidalProjection (F.adjoint (f-(2 : ℝ) • F₁ (v : L2)))) :
    gram (F.comp solenoidalSpace.subtypeL) a =
      (F.comp solenoidalSpace.subtypeL).adjoint (f-(2 : ℝ) • F₁ (v : L2)) := by
  apply Subtype.ext
  simpa only [gram, adjoint_comp, Submodule.adjoint_subtypeL, comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    solenoidalProjection] using h


namespace StrongMeanEvolution

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)









end StrongMeanEvolution
end EulerMeanVariationalInverse
