import Euler.MeanVelocityOperator
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




/-- The actual strong acceleration pays only the inverse Gram and coefficient norms. -/
theorem acceleration_norm
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x) :
    ‖s.acceleration‖ ≤ (‖FInv‖+1)^2*‖F‖*(‖f‖+2*‖F₁‖*‖s.velocityLp‖) := by
  have heq : ∀ᵐ t ∂timeMeasure T,
      gram (extendPath T hT (solenoidalFrame T F) t) (s.acceleration t) =
      (solenoidalFrame T F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • solenoidalFrame T F₁ (projIcc 0 T hT t) (s.velocityLp t)) := by
    filter_upwards [s.equation, s.velocity_ae] with t ht hv
    have hh := congrArg (fun v : solenoidalSpace =>
      solenoidalProjection ((F (projIcc 0 T hT t)).adjoint
        (f t-(2 : ℝ) • F₁ (projIcc 0 T hT t) (v : L2)))) hv
    exact gram_equation_of_ordinary (F (projIcc 0 T hT t)) (F₁ (projIcc 0 T hT t))
      (f t) (s.acceleration t) (s.velocityLp t) (ht.trans hh.symm)
  have h := EulerTransverseStrongEstimates.acceleration_norm T (solenoidalFrame T F)
    (solenoidalFrame T F₁) (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv F hInv) hT s.velocityLp s.acceleration f heq
  have h' : ‖s.acceleration‖ ≤ (‖FInv‖+1)^2*‖solenoidalFrame T F‖*
      (‖f‖+2*‖solenoidalFrame T F₁‖*‖s.velocityLp‖) := by
    simpa only [meanFrameCoercivity, inv_inv] using h
  apply h'.trans
  gcongr
  · exact solenoidalFrame_norm_le T F
  · exact solenoidalFrame_norm_le T F₁





end StrongMeanEvolution
end EulerMeanVariationalInverse
