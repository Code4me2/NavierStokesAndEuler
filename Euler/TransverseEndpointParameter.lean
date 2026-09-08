import Euler.TransverseFixedEndpoint
import Euler.TransverseParameterRegularity

/-!
Actual parameter regularity of the nonzero-terminal transverse inverse.
The initial-zero energy and fixed-coordinate correction depend smoothly on
the coefficient paths.  An explicit affine coordinate trial implements the
same terminal coordinate at neighboring labels.
-/

noncomputable section


namespace EulerTransverseEndpointParameter

open Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTimeLpCoefficientMap EulerTransverseVariationalInverse EulerTransverseGramInverse
  EulerTransverseFixedSpaceInverse EulerTransverseParameterRegularity
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerCoerciveProjection EulerHilbertCoerciveParameter
open scoped ContDiff

variable {P U E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  {n : ℕ∞ω}

theorem contDiff_initialEnergy (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (fun x => energyOperator T hT (H x)) :=
  contDiff_const.sub
    (contDiff_const.clm_comp ((contDiff_timeMultiplier T hT H hH).clm_comp contDiff_const))


variable (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)




section AffineTrial

variable (A A₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))

/-- The exact derivative of `(t/T) Q(t) ξT`. -/
def affineTrial : U →L[ℝ] TimeLp T E :=
  (initialProductDerivative T hT A A₁).comp
    ((constantFieldOperator T hT).comp (T⁻¹ • ContinuousLinearMap.id ℝ U))

theorem affineTrial_primitive
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (ξT : U) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (affineTrial T hT A A₁ ξT) t =
      A t (((t : ℝ) / T) • ξT) := by
  change initialPrimitive T hT
    (initialProductDerivative T hT A A₁ (constantFieldOperator T hT (T⁻¹ • ξT))) t = _
  rw [initialPrimitive_initialProductDerivative T hT A A₁ hA,
    initialPrimitive_constantFieldOperator, smul_smul, div_eq_mul_inv]

theorem affineTrial_terminal (hTpos : 0 < T)
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (ξT : U) :
    initialPrimitive T hT (affineTrial T hT A A₁ ξT) ⟨T, hT, le_rfl⟩ =
      A ⟨T, hT, le_rfl⟩ ξT := by
  rw [affineTrial_primitive T hT A A₁ hA, div_self hTpos.ne', one_smul]

theorem affineTrial_tangent
    (hA : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT A) (A₁ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t v, ⟪m t, A t v⟫_ℝ = 0)
    (ξT : U) (t : Icc (0 : ℝ) T) :
    ⟪m t, initialPrimitive T hT (affineTrial T hT A A₁ ξT) t⟫_ℝ = 0 := by
  rw [affineTrial_primitive T hT A A₁ hA]
  exact hm t _

end AffineTrial



end EulerTransverseEndpointParameter
