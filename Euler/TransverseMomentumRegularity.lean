import Euler.TransverseVariationalInverse
import Euler.TransverseGramInverse
import Euler.TimeWeakDerivative
import Euler.TimeH1OperatorProduct

/-!
# Actual momentum regularity of the transverse variational inverse

The admissible tests are constructed by differentiating `Q(t) Jv(t)` with the
proved time-H¹ product rule. The weak equation then forces `Q* η_t` to have an
absolutely continuous representative. No momentum equation or second derivative
of the solved displacement is included in the assumptions.
-/

noncomputable section

namespace EulerTransverseMomentumRegularity

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTransverseVariationalInverse EulerTransverseGramInverse
  EulerTimeWeakDerivative EulerTimeH1OperatorProduct

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))

/-- The literal transverse momentum as an actual L² field. -/
def momentum (u : TimeLp T E) : TimeLp T U := (timeMultiplier T hT Q).adjoint u

/-- The forcing for the momentum derivative, before using the frame ODE. -/
def momentumForcing (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (u f : TimeLp T E) : TimeLp T U :=
  (timeMultiplier T hT Q₁).adjoint u -
    (timeMultiplier T hT Q).adjoint
      (timeMultiplier T hT H (primitiveTimeLp T hT u)) +
    (timeMultiplier T hT Q).adjoint f

/-- The momentum field is pointwise `Q(t)* u(t)` almost everywhere. -/
theorem momentum_ae (u : TimeLp T E) :
    (momentum T hT Q u : ℝ → U) =ᵐ[timeMeasure T]
      fun t => (extendPath T hT Q t).adjoint (u t) := by
  unfold momentum
  rw [timeMultiplier_adjoint]
  exact timeMultiplier_ae T hT (adjointPath T Q) u

/-- The momentum forcing has its literal pointwise expression. -/
theorem momentumForcing_ae (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (u f : TimeLp T E) :
    (momentumForcing T hT Q Q₁ H u f : ℝ → U) =ᵐ[timeMeasure T]
      fun t => (extendPath T hT Q₁ t).adjoint (u t) -
        (extendPath T hT Q t).adjoint
          (extendPath T hT H t (realPrimitive T u t)) +
        (extendPath T hT Q t).adjoint (f t) := by
  change (momentum T hT Q₁ u -
      momentum T hT Q (timeMultiplier T hT H (primitiveTimeLp T hT u)) +
      momentum T hT Q f : TimeLp T U) =ᵐ[timeMeasure T] _
  filter_upwards [Lp.coeFn_add
      (momentum T hT Q₁ u -
        momentum T hT Q (timeMultiplier T hT H (primitiveTimeLp T hT u)))
      (momentum T hT Q f),
    Lp.coeFn_sub (momentum T hT Q₁ u)
      (momentum T hT Q (timeMultiplier T hT H (primitiveTimeLp T hT u))),
    momentum_ae T hT Q₁ u,
    momentum_ae T hT Q (timeMultiplier T hT H (primitiveTimeLp T hT u)),
    momentum_ae T hT Q f,
    timeMultiplier_ae T hT H (primitiveTimeLp T hT u),
    primitiveTimeLp_ae T hT u] with t hadd hsub hq₁ hq hqf hHu hJu
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, hq₁, hq, hqf, hHu, hJu]

/-- Every zero-endpoint coordinate test gives a genuine admissible physical test. -/
theorem productDerivative_mem_transverse
    (hQ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E)
    (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (v : TimeLp T U) (hv : initialTrace T hT v = 0) :
    productDerivative T hT Q Q₁ v ∈ transverseDerivatives T hT m := by
  constructor
  · rw [initialTrace_productDerivative T hT Q Q₁ hQ, hv, map_zero]
  · intro t
    rw [terminalPrimitive_productDerivative T hT Q Q₁ hQ]
    exact hm t _

/-- Generic momentum extraction from the actual product-test identity. This also
applies to closed spatial Hilbert constraints, such as the solenoidal mean space. -/
theorem momentum_weak_of_product_tests
    (hQ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u f : TimeLp T E)
    (v : TimeLp T U)
    (htest : ⟪u, productDerivative T hT Q Q₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (primitiveTimeLp T hT u),
        primitiveTimeLp T hT (productDerivative T hT Q Q₁ v)⟫_ℝ =
      -⟪f, primitiveTimeLp T hT (productDerivative T hT Q Q₁ v)⟫_ℝ) :
    ⟪momentum T hT Q u, v⟫_ℝ =
      -⟪momentumForcing T hT Q Q₁ H u f, primitiveTimeLp T hT v⟫_ℝ := by
  rw [primitiveTimeLp_productDerivative T hT Q Q₁ hQ] at htest
  simp only [productDerivative, add_apply, comp_apply, inner_add_right] at htest
  simp only [momentum, momentumForcing, inner_add_left, inner_sub_left,
    adjoint_inner_left]
  linarith only [htest]



end EulerTransverseMomentumRegularity
