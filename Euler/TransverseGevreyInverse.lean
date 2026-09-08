import Euler.TransverseCoefficientGevrey
import Euler.HilbertCoerciveGevrey

/-!
# Uniform factorial estimates for the constructed transverse inverse

Every constant is an explicit polynomial in the interval length, frame
bounds, potential bound, and reciprocal frame lower bound. The same radius
works at every derivative order and input shift. The recurrence is derived
from the actual inverse equation, not assumed for an abstract jet.
-/

noncomputable section

open scoped ContDiff

namespace EulerTransverseGevreyInverse

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse
  EulerTransverseParameterRegularity EulerTransverseCoefficientGevrey
  EulerHilbertCoerciveGevrey EulerOperatorGevreyCalculus EulerGevrey
  EulerCoerciveProjection EulerTransverseGramInverse EulerTransverseCoordinateRegularity
  EulerTransverseVariationalInverse EulerVolterraConvolution EulerTimeLpCoefficientMap
  EulerTimeLpCoefficientGevrey

/-- Uniform polynomial bound for the inverse frame transport. -/
def transportCeiling (T C₀ C₁ c : ℝ) : ℝ :=
  1 + ((2*(c⁻¹)^2*C₀^2*C₁ + c⁻¹*C₁)*T + c⁻¹*C₀)

/-- Uniform polynomial bound for the inverse of the transported form. -/
def inverseCost (T C₀ C₁ c : ℝ) : ℝ := 2 * (transportCeiling T C₀ C₁ c)^2

/-- One polynomial top constant handles both coefficient and forcing amplitudes. -/
def solveCost (T C₀ C₁ CH c : ℝ) : ℝ :=
  1 + inverseCost T C₀ C₁ c * (formCost T C₀ C₁ CH + forcingCost T C₀ C₁ + 1)

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace U] [CompleteSpace E] in
/-- The explicit fixed-space coercivity gives the promised polynomial inverse bound. -/
theorem fixedCoercivity_inv_le (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (C₀ C₁ : ℝ)
    (hQ : ‖Q‖ ≤ C₀) (hQ₁ : ‖Q₁‖ ≤ C₁) :
    (fixedCoercivity T Q Q₁ c)⁻¹ ≤ inverseCost T C₀ C₁ c := by
  have ht : transportCost T Q Q₁ c ≤ transportCeiling T C₀ C₁ c := by
    unfold transportCost transportCeiling
    gcongr
  have ht0 := (transportCost_pos T hT Q Q₁ c hc).le
  have he : (fixedCoercivity T Q Q₁ c)⁻¹ = 2*(transportCost T Q Q₁ c)^2 := by
    simp only [fixedCoercivity, div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) (by norm_num)


variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ x t v, c * ‖v‖^2 ≤ ‖Q x t v‖^2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2) ≤ 1/2)
  (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁) (hH : ContDiff ℝ ∞ H)
  (Rc C₀ C₁ CH : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
  (hbH : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant Rc 0 n)




end EulerTransverseGevreyInverse
