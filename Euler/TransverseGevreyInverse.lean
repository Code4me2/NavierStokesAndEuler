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

/-- The top constant is at least one for all nonnegative coefficient bounds. -/
theorem solveCost_one_le (T C₀ C₁ CH c : ℝ)
    (hT : 0 ≤ T) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) :
    1 ≤ solveCost T C₀ C₁ CH c := by
  unfold solveCost
  have h : 0 ≤ inverseCost T C₀ C₁ c *
      (formCost T C₀ C₁ CH + forcingCost T C₀ C₁ + 1) := by
    unfold inverseCost formCost forcingCost derivativeCost
    positivity
  linarith

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

include hQ hQ₁ hH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH in
/-- The actual zero-endpoint coordinate solve has a single-shift factorial
bound with a radius uniform in the derivative order and input shift. -/
theorem fixedFrameSolution_gevrey
    (R : ℝ) (hR : 2 * solveCost T C₀ C₁ CH c * (Rc+1) ≤ R)
    (f : P → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y =>
      fixedFrameSolver T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
        K hK (hPotential y) hsmall (f y)) x‖ ≤ majorant R (d+1) n := by
  let A := fun y => fixedFrameOperator T hT (Q y) (Q₁ y) (H y)
  let δ := fun y => fixedCoercivity T (Q y) (Q₁ y) c
  let rhs := fun y => (-(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint) (f y)
  have hδ : ∀ y, 0 < δ y := fun y => fixedCoercivity_pos T hT (Q y) (Q₁ y) c hc
  have hAco : ∀ y v, δ y * ‖v‖^2 ≤ ⟪A y v, v⟫_ℝ := fun y =>
    fixedFrameOperator_coercive T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall
  have hAreg : ContDiff ℝ ∞ A := contDiff_fixedFrameOperator T hT Q Q₁ H hQ hQ₁ hH
  have hrhs : ContDiff ℝ ∞ rhs :=
    (contDiff_adjoint (contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁)).neg.clm_apply hf
  have hM := solveCost_one_le T C₀ C₁ CH c hT hC₀ hC₁ hCH
  have hR0 : 0 ≤ R := by nlinarith
  have hRcR : Rc ≤ R := by nlinarith
  have hCR : 0 ≤ formCost T C₀ C₁ CH := by unfold formCost; positivity
  have hFR : 0 ≤ forcingCost T C₀ C₁ := by unfold forcingCost derivativeCost; positivity
  have hI : 0 ≤ inverseCost T C₀ C₁ c := by unfold inverseCost; positivity
  have hMC : inverseCost T C₀ C₁ c * formCost T C₀ C₁ CH ≤ solveCost T C₀ C₁ CH c := by
    unfold solveCost
    nlinarith
  have hMF : inverseCost T C₀ C₁ c * forcingCost T C₀ C₁ ≤ solveCost T C₀ C₁ CH c := by
    unfold solveCost
    nlinarith
  have hinv (y : P) : (δ y)⁻¹ ≤ inverseCost T C₀ C₁ c := by
    apply fixedCoercivity_inv_le T hT (Q y) (Q₁ y) c hc C₀ C₁
    · simpa only [norm_iteratedFDeriv_zero, majorant, Nat.add_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using hbQ 0 y
    · simpa only [norm_iteratedFDeriv_zero, majorant, Nat.add_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using hbQ₁ 0 y
  have hbA (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ (j+1) A y‖ ≤
      formCost T C₀ C₁ CH * (Rc^(j+1) * ((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero] using
      fixedFrameOperator_bound T hT Q Q₁ H hQ hQ₁ hH Rc C₀ C₁ CH hRc hC₀ hC₁ hCH
        hbQ hbQ₁ hbH (j+1) y
  have hbQR (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q y‖ ≤ C₀*majorant R 0 j :=
    (hbQ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 j) hC₀)
  have hbQ₁R (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q₁ y‖ ≤ C₁*majorant R 0 j :=
    (hbQ₁ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 j) hC₁)
  have hbrhs := fixedForcing_bound T hT Q Q₁ hQ hQ₁ R C₀ C₁ hR0 hC₀ hC₁ hbQR hbQ₁R
    f hf d hbf
  exact coerciveSolution_gevrey_amplitudes A δ hδ hAco rhs hAreg hrhs
    (inverseCost T C₀ C₁ c) (formCost T C₀ C₁ CH) (forcingCost T C₀ C₁)
    (solveCost T C₀ C₁ CH c) Rc R hCR hFR hM hMC hMF hRc hR hinv hbA d hbrhs n x



end EulerTransverseGevreyInverse
