import Euler.MeanAccelerationGevrey
import Euler.MeanPhysicalTranslation
import Euler.MeanContinuousVelocity

/-!
# All-order estimates for the genuine strong mean fields

The actual coordinate velocity estimate supplied by the weak inverse gives
the next-shift acceleration estimate and the physical B, B_t estimates.
The constants are fixed polynomials in the coefficient amplitudes and the
proved inverse bound; none depends on the derivative order.
-/

noncomputable section

namespace EulerMeanStrongGevrey

open EulerGevrey

/-- Enlarging the integer shift preserves a factorial bound when the radius is at least one. -/
theorem majorant_shift_mono (R : ℝ) (hR : 1 ≤ R) (d n : ℕ) :
    majorant R d n ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have h : majorant R d n ≤ R*majorant R d n := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (majorant_nonneg R hR0 d n)
  exact h.trans (majorant_shift_le R hR0 d n)

end EulerMeanStrongGevrey

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanGramTranslation EulerMeanAccelerationGevrey EulerMeanStrongGevrey
  EulerTimeLp EulerVolterraConvolution EulerTimeLpGramGevrey EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The genuine acceleration is spatially smooth once the solved coordinate
velocity and prescribed coefficients and forcing are. -/
theorem acceleration_orbit_contDiff
    (c : ℝ) (hc : 0 < c)
    (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration) := by
  have heq := congrArg (fun v : TimeLp T solenoidalSpace =>
    fun a : Space => timeSolenoidalTranslation T a v) (s.acceleration_eq_meanAcceleration c hc hLower)
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ ∞ g) heq)
    (meanAcceleration_translation_contDiff T hT F F₁ c hc hLower s.velocityLp f hF hF₁ hv hf)

variable (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
  (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
  (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R) (hRcR : Rc ≤ R)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
  (hstrong : 2*gramCost c CF (3*CF*(Cf+6*CF₁))*(Rc+1) ≤ R)
  (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0 n)
  (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc 0 n)
  (d : ℕ)
  (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤ Cf*majorant R d n)
  (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp) a‖ ≤ majorant R (d+1) n)



end EulerMeanVariationalInverse.StrongMeanEvolution
