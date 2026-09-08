import Euler.EulerFiniteLifespan
import Euler.OrdinaryEulerMaximal
import Euler.OrdinaryEulerContinuation

/-! C¹ breakdown for the concrete compactly supported datum. The
infinite-limsup statement is expressed directly: after every time below
the maximal time, the actual gradient supremum exceeds every real bound.
The norms are bounded-continuous-function norms at individual times,
not totalized real L∞ seminorms of unverified measurable fields. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

def maximalVelocityNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t)‖

def maximalGradientNorm (t : L.Time) : ℝ := ‖finiteField (L.maximalField t).derivative‖

def maximalC1Norm (t : L.Time) : ℝ := L.maximalVelocityNorm t+L.maximalGradientNorm t

theorem maximalVelocityNorm_nonneg (t : L.Time) : 0 ≤ L.maximalVelocityNorm t := norm_nonneg _



theorem maximalGradientNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalGradientNorm t ≤ K ↔ ∀ x, ‖fderiv ℝ (L.maximalVelocity t) x‖ ≤ K := by
  rw [maximalGradientNorm,BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply]
  rfl

theorem maximalVelocityNorm_continuous : Continuous L.maximalVelocityNorm :=
  (continuous_finiteField L.maximalField L.maximalField_jet_continuous).norm

theorem maximalGradientNorm_continuous : Continuous L.maximalGradientNorm :=
  (continuous_finiteField (fun t => (L.maximalField t).derivative)
    (continuous_jetLp_derivative L.maximalField L.maximalField_jet_continuous)).norm

theorem maximalC1Norm_continuous : Continuous L.maximalC1Norm :=
  L.maximalVelocityNorm_continuous.add L.maximalGradientNorm_continuous


theorem maximalVelocity_gradient_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ (t : L.Time) (x : Space), τ < t ∧ K < ‖fderiv ℝ (L.maximalVelocity t) x‖ := by
  obtain ⟨S,hS,hSL,t,x,ht,hx⟩ := L.gradient_unbounded_near_endpoint τ K hτ
  refine ⟨L.shorterTime S hSL t,x,ht,?_⟩
  rwa [L.maximalVelocity_eq_evolution S hS hSL t]

theorem maximalGradientNorm_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ t : L.Time, τ < t ∧ K < L.maximalGradientNorm t := by
  obtain ⟨t,x,ht,hx⟩ := L.maximalVelocity_gradient_unbounded_near_endpoint τ K hτ
  exact ⟨t,ht,hx.trans_le ((L.maximalGradientNorm_le_iff t _).mp le_rfl x)⟩

theorem maximalC1Norm_unbounded_near_endpoint (τ K : ℝ) (hτ : τ < L.duration) :
    ∃ t : L.Time, τ < t ∧ K < L.maximalC1Norm t := by
  obtain ⟨t,ht,hK⟩ := L.maximalGradientNorm_unbounded_near_endpoint τ K hτ
  exact ⟨t,ht,hK.trans_le (le_add_of_nonneg_left (L.maximalVelocityNorm_nonneg t))⟩

end EulerOrdinarySobolev.FiniteLifespan

namespace EulerPacketInduction

open EulerOrdinarySobolev

abbrev MaximalTime : Type := lifespan.Time

def maximalC1Norm (t : MaximalTime) : ℝ := lifespan.maximalC1Norm t

end EulerPacketInduction
