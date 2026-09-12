import NavierStokes.R3CompactCandidate
import NavierStokes.PeriodicForceDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open Set
open scoped ContDiff

namespace UnforcedRestart.ActualForcingBudget
open NavierStokes NavierStokes.ProblemStatement

/-- A uniform bound on each actual force jet, including the terminal time.
The constant is existential, not a perturbative smallness assertion. -/
theorem compact_jet_bound {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖ ≤ C := by
  obtain ⟨S, hS, hs⟩ := h.force_support
  obtain ⟨C, hC, hb⟩ := CompactSpatialForceDecay.jet_decay hS h.force_smooth hs
    h.force_time_support m 0
  exact ⟨C, hC, by simpa using hb⟩

/-- The time integrals below are genuine integrals of continuous functions. -/
theorem compact_jet_intervalIntegrable {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) (m : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x : Space) :
    IntervalIntegrable
      (fun t => ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact ((PeriodicForceDecay.futureJet_continuous h.force_smooth m).comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun t ht => show (t, x) ∈ futureDomain from ⟨ha.trans ht.1, mem_univ x⟩)).norm

/-- Pointwise-in-space time-integrated jet budget. This does not exchange
an integral and a supremum, and is not a PDE stability theorem. -/
theorem compact_time_integral_bound {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ x : Space,
      (∫ t in a..b, ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖) ≤
        C * (b - a) := by
  obtain ⟨C, hC, hb⟩ := compact_jet_bound h m
  refine ⟨C, hC, ?_⟩
  intro a b ha hab x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := C)
    (f := fun t => ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖) (by
      intro t ht
      rw [uIoc_of_le hab] at ht
      simpa only [Real.norm_eq_abs, abs_norm] using hb t (ha.trans ht.1.le) x)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  exact (le_abs_self _).trans hi

/-- Smoothness/support give small budgets against a FIXED tolerance. -/
theorem compact_short_budget {u f : VelocityField} {p : PressureField}
    (h : R3CompactCandidate.Properties u p f) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a < δ → ∀ x : Space,
      (∫ t in a..b, ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖) < ε := by
  obtain ⟨C, hC, hb⟩ := compact_time_integral_bound h m
  refine ⟨ε / C, div_pos hε hC, ?_⟩
  intro a b ha hab hlen x
  apply (hb a b ha hab x).trans_lt
  have hh := (lt_div_iff₀ hC).mp hlen
  simpa only [mul_comm] using hh

end UnforcedRestart.ActualForcingBudget

#print axioms UnforcedRestart.ActualForcingBudget.compact_jet_bound
#print axioms UnforcedRestart.ActualForcingBudget.compact_jet_intervalIntegrable
#print axioms UnforcedRestart.ActualForcingBudget.compact_time_integral_bound
#print axioms UnforcedRestart.ActualForcingBudget.compact_short_budget
