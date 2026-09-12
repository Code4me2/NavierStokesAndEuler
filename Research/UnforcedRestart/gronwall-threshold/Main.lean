import NavierStokes.GronwallInterior

/-!
Scalar infrastructure only. `A` is a primitive of the growth coefficient;
`B` is a primitive of the exponentially weighted source. No PDE, spatial
integrability, existence, or growth-transfer assertion is made here.
-/

open Set

namespace UnforcedRestart.GronwallThreshold

/-- Variable-coefficient integrating-factor bound, with arbitrary initial error.
Only continuity on the closed interval and derivatives in its interior are needed.
The primitives need not be normalized at the left endpoint. -/
theorem weighted_budget {a b : ℝ} {E E' A k B g : ℝ → ℝ}
    (hab : a ≤ b)
    (hE : ContinuousOn E (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hB : ContinuousOn B (Icc a b))
    (hdE : ∀ t ∈ Ioo a b, HasDerivAt E (E' t) t)
    (hdA : ∀ t ∈ Ioo a b, HasDerivAt A (k t) t)
    (hdB : ∀ t ∈ Ioo a b, HasDerivAt B (Real.exp (-A t) * g t) t)
    (hineq : ∀ t ∈ Ioo a b, E' t ≤ k t * E t + g t) :
    ∀ t ∈ Icc a b,
      Real.exp (-A t) * E t ≤ Real.exp (-A a) * E a + B t - B a := by
  let G : ℝ → ℝ := fun t => Real.exp (-A t) * E t - B t
  let G' : ℝ → ℝ := fun t => Real.exp (-A t) * (E' t - k t * E t - g t)
  have hc : ContinuousOn G (Icc a b) :=
    ((Real.continuous_exp.comp_continuousOn hA.neg).mul hE).sub hB
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt G (G' t) t := by
    convert! (((hdA t ht).neg.exp).mul (hdE t ht)).sub (hdB t ht) using 1
    dsimp [G, G']
    ring
  have hmono : AntitoneOn G (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hc
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by linarith [hineq t ht'])
  intro t ht
  have hm := hmono ⟨le_rfl, hab⟩ ht ht.1
  dsimp only [G] at hm
  linarith

/-- Pointwise error threshold from a weighted source budget. This retains the
initial error and requires no sign restrictions on the scalar functions. -/
theorem threshold {a b t q : ℝ} {E E' A k B g : ℝ → ℝ}
    (hab : a ≤ b)
    (hE : ContinuousOn E (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hB : ContinuousOn B (Icc a b))
    (hdE : ∀ s ∈ Ioo a b, HasDerivAt E (E' s) s)
    (hdA : ∀ s ∈ Ioo a b, HasDerivAt A (k s) s)
    (hdB : ∀ s ∈ Ioo a b, HasDerivAt B (Real.exp (-A s) * g s) s)
    (hineq : ∀ s ∈ Ioo a b, E' s ≤ k s * E s + g s)
    (ht : t ∈ Icc a b)
    (hbudget : Real.exp (-A a) * E a + B t - B a ≤ Real.exp (-A t) * q) :
    E t ≤ q := by
  have hw := weighted_budget hab hE hA hB hdE hdA hdB hineq t ht
  have hh := hw.trans hbudget
  nlinarith [Real.exp_pos (-A t)]

/-- Equal restart data, normalized budget primitive, and an energy tolerance
`δ²`. No inference from this scalar energy tolerance to pointwise velocity. -/
theorem zero_initial_threshold {a b t δ : ℝ} {E E' A k B g : ℝ → ℝ}
    (hab : a ≤ b)
    (hE : ContinuousOn E (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hB : ContinuousOn B (Icc a b))
    (hdE : ∀ s ∈ Ioo a b, HasDerivAt E (E' s) s)
    (hdA : ∀ s ∈ Ioo a b, HasDerivAt A (k s) s)
    (hdB : ∀ s ∈ Ioo a b, HasDerivAt B (Real.exp (-A s) * g s) s)
    (hineq : ∀ s ∈ Ioo a b, E' s ≤ k s * E s + g s)
    (hzero : E a = 0) (hBzero : B a = 0)
    (ht : t ∈ Icc a b)
    (hbudget : B t ≤ Real.exp (-A t) * δ ^ 2) :
    E t ≤ δ ^ 2 := by
  apply threshold hab hE hA hB hdE hdA hdB hineq ht
  simpa only [hzero, hBzero, mul_zero, zero_add, sub_zero] using hbudget

end UnforcedRestart.GronwallThreshold

#print axioms UnforcedRestart.GronwallThreshold.weighted_budget
#print axioms UnforcedRestart.GronwallThreshold.threshold
#print axioms UnforcedRestart.GronwallThreshold.zero_initial_threshold
