import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar closure of the whole-space comparison estimate

The localized energy may have derivatives only in the interior of the time
interval. The integrating-factor argument below therefore uses continuity on
the closed interval and the mean-value theorem on its interior. In particular,
no energy inequality at a time endpoint is assumed.
-/


noncomputable section

open Set

namespace NavierStokesR3.ComparisonGronwall

/-- The weighted perturbed Gronwall estimate with a nonpositive initial value.
Only interior derivatives of `E` are needed. -/
theorem exp_neg_mul_le_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, Real.exp (-K * t) * E t ≤ ε * t := by
  let G : ℝ → ℝ := fun t => Real.exp (-K * t) * E t - ε * t
  let G' : ℝ → ℝ := fun t => Real.exp (-K * t) * (E' t - K * E t) - ε
  have hgcont : ContinuousOn G (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hcont).sub (continuous_const.mul continuous_id).continuousOn
  have hgderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt G (G' t) t := by
    have hexp := ((hasDerivAt_id t).const_mul (-K)).exp
    convert! (hexp.mul (hderiv t ht)).sub ((hasDerivAt_id t).const_mul ε) using 1
    try dsimp [G, G']
    ring
  have hG : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      have hexp : Real.exp (-K * t) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) ht'.1.le)
      have hfirst : Real.exp (-K * t) * (E' t - K * E t) ≤
          Real.exp (-K * t) * ε :=
        mul_le_mul_of_nonneg_left (by linarith [hbound t ht']) (Real.exp_pos _).le
      have hsecond : Real.exp (-K * t) * ε ≤ ε := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hε
      dsimp only [G']
      linarith
  intro t ht
  have hle := hG ⟨le_rfl, hT⟩ ht ht.1
  have hzero : G 0 ≤ 0 := by simpa [G] using hinitial
  have hnonpos := hle.trans hzero
  exact sub_nonpos.mp hnonpos

/-- Perturbed Gronwall, retaining the actual time in the bound. -/
theorem le_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * t * Real.exp (K * t) := by
  intro t ht
  have hweighted := exp_neg_mul_le_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht
  have hmul := mul_le_mul_of_nonneg_right hweighted (Real.exp_pos (K * t)).le
  have hexp : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]
    have hcancel : -K * t + K * t = 0 := by ring
    rw [hcancel, Real.exp_zero]
  calc
    E t = Real.exp (-K * t) * E t * Real.exp (K * t) := by
      calc
        E t = E t * 1 := (mul_one _).symm
        _ = E t * (Real.exp (-K * t) * Real.exp (K * t)) := by rw [hexp]
        _ = _ := by ring
    _ ≤ ε * t * Real.exp (K * t) := hmul

/-- Perturbed Gronwall with one bound valid throughout the closed interval. -/
theorem le_uniform_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * T * Real.exp (K * T) := by
  intro t ht
  calc
    E t ≤ ε * t * Real.exp (K * t) :=
      le_exp_mul_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht
    _ ≤ ε * T * Real.exp (K * T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left ht.2 hε
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
      · exact (Real.exp_pos _).le
      · exact mul_nonneg hε hT

/-- A forcing error of order `1 / R` gives a uniform energy error of the same
order. The numerator depends only on `C`, `K`, and the time interval. -/
theorem le_div_radius_of_deriv_le {T K C R : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 < R)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + C / R) :
    ∀ t ∈ Icc 0 T, E t ≤ (C * T * Real.exp (K * T)) / R := by
  intro t ht
  have hle := le_uniform_exp_mul_of_deriv_le hT hK (div_nonneg hC hR.le)
    hcont hinitial.le hderiv hbound t ht
  convert! hle using 1
  ring




end NavierStokesR3.ComparisonGronwall
