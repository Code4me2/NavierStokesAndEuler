import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gronwall's inequality with interior derivatives

Both Navier--Stokes uniqueness proofs (`PeriodicUniqueness` on the torus,
`R3/WholeSpaceEnergyLimit` on `ℝ³`) control a difference energy that is
continuous on a closed time interval but differentiable only in its interior.
Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` asks for right
derivatives on `Ico a b`, including at `a`, so it does not apply directly. The
integrating-factor argument below is the one lemma both proofs use; the
perturbed form `E' ≤ K E + ε` is the general one, the unperturbed
`eq_zero_of_deriv_le` (zero initial energy, zero perturbation) is its instance.
-/

noncomputable section

open Set

namespace NavierStokes.GronwallInterior

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

/-- The unperturbed case on an arbitrary interval `[a, b]`: a nonnegative
energy vanishing at `a` with `E' ≤ K E` in the interior vanishes throughout.
This is the form the torus uniqueness proof uses; it is the shifted `ε = 0`
instance of `exp_neg_mul_le_of_deriv_le`. -/
theorem eq_zero_of_deriv_le {a b K : ℝ} {E E' : ℝ → ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn E (Icc a b)) (hinitial : E a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo a b, E' t ≤ K * E t) :
    ∀ t ∈ Icc a b, E t = 0 := by
  intro t ht
  have hshift := exp_neg_mul_le_of_deriv_le (T := b - a) (K := max K 0) (ε := 0)
    (E := fun s => E (a + s)) (E' := fun s => E' (a + s)) (by linarith)
    (le_max_right _ _) le_rfl
    (hcont.comp (continuous_const.add continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩))
    (by simp [hinitial])
    (fun s hs => (hderiv (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩).comp_const_add a s)
    (fun s hs => by
      have hs' : a + s ∈ Ioo a b := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hE := hnonneg (a + s) ⟨hs'.1.le, hs'.2.le⟩
      linarith [hbound (a + s) hs', mul_le_mul_of_nonneg_right (le_max_left K 0) hE])
    (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hta : a + (t - a) = t := by ring
  rw [hta, zero_mul] at hshift
  have hE : E t ≤ 0 := by nlinarith [Real.exp_pos (-max K 0 * (t - a))]
  exact le_antisymm hE (hnonneg t ht)

end NavierStokes.GronwallInterior
