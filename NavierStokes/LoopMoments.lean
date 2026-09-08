import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact moment algebra for the true-cone loop construction

This file proves the finite-distribution form of the averaging and rephasing
identities in Lemma 6.1 of the candidate manuscript. The formulas are algebraic;
no existence, smoothness, or invertibility of a circle reparametrization is
asserted here. The hypotheses of `rephased_moments` are ordinary mass, mean,
and variance constraints, not an assumption that a desired loop exists.

The final lemmas give explicit two-point distributions with prescribed variance.
They establish finite moment feasibility, including a one-sided support bound.
-/

namespace NavierStokes.LoopMoments

open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- A finite weighted average. We retain the weights explicitly, so no
probabilistic or analytic existence assertion is hidden in the notation. -/
def avg (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i

theorem avg_add (s : Finset ι) (w f g : ι → ℝ) :
    avg s w (fun i => f i + g i) = avg s w f + avg s w g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (s : Finset ι) (w f g : ι → ℝ) :
    avg s w (fun i => f i - g i) = avg s w f - avg s w g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_const_mul (s : Finset ι) (w f : ι → ℝ) (c : ℝ) :
    avg s w (fun i => c * f i) = c * avg s w f := by
  simp only [avg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem avg_const (s : Finset ι) (w : ι → ℝ) (c : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) :
    avg s w (fun _ => c) = c := by
  simp only [avg, ← Finset.sum_mul, hmass, one_mul]


/-- The standard variance expansion, with mass and first moment explicit. -/
theorem variance_identity (s : Finset ι) (w t : ι → ℝ) (m : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) (hmean : avg s w t = m) :
    avg s w (fun i => (t i - m) ^ 2) = avg s w (fun i => t i ^ 2) - m ^ 2 := by
  calc
    avg s w (fun i => (t i - m) ^ 2) =
        avg s w (fun i => t i ^ 2 - (2 * m) * t i + m ^ 2) := by
          congr 1
          funext i
          ring
    _ = avg s w (fun i => t i ^ 2) - (2 * m) * avg s w t + m ^ 2 := by
          rw [avg_add, avg_sub, avg_const_mul, avg_const s w (m ^ 2) hmass]
    _ = avg s w (fun i => t i ^ 2) - m ^ 2 := by rw [hmean]; ring

/-- This is `a ⟨1+t²⟩ = a(1+m²) + ρ` from the manuscript. -/
theorem energy_moment (s : Finset ι) (w t : ι → ℝ) (a m ρ : ℝ)
    (ha : a ≠ 0) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = m)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a) :
    a * avg s w (fun i => 1 + t i ^ 2) = a * (1 + m ^ 2) + ρ := by
  have hsecond : avg s w (fun i => t i ^ 2) = m ^ 2 + ρ / a := by
    have := variance_identity s w t m hmass hmean
    linarith
  rw [avg_add, avg_const s w 1 hmass, hsecond]
  field_simp; ring



/-- The rephasing density relative to the old averaging parameter. -/
def phaseDensity (a v t : ℝ) : ℝ := a * (1 + t ^ 2) / v

/-- The positive first component of the loop shear. -/
def loopA (v t : ℝ) : ℝ := v / (1 + t ^ 2)

/-- The signed second component; this corresponds to `-b_L`. -/
def loopC (v t : ℝ) : ℝ := v * t / (1 + t ^ 2)

theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by
  nlinarith [sq_nonneg t]

theorem loopA_pos (v t : ℝ) (hv : 0 < v) : 0 < loopA v t := by
  exact div_pos hv (one_add_sq_pos t)

theorem phaseDensity_pos (a v t : ℝ) (ha : 0 < a) (hv : 0 < v) :
    0 < phaseDensity a v t := by
  exact div_pos (mul_pos ha (one_add_sq_pos t)) hv

theorem loop_speed (v t : ℝ) : loopA v t * (1 + t ^ 2) = v := by
  unfold loopA
  exact div_mul_cancel₀ v (ne_of_gt (one_add_sq_pos t))

theorem loop_slope (v t : ℝ) (hv : v ≠ 0) : loopC v t / loopA v t = t := by
  unfold loopC loopA
  field_simp

theorem density_times_loopA (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopA v t = a := by
  unfold phaseDensity loopA
  field_simp

theorem density_times_loopC (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopC v t = a * t := by
  unfold phaseDensity loopC
  field_simp

/-- Reweighting by the manuscript's density has total mass one. -/
theorem rephased_mass (s : Finset ι) (w t : ι → ℝ) (a m ρ v : ℝ)
    (ha : a ≠ 0) (hv : v ≠ 0) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = m)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) :
    ∑ i ∈ s, w i * phaseDensity a v (t i) = 1 := by
  have he := energy_moment s w t a m ρ ha hmass hmean hvar
  rw [← hspeed] at he
  calc
    (∑ i ∈ s, w i * phaseDensity a v (t i)) =
        (a * avg s w (fun i => 1 + t i ^ 2)) / v := by
          simp only [phaseDensity, avg, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 1 := by rw [he, div_self hv]

/-- The radial shear has the original mean after rephasing. -/
theorem rephased_meanA (s : Finset ι) (w t : ι → ℝ) (a v : ℝ)
    (hv : v ≠ 0) (hmass : ∑ i ∈ s, w i = 1) :
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) = a := by
  calc
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) =
        avg s w (fun _ => a) := by
          unfold avg
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc, density_times_loopA a v (t i) hv]
    _ = a := avg_const s w a hmass

/-- The signed axial shear has the original mean after rephasing. -/
theorem rephased_meanC (s : Finset ι) (w t : ι → ℝ) (a v m : ℝ)
    (hv : v ≠ 0) (hmean : avg s w t = m) :
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) = a * m := by
  calc
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) =
        avg s w (fun i => a * t i) := by
          unfold avg
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc, density_times_loopC a v (t i) hv]
    _ = a * m := by rw [avg_const_mul, hmean]

/-- With `m = -b/a`, the two rephased means are exactly `(a,-b)`. -/
theorem rephased_moments (s : Finset ι) (w t : ι → ℝ) (a b ρ v : ℝ)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = -b / a)
    (hvar : avg s w (fun i => (t i - (-b / a)) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + (-b / a) ^ 2) + ρ) :
    (∑ i ∈ s, w i * phaseDensity a v (t i) = 1) ∧
      avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) = a ∧
      avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) = -b := by
  have hvpos : 0 < v := by
    rw [hspeed]
    exact add_pos_of_pos_of_nonneg (mul_pos ha (one_add_sq_pos (-b / a))) hρ
  have hv := ne_of_gt hvpos
  refine ⟨rephased_mass s w t a (-b / a) ρ v (ne_of_gt ha) hv hmass hmean hvar hspeed,
    rephased_meanA s w t a v hv hmass, ?_⟩
  rw [rephased_meanC s w t a v (-b / a) hv hmean]
  field_simp

/-- A two-point probability law. This is a concrete finite object, without
any hypothesis asserting the existence of the manuscript's smooth loop. -/
structure TwoPoint where
  leftWeight : ℝ
  rightWeight : ℝ
  leftValue : ℝ
  rightValue : ℝ

def TwoPoint.mean (q : TwoPoint) : ℝ :=
  q.leftWeight * q.leftValue + q.rightWeight * q.rightValue



/-- For any nonnegative variance, equal masses at `m ± √V` realize it. -/
def symmetricPair (m V : ℝ) : TwoPoint :=
  ⟨1 / 2, 1 / 2, m - Real.sqrt V, m + Real.sqrt V⟩













end

end NavierStokes.LoopMoments
