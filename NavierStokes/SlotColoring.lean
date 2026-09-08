import NavierStokes.SlotGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Real.Sqrt

/-!
# Physical grid labels, bounded degree, and an explicit finite coloring

Labels consist of a dyadic level, three integer grid coordinates, and a sign.
The physical mesh at exponent `a` is `2^(-n*a)/n^6`, namely the mesh
`S_n^-3` with `S_n=n²`, rescaled by `Q_n^a` with `Q_n=2^-n`.
Closed boxes of two mesh widths include the fixed small enlargement of the
one-mesh supports in the manuscript.
-/

noncomputable section

namespace NavierStokes.SlotColoring

open Set
open scoped BigOperators

abbrev Grid := Fin 3 → ℤ
abbrev Position := Fin 3 → ℝ
abbrev Label := ℕ × (Grid × Bool)

def dyadicQ (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ))

def spacing (a : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) * a) / (n : ℝ) ^ 6

theorem spacing_eq_scaled_mesh (a : ℝ) (n : ℕ) :
    spacing a n = dyadicQ n ^ a * (1 / (((n : ℝ) ^ 2) ^ 3)) := by
  unfold spacing dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [← pow_mul]
  norm_num
  ring

theorem spacing_pos (a : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < spacing a n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos hn' _)



def axisExponent (D : ℝ) : Fin 3 → ℝ := ![1 / 2, D, 1]
def width (D : ℝ) (j : Fin 3) (n : ℕ) : ℝ := spacing (axisExponent D j) n
def ratioBound (D : ℝ) : ℝ := (5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * (1 + |D|))

theorem width_pos (D : ℝ) (j : Fin 3) {n : ℕ} (hn : 1 ≤ n) : 0 < width D j n :=
  spacing_pos _ hn


def physicalBox (D : ℝ) (L : Label) : Set Position :=
  {x | ∀ j, |x j - width D j L.1 * (L.2.1 j : ℝ)| ≤ 2 * width D j L.1}

/-- The exact enlarged-box interaction relation used for coloring. -/
structure Adj (D : ℝ) (L M : Label) : Prop where
  left_positive : 1 ≤ L.1
  right_positive : 1 ≤ M.1
  distinct : L ≠ M
  left_level_le : L.1 ≤ M.1 + 4
  right_level_le : M.1 ≤ L.1 + 4
  overlap : (physicalBox D L ∩ physicalBox D M).Nonempty

theorem overlapping_centers (D : ℝ) (L M : Label)
    (hov : (physicalBox D L ∩ physicalBox D M).Nonempty) (j : Fin 3) :
    |width D j L.1 * (L.2.1 j : ℝ) - width D j M.1 * (M.2.1 j : ℝ)| ≤
      2 * (width D j L.1 + width D j M.1) := by
  obtain ⟨x, hx, hy⟩ := hov
  have htriangle := abs_sub_le (width D j L.1 * (L.2.1 j : ℝ)) (x j)
    (width D j M.1 * (M.2.1 j : ℝ))
  rw [abs_sub_comm (width D j L.1 * (L.2.1 j : ℝ)) (x j)] at htriangle
  linarith [hx j, hy j]

theorem same_level_grid_gap (D : ℝ) (L M : Label) (hn : 1 ≤ L.1)
    (hl : L.1 = M.1) (hov : (physicalBox D L ∩ physicalBox D M).Nonempty) (j : Fin 3) :
    |L.2.1 j - M.2.1 j| ≤ (4 : ℤ) := by
  have h := overlapping_centers D L M hov j
  rw [← hl, ← mul_sub, abs_mul, abs_of_pos (width_pos D j hn)] at h
  have hr : |(L.2.1 j : ℝ) - (M.2.1 j : ℝ)| ≤ 4 := by
    nlinarith [width_pos D j hn]
  exact_mod_cast hr

def intColor (z : ℤ) : Fin 5 :=
  ⟨(z % 5).toNat, by
    have h0 := Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 5)
    omega⟩

theorem intColor_eq_of_close {z w : ℤ} (hc : intColor z = intColor w)
    (hd : |z - w| ≤ 4) : z = w := by
  have hv := congrArg Fin.val hc
  dsimp [intColor] at hv
  have hz0 := Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0)
  have hw0 := Int.emod_nonneg w (by norm_num : (5 : ℤ) ≠ 0)
  have hdiff := abs_le.mp hd
  omega

abbrev Palette := Fin 9 × ((Fin 3 → Fin 5) × Bool)

def colorData (L : Label) : Palette :=
  (⟨L.1 % 9, Nat.mod_lt _ (by norm_num)⟩, (fun j => intColor (L.2.1 j), L.2.2))

theorem palette_card : Fintype.card Palette = 2250 := by
  norm_num [Palette, Fintype.card_prod, Fintype.card_fun]

/-- This is a constructed coloring, not a coloring hypothesis. -/
theorem colorData_proper (D : ℝ) {L M : Label} (h : Adj D L M) : colorData L ≠ colorData M := by
  intro hc
  have hlevel := congrArg (fun c : Palette => c.1.val) hc
  change L.1 % 9 = M.1 % 9 at hlevel
  have hl : L.1 = M.1 := by
    have h1 := h.left_level_le
    have h2 := h.right_level_le
    omega
  have hg : L.2.1 = M.2.1 := by
    funext j
    apply intColor_eq_of_close
    · exact congrArg (fun c : Palette => c.2.1 j) hc
    · exact same_level_grid_gap D L M h.left_positive hl h.overlap j
  have hs : L.2.2 = M.2.2 := congrArg (fun c : Palette => c.2.2) hc
  exact h.distinct (Prod.ext hl (Prod.ext hg hs))

def color (L : Label) : Fin (Fintype.card Palette) := (Fintype.equivFin Palette) (colorData L)

theorem color_proper (D : ℝ) {L M : Label} (h : Adj D L M) : color L ≠ color M := by
  intro hc
  exact colorData_proper D h ((Fintype.equivFin Palette).injective hc)



















/-- The expanding eigenvalue of the actual covering matrix. -/
def coverGrowth : ℝ := 4 + Real.sqrt 2

theorem log_coverGrowth_pos : 0 < Real.log coverGrowth := by
  apply Real.log_pos
  unfold coverGrowth
  linarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The real expression whose floor defines the manuscript's native index. -/
def nativeArgument (h : ℝ) (n : ℕ) : ℝ :=
  Real.log (dyadicQ n ^ (-1 - h) / (n : ℝ) ^ 2) / Real.log coverGrowth

def nativeIndex (h : ℝ) (n : ℕ) : ℕ := ⌊nativeArgument h n⌋₊

theorem nativeArgument_expanded (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    nativeArgument h n =
      ((n : ℝ) * (1 + h) * Real.log 2 - 2 * Real.log (n : ℝ)) / Real.log coverGrowth := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq : 0 < dyadicQ n := Real.rpow_pos_of_pos (by norm_num) _
  unfold nativeArgument
  rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hq _)) (pow_ne_zero 2 hn'),
    Real.log_rpow hq, Real.log_pow]
  unfold dyadicQ
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring

def nativeGapBudget (h : ℝ) : ℝ :=
  (4 * (1 + h) * Real.log 2 + 2 * Real.log 5) / Real.log coverGrowth

def nativeGap (h : ℝ) : ℕ := ⌈nativeGapBudget h⌉₊ + 1

theorem log_level_gap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    |Real.log (n : ℝ) - Real.log (m : ℝ)| ≤ Real.log 5 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn5 : (n : ℝ) ≤ 5 * (m : ℝ) := by exact_mod_cast (by omega : n ≤ 5 * m)
  have hm5 : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (by omega : m ≤ 5 * n)
  have h1 := Real.log_le_log hn' hn5
  have h2 := Real.log_le_log hm' hm5
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hm')] at h1
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hn')] at h2
  rw [abs_le]
  constructor <;> linarith

theorem nativeArgument_gap (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    |nativeArgument h n - nativeArgument h m| ≤ nativeGapBudget h := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have h1h : 0 ≤ 1 + h := by linarith
  have hdiff : |(n : ℝ) - (m : ℝ)| ≤ 4 := by
    have hn' : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have hm' : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  have hlogs := log_level_gap hn hm hnm hmn
  have hnum :
      |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
        2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| ≤
      4 * (1 + h) * Real.log 2 + 2 * Real.log 5 := by
    calc
      _ ≤ |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2| +
          |2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| := abs_sub _ _
      _ = |(n : ℝ) - (m : ℝ)| * (1 + h) * Real.log 2 +
          2 * |Real.log (n : ℝ) - Real.log (m : ℝ)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlog2, abs_of_nonneg h1h,
              abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiff h1h) hlog2)
        (mul_le_mul_of_nonneg_left hlogs (by norm_num))
  calc
    |nativeArgument h n - nativeArgument h m| =
        |(((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
          2 * (Real.log (n : ℝ) - Real.log (m : ℝ))) / Real.log coverGrowth| := by
            rw [nativeArgument_expanded h hn, nativeArgument_expanded h hm]
            congr 1
            ring
    _ = |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
        2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| / Real.log coverGrowth := by
          rw [abs_div, abs_of_pos log_coverGrowth_pos]
    _ ≤ nativeGapBudget h := div_le_div_of_nonneg_right hnum log_coverGrowth_pos.le

theorem natFloor_gap_le (u v C : ℝ) (h : u - v ≤ C) :
    ⌊u⌋₊ ≤ ⌊v⌋₊ + (⌈C⌉₊ + 1) := by
  apply Nat.floor_le_of_le
  push_cast
  linarith [Nat.lt_floor_add_one v, Nat.le_ceil C]

/-- The actual adjacent native indices have an explicit uniform gap. -/
theorem nativeIndex_gap (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    nativeIndex h n ≤ nativeIndex h m + nativeGap h ∧
      nativeIndex h m ≤ nativeIndex h n + nativeGap h := by
  have hg := abs_le.mp (nativeArgument_gap h hh hn hm hnm hmn)
  constructor
  · exact natFloor_gap_le _ _ _ hg.2
  · exact natFloor_gap_le _ _ _ (by linarith [hg.1])

theorem nat_square_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hmul := Nat.mul_le_mul_right n hn
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- `n=4` is already a valid uniform threshold for nonnegative native indices
when `h≥0`; the manuscript subsequently retains still larger bands. -/
theorem nativeArgument_nonneg (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ nativeArgument h n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsquare : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast nat_square_le_two_pow hn
  have hq : (n : ℝ) ^ 2 ≤ dyadicQ n ^ (-1 - h) := by
    unfold dyadicQ
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := hsquare
      _ = (2 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) * (-1 - h)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hratio : 1 ≤ dyadicQ n ^ (-1 - h) / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ (pow_pos hn' 2)).mpr
    simpa using hq
  exact div_nonneg (Real.log_nonneg hratio) log_coverGrowth_pos.le



end NavierStokes.SlotColoring
