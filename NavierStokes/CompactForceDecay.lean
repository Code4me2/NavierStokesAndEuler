import NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Decay of all derivatives of a smooth periodic force with bounded time support

Each actual iterated derivative is continuous and spatially periodic, hence
bounded on a compact time interval after reduction to a fundamental cube.
Beyond the time support it is zero by locality of differentiation.
-/

namespace NavierStokes.CompactForceDecay

noncomputable section

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology



/-- Integer coordinate translation. -/
def integerShift (n : Fin 3 → ℤ) : Space :=
  ∑ i : Fin 3, n i • coordinateVector i

@[simp] theorem integerShift_apply (n : Fin 3 → ℤ) (j : Fin 3) :
    integerShift n j = (n j : ℝ) := by
  change (EuclideanSpace.proj j) (integerShift n) = _
  simp [integerShift, coordinateVector, zsmul_eq_mul]

/-- The coordinatewise fractional part of a spatial point. -/
def fractionalPoint (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => Int.fract (x i))


theorem fractionalPoint_eq_sub (x : Space) :
    fractionalPoint x = x - integerShift (fun i => Int.floor (x i)) := by
  ext i
  simp only [fractionalPoint, WithLp.equiv_symm_apply, PiLp.toLp_apply, PiLp.sub_apply,
    integerShift_apply]
  exact (Int.self_sub_floor _).symm

variable {V : Type*}

theorem periodic_integerShift {g : SpaceTime → V}
    (hg : UnitSpatialPeriodsOn univ g) (t : ℝ) (n : Fin 3 → ℤ) :
    Function.Periodic (fun x : Space => g (t, x)) (integerShift n) := by
  have hbase (i : Fin 3) : Function.Periodic (fun x : Space => g (t, x))
      (coordinateVector i) := fun x => hg t (mem_univ _) x i
  have hs (s : Finset (Fin 3)) : Function.Periodic (fun x : Space => g (t, x))
      (∑ i ∈ s, n i • coordinateVector i) := by
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hbase i).zsmul (n i)).add_period ih
  exact hs Finset.univ


section Normed

variable [NormedAddCommGroup V]


variable [NormedSpace ℝ V]

/-- Unit spatial periods pass to the full derivative tensor, including all
time and mixed derivatives. No derivative bound is assumed here. -/
theorem iteratedFDeriv_periods {f : SpaceTime → V}
    (hf : UnitSpatialPeriodsOn univ f) (m : ℕ) :
    UnitSpatialPeriodsOn univ (iteratedFDeriv ℝ m f) := by
  intro t _ x i
  have heq : (fun z : SpaceTime => f (z + (0, coordinateVector i))) = f := by
    funext z
    change f (z.1 + 0, z.2 + coordinateVector i) = f z
    simpa only [add_zero] using hf z.1 (mem_univ _) z.2 i
  have hd := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f)
    m (0, coordinateVector i) (t, x)
  rw [heq] at hd
  simpa using hd.symm

/-- Differentiation is local: every full derivative vanishes at times strictly
after a uniform zero-tail threshold, including derivative order zero. -/
theorem iteratedFDeriv_eq_zero_after {f : SpaceTime → V} {T : ℝ}
    (hzero : ∀ t : ℝ, T ≤ t → ∀ x : Space, f (t, x) = 0)
    (m : ℕ) {t : ℝ} (ht : T < t) (x : Space) :
    iteratedFDeriv ℝ m f (t, x) = 0 := by
  have heq : f =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
    have hU : {z : SpaceTime | T < z.1} ∈ 𝓝 (t, x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [hU] with z hz
    exact hzero z.1 hz.le z.2
  have heq' : f =ᶠ[𝓝[univ] (t, x)] (fun _ => 0) := by
    simpa only [nhdsWithin_univ] using heq
  have hj := heq'.iteratedFDerivWithin_eq heq.self_of_nhds m (𝕜 := ℝ)
  simpa [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero] using hj

end Normed


/-- The four coordinate directions in the product spacetime norm. -/
def spacetimeCoordinate : Fin 4 → SpaceTime :=
  Fin.cases (1, 0) (fun i : Fin 3 => (0, coordinateVector i))

@[simp] theorem norm_spacetimeCoordinate (i : Fin 4) : ‖spacetimeCoordinate i‖ = 1 := by
  refine Fin.cases ?_ ?_ i
  · simp [spacetimeCoordinate, Prod.norm_def]
  · intro j
    simp [spacetimeCoordinate, Prod.norm_def, coordinateVector]

/-- Evaluating a full derivative on coordinate unit vectors, then taking one
output component, is controlled by its full multilinear operator norm. -/
theorem mixed_component_le_full (f : VelocityField) (m : ℕ) (z : SpaceTime)
    (directions : Fin m → Fin 4) (j : Fin 3) :
    |(iteratedFDeriv ℝ m f z (fun i => spacetimeCoordinate (directions i))) j| ≤
      ‖iteratedFDeriv ℝ m f z‖ := by
  have hproj := PiLp.norm_apply_le
    (iteratedFDeriv ℝ m f z (fun i => spacetimeCoordinate (directions i))) j
  have hop := (iteratedFDeriv ℝ m f z).le_opNorm
    (fun i => spacetimeCoordinate (directions i))
  have heval : ‖iteratedFDeriv ℝ m f z (fun i => spacetimeCoordinate (directions i))‖ ≤
      ‖iteratedFDeriv ℝ m f z‖ := by simpa using hop
  simpa only [Real.norm_eq_abs] using hproj.trans heval


end

end NavierStokes.CompactForceDecay
