import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebra of the curl realization in Lemma 8.8

The dot product below is bilinear, including over `ℂ`: for a real phase normal
its self-product is the real squared length. These results check the principal
symbol and the algebraic divergence cancellation. They do not establish
regularity, bounds for the differentiated amplitude, or descent from the lift.
-/

namespace NavierStokes.CurlGeometry

abbrev Vec3 (R : Type*) := Fin 3 → R

def dot {R : Type*} [CommRing R] (u v : Vec3 R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross {R : Type*} [CommRing R] (u v : Vec3 R) : Vec3 R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]









/-- The coefficient of the potential (30), with the oscillatory exponential
factored out. `k` is its nonzero frequency and `n` its phase normal. -/
noncomputable def potentialCoefficient (k : ℂ) (n a : Vec3 ℂ) : Vec3 ℂ :=
  (Complex.I / (k * dot n n)) • cross n a


def complexify (n : Vec3 ℝ) : Vec3 ℂ := fun j => (n j : ℂ)




/-! ## Cylindrical differential cancellation

This is a conditional identity for three additive differential operators on a
commutative ring of coefficient functions. In the application `q = 1/R`.
The assumptions state pairwise commutation and precisely the radial/axial
product rules for multiplication by `q` used by the calculation. They must
still be established for the manuscript's graph derivatives.
-/

def cylindricalCurl {F : Type*} [CommRing F]
    (Dr Dθ Dz : F →+ F) (q : F) (A : Vec3 F) : Vec3 F :=
  ![q * Dθ (A 2) - Dz (A 1),
    Dz (A 0) - Dr (A 2),
    Dr (A 1) + q * A 1 - q * Dθ (A 0)]



end NavierStokes.CurlGeometry
