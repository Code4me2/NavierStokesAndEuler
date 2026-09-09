import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact differential calculus on the auxiliary graph

The physical variables are `(r,t)` and the auxiliary variable is in `ℝ²`.
The graph is `Y(r,t) = r^d • vr + t • vt`, as in Definition 8.1 of the
candidate manuscript. The radial formulas below are stated away from `r = 0`.
All differential operators use Mathlib's actual Fréchet derivatives.
-/

noncomputable section

namespace NavierStokes.GraphCalculus

abbrev Plane := ℝ × ℝ
abbrev Lift := Plane × Plane

/-- The radial coefficient in the exact graph derivative. -/
def radialSpeed (d r : ℝ) : ℝ := d * r ^ (d - 1)
















private def radiusProjection : Lift →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane)















end NavierStokes.GraphCalculus
