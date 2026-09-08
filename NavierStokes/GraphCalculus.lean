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

/-- Embed physical radial/time coordinates in the auxiliary lift. -/
def graph (d : ℝ) (vr vt : Plane) (q : Plane) : Lift :=
  (q, q.1 ^ d • vr + q.2 • vt)

def pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ) : Plane → ℝ :=
  fun q => F (graph d vr vt q)

def radialVector (d : ℝ) (vr : Plane) (p : Lift) : Lift :=
  ((1, 0), radialSpeed d p.1.1 • vr)

def timeVector (vt : Plane) : Lift := ((0, 1), vt)

/-- Differentiation along a vector field, defined by the genuine derivative. -/
def along (V : Lift → Lift) (F : Lift → ℝ) (p : Lift) : ℝ :=
  fderiv ℝ F p (V p)


def timeOp (vt : Plane) (F : Lift → ℝ) : Lift → ℝ :=
  along (fun _ => timeVector vt) F


def partialT (u : Plane → ℝ) (q : Plane) : ℝ :=
  deriv (fun t => u (q.1, t)) q.2



/-- The time direction has constant graph velocity. -/
theorem hasDerivAt_graph_time (d : ℝ) (vr vt : Plane) (r t : ℝ) :
    HasDerivAt (fun s => graph d vr vt (r, s)) (timeVector vt) t := by
  have hb := (hasDerivAt_const t (r ^ d • vr)).add ((hasDerivAt_id t).smul_const vt)
  have hq := (hasDerivAt_const t r).prodMk (hasDerivAt_id t)
  simpa [graph, timeVector] using hq.prodMk hb


/-- First time derivative of the physical pullback equals the exact graph operator. -/
theorem partialT_pullback (d : ℝ) (vr vt : Plane) (F : Lift → ℝ) (q : Plane)
    (hF : DifferentiableAt ℝ F (graph d vr vt q)) :
    partialT (pullback d vr vt F) q = timeOp vt F (graph d vr vt q) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt q.2
    (hasDerivAt_graph_time d vr vt q.1 q.2)).deriv


private def radiusProjection : Lift →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane Plane)















end NavierStokes.GraphCalculus
