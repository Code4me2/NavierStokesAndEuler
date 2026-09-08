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

def radialOp (d : ℝ) (vr : Plane) (F : Lift → ℝ) : Lift → ℝ :=
  along (radialVector d vr) F

def timeOp (vt : Plane) (F : Lift → ℝ) : Lift → ℝ :=
  along (fun _ => timeVector vt) F

def partialR (u : Plane → ℝ) (q : Plane) : ℝ :=
  deriv (fun r => u (r, q.2)) q.1

def partialT (u : Plane → ℝ) (q : Plane) : ℝ :=
  deriv (fun t => u (q.1, t)) q.2


/-- Exact derivative of the graph along a radial coordinate line. -/
theorem hasDerivAt_graph_radial (d : ℝ) (vr vt : Plane) (r t : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => graph d vr vt (s, t))
      (radialVector d vr (graph d vr vt (r, t))) r := by
  have hp := (Real.hasDerivAt_rpow_const (p := d) (Or.inl hr)).smul_const vr
  have hb := hp.add (hasDerivAt_const r (t • vt))
  have hq := (hasDerivAt_id r).prodMk (hasDerivAt_const r t)
  simpa [graph, radialVector, radialSpeed] using hq.prodMk hb

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

/-- This form keeps the exponent arithmetic of the derivative explicit. -/
def radialAcceleration (d r : ℝ) : ℝ :=
  d * ((d - 1) * r ^ (d - 1 - 1))

private theorem hasFDerivAt_radialVector (d : ℝ) (vr : Plane) (p : Lift)
    (hr : p.1.1 ≠ 0) :
    HasFDerivAt (radialVector d vr)
      ((0 : Lift →L[ℝ] Plane).prod
        (((radialAcceleration d p.1.1) • radiusProjection).smulRight vr)) p := by
  have hrad : HasFDerivAt (fun z : Lift => z.1.1) radiusProjection p :=
    radiusProjection.hasFDerivAt
  have hpow := hrad.rpow_const (p := d - 1) (Or.inl hr)
  have hs : HasFDerivAt (fun z : Lift => radialSpeed d z.1.1)
      (radialAcceleration d p.1.1 • radiusProjection) p := by
    simpa only [radialSpeed, radialAcceleration, Pi.smul_apply, smul_eq_mul, smul_smul] using
      hpow.fun_const_smul d
  exact (hasFDerivAt_const (1, 0) p).prodMk (hs.smul_const vr)

theorem differentiableAt_radialVector (d : ℝ) (vr : Plane) (p : Lift)
    (hr : p.1.1 ≠ 0) : DifferentiableAt ℝ (radialVector d vr) p :=
  (hasFDerivAt_radialVector d vr p hr).differentiableAt












end NavierStokes.GraphCalculus
