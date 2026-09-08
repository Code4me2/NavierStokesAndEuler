import NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Abel

/-!
# Calculus of the physical Navier--Stokes residual

These identities concern the ordinary Frechet derivatives used by the actual
PDE target in `ProblemStatement`. The velocity hypotheses give two continuous
spatial derivatives on the time slice and a differentiable time slice at the
point in question. No abstract differential operators are assumed linear.
-/

noncomputable section

namespace NavierStokes.ResidualCalculus

open ProblemStatement Set
open scoped BigOperators ContDiff

/-- Time differentiation is additive for differentiable velocity time slices. -/
theorem temporalDerivative_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (he : DifferentiableAt ℝ (fun s : ℝ => e (s, x)) t) :
    temporalDerivative (fun z => u z + e z) t x =
      temporalDerivative u t x + temporalDerivative e t x := by
  unfold temporalDerivative
  rw [fderiv_fun_add hu he]
  rfl

/-- The spatial derivative is additive under actual spatial differentiability. -/
theorem spatialDerivative_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (he : DifferentiableAt ℝ (fun y : Space => e (t, y)) x) :
    spatialDerivative (fun z => u z + e z) t x =
      spatialDerivative u t x + spatialDerivative e t x := by
  exact fderiv_fun_add hu he

/-- Pressure-gradient additivity follows from derivative additivity and the
fixed Euclidean coordinate basis in the PDE target. -/
theorem pressureGradient_add
    (p q : PressureField) (t : ℝ) (x : Space)
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x)
    (hq : DifferentiableAt ℝ (fun y : Space => q (t, y)) x) :
    pressureGradient (fun z => p z + q z) t x =
      pressureGradient p t x + pressureGradient q t x := by
  unfold pressureGradient
  rw [fderiv_fun_add hp hq]
  simp only [add_apply, add_smul, Finset.sum_add_distrib]

/-- Divergence remains additive for these same genuine spatial derivatives. -/
theorem spatialDivergence_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (he : DifferentiableAt ℝ (fun y : Space => e (t, y)) x) :
    spatialDivergence (fun z => u z + e z) t x =
      spatialDivergence u t x + spatialDivergence e t x := by
  unfold spatialDivergence
  rw [spatialDerivative_add u e t x hu he]
  simp only [add_apply, PiLp.add_apply, Finset.sum_add_distrib]



/-- The quadratic advection term produces exactly its two cross terms and the
self-advection of the perturbation. -/
theorem advection_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (he : DifferentiableAt ℝ (fun y : Space => e (t, y)) x) :
    advection (fun z => u z + e z) t x =
      advection u t x + spatialDerivative u t x (e (t, x)) +
        spatialDerivative e t x (u (t, x)) + advection e t x := by
  unfold advection
  rw [spatialDerivative_add u e t x hu he]
  simp only [add_apply, map_add]
  abel





/-- A constant spatial scalar factors out of the actual spatial derivative. -/
theorem spatialDerivative_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    spatialDerivative (fun z => c • u z) t x = c • spatialDerivative u t x := by
  exact fderiv_fun_const_smul hu c


/-- Constant-scalar linearity of divergence, using coordinate evaluation. -/
theorem spatialDivergence_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    spatialDivergence (fun z => c • u z) t x = c * spatialDivergence u t x := by
  unfold spatialDivergence
  rw [spatialDerivative_const_smul u t x c hu]
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]






end NavierStokes.ResidualCalculus
