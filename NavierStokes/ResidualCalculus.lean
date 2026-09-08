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

/-- The spatial C² hypothesis gives differentiability of each first directional
derivative. This is the second-derivative fact needed for the Laplacian. -/
theorem differentiable_spatial_direction
    (u : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y))) (v : Space) :
    Differentiable ℝ (fun y : Space => spatialDerivative u t y v) := by
  have hfirst : ContDiff ℝ 1 (fderiv ℝ (fun y : Space => u (t, y))) :=
    hu.fderiv_right (by norm_num)
  exact (hfirst.clm_apply contDiff_const).differentiable (by norm_num)

/-- Additivity of the concrete iterated-derivative Laplacian on C² slices. -/
theorem spatialLaplacian_add
    (u e : VelocityField) (t : ℝ) (x : Space)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y)))
    (he : ContDiff ℝ 2 (fun y : Space => e (t, y))) :
    spatialLaplacian (fun z => u z + e z) t x =
      spatialLaplacian u t x + spatialLaplacian e t x := by
  have hdu := hu.differentiable (by norm_num)
  have hde := he.differentiable (by norm_num)
  have hsum : ∀ y : Space,
      spatialDerivative (fun z => u z + e z) t y =
        spatialDerivative u t y + spatialDerivative e t y :=
    fun y => spatialDerivative_add u e t y (hdu y) (hde y)
  unfold spatialLaplacian
  simp_rw [hsum, add_apply]
  simp_rw [fderiv_fun_add
    (differentiable_spatial_direction u t hu _ x)
    (differentiable_spatial_direction e t he _ x), add_apply]
  exact Finset.sum_add_distrib

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

/-- Constant-scalar linearity of the actual pressure gradient. -/
theorem pressureGradient_const_smul
    (p : PressureField) (t : ℝ) (x : Space) (c : ℝ)
    (hp : DifferentiableAt ℝ (fun y : Space => p (t, y)) x) :
    pressureGradient (fun z => c • p z) t x = c • pressureGradient p t x := by
  unfold pressureGradient
  rw [fderiv_fun_const_smul hp c]
  simp only [smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Constant-scalar linearity of divergence, using coordinate evaluation. -/
theorem spatialDivergence_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    spatialDivergence (fun z => c • u z) t x = c * spatialDivergence u t x := by
  unfold spatialDivergence
  rw [spatialDerivative_const_smul u t x c hu]
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Constant-scalar linearity of the concrete second spatial derivative. -/
theorem spatialLaplacian_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : ContDiff ℝ 2 (fun y : Space => u (t, y))) :
    spatialLaplacian (fun z => c • u z) t x = c • spatialLaplacian u t x := by
  have hdu := hu.differentiable (by norm_num)
  have hscale : ∀ y : Space,
      spatialDerivative (fun z => c • u z) t y = c • spatialDerivative u t y :=
    fun y => spatialDerivative_const_smul u t y c (hdu y)
  unfold spatialLaplacian
  simp_rw [hscale, smul_apply]
  simp_rw [fderiv_fun_const_smul (differentiable_spatial_direction u t hu _ x) c,
    smul_apply]
  exact (Finset.smul_sum).symm

/-- Velocity scaling squares in advection, because both the direction and the
spatial derivative scale. -/
theorem advection_const_smul
    (u : VelocityField) (t : ℝ) (x : Space) (c : ℝ)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    advection (fun z => c • u z) t x = (c * c) • advection u t x := by
  unfold advection
  rw [spatialDerivative_const_smul u t x c hu]
  simp only [smul_apply, map_smul, smul_smul]

/-- The time derivative of a switched velocity includes the derivative of the
switch; it is proved using the Frechet derivative product rule. -/
theorem temporalDerivative_time_smul
    (u : VelocityField) (a : ℝ → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ a t)
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t) :
    temporalDerivative (fun z => a z.1 • u z) t x =
      a t • temporalDerivative u t x + (fderiv ℝ a t 1) • u (t, x) := by
  unfold temporalDerivative
  rw [fderiv_fun_smul ha hu]
  rfl



end NavierStokes.ResidualCalculus
