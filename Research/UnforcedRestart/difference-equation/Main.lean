import NavierStokes.SolutionDifference

/-! Actual-field difference algebra. No existence or integration is asserted.
The primary convention is forced reference minus comparator, `w = u - v`.
The reversed convention is provided separately. -/

noncomputable section
open scoped ContDiff
open NavierStokes.ProblemStatement NavierStokes.SolutionDifference

namespace UnforcedRestart.DifferenceEquation

/-- Same constant viscosity in both equations; built from the repository operators. -/
def residual (ν : ℝ) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + advection u t x - ν • spatialLaplacian u t x +
    pressureGradient p t x

theorem residual_one (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) :
    residual 1 u p t x = navierStokesResidual u p t x := by
  simp [residual, navierStokesResidual]

/-- Exact unequal-force identity. Positivity of viscosity is unnecessary for this
algebra (and required separately for dissipative estimates). -/
theorem difference_forces {ν : ℝ} {u v f g : VelocityField}
    {p q : PressureField} {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hfu : residual ν u p t x = f (t, x))
    (hgv : residual ν v q t x = g (t, x)) :
    temporalDerivative (u - v) t x = ν • spatialLaplacian (u - v) t x -
      spatialDerivative u t x ((u - v) (t, x)) -
      spatialDerivative (u - v) t x (v (t, x)) -
      pressureGradient (p - q) t x + (f (t, x) - g (t, x)) := by
  have ha := advection_difference hu hv x
  rw [temporalDerivative_sub htu htv, spatialLaplacian_sub hu hv,
    pressureGradient_sub hp hq, smul_sub]
  have heq := congrArg₂ (fun a b : Space => a - b) hfu hgv
  unfold residual at heq
  rw [show temporalDerivative u t x + advection u t x - ν • spatialLaplacian u t x +
      pressureGradient p t x -
      (temporalDerivative v t x + advection v t x - ν • spatialLaplacian v t x +
        pressureGradient q t x) =
      temporalDerivative u t x - temporalDerivative v t x +
        (advection u t x - advection v t x) -
        (ν • spatialLaplacian u t x - ν • spatialLaplacian v t x) +
        (pressureGradient p t x - pressureGradient q t x) by abel, ha] at heq
  apply sub_eq_zero.mp
  have hz := sub_eq_zero.mpr heq
  convert hz using 1
  abel

/-- Forced reference minus unforced comparator, viscosity exactly one. -/
theorem forced_unforced {u v f : VelocityField} {p q : PressureField}
    {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hfu : navierStokesResidual u p t x = f (t, x))
    (hzero : navierStokesResidual v q t x = 0) :
    temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
      spatialDerivative u t x ((u - v) (t, x)) -
      spatialDerivative (u - v) t x (v (t, x)) -
      pressureGradient (p - q) t x + f (t, x) := by
  simpa only [one_smul, Pi.zero_apply, sub_zero] using
    difference_forces (ν := 1) (g := 0) hu hv hp hq htu htv
      ((residual_one u p t x).trans hfu) ((residual_one v q t x).trans hzero)

/-- User convention: unforced comparator minus forced reference, hence minus force.
The transport decomposition changes when the roles are exchanged. -/
theorem unforced_forced {ν : ℝ} {u v f : VelocityField} {p q : PressureField}
    {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hfu : residual ν u p t x = f (t, x))
    (hzero : residual ν v q t x = 0) :
    temporalDerivative (v - u) t x = ν • spatialLaplacian (v - u) t x -
      spatialDerivative v t x ((v - u) (t, x)) -
      spatialDerivative (v - u) t x (u (t, x)) -
      pressureGradient (q - p) t x - f (t, x) := by
  simpa only [Pi.zero_apply, zero_sub, sub_eq_add_neg, zero_add] using
    difference_forces (f := 0) hv hu hq hp htv htu hzero hfu

/-- On a closed smooth slab the ordinary time-derivative equation is obtained
only at interior times. No endpoint within-derivative identification is used. -/
theorem forced_unforced_on_slab {u v f : VelocityField} {p q : PressureField}
    {a b : ℝ}
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hv : ContDiffOn ℝ ∞ v (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hq : ContDiffOn ℝ ∞ q (slab a b))
    (hfu : ∀ t ∈ Set.Ioo a b, ∀ x : Space,
      navierStokesResidual u p t x = f (t, x))
    (hzero : ∀ t ∈ Set.Ioo a b, ∀ x : Space,
      navierStokesResidual v q t x = 0) :
    ∀ t ∈ Set.Ioo a b, ∀ x : Space,
      temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
        spatialDerivative u t x ((u - v) (t, x)) -
        spatialDerivative (u - v) t x (v (t, x)) -
        pressureGradient (p - q) t x + f (t, x) := by
  intro t ht x
  have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact forced_unforced (spatial_smooth hu ht') (spatial_smooth hv ht')
    (spatial_smooth hp ht') (spatial_smooth hq ht')
    (time_differentiable_at_interior hu ht x)
    (time_differentiable_at_interior hv ht x) (hfu t ht x) (hzero t ht x)

/-- Divergence subtraction requires spatial regularity, not equality of forces. -/
theorem divergence_free_difference {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hdu : ∀ x : Space, spatialDivergence u t x = 0)
    (hdv : ∀ x : Space, spatialDivergence v t x = 0) :
    ∀ x : Space, spatialDivergence (u - v) t x = 0 := by
  intro x
  rw [spatialDivergence_sub hu hv x, hdu x, hdv x, sub_self]

/-- Arbitrary shared restart datum, not the zero-datum Solution structure. -/
theorem restart_difference_zero {u v : VelocityField} {a : Space → Space} {t₀ : ℝ}
    (hu : ∀ x : Space, u (t₀, x) = a x)
    (hv : ∀ x : Space, v (t₀, x) = a x) :
    ∀ x : Space, (u - v) (t₀, x) = 0 := by
  intro x
  simp only [Pi.sub_apply, hu x, hv x, sub_self]

end UnforcedRestart.DifferenceEquation

#print axioms UnforcedRestart.DifferenceEquation.residual
#print axioms UnforcedRestart.DifferenceEquation.residual_one
#print axioms UnforcedRestart.DifferenceEquation.difference_forces
#print axioms UnforcedRestart.DifferenceEquation.forced_unforced
#print axioms UnforcedRestart.DifferenceEquation.unforced_forced
#print axioms UnforcedRestart.DifferenceEquation.forced_unforced_on_slab
#print axioms UnforcedRestart.DifferenceEquation.divergence_free_difference
#print axioms UnforcedRestart.DifferenceEquation.restart_difference_zero
