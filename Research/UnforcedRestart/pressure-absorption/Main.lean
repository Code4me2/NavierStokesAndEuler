import NavierStokes.ResidualCalculus
import NavierStokes.SolutionDifference

/-! Pressure correction for the actual viscosity-one residual; no potential existence claim. -/
noncomputable section
namespace UnforcedRestart.PressureAbsorption
open NavierStokes NavierStokes.ProblemStatement Set
open scoped ContDiff

/-- The minus sign removes a gradient force. Only pressure slices need regularity. -/
theorem residual_sub_pressure (u : VelocityField) (p φ : PressureField) (t : ℝ)
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hφ : ContDiff ℝ ∞ (fun x : Space => φ (t, x))) (x : Space) :
    navierStokesResidual u (p - φ) t x =
      navierStokesResidual u p t x - pressureGradient φ t x := by
  unfold navierStokesResidual
  rw [SolutionDifference.pressureGradient_sub hp hφ]
  abel

/-- Exact remaining force; no assertion that it is a Helmholtz projection. -/
theorem residual_after_correction (u f : VelocityField) (p φ : PressureField) (t : ℝ)
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hφ : ContDiff ℝ ∞ (fun x : Space => φ (t, x))) (x : Space)
    (heq : navierStokesResidual u p t x = f (t, x)) :
    navierStokesResidual u (p - φ) t x = f (t, x) - pressureGradient φ t x := by
  rw [residual_sub_pressure u p φ t hp hφ x, heq]

/-- Absorption is equivalent to a genuine spatial-gradient identity at the point. -/
theorem unforced_iff_gradient (u f : VelocityField) (p φ : PressureField) (t : ℝ)
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hφ : ContDiff ℝ ∞ (fun x : Space => φ (t, x))) (x : Space)
    (heq : navierStokesResidual u p t x = f (t, x)) :
    navierStokesResidual u (p - φ) t x = 0 ↔ f (t, x) = pressureGradient φ t x := by
  rw [residual_after_correction u f p φ t hp hφ x heq, sub_eq_zero]

/-- Closed-domain smoothness is preserved; this does not extend the domain. -/
theorem corrected_pressure_smooth {D : Set SpaceTime} {p φ : PressureField}
    (hp : ContDiffOn ℝ ∞ p D) (hφ : ContDiffOn ℝ ∞ φ D) :
    ContDiffOn ℝ ∞ (p - φ) D := hp.sub hφ

/-- An admissible periodic potential preserves the repository pressure convention. -/
theorem corrected_pressure_periodic {I : Set ℝ} {p φ : PressureField}
    (hp : UnitSpatialPeriodsOn I p) (hφ : UnitSpatialPeriodsOn I φ) :
    UnitSpatialPeriodsOn I (p - φ) := by
  intro t ht x i
  change p (t, x + coordinateVector i) - φ (t, x + coordinateVector i) = _
  rw [hp t ht x i, hφ t ht x i]
  rfl

/-- Conditional equation on any chosen time set, without zero-datum restart packaging. -/
theorem absorb_on (I : Set ℝ) (u f : VelocityField) (p φ : PressureField)
    (hp : ∀ t ∈ I, ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hφ : ∀ t ∈ I, ContDiff ℝ ∞ (fun x : Space => φ (t, x)))
    (heq : ∀ t ∈ I, ∀ x : Space, navierStokesResidual u p t x = f (t, x))
    (hgrad : ∀ t ∈ I, ∀ x : Space, f (t, x) = pressureGradient φ t x) :
    ∀ t ∈ I, ∀ x : Space, navierStokesResidual u (p - φ) t x = 0 := by
  intro t ht x
  exact (unforced_iff_gradient u f p φ t (hp t ht) (hφ t ht) x (heq t ht x)).2
    (hgrad t ht x)

/-- A time-only gauge has zero spatial gradient, with no temporal regularity needed. -/
theorem time_gauge_gradient (c : ℝ → ℝ) (t : ℝ) (x : Space) :
    pressureGradient (fun z => c z.1) t x = 0 := by
  simp [pressureGradient]

#print axioms time_gauge_gradient
#print axioms residual_sub_pressure
#print axioms residual_after_correction
#print axioms unforced_iff_gradient
#print axioms corrected_pressure_smooth
#print axioms corrected_pressure_periodic
#print axioms absorb_on
end UnforcedRestart.PressureAbsorption
