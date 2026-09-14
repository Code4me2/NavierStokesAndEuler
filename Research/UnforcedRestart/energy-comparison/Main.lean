import NavierStokes.PeriodicUniqueness

/-! Periodic relative energy with actual residual difference, viscosity one.
No existence or smallness assertion. All spatial boundary cancellations are
proved by the imported periodic integration lemmas. -/
noncomputable section
open Set
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace UnforcedRestart.EnergyComparison
open NavierStokes.ProblemStatement NavierStokes.SolutionDifference
open NavierStokes.PeriodicIntegration NavierStokes.PeriodicUniqueness

theorem forced_energy_balance {u v : VelocityField} {p q : PressureField} {f : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hpq : UnitPeriods (fun x : Space => q (t, x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hf : Continuous (fun x : Space => f (t, x)))
    (hNS : ∀ x, navierStokesResidual u p t x - navierStokesResidual v q t x = f (t, x)) :
    energyRate u v t = -2 * dissipation (u - v) t - 2 * coupling u (u - v) t +
      2 * cubeIntegral (fun x => ⟪(u - v) (t, x), f (t, x)⟫_ℝ) := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hpw : UnitPeriods (fun x : Space => (u - v) (t, x)) := unitPeriods_sub hpu hpv
  have hdw : ∀ x, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdu x, hdv x, sub_self]
  have hL := (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hN := (hw.inner ℝ ((hu.fderiv_right infty_add_one_le_infty).clm_apply hw)).continuous
  have hT := (hw.inner ℝ ((hw.fderiv_right infty_add_one_le_infty).clm_apply hv)).continuous
  have hP := (hw.inner ℝ (pressureGradient_contDiff (p := p - q) (t := t) (hp.sub hq))).continuous
  have hF : Continuous (fun x => ⟪(u - v) (t, x), f (t, x)⟫_ℝ) :=
    hw.continuous.inner hf
  have hdiff (x : Space) :
      temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
        spatialDerivative u t x ((u - v) (t, x)) -
        spatialDerivative (u - v) t x (v (t, x)) - pressureGradient (p - q) t x + f (t, x) := by
    have heq := hNS x
    have ha := advection_difference hu hv x
    rw [temporalDerivative_sub (htu x) (htv x), spatialLaplacian_sub hu hv,
      pressureGradient_sub hp hq]
    rw [← heq]
    unfold navierStokesResidual
    have ha' := sub_eq_zero.mpr ha
    apply sub_eq_zero.mp
    convert congrArg Neg.neg ha' using 1 <;> abel
  have hEq : (fun x => ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) =
      (fun x => ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ +
        ⟪(u - v) (t, x), f (t, x)⟫_ℝ) := by
    funext x
    rw [hdiff x]
    simp only [inner_sub_right, inner_add_right]
  unfold energyRate
  rw [cubeIntegral_const_mul, hEq]
  change 2 * cubeIntegral (fun x =>
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => u (t, y)) x ((u - v) (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => (u - v) (t, y)) x (v (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ +
    ⟪(u - v) (t, x), f (t, x)⟫_ℝ) = _
  rw [cubeIntegral_add (((hL.fun_sub hN).fun_sub hT).fun_sub hP) hF,
    cubeIntegral_sub ((hL.fun_sub hN).fun_sub hT) hP, cubeIntegral_sub (hL.fun_sub hN) hT,
    cubeIntegral_sub hL hN, cubeIntegral_laplacian_energy hw hpw,
    cubeIntegral_transport_energy_zero hw hv hpw hpv hdv,
    cubeIntegral_pressure_energy_zero hw (hp.sub hq) hpw (unitPeriods_sub hpp hpq) hdw]
  simp only [sub_zero, dissipation, coupling, spatialDerivative]
  ring


/-- Young's inequality integrated on the actual cube (no force periodicity needed). -/
theorem forcing_work_le {w f : VelocityField} {t : ℝ}
    (hw : Continuous (fun x : Space => w (t, x)))
    (hf : Continuous (fun x : Space => f (t, x))) :
    2 * cubeIntegral (fun x => ⟪w (t, x), f (t, x)⟫_ℝ) ≤
      cubeIntegral (fun x => ‖w (t, x)‖ ^ 2) +
      cubeIntegral (fun x => ‖f (t, x)‖ ^ 2) := by
  have hw2 : Continuous (fun x => ‖w (t, x)‖ ^ 2) := hw.norm.pow 2
  have hf2 : Continuous (fun x => ‖f (t, x)‖ ^ 2) := hf.norm.pow 2
  rw [← cubeIntegral_const_mul, ← cubeIntegral_add hw2 hf2]
  apply cubeIntegral_mono_on_cube
    (continuous_const.mul (hw.inner hf)) ((hw.norm.pow 2).add (hf.norm.pow 2))
  intro y _
  change 2 * ⟪w (t, toSpace y), f (t, toSpace y)⟫_ℝ ≤
    ‖w (t, toSpace y)‖ ^ 2 + ‖f (t, toSpace y)‖ ^ 2
  have h := (le_abs_self ⟪w (t, toSpace y), f (t, toSpace y)⟫_ℝ).trans
    (abs_real_inner_le_norm (w (t, toSpace y)) (f (t, toSpace y)))
  nlinarith [sq_nonneg (‖w (t, toSpace y)‖ - ‖f (t, toSpace y)‖)]

theorem forced_energy_rate_le {u v : VelocityField} {p q : PressureField} {f : VelocityField} {t B : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hpq : UnitPeriods (fun x : Space => q (t, x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hf : Continuous (fun x : Space => f (t, x)))
    (hNS : ∀ x, navierStokesResidual u p t x - navierStokesResidual v q t x = f (t, x))
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    energyRate u v t + 2 * dissipation (u - v) t ≤
      (2 * B + 1) * energy u v t + cubeIntegral (fun x => ‖f (t, x)‖ ^ 2) := by
  have hb := forced_energy_balance hu hv hp hq hpu hpv hpp hpq hdu hdv htu htv hf hNS
  have hc := neg_coupling_le_energy hu hv hB
  have hf' := forcing_work_le (w := u - v) (f := f) (hu.sub hv).continuous hf
  change 2 * cubeIntegral (fun x => ⟪(u - v) (t, x), f (t, x)⟫_ℝ) ≤
    energy u v t + cubeIntegral (fun x => ‖f (t, x)‖ ^ 2) at hf'
  linarith

#print axioms forced_energy_balance
#print axioms forcing_work_le
#print axioms forced_energy_rate_le
end UnforcedRestart.EnergyComparison
