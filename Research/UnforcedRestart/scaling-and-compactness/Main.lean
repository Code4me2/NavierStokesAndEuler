import NavierStokes.ComparatorBridge
import NavierStokes.BaseResidual

/-! Scaling identities only: no compactness or unforced existence theorem. -/
noncomputable section
open NavierStokes NavierStokes.ProblemStatement

namespace UnforcedRestart.ScalingAndCompactness

/-- Parabolic velocity zoom about `(T,0)`, in the repository's spacetime type. -/
def zoomVelocity (r T : ℝ) (u : VelocityField) : VelocityField :=
  fun z => r • u (T + r ^ 2 * z.1, r • z.2)

/-- Corresponding force zoom. Its PDE interpretation requires chain rules. -/
def zoomForce (r T : ℝ) (f : VelocityField) : VelocityField :=
  fun z => r ^ 3 • f (T + r ^ 2 * z.1, r • z.2)

/-- Fixed positive viscosity has the same coefficient after parabolic scaling. -/
theorem viscosity_coefficient (r ν : ℝ) : r * (ν * r ^ 2) = ν * r ^ 3 := by
  ring

/-- A bound on the actual sampled force, not a bound inferred from axial jets. -/
theorem zoomForce_norm_le {r T M : ℝ} (hr : 0 ≤ r) (f : VelocityField)
    (z : SpaceTime) (hf : ‖f (T + r ^ 2 * z.1, r • z.2)‖ ≤ M) :
    ‖zoomForce r T f z‖ ≤ r ^ 3 * M := by
  dsimp [zoomForce]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr 3)]
  exact mul_le_mul_of_nonneg_left hf (pow_nonneg hr 3)

/-- Even mere continuity of the force at the zoom center gives pointwise vanishing.
This contains no assertion about convergence of the zoomed velocities. -/
theorem zoomForce_tendsto {T : ℝ} {f : VelocityField}
    (hf : ContinuousAt f (T, 0)) (z : SpaceTime) :
    Filter.Tendsto (fun r : ℝ => zoomForce r T f z) (nhds 0) (nhds 0) := by
  have hm : ContinuousAt (fun r : ℝ => (T + r ^ 2 * z.1, r • z.2)) 0 := by
    fun_prop
  have hc : ContinuousAt (fun r : ℝ => f (T + r ^ 2 * z.1, r • z.2)) 0 := by
    exact ContinuousAt.comp (f := fun r : ℝ => (T + r ^ 2 * z.1, r • z.2))
      (by simpa using hf) hm
  have hp : ContinuousAt (fun r : ℝ => r ^ 3) 0 := by fun_prop
  simpa [zoomForce] using hp.tendsto.smul hc.tendsto

/-- The super-parabolic factor of the actual base exponent. -/
theorem axis_power {r : ℝ} (hr : 0 < r) (h : ℝ) :
    r * (r ^ 2) ^ (-(1 / 2 + h)) = r ^ (-2 * h) := by
  have hp : (r ^ 2) ^ (-(1 / 2 + h)) = r ^ (2 * (-(1 / 2 + h))) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num
  calc
    r * (r ^ 2) ^ (-(1 / 2 + h)) = r ^ (1 : ℝ) * r ^ (2 * (-(1 / 2 + h))) := by
      rw [Real.rpow_one, hp]
    _ = r ^ (1 + 2 * (-(1 / 2 + h))) := (Real.rpow_add hr _ _).symm
    _ = r ^ (-2 * h) := by congr 1; ring

/-- Exact scaled norm of the repository's base, with every base hypothesis exposed.
The final assembled candidate requires the separate eventual-origin transfer. -/
theorem base_zoom_axis {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (C : ℝ)
    (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) (h0 : 0 < d.axial 0 (0, 0))
    {r : ℝ} (hr : 0 < r) :
    ‖zoomVelocity r 1 (SlowBorelBase.baseVelocity a h C d) (-1, 0)‖ =
      r ^ (-2 * h) * d.axial 0 (0, 0) := by
  have ht : 1 + r ^ 2 * (-1) < 1 := by nlinarith [sq_pos_of_pos hr]
  have htime : 1 - (1 + r ^ 2 * (-1)) = r ^ 2 := by ring
  simp only [zoomVelocity, smul_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [BaseResidual.baseVelocity_norm_at_origin ha hh hh1 hd C hz h0 ht, htime]
  change r * ((r ^ 2) ^ (-(1 / 2 + h)) * d.axial 0 (0, 0)) = _
  rw [← mul_assoc, axis_power hr]

end UnforcedRestart.ScalingAndCompactness

#print axioms UnforcedRestart.ScalingAndCompactness.zoomVelocity
#print axioms UnforcedRestart.ScalingAndCompactness.zoomForce
#print axioms UnforcedRestart.ScalingAndCompactness.viscosity_coefficient
#print axioms UnforcedRestart.ScalingAndCompactness.zoomForce_norm_le
#print axioms UnforcedRestart.ScalingAndCompactness.zoomForce_tendsto
#print axioms UnforcedRestart.ScalingAndCompactness.axis_power
#print axioms UnforcedRestart.ScalingAndCompactness.base_zoom_axis
