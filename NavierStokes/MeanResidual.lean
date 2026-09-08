import NavierStokes.CylindricalResidual
import NavierStokes.TransportPrimitive

/-!
# Exact angularly averaged Navier--Stokes balances

The average is a normalized actual interval integral. All coordinate derivatives
are Fréchet derivatives on spacetime, and the Reynolds products include the
entire oscillatory velocity.
-/

namespace NavierStokes.MeanResidual

noncomputable section

open ProblemStatement Set Filter MeasureTheory
open AxisymmetricFields (projection)
open AxisymmetricResidual (pack pack_zero pack_one pack_two)
open scoped ContDiff Topology Interval

abbrev Scalar := SpaceTime → ℝ
abbrev Components := Fin 3 → Scalar

noncomputable def period : ℝ := 2 * Real.pi
noncomputable def angularVector : SpaceTime := (0, coordinateVector 1)
noncomputable def angularShift (q : SpaceTime) (a : ℝ) : SpaceTime := q + a • angularVector
noncomputable def radius (q : SpaceTime) : ℝ := q.2 0

theorem period_pos : 0 < period := mul_pos (by norm_num) Real.pi_pos
theorem period_ne_zero : period ≠ 0 := ne_of_gt period_pos

@[simp] theorem angularShift_zero (q : SpaceTime) : angularShift q 0 = q := by
  simp [angularShift]

@[simp] theorem radius_angularShift (q : SpaceTime) (a : ℝ) :
    radius (angularShift q a) = radius q := by
  simp [radius, angularShift, angularVector, coordinateVector]

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def direction (v : SpaceTime) (f : SpaceTime → E) (q : SpaceTime) : E :=
  fderiv ℝ f q v

noncomputable def dt (f : SpaceTime → E) := direction (1, 0) f
noncomputable def dr (f : SpaceTime → E) := direction (0, coordinateVector 0) f
noncomputable def dtheta (f : SpaceTime → E) := direction angularVector f
noncomputable def dz (f : SpaceTime → E) := direction (0, coordinateVector 2) f

noncomputable def average (f : SpaceTime → E) (q : SpaceTime) : E :=
  period⁻¹ • ∫ a in (0 : ℝ)..period, f (angularShift q a)

def AngularContinuous (f : SpaceTime → E) : Prop :=
  ∀ q, Continuous (fun a => f (angularShift q a))

def AngularPeriodic (f : SpaceTime → E) : Prop :=
  ∀ q, f (angularShift q period) = f q

def AngularInvariant (f : SpaceTime → E) : Prop :=
  ∀ q a, f (angularShift q a) = f q

theorem contDiff_angularShift :
    ContDiff ℝ ∞ (fun qa : SpaceTime × ℝ => angularShift qa.1 qa.2) :=
  contDiff_fst.add (contDiff_snd.smul contDiff_const)

theorem direction_smooth (v : SpaceTime) {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (direction v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

@[fun_prop] theorem direction_continuous (v : SpaceTime) {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) : Continuous (direction v f) := (direction_smooth v hf).continuous

@[fun_prop] theorem continuous_angularShift (q : SpaceTime) : Continuous (angularShift q) :=
  continuous_const.add (continuous_id.smul continuous_const)

omit [NormedSpace ℝ E] in
theorem angularContinuous_of_continuous {f : SpaceTime → E} (hf : Continuous f) :
    AngularContinuous f := by
  intro q
  exact hf.comp (continuous_const.add (continuous_id.smul continuous_const))

omit [NormedSpace ℝ E] in
theorem AngularContinuous.add {f g : SpaceTime → E}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    AngularContinuous (fun q => f q + g q) := fun q => (hf q).add (hg q)

omit [NormedSpace ℝ E] in
theorem AngularContinuous.sub {f g : SpaceTime → E}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    AngularContinuous (fun q => f q - g q) := fun q => (hf q).sub (hg q)

theorem AngularContinuous.mul {f g : Scalar}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    AngularContinuous (fun q => f q * g q) := fun q => (hf q).mul (hg q)

theorem AngularContinuous.div_radius {f : Scalar} (hf : AngularContinuous f) (n : ℕ) :
    AngularContinuous (fun q => f q / radius q ^ n) := by
  intro q
  simpa only [radius_angularShift] using (hf q).div_const (radius q ^ n)

theorem AngularContinuous.const_mul {f : Scalar} (hf : AngularContinuous f) (c : ℝ) :
    AngularContinuous (fun q => c * f q) := fun q => continuous_const.mul (hf q)


theorem average_add {f g : SpaceTime → E} (hf : AngularContinuous f)
    (hg : AngularContinuous g) (q : SpaceTime) :
    average (fun y => f y + g y) q = average f q + average g q := by
  unfold average
  rw [intervalIntegral.integral_add ((hf q).intervalIntegrable _ _)
    ((hg q).intervalIntegrable _ _), smul_add]

theorem average_sub {f g : SpaceTime → E} (hf : AngularContinuous f)
    (hg : AngularContinuous g) (q : SpaceTime) :
    average (fun y => f y - g y) q = average f q - average g q := by
  unfold average
  rw [intervalIntegral.integral_sub ((hf q).intervalIntegrable _ _)
    ((hg q).intervalIntegrable _ _), smul_sub]



theorem average_mul_invariant {a f : Scalar} (ha : AngularInvariant a) (q : SpaceTime) :
    average (fun y => a y * f y) q = a q * average f q := by
  change ∀ q θ, a (angularShift q θ) = a q at ha
  simp only [average, ha, intervalIntegral.integral_const_mul, smul_eq_mul]
  ring



theorem average_const_mul (c : ℝ) (f : Scalar) (q : SpaceTime) :
    average (fun y => c * f y) q = c * average f q :=
  average_mul_invariant (fun _ _ => rfl) q

theorem average_congr {f g : SpaceTime → E} {q : SpaceTime}
    (h : ∀ a ∈ uIcc (0 : ℝ) period, f (angularShift q a) = g (angularShift q a)) :
    average f q = average g q := by
  unfold average
  congr 1
  exact intervalIntegral.integral_congr h

theorem average_smooth [CompleteSpace E] {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (average f) :=
  (TransportPrimitive.parameterIntegral_contDiff (hf.comp contDiff_angularShift)
    0 period).const_smul _


theorem AngularPeriodic.direction {f : SpaceTime → E} (hp : AngularPeriodic f)
    (v : SpaceTime) : AngularPeriodic (direction v f) := by
  intro q
  have he : (fun x => f (x + period • angularVector)) = f := funext hp
  have hd := congrArg (fun F => fderiv ℝ F q) he
  rw [fderiv_comp_add_right] at hd
  exact congrArg (fun L : SpaceTime →L[ℝ] E => L v) hd

theorem AngularInvariant.direction {f : SpaceTime → E} (hp : AngularInvariant f)
    (v : SpaceTime) : AngularInvariant (direction v f) := by
  intro q a
  have he : (fun x => f (x + a • angularVector)) = f := funext (fun x => hp x a)
  have hd := congrArg (fun F => fderiv ℝ F q) he
  rw [fderiv_comp_add_right] at hd
  exact congrArg (fun L : SpaceTime →L[ℝ] E => L v) hd

theorem AngularPeriodic.mul {f g : Scalar} (hf : AngularPeriodic f) (hg : AngularPeriodic g) :
    AngularPeriodic (fun q => f q * g q) := by
  intro q
  change f (angularShift q period) * g (angularShift q period) = f q * g q
  rw [hf q, hg q]



theorem direction_add {f g : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v q : SpaceTime) :
    direction v (fun y => f y + g y) q = direction v f q + direction v g q := by
  unfold direction
  rw [fderiv_fun_add (hf.differentiable (by simp) q) (hg.differentiable (by simp) q)]
  rfl

theorem direction_sub {f g : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v q : SpaceTime) :
    direction v (fun y => f y - g y) q = direction v f q - direction v g q := by
  unfold direction
  rw [fderiv_fun_sub (hf.differentiable (by simp) q) (hg.differentiable (by simp) q)]
  rfl






noncomputable def velocity (w : Components) : VelocityField :=
  fun q => pack (w 0 q) (w 1 q) (w 2 q)

@[simp] theorem velocity_apply (w : Components) (q : SpaceTime) (i : Fin 3) :
    velocity w q i = w i q := by
  fin_cases i <;> simp [velocity]

theorem velocity_smooth {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i)) :
    ContDiff ℝ ∞ (velocity w) :=
  (((hw 0).smul contDiff_const).add ((hw 1).smul contDiff_const)).add
    ((hw 2).smul contDiff_const)



noncomputable def laplacian (f : Scalar) (q : SpaceTime) : ℝ :=
  dr (dr f) q + dr f q / radius q + dtheta (dtheta f) q / radius q ^ 2 + dz (dz f) q

noncomputable def meanLaplacian (f : Scalar) (q : SpaceTime) : ℝ :=
  dr (dr f) q + dr f q / radius q + dz (dz f) q

noncomputable def radialDivergence (c : ℝ) (f : Scalar) (q : SpaceTime) : ℝ :=
  dr f q + c / radius q * f q

noncomputable def divergence (w : Components) (q : SpaceTime) : ℝ :=
  dr (w 0) q + w 0 q / radius q + dtheta (w 1) q / radius q + dz (w 2) q

noncomputable def transport (w : Components) (f : Scalar) (q : SpaceTime) : ℝ :=
  w 0 q * dr f q + w 1 q / radius q * dtheta f q + w 2 q * dz f q

noncomputable def residualRadial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 0) q + transport w (w 0) q - (w 1 q) ^ 2 / radius q - laplacian (w 0) q +
    w 0 q / radius q ^ 2 + 2 * dtheta (w 1) q / radius q ^ 2 + dr p q

noncomputable def residualAngular (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 1) q + transport w (w 1) q + w 0 q * w 1 q / radius q - laplacian (w 1) q +
    w 1 q / radius q ^ 2 - 2 * dtheta (w 0) q / radius q ^ 2 + dtheta p q / radius q

noncomputable def residualAxial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 2) q + transport w (w 2) q - laplacian (w 2) q + dz p q



































omit [NormedSpace ℝ E] in
theorem AngularInvariant.add {f g : SpaceTime → E}
    (hf : AngularInvariant f) (hg : AngularInvariant g) :
    AngularInvariant (fun q => f q + g q) := by
  intro q a
  exact congrArg₂ (· + ·) (hf q a) (hg q a)

theorem AngularInvariant.mul {f g : Scalar}
    (hf : AngularInvariant f) (hg : AngularInvariant g) :
    AngularInvariant (fun q => f q * g q) := by
  intro q a
  exact congrArg₂ (· * ·) (hf q a) (hg q a)

omit [NormedSpace ℝ E] in
theorem AngularPeriodic.add {f g : SpaceTime → E}
    (hf : AngularPeriodic f) (hg : AngularPeriodic g) :
    AngularPeriodic (fun q => f q + g q) := by
  intro q
  exact congrArg₂ (· + ·) (hf q) (hg q)

/-- The complete velocity split, with no omission of any part of `osc`. -/
noncomputable def total (base mean osc : Components) : Components :=
  fun i q => base i q + mean i q + osc i q

/-- The exact Reynolds product of the full oscillatory fields. -/
noncomputable def covariance (osc : Components) (i j : Fin 3) : Scalar :=
  average (fun q => osc i q * osc j q)

noncomputable def fluxDifference (base mean osc : Components) (i j : Fin 3) : Scalar :=
  fun q => base i q * mean j q + mean i q * base j q +
    mean i q * mean j q + covariance osc i j q

theorem covariance_smooth {osc : Components} (ho : ∀ i, ContDiff ℝ ∞ (osc i)) (i j : Fin 3) :
    ContDiff ℝ ∞ (covariance osc i j) := average_smooth ((ho i).mul (ho j))

theorem covariance_symm (osc : Components) (i j : Fin 3) : covariance osc i j = covariance osc j i := by
  simp only [covariance, mul_comm]












noncomputable def baseAngular (b : Components) (q : SpaceTime) : ℝ :=
  dt (b 1) q + radialDivergence 2 (fun y => b 0 y * b 1 y) q +
    dz (fun y => b 2 y * b 1 y) q - meanLaplacian (b 1) q + b 1 q / radius q ^ 2




/-- Required physical radial pressure derivative in (32). -/
noncomputable def gr (b m o : Components) (q : SpaceTime) : ℝ :=
  -(dt (m 0) q + radialDivergence 1 (fluxDifference b m o 0 0) q +
    dz (fluxDifference b m o 2 0) q - fluxDifference b m o 1 1 q / radius q -
    meanLaplacian (m 0) q + m 0 q / radius q ^ 2)













/-- The perturbation pressure is defined from its actual angular mean. -/
noncomputable def meanPressure (p pb : Scalar) : Scalar := fun q => average p q - pb q

theorem meanPressure_smooth {p pb : Scalar} (hp : ContDiff ℝ ∞ p) (hpb : ContDiff ℝ ∞ pb) :
    ContDiff ℝ ∞ (meanPressure p pb) := (average_smooth hp).sub hpb



def Represents (u : VelocityField) (w : Components) : Prop :=
  ∀ q : SpaceTime, u (q.1, CylindricalResidual.chart q.2) =
    CylindricalResidual.frame (q.2 1) (velocity w q)

theorem Represents.components {u : VelocityField} {w : Components} (h : Represents u w) :
    CylindricalResidual.velocityComponents u = velocity w := by
  funext q
  change CylindricalResidual.frame (-(q.2 1)) (u (q.1, CylindricalResidual.chart q.2)) = velocity w q
  rw [h q, CylindricalResidual.frame_inverse]









end

end NavierStokes.MeanResidual
