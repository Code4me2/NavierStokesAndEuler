import NavierStokes.SolutionDifference
import NavierStokes.GronwallInterior
import NavierStokes.PeriodicIntegration
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Classical uniqueness for periodic Navier--Stokes fields

The `L²` energy method on the unit cube for the operators of
`ProblemStatement`: periodic integration by parts kills the pressure and the
transport term, the viscous term is dissipative, and the one indefinite term is
bounded by the gradient of the reference solution. The difference algebra is
shared with the whole-space proof (`SolutionDifference`); the Gronwall step is
`GronwallInterior.eq_zero_of_deriv_le`. This module also holds the two
periodicity facts the periodic exclusion needs: every point has a
representative in the unit cube, and a continuous periodic field is bounded on
a closed time slab.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokes.PeriodicUniqueness

open ProblemStatement SolutionDifference

/-- Unit coordinate periods imply invariance under every integer lattice
translation; no quotient or fundamental-domain claim is assumed. -/
theorem periodic_lattice {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i))
    (n : Fin 3 → ℤ) : Function.Periodic f (∑ i : Fin 3, n i • coordinateVector i) := by
  have hsum (s : Finset (Fin 3)) : Function.Periodic f (∑ i ∈ s, n i • coordinateVector i) := by
    induction s using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert i s his ih =>
      simpa only [Finset.sum_insert his] using ((hf i).zsmul (n i)).add_period ih
  simpa using hsum Finset.univ

/-- Each point has a representative in the unit cube with the same value
under every function having the three unit coordinate periods. -/
theorem exists_cube_representative {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i)) (x : Space) :
    ∃ y : Space, (∀ i : Fin 3, y i ∈ Icc (0 : ℝ) 1) ∧ f y = f x := by
  let y : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => Int.fract (x i))
  have hy : ∀ i : Fin 3, y i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨Int.fract_nonneg (x i), (Int.fract_lt_one (x i)).le⟩
  refine ⟨y, hy, ?_⟩
  have hxy : x = y + ∑ i : Fin 3, (⌊x i⌋ : ℤ) • coordinateVector i := by
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    ext j
    change x j = (EuclideanSpace.proj j) (y + ∑ i : Fin 3, (⌊x i⌋ : ℤ) • coordinateVector i)
    simp only [map_add, map_sum, map_zsmul]
    simp [y, coordinateVector, Int.fract_add_floor]
  have hp := periodic_lattice hf (fun i => ⌊x i⌋)
  rw [hxy]
  exact (hp y).symm

theorem periodic_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hp : ∀ x : Space, ∀ i : Fin 3, f (x + coordinateVector i) = f x)
    (x : Space) (i : Fin 3) :
    fderiv ℝ f (x + coordinateVector i) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right (coordinateVector i)]
  exact congrArg (fun g : Space → V => fderiv ℝ g x) (funext (fun y => hp y i))

open PeriodicIntegration

/-- The closed unit cube as a compact subset of `Space`. -/
def cubeImage : Set Space := toSpace '' cube

theorem isCompact_cubeImage : IsCompact cubeImage :=
  (show IsCompact cube from isCompact_Icc).image toSpace.continuous

/-- `exists_cube_representative`, with the representative in `cubeImage`. -/
theorem exists_cubeImage_representative {W : Type*} {f : Space → W}
    (hf : ∀ i : Fin 3, Function.Periodic f (coordinateVector i)) (x : Space) :
    ∃ y ∈ cubeImage, f y = f x := by
  obtain ⟨y, hy, hfy⟩ := exists_cube_representative hf x
  exact ⟨y, ⟨toSpace.symm y, ⟨fun i => (hy i).1, fun i => (hy i).2⟩,
    toSpace.apply_symm_apply y⟩, hfy⟩

/-- Compactness bounds a relatively continuous periodic field on an entire
closed time slab, uniformly over all spatial points. -/
theorem periodic_bound_on_slab {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ (univ : Set Space)))
    (hperiod : UnitSpatialPeriodsOn (Icc a b) g) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x : Space, ‖g (t, x)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_cubeImage).exists_bound_of_continuousOn
    (hg.mono (fun z hz => ⟨hz.1, mem_univ z.2⟩))
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht x
  obtain ⟨z, hz, hzx⟩ := exists_cubeImage_representative
    (f := fun y : Space => g (t, y)) (fun i y => hperiod t ht y i) x
  calc
    ‖g (t, x)‖ = ‖g (t, z)‖ := congrArg norm hzx.symm
    _ ≤ B := hB (t, z) ⟨ht, hz⟩
    _ ≤ max B 1 := le_max_left _ _

theorem component_periodic {f : Space → Space} (hf : UnitPeriods f) (j : Fin 3) :
    UnitPeriods (fun x => f x j) := by
  intro x i
  exact congrArg (fun v : Space => v j) (hf x i)

theorem spatial_partial_periodic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : UnitPeriods f) (i : Fin 3) : UnitPeriods (spatialPartial i f) := by
  intro x j
  exact congrArg (fun A : Space →L[ℝ] V => A (coordinateVector i)) (periodic_fderiv hf x j)

theorem normsq_periodic {f : Space → Space} (hf : UnitPeriods f) :
    UnitPeriods (fun x => ‖f x‖ ^ 2) := by
  intro x i
  exact congrArg (fun v : Space => ‖v‖ ^ 2) (hf x i)

/-- Scalar transport integration by parts, derived from the three
coordinate identities on the unit cube. -/
theorem cubeIntegral_fderiv_apply {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hpf : UnitPeriods f) (hpv : UnitPeriods v) :
    cubeIntegral (fun x => fderiv ℝ f x (v x)) =
      -cubeIntegral (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) := by
  have hleft : (fun x => fderiv ℝ f x (v x)) =
      (fun x => ∑ i : Fin 3, v x i * spatialPartial i f x) := by
    funext x
    exact fderiv_apply_eq_sum f x (v x)
  have hright : (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, f x * spatialPartial i v x i) := by
    funext x
    exact Finset.mul_sum _ _ _
  rw [hleft, hright]
  dsimp only [spatialPartial]
  rw [cubeIntegral_sum Finset.univ _ (fun i _ =>
      (component_contDiff hv i).continuous.fun_mul (spatial_partial_contDiff hf i).continuous),
    cubeIntegral_sum Finset.univ _ (fun i _ =>
      hf.continuous.fun_mul (component_contDiff (spatial_partial_contDiff hv i) i).continuous),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := cubeIntegral_mul_partial ((component_contDiff hv i).of_le (natCast_le_infty 1))
    (hf.of_le (natCast_le_infty 1)) (component_periodic hpv i) hpf i
  simpa only [spatialPartial, fderiv_component hv] using h

theorem cubeIntegral_fderiv_apply_zero {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hpf : UnitPeriods f) (hpv : UnitPeriods v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    cubeIntegral (fun x => fderiv ℝ f x (v x)) = 0 := by
  rw [cubeIntegral_fderiv_apply hf hv hpf hpv]
  simp only [hdiv, mul_zero, cubeIntegral_zero, neg_zero]

/-- Divergence-free transport has zero contribution to the energy. -/
theorem cubeIntegral_transport_energy_zero {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hpw : UnitPeriods w) (hpv : UnitPeriods v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    cubeIntegral (fun x => ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) = 0 := by
  have h := cubeIntegral_fderiv_apply_zero (hw.norm_sq ℝ) hv (normsq_periodic hpw) hpv hdiv
  have hfun : (fun x => fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      (fun x => 2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) := by
    funext x
    exact fderiv_normsq hw x (v x)
  rw [hfun, cubeIntegral_const_mul] at h
  linarith

/-- Vector integration by parts follows from the scalar derivative of
the Euclidean inner product; it is not assumed as an energy identity. -/
theorem cubeIntegral_inner_partial {f g : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : UnitPeriods f) (hpg : UnitPeriods g) (i : Fin 3) :
    cubeIntegral (fun x => ⟪f x, spatialPartial i g x⟫_ℝ) =
      -cubeIntegral (fun x => ⟪spatialPartial i f x, g x⟫_ℝ) := by
  have hp : UnitPeriods (fun x => ⟪f x, g x⟫_ℝ) := by
    intro x j
    change ⟪f (x + coordinateVector j), g (x + coordinateVector j)⟫_ℝ = _
    rw [hpf x j, hpg x j]
  have h := cubeIntegral_partial_eq_zero ((hf.inner ℝ hg).of_le (natCast_le_infty 1)) hp i
  have hfun : spatialPartial i (fun x => ⟪f x, g x⟫_ℝ) =
      (fun x => ⟪f x, spatialPartial i g x⟫_ℝ + ⟪spatialPartial i f x, g x⟫_ℝ) := by
    funext x
    exact fderiv_inner hf hg x (coordinateVector i)
  rw [hfun] at h
  dsimp only [spatialPartial] at h ⊢
  rw [cubeIntegral_add
    (hf.inner ℝ (spatial_partial_contDiff hg i)).continuous
    ((spatial_partial_contDiff hf i).inner ℝ hg).continuous] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The viscosity term is minus the actual integrated sum of squared
coordinate derivatives of the difference field. -/
theorem cubeIntegral_laplacian_energy {w : VelocityField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x)))
    (hpw : UnitPeriods (fun x : Space => w (t, x))) :
    cubeIntegral (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      -(∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2)) := by
  have hsum : cubeIntegral (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      ∑ i : Fin 3, cubeIntegral (fun x =>
        ⟪w (t, x), spatialPartial i (spatialPartial i (fun y => w (t, y))) x⟫_ℝ) := by
    simp only [spatialLaplacian, inner_sum]
    exact cubeIntegral_sum Finset.univ _ (fun i _ =>
      (hw.inner ℝ (spatial_partial_contDiff (spatial_partial_contDiff hw i) i)).continuous)
  rw [hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold spatialPartial
  simpa only [spatialPartial, real_inner_self_eq_norm_sq] using
    cubeIntegral_inner_partial hw (spatial_partial_contDiff hw i) hpw
      (spatial_partial_periodic hpw i) i

/-- Pressure has zero energy contribution when the difference velocity
is divergence free. -/
theorem cubeIntegral_pressure_energy_zero {w : VelocityField} {p : PressureField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hpw : UnitPeriods (fun x : Space => w (t, x)))
    (hpp : UnitPeriods (fun x : Space => p (t, x)))
    (hdiv : ∀ x, spatialDivergence w t x = 0) :
    cubeIntegral (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) = 0 := by
  have hfun : (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) =
      (fun x => fderiv ℝ (fun y => p (t, y)) x (w (t, x))) := by
    funext x
    exact inner_pressureGradient p t x (w (t, x))
  rw [hfun]
  exact cubeIntegral_fderiv_apply_zero hp hw hpp hpw hdiv

theorem unitPeriods_sub {V : Type*} [Sub V] {f g : Space → V}
    (hf : UnitPeriods f) (hg : UnitPeriods g) : UnitPeriods (f - g) := by
  intro x i
  change f (x + coordinateVector i) - g (x + coordinateVector i) = f x - g x
  rw [hf x i, hg x i]

/-- Squared `L²` distance, using the actual unit-cube Lebesgue integral. -/
noncomputable def energy (u v : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => ‖(u - v) (t, x)‖ ^ 2)

noncomputable def energyRate (u v : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ)

noncomputable def dissipation (w : VelocityField) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i (fun y => w (t, y)) x‖ ^ 2)

noncomputable def coupling (u w : VelocityField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x => ⟪w (t, x), spatialDerivative u t x (w (t, x))⟫_ℝ)

theorem energy_nonneg (u v : VelocityField) (t : ℝ) : 0 ≤ energy u v t :=
  cubeIntegral_nonneg (fun _ => sq_nonneg _)

theorem dissipation_nonneg (w : VelocityField) (t : ℝ) : 0 ≤ dissipation w t :=
  Finset.sum_nonneg (fun _ _ => cubeIntegral_nonneg (fun _ => sq_nonneg _))

/-- The exact difference-energy balance, derived from the actual PDE,
pressure cancellation, divergence-free transport, and viscous integration
by parts. No energy inequality is an input. -/
theorem energy_balance {u v : VelocityField} {p q : PressureField} {t : ℝ}
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
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x) :
    energyRate u v t = -2 * dissipation (u - v) t - 2 * coupling u (u - v) t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  have hpw : UnitPeriods (fun x : Space => (u - v) (t, x)) := unitPeriods_sub hpu hpv
  have hdw : ∀ x, spatialDivergence (u - v) t x = 0 := by
    intro x
    rw [spatialDivergence_sub hu hv, hdu x, hdv x, sub_self]
  have hL := (hw.inner ℝ (spatialLaplacian_contDiff hw)).continuous
  have hN := (hw.inner ℝ ((hu.fderiv_right infty_add_one_le_infty).clm_apply hw)).continuous
  have hT := (hw.inner ℝ ((hw.fderiv_right infty_add_one_le_infty).clm_apply hv)).continuous
  have hP := (hw.inner ℝ (pressureGradient_contDiff (p := p - q) (t := t) (hp.sub hq))).continuous
  have hEq : (fun x => ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) =
      (fun x => ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative u t x ((u - v) (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), spatialDerivative (u - v) t x (v (t, x))⟫_ℝ -
        ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) := by
    funext x
    rw [difference_equation hu hv hp hq (htu x) (htv x) (hNS x)]
    simp only [inner_sub_right]
  unfold energyRate
  rw [cubeIntegral_const_mul, hEq]
  change 2 * cubeIntegral (fun x =>
    ⟪(u - v) (t, x), spatialLaplacian (u - v) t x⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => u (t, y)) x ((u - v) (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), fderiv ℝ (fun y => (u - v) (t, y)) x (v (t, x))⟫_ℝ -
    ⟪(u - v) (t, x), pressureGradient (p - q) t x⟫_ℝ) = _
  rw [cubeIntegral_sub ((hL.fun_sub hN).fun_sub hT) hP, cubeIntegral_sub (hL.fun_sub hN) hT,
    cubeIntegral_sub hL hN, cubeIntegral_laplacian_energy hw hpw,
    cubeIntegral_transport_energy_zero hw hv hpw hpv hdv,
    cubeIntegral_pressure_energy_zero hw (hp.sub hq) hpw (unitPeriods_sub hpp hpq) hdw]
  simp only [sub_zero, dissipation, coupling, spatialDerivative]
  ring

/-- Integrating the pointwise nonlinear bound only needs a gradient bound
on the compact unit cube. -/
theorem neg_coupling_le_energy {u v : VelocityField} {t B : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    -coupling u (u - v) t ≤ B * energy u v t := by
  have hw : ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) := hu.sub hv
  unfold coupling energy
  rw [← cubeIntegral_neg, ← cubeIntegral_const_mul]
  apply cubeIntegral_mono_on_cube
    (hw.inner ℝ ((hu.fderiv_right infty_add_one_le_infty).clm_apply hw)).continuous.neg
    (continuous_const.mul (hw.norm_sq ℝ).continuous)
  intro y hy
  exact nonlinear_energy_bound _ _ (hB y hy)

theorem energy_rate_le {u v : VelocityField} {p q : PressureField} {t B : ℝ}
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
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hB : ∀ y ∈ cube, ‖spatialDerivative u t (toSpace y)‖ ≤ B) :
    energyRate u v t ≤ (2 * B) * energy u v t := by
  rw [energy_balance hu hv hp hq hpu hpv hpp hpq hdu hdv htu htv hNS]
  have hc := neg_coupling_le_energy hu hv hB
  have hd := dissipation_nonneg (u - v) t
  nlinarith

theorem energy_continuousOn {a b : ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hv : ContDiffOn ℝ ∞ v (slab a b)) :
    ContinuousOn (energy u v) (Icc a b) := by
  have hF : ContDiffOn ℝ ∞ (fun z : SpaceTime => ‖(u - v) z‖ ^ 2)
      (Icc a b ×ˢ univ) := (hu.sub hv).norm_sq ℝ
  exact cubeIntegral_continuousOn_Icc hF.continuousOn

/-- Differentiation under the genuine spatial integral is justified by
joint smoothness and compactness of the cube. -/
theorem energy_hasDerivAt {a b t : ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (hv : ContDiffOn ℝ ∞ v (slab a b))
    (ht : t ∈ Ioo a b) : HasDerivAt (energy u v) (energyRate u v t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => ‖(u - v) z‖ ^ 2)
      (Ioo a b ×ˢ univ) :=
    (((hu.sub hv).norm_sq ℝ).of_le (natCast_le_infty 1)).mono
      (fun z hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
  have h := hasDerivAt_cubeIntegral_of_contDiffOn isOpen_Ioo hF ht
  have hrate : (fun x => deriv (fun s : ℝ => ‖(u - v) (s, x)‖ ^ 2) t) =
      (fun x => 2 * ⟪(u - v) (t, x), temporalDerivative (u - v) t x⟫_ℝ) := by
    funext x
    exact (energy_density_derivative
      (time_differentiable_at_interior (u := u - v) (hu.sub hv) ht x)).deriv
  rw [hrate] at h
  exact h

theorem energy_initial_zero {u v : VelocityField} {a : ℝ}
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) : energy u v a = 0 := by
  have hzero : (fun x => ‖(u - v) (a, x)‖ ^ 2) = (fun _ : Space => (0 : ℝ)) := by
    funext x
    simp only [Pi.sub_apply, hinitial x, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  unfold energy
  rw [hzero, cubeIntegral_zero]

/-- Zero squared `L²` difference implies equality everywhere, using
continuity on the cube and the explicitly proved periodic representatives. -/
theorem eq_of_energy_zero {u v : VelocityField} {t : ℝ}
    (hu : Continuous (fun x : Space => u (t, x)))
    (hv : Continuous (fun x : Space => v (t, x)))
    (hpu : UnitPeriods (fun x : Space => u (t, x)))
    (hpv : UnitPeriods (fun x : Space => v (t, x)))
    (hzero : energy u v t = 0) (x : Space) : u (t, x) = v (t, x) := by
  have hc := eq_zero_on_cube_of_integral_norm_sq_eq_zero (hu.sub hv) hzero
  have hpw : UnitPeriods (fun z : Space => (u - v) (t, z)) := unitPeriods_sub hpu hpv
  obtain ⟨z, ⟨y, hy, rfl⟩, hzx⟩ := exists_cubeImage_representative
    (f := fun z : Space => (u - v) (t, z)) (fun i y => hpw y i) x
  exact sub_eq_zero.mp (hzx.symm.trans (hc y hy))

/-- Classical uniqueness on a compact time interval for the exact periodic
Navier--Stokes equation of `ProblemStatement`, with viscosity one. Both
solutions have the same force and initial datum. The energy inequality,
uniform gradient bound, and spatial integration identities are conclusions
of the preceding proofs, not assumptions of this theorem. -/
theorem classical_uniqueness_on_Icc {a b : ℝ}
    {u v : VelocityField} {p q : PressureField} {f : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hv : ContDiffOn ℝ ∞ v (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hq : ContDiffOn ℝ ∞ q (slab a b))
    (hpu : UnitSpatialPeriodsOn (Icc a b) u)
    (hpv : UnitSpatialPeriodsOn (Icc a b) v)
    (hpp : UnitSpatialPeriodsOn (Icc a b) p)
    (hpq : UnitSpatialPeriodsOn (Icc a b) q)
    (hdu : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo a b, ∀ x : Space, spatialDivergence v t x = 0)
    (hNSu : ∀ t ∈ Ioo a b, ∀ x : Space, navierStokesResidual u p t x = f (t, x))
    (hNSv : ∀ t ∈ Ioo a b, ∀ x : Space, navierStokesResidual v q t x = f (t, x))
    (hinitial : ∀ x : Space, u (a, x) = v (a, x)) :
    ∀ t ∈ Icc a b, ∀ x : Space, u (t, x) = v (t, x) := by
  by_cases hab : a < b
  · have hcompact : IsCompact (toSpace '' cube) :=
      (show IsCompact cube from isCompact_Icc).image toSpace.continuous
    obtain ⟨B, _, hB⟩ := exists_gradient_bound hab hu hcompact
    have hbound : ∀ t ∈ Ioo a b, energyRate u v t ≤ (2 * B) * energy u v t := by
      intro t ht
      have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
      exact energy_rate_le (spatial_smooth hu ht') (spatial_smooth hv ht')
        (spatial_smooth hp ht') (spatial_smooth hq ht')
        (hpu t ht') (hpv t ht') (hpp t ht') (hpq t ht') (hdu t ht) (hdv t ht)
        (time_differentiable_at_interior hu ht) (time_differentiable_at_interior hv ht)
        (fun x => (hNSu t ht x).trans (hNSv t ht x).symm)
        (fun y hy => hB t ht' (toSpace y) ⟨y, hy, rfl⟩)
    have hzero := GronwallInterior.eq_zero_of_deriv_le hab.le (energy_continuousOn hu hv)
      (energy_initial_zero hinitial) (fun t _ => energy_nonneg u v t)
      (fun t ht => energy_hasDerivAt hu hv ht) hbound
    intro t ht x
    exact eq_of_energy_zero (spatial_smooth hu ht).continuous (spatial_smooth hv ht).continuous
      (hpu t ht) (hpv t ht) (hzero t ht) x
  · intro t ht x
    have ht' : t = a := le_antisymm (ht.2.trans (le_of_not_gt hab)) ht.1
    simpa only [ht'] using hinitial x


end NavierStokes.PeriodicUniqueness
