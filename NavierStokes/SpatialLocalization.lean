import NavierStokes.PeriodicLocalization
import NavierStokes.SolenoidalDiagonal
import NavierStokes.CylindricalResidual
import NavierStokes.ResidualRegularity
import NavierStokes.TimeLocalization

/-!
# Spatial localization through actual Cartesian potentials

The fixed cutoff is a smooth function of `x₀² + x₁²` and `x₂`.  It is one
on an open cylinder containing the origin and has support strictly inside a
unit period cube.  We multiply the potential before taking any curl, and
periodize the resulting potential by the actual locally finite lattice sum.
The pressure is cut and periodized as a scalar.

The conclusions concern the spatial construction and the existing time
activation.  No terminal residual limit is assumed or asserted here.
-/

namespace NavierStokes.SpatialLocalization

noncomputable section

open ProblemStatement Set Filter
open AxisymmetricFields (projection)
open scoped ContDiff Topology

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- Squared distance to the symmetry axis, with no square-root singularity. -/
noncomputable def radialSquare (x : Space) : ℝ := (x 0) ^ 2 + (x 1) ^ 2

theorem radialSquare_nonneg (x : Space) : 0 ≤ radialSquare x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem radialSquare_contDiff : ContDiff ℝ ∞ radialSquare :=
  ((projection 0).contDiff.pow 2).add ((projection 1).contDiff.pow 2)

/-- A globally smooth profile in squared radius and axial position. -/
noncomputable def cutoffProfile (p : ℝ × ℝ) : ℝ :=
  SmoothCutoffs.cutoff (16 * p.1) * SmoothCutoffs.cutoff (4 * p.2)

theorem cutoffProfile_contDiff : ContDiff ℝ ∞ cutoffProfile :=
  (SmoothCutoffs.cutoff_contDiff.comp (contDiff_const.mul contDiff_fst)).mul
    (SmoothCutoffs.cutoff_contDiff.comp (contDiff_const.mul contDiff_snd))

/-- The explicit spatial cutoff used in both the potential and the pressure. -/
noncomputable def spatialCutoff (x : Space) : ℝ :=
  cutoffProfile (radialSquare x, x 2)

theorem spatialCutoff_contDiff : ContDiff ℝ ∞ spatialCutoff :=
  cutoffProfile_contDiff.comp (radialSquare_contDiff.prodMk (projection 2).contDiff)



/-- The closed support cylinder has radius `1/4` and height `1/2`. -/
noncomputable def supportCylinder : Set Space :=
  {x | radialSquare x ≤ 1 / 16 ∧ |x 2| ≤ 1 / 4}

theorem isClosed_supportCylinder : IsClosed supportCylinder :=
  (isClosed_le radialSquare_contDiff.continuous continuous_const).inter
    (isClosed_le (projection 2).continuous.abs continuous_const)

theorem isCompact_supportCylinder : IsCompact supportCylinder := by
  convert! AxisymmetricFields.isCompact_cylinder (1 / 32) (1 / 4) using 1
  ext x
  simp only [supportCylinder, Set.mem_ofPred_eq, AxisymmetricFields.radialEnergy, radialSquare]
  constructor <;> intro hx <;> constructor
  · linarith [hx.1]
  · exact hx.2
  · linarith [hx.1]
  · exact hx.2

theorem spatialCutoff_support_subset : Function.support spatialCutoff ⊆ supportCylinder := by
  intro x hx
  have hprod : SmoothCutoffs.cutoff (16 * radialSquare x) *
      SmoothCutoffs.cutoff (4 * x 2) ≠ 0 := hx
  have hr : 16 * radialSquare x < 1 := by
    by_contra h
    exact (mul_ne_zero_iff.mp hprod).1
      (SmoothCutoffs.cutoff_zero_of_one_le (le_of_not_gt h))
  have hz : |4 * x 2| < 1 := by
    by_contra h
    exact (mul_ne_zero_iff.mp hprod).2
      (SmoothCutoffs.cutoff_zero_of_one_le_abs (le_of_not_gt h))
  simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)] at hz
  exact ⟨by linarith, by linarith⟩

theorem spatialCutoff_tsupport_subset : tsupport spatialCutoff ⊆ supportCylinder :=
  closure_minimal spatialCutoff_support_subset isClosed_supportCylinder


theorem supportCylinder_coordinate_bound {x : Space} (hx : x ∈ supportCylinder)
    (i : Fin 3) : |x i| ≤ 1 / 4 := by
  have hr := hx.1
  change (x 0) ^ 2 + (x 1) ^ 2 ≤ 1 / 16 at hr
  fin_cases i
  · change |x 0| ≤ 1 / 4
    have hs : |x 0| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0)]
  · change |x 1| ≤ 1 / 4
    have hs : |x 1| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1)]
  · exact hx.2


/-- An open cylinder on which the cutoff is identically one. -/
noncomputable def plateau : Set Space := {x | radialSquare x < 1 / 32 ∧ |x 2| < 1 / 8}

theorem isOpen_plateau : IsOpen plateau :=
  (isOpen_lt radialSquare_contDiff.continuous continuous_const).inter
    (isOpen_lt (projection 2).continuous.abs continuous_const)

theorem zero_mem_plateau : (0 : Space) ∈ plateau := by
  norm_num [plateau, radialSquare]

theorem spatialCutoff_eq_one {x : Space} (hx : x ∈ plateau) : spatialCutoff x = 1 := by
  have hr : |16 * radialSquare x| ≤ 1 / 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (radialSquare_nonneg x))]
    linarith [hx.1]
  have hz : |4 * x 2| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith [hx.2]
  simp only [spatialCutoff, cutoffProfile, SmoothCutoffs.cutoff_one_of_abs_le hr,
    SmoothCutoffs.cutoff_one_of_abs_le hz, one_mul]

theorem spatialCutoff_eventually_one {x : Space} (hx : x ∈ plateau) :
    spatialCutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_plateau.mem_nhds hx] with y hy
  exact spatialCutoff_eq_one hy

theorem plateau_subset_innerCube : plateau ⊆ PeriodicLocalization.innerCube (1 / 4) := by
  intro x hx i
  have hb : x ∈ supportCylinder := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have := supportCylinder_coordinate_bound hb i
  linarith

/-- Multiplication of the actual Cartesian potential, before any curl. -/
noncomputable def cutPotential (A : VelocityField) : VelocityField :=
  fun z => spatialCutoff z.2 • A z

noncomputable def cutPressure (p : PressureField) : PressureField :=
  fun z => spatialCutoff z.2 * p z

noncomputable def cutVelocity (A : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (cutPotential A)

theorem cutPotential_supported (A : VelocityField) :
    PeriodicLocalization.SupportedInCube (1 / 4) (cutPotential A) := by
  intro z hz i
  have hc : spatialCutoff z.2 ≠ 0 := by
    intro h
    exact hz (by simp only [cutPotential, h, zero_smul])
  exact supportCylinder_coordinate_bound (spatialCutoff_support_subset hc) i

theorem cutPressure_supported (p : PressureField) :
    PeriodicLocalization.SupportedInCube (1 / 4) (cutPressure p) := by
  intro z hz i
  have hc : spatialCutoff z.2 ≠ 0 := by
    intro h
    exact hz (by simp only [cutPressure, h, zero_mul])
  exact supportCylinder_coordinate_bound (spatialCutoff_support_subset hc) i

theorem cutVelocity_tsupport (A : VelocityField) (t : ℝ) :
    tsupport (fun x => cutVelocity A (t, x)) ⊆ supportCylinder :=
  (SpatialCurl.tsupport_curl_cutoff_subset spatialCutoff (fun x => A (t, x))).trans
    spatialCutoff_tsupport_subset



/-- The actual lattice sum of the cut potential. -/
noncomputable def periodicPotential (A : VelocityField) : VelocityField :=
  PeriodicLocalization.periodize (cutPotential A)

noncomputable def periodicVelocity (A : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (periodicPotential A)

noncomputable def periodicPressure (p : PressureField) : PressureField :=
  PeriodicLocalization.periodize (cutPressure p)



theorem periodicPotential_smoothOn {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicPotential A) (times ×ˢ (univ : Set Space)) :=
  PeriodicLocalization.contDiffOn_periodize (cutPotential_supported A)
    ((spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.smul hA)

theorem periodicVelocity_smoothOn {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicVelocity A) (times ×ˢ (univ : Set Space)) :=
  SpatialCurl.contDiffOn_spatialCurl (periodicPotential_smoothOn hA) (by simp)

theorem periodicPressure_smoothOn {p : PressureField} {times : Set ℝ}
    (hp : ContDiffOn ℝ ∞ p (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicPressure p) (times ×ˢ (univ : Set Space)) :=
  PeriodicLocalization.contDiffOn_periodize (cutPressure_supported p)
    ((spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.mul hp)

theorem periodicPotential_periodic (A : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicPotential A) :=
  PeriodicLocalization.unitSpatialPeriodsOn_periodize (cutPotential A) times

theorem periodicVelocity_periodic (A : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicVelocity A) :=
  SpatialCurl.spatialCurl_periodic (periodicPotential_periodic A times)

theorem periodicPressure_periodic (p : PressureField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicPressure p) :=
  PeriodicLocalization.unitSpatialPeriodsOn_periodize (cutPressure p) times

theorem periodicVelocity_divergence_free {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) {t : ℝ}
    (ht : t ∈ times) (x : Space) : spatialDivergence (periodicVelocity A) t x = 0 :=
  SpatialCurl.spatialDivergence_spatialCurl_on
    ((periodicPotential_smoothOn hA).of_le (nat_le_infty 2)) ht x

/-- Throughout the central no-overlap cube, periodization agrees locally
with the actual cut field, including its cutoff derivative terms. -/
theorem periodicVelocity_eventuallyEq_cut (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicVelocity A =ᶠ[𝓝 z] cutVelocity A :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq
    (PeriodicLocalization.periodize_eventuallyEq (cutPotential_supported A) hz)

theorem periodicPressure_eventuallyEq_cut (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicPressure p =ᶠ[𝓝 z] cutPressure p :=
  PeriodicLocalization.periodize_eventuallyEq (cutPressure_supported p) hz

theorem periodic_residual_eventuallyEq_cut (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    (fun w => navierStokesResidual (periodicVelocity A) (periodicPressure p) w.1 w.2)
      =ᶠ[𝓝 z] (fun w => navierStokesResidual (cutVelocity A) (cutPressure p) w.1 w.2) :=
  ResidualRegularity.residual_eventuallyEq (periodicVelocity_eventuallyEq_cut A hz)
    (periodicPressure_eventuallyEq_cut p hz)


theorem cutPotential_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : cutPotential A =ᶠ[𝓝 z] A := by
  have he := (spatialCutoff_eventually_one hz).comp_tendsto continuous_snd.continuousAt
  filter_upwards [he] with w hw
  change spatialCutoff w.2 = 1 at hw
  simp only [cutPotential, hw, one_smul]

theorem cutPressure_eventuallyEq (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : cutPressure p =ᶠ[𝓝 z] p := by
  have he := (spatialCutoff_eventually_one hz).comp_tendsto continuous_snd.continuousAt
  filter_upwards [he] with w hw
  change spatialCutoff w.2 = 1 at hw
  simp only [cutPressure, hw, one_mul]

/-- Local equality includes all nearby physical times and all spatial directions. -/
theorem periodicPotential_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : periodicPotential A =ᶠ[𝓝 z] A :=
  (PeriodicLocalization.periodize_eventuallyEq (cutPotential_supported A)
    (plateau_subset_innerCube hz)).trans (cutPotential_eventuallyEq A hz)

theorem periodicVelocity_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : periodicVelocity A =ᶠ[𝓝 z] SpatialCurl.spatialCurl A :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq (periodicPotential_eventuallyEq A hz)

theorem periodicPressure_eventuallyEq (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : periodicPressure p =ᶠ[𝓝 z] p :=
  (PeriodicLocalization.periodize_eventuallyEq (cutPressure_supported p)
    (plateau_subset_innerCube hz)).trans (cutPressure_eventuallyEq p hz)

theorem periodicVelocity_eq (A : VelocityField) {z : SpaceTime} (hz : z.2 ∈ plateau) :
    periodicVelocity A z = SpatialCurl.spatialCurl A z :=
  (periodicVelocity_eventuallyEq A hz).self_of_nhds







theorem periodicVelocity_origin (A : VelocityField) (t : ℝ) :
    periodicVelocity A (t, 0) = SpatialCurl.spatialCurl A (t, 0) :=
  periodicVelocity_eq A zero_mem_plateau



/-- The previously constructed time switch is applied to the spatially
localized fields.  It is independent of the spatial variables. -/
noncomputable def localizedVelocity (A : VelocityField) : VelocityField :=
  TimeLocalization.activatedVelocity (periodicVelocity A)

noncomputable def localizedPressure (p : PressureField) : PressureField :=
  TimeLocalization.activatedPressure (periodicPressure p)















theorem localizedVelocity_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) :
    localizedVelocity A =ᶠ[𝓝 z] SpatialCurl.spatialCurl A :=
  (TimeLocalization.activatedVelocity_eventuallyEq_late _ ht z.2).trans
    (periodicVelocity_eventuallyEq A hz)

theorem localizedPressure_eventuallyEq (p : PressureField) {z : SpaceTime}
    (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) :
    localizedPressure p =ᶠ[𝓝 z] p :=
  (TimeLocalization.activatedPressure_eventuallyEq_late _ ht z.2).trans
    (periodicPressure_eventuallyEq p hz)

theorem localizedVelocity_eq (A : VelocityField) {z : SpaceTime}
    (ht : 3 / 4 ≤ z.1) (hz : z.2 ∈ plateau) :
    localizedVelocity A z = SpatialCurl.spatialCurl A z := by
  rw [localizedVelocity, TimeLocalization.activatedVelocity_eq_late _ ht,
    periodicVelocity_eq A hz]








theorem localizedVelocity_origin (A : VelocityField) {t : ℝ} (ht : 3 / 4 ≤ t) :
    localizedVelocity A (t, 0) = SpatialCurl.spatialCurl A (t, 0) :=
  localizedVelocity_eq A ht zero_mem_plateau

theorem localizedVelocity_origin_blowup (A : VelocityField)
    (hA : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    Tendsto (fun t : ℝ => ‖localizedVelocity A (t, 0)‖) (𝓝[<] 1) atTop := by
  apply hA.congr'
  have hlate : ∀ᶠ t in 𝓝[<] (1 : ℝ), 3 / 4 < t :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [hlate] with t ht
  rw [localizedVelocity_origin A ht.le]

private theorem unbounded_of_origin_blowup {u : VelocityField}
    (hu : Tendsto (fun t : ℝ => ‖u (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne u := by
  intro M _ δ hδ
  have hlow : Ioi (max 0 (1 - δ)) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (max_lt (by norm_num) (by linarith)))
  have hlarge : ∀ᶠ t in 𝓝[<] (1 : ℝ), M < ‖u (t, 0)‖ :=
    hu.eventually (eventually_gt_atTop M)
  have hbefore : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t, ht, hMt, hlo⟩ := (hbefore.and (hlarge.and hlow)).exists
  exact ⟨t, 0, ⟨(le_max_left _ _).trans_lt hlo, ht⟩,
    (le_max_right _ _).trans_lt hlo, hMt⟩

theorem localizedVelocity_speed_unbounded (A : VelocityField)
    (hA : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne (localizedVelocity A) :=
  unbounded_of_origin_blowup (localizedVelocity_origin_blowup A hA)


end

end NavierStokes.SpatialLocalization
