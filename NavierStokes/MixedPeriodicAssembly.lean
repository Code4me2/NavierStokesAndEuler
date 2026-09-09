import NavierStokes.R3CompactCandidate
import NavierStokes.JointResidualLimits
import NavierStokes.SpatialLocalization
import NavierStokes.DirectAngularDiagonal
import Mathlib.Algebra.Order.Round

/-!
# The compact candidate from the mixed sums, and its lattice periodization

The manuscript cuts direct angular means as vector fields, separately from
the potentials whose curls give the other components.  The construction here
keeps that distinction (`cutVelocity`).  The existing spatial cutoff is
axisymmetric; its action on direct angular means can therefore be supplied by
the angular-field calculus.  No compactly supported potential for an arbitrary
angular mean is postulated.

The inputs are the original mixed fields `A`, `v`, `p`, smooth before time
one, their one-sided extensions off the origin, and the joint vanishing of the
residual jets at the origin.  The order of construction is:

1. the compact whole-space candidate on the cut fields, supported in
   `SpatialLocalization.supportCylinder` (`exists_compact_candidate`, through
   `R3CompactCandidate.of_limits`); the force's jets at time one are the
   boundary limits of the cut residual (`JointResidualLimits.boundaryLimits`);
2. the periodic candidate as the lattice sum of the compact one
   (`candidate_of_periodization`, `exists_candidate_force`).

The support cylinder lies in `PeriodicLocalization.innerCube (1/4)`, so the
lattice translates of the cut fields have disjoint supports: the periodized
fields agree with a single translate near every point, and every property of
the periodic candidate is checked on one copy after moving the point to its
fundamental-cube representative.  Nothing here establishes the correction
iteration or the existence of the singular incoming fields.
-/

noncomputable section

namespace NavierStokes.MixedPeriodicAssembly

open ProblemStatement Set Filter
open scoped Topology ContDiff BigOperators

/-- The direct field is added after taking the curl. -/
def velocity (A v : VelocityField) : VelocityField :=
  fun z => SpatialCurl.spatialCurl A z + v z

/-- Spatial localization keeps every potential-cutoff derivative. -/
def cutVelocity (A v : VelocityField) : VelocityField :=
  fun z => SpatialLocalization.cutVelocity A z + SpatialLocalization.cutPotential v z

/-- Periodize the cut potential and the cut direct field separately. -/
def periodicVelocity (A v : VelocityField) : VelocityField :=
  fun z => SpatialLocalization.periodicVelocity A z +
    PeriodicLocalization.periodize (SpatialLocalization.cutPotential v) z

def originalResidual (A v : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (velocity A v) p z.1 z.2

def cutResidual (A v : VelocityField) (p : PressureField) : VelocityField :=
  fun z => navierStokesResidual (cutVelocity A v)
    (SpatialLocalization.cutPressure p) z.1 z.2

/-! ## Fundamental-cube representatives -/

/-- The nearest lattice point to `x`; `representative x` is `x` moved into the
inner cube by that lattice translation. Its discontinuities are harmless: it is
only used to evaluate periodic fields at one point of each lattice orbit. -/
def nearestIndex (x : Space) : Fin 3 → ℤ := fun i => round (x i)

def representative (x : Space) : Space :=
  x - CompactForceDecay.integerShift (nearestIndex x)

theorem representative_mem_innerCube (x : Space) :
    representative x ∈ PeriodicLocalization.innerCube (1 / 4) := by
  intro i
  have h := abs_sub_round (x i)
  change |(representative x) i| < 1 - 1 / 4
  simp only [representative, PiLp.sub_apply, CompactForceDecay.integerShift_apply, nearestIndex]
  linarith

@[simp] theorem representative_zero : representative (0 : Space) = 0 := by
  ext i
  simp [representative, nearestIndex, CompactForceDecay.integerShift_apply]

/-- A field with unit spatial periods at time `t` takes the same value at a
point and at its representative. -/
theorem eq_representative {V : Type*} {g : SpaceTime → V} {times : Set ℝ}
    (hg : UnitSpatialPeriodsOn times g) {t : ℝ} (ht : t ∈ times) (x : Space) :
    g (t, representative x) = g (t, x) :=
  (CompactForceDecay.periodic_integerShift (g := fun z : SpaceTime => g (t, z.2))
    (fun _ _ y i => hg t ht y i) t (nearestIndex x)).sub_eq x

/-! ## Smoothness, periods and local agreement of the periodized fields -/

theorem periodicVelocity_smoothOn {A v : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicVelocity A v) (times ×ˢ (univ : Set Space)) :=
  (SpatialLocalization.periodicVelocity_smoothOn hA).add
    (PeriodicLocalization.contDiffOn_periodize (SpatialLocalization.cutPotential_supported v)
      ((SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.smul hv))

theorem periodicVelocity_periodic (A v : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicVelocity A v) := by
  intro t ht x i
  simp only [periodicVelocity,
    SpatialLocalization.periodicVelocity_periodic A times t ht x i,
    PeriodicLocalization.unitSpatialPeriodsOn_periodize
      (SpatialLocalization.cutPotential v) times t ht x i]

theorem periodicVelocity_eventuallyEq_cut (A v : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicVelocity A v =ᶠ[𝓝 z] cutVelocity A v :=
  (SpatialLocalization.periodicVelocity_eventuallyEq_cut A hz).add
    (PeriodicLocalization.periodize_eventuallyEq
      (SpatialLocalization.cutPotential_supported v) hz)

theorem cutVelocity_eventuallyEq (A v : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ SpatialLocalization.plateau) :
    cutVelocity A v =ᶠ[𝓝 z] velocity A v :=
  (SolenoidalDiagonal.spatialCurl_eventuallyEq
    (SpatialLocalization.cutPotential_eventuallyEq A hz)).add
      (SpatialLocalization.cutPotential_eventuallyEq v hz)

theorem periodicVelocity_eventuallyEq (A v : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ SpatialLocalization.plateau) :
    periodicVelocity A v =ᶠ[𝓝 z] velocity A v :=
  (periodicVelocity_eventuallyEq_cut A v (SpatialLocalization.plateau_subset_innerCube hz)).trans
    (cutVelocity_eventuallyEq A v hz)

theorem periodicVelocity_origin (A v : VelocityField) (t : ℝ) :
    periodicVelocity A v (t, 0) = velocity A v (t, 0) :=
  (periodicVelocity_eventuallyEq A v SpatialLocalization.zero_mem_plateau).self_of_nhds

theorem cutVelocity_origin (A v : VelocityField) (t : ℝ) :
    cutVelocity A v (t, 0) = velocity A v (t, 0) :=
  (cutVelocity_eventuallyEq A v SpatialLocalization.zero_mem_plateau).self_of_nhds

theorem activated_periodicVelocity_eventuallyEq_cut (A v : VelocityField) (z : SpaceTime)
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    TimeLocalization.activatedVelocity (periodicVelocity A v) =ᶠ[𝓝 z]
      TimeLocalization.activatedVelocity (cutVelocity A v) := by
  filter_upwards [periodicVelocity_eventuallyEq_cut A v hz] with w hw
  simp only [TimeLocalization.activatedVelocity, hw]

theorem activated_periodicPressure_eventuallyEq_cut (p : PressureField) (z : SpaceTime)
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p) =ᶠ[𝓝 z]
      TimeLocalization.activatedPressure (SpatialLocalization.cutPressure p) := by
  filter_upwards [SpatialLocalization.periodicPressure_eventuallyEq_cut p hz] with w hw
  simp only [TimeLocalization.activatedPressure, hw]

theorem cutResidual_eventuallyEq_original (A v : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ SpatialLocalization.plateau) :
    cutResidual A v p =ᶠ[𝓝 z] originalResidual A v p :=
  ResidualRegularity.residual_eventuallyEq (cutVelocity_eventuallyEq A v hz)
    (SpatialLocalization.cutPressure_eventuallyEq p hz)

theorem spatialDivergence_congr {u v : VelocityField} {z : SpaceTime}
    (he : u =ᶠ[𝓝 z] v) : spatialDivergence u z.1 z.2 = spatialDivergence v z.1 z.2 := by
  unfold spatialDivergence spatialDerivative
  rw [ResidualRegularity.space_fderiv_congr he]

theorem spatialDivergence_periodic {u : VelocityField} {times : Set ℝ}
    (hu : UnitSpatialPeriodsOn times u) :
    UnitSpatialPeriodsOn times (fun z => spatialDivergence u z.1 z.2) := by
  intro t ht x i
  unfold spatialDivergence spatialDerivative
  have he := ResidualRegularity.space_fderiv_periods hu t ht x i
  dsimp only at he ⊢
  rw [he]

theorem spatialDivergence_add {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) x)
    (hv : DifferentiableAt ℝ (fun y => v (t, y)) x) :
    spatialDivergence (fun z => u z + v z) t x =
      spatialDivergence u t x + spatialDivergence v t x := by
  simp only [spatialDivergence, spatialDerivative, fderiv_fun_add hu hv,
    _root_.add_apply, PiLp.add_apply, Finset.sum_add_distrib]

/-! ## The cut fields: smoothness, support, divergence, blowup -/

theorem cutVelocity_smoothOn {A v : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (cutVelocity A v) (times ×ˢ (univ : Set Space)) := by
  have hc : ContDiffOn ℝ ∞ (fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2)
      (times ×ˢ (univ : Set Space)) :=
    (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn
  exact (SpatialCurl.contDiffOn_spatialCurl (hc.smul hA) (by simp)).add (hc.smul hv)

theorem cutPressure_smoothOn {p : PressureField} {times : Set ℝ}
    (hp : ContDiffOn ℝ ∞ p (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (SpatialLocalization.cutPressure p) (times ×ˢ (univ : Set Space)) :=
  (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.mul hp

theorem cutVelocity_zero_outside (A v : VelocityField) (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) : cutVelocity A v (t, x) = 0 := by
  have hcurl : SpatialLocalization.cutVelocity A (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => SpatialLocalization.cutVelocity A (t, y))
      (fun hm => hx (SpatialLocalization.cutVelocity_tsupport A t hm))
  have hc : SpatialLocalization.spatialCutoff x = 0 := by
    by_contra hn
    exact hx (SpatialLocalization.spatialCutoff_support_subset hn)
  simp [cutVelocity, SpatialLocalization.cutPotential, hcurl, hc]

theorem cutPressure_zero_outside (p : PressureField) (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) :
    SpatialLocalization.cutPressure p (t, x) = 0 := by
  have hc : SpatialLocalization.spatialCutoff x = 0 := by
    by_contra hn
    exact hx (SpatialLocalization.spatialCutoff_support_subset hn)
  simp [SpatialLocalization.cutPressure, hc]

theorem activated_cutVelocity_zero_outside (A v : VelocityField) (t : ℝ) {x : Space}
    (hx : x ∉ SpatialLocalization.supportCylinder) :
    TimeLocalization.activatedVelocity (cutVelocity A v) (t, x) = 0 := by
  simp [TimeLocalization.activatedVelocity, cutVelocity_zero_outside A v t hx]

/-- Vanishing off the support cylinder is a support bound in the cube of
half-width `1/4`, the bound `PeriodicLocalization` needs. -/
theorem supportedInCube_of_zero_outside {V : Type*} [NormedAddCommGroup V] {g : SpaceTime → V}
    (hg : ∀ t : ℝ, ∀ x : Space, x ∉ SpatialLocalization.supportCylinder → g (t, x) = 0) :
    PeriodicLocalization.SupportedInCube (1 / 4) g := by
  intro z hz i
  refine SpatialLocalization.supportCylinder_coordinate_bound ?_ i
  by_contra hx
  exact hz (hg z.1 z.2 hx)

/-- The angular-field calculus supplies `hd` from axisymmetry; the curl
component introduces no divergence. -/
theorem cutVelocity_divergence_free {A v : VelocityField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hd : ∀ t < 1, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    {t : ℝ} (ht : t < 1) (x : Space) : spatialDivergence (cutVelocity A v) t x = 0 := by
  have hc : ContDiffOn ℝ ∞ (fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2)
      (Iio 1 ×ˢ (univ : Set Space)) :=
    (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn
  have hleft := SpatialCurl.contDiff_spatialSlice
    (SpatialCurl.contDiffOn_spatialCurl (m := ∞) (hc.smul hA) (by simp)) ht
  have hright := SpatialCurl.contDiff_spatialSlice (hc.smul hv) ht
  change spatialDivergence (fun z =>
    SpatialCurl.spatialCurl ((fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2) • A) z +
      ((fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2) • v) z) t x = 0
  rw [spatialDivergence_add
    (hleft.differentiable (by simp) x) (hright.differentiable (by simp) x),
    SpatialCurl.spatialDivergence_spatialCurl_on ((hc.smul hA).of_le (natCast_le_infty 2)) ht x]
  change 0 + spatialDivergence (SpatialLocalization.cutPotential v) t x = 0
  rw [hd t ht x, add_zero]

theorem cutVelocity_speed_unbounded {A v : VelocityField}
    (haxis : Tendsto (fun t : ℝ => ‖velocity A v (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne (cutVelocity A v) := by
  have hb : Tendsto (fun t : ℝ => ‖cutVelocity A v (t, 0)‖) (𝓝[<] 1) atTop := by
    simpa only [cutVelocity_origin] using haxis
  intro M _ δ hδ
  have hlow : Ioi (max 0 (1 - δ)) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (max_lt (by norm_num) (by linarith)))
  have hlarge := hb.eventually (eventually_gt_atTop M)
  have hbefore : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t, ht, hMt, hlo⟩ := (hbefore.and (hlarge.and hlow)).exists
  exact ⟨t, 0, ⟨(le_max_left _ _).trans_lt hlo, ht⟩,
    (le_max_right _ _).trans_lt hlo, hMt⟩

/-! ## The residual of the cut fields: local extensions and jets -/

theorem cutResidual_smoothOn {A v : VelocityField} {p : PressureField} {U : Set SpaceTime}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hv : ContDiffOn ℝ ∞ v U) (hp : ContDiffOn ℝ ∞ p U) :
    ContDiffOn ℝ ∞ (cutResidual A v p) U := by
  have hc : ContDiffOn ℝ ∞ (fun z : SpaceTime => SpatialLocalization.spatialCutoff z.2) U :=
    (SpatialLocalization.spatialCutoff_contDiff.comp contDiff_snd).contDiffOn
  have hAc : ContDiffOn ℝ ∞ (SpatialLocalization.cutPotential A) U := hc.smul hA
  have hcurl : ContDiffOn ℝ ∞ (SpatialLocalization.cutVelocity A) U := by
    intro z hz
    exact (SpatialCurl.contDiffAt_spatialCurl
      (hAc.contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt
  exact ResidualRegularity.contDiffOn_residual hU (hcurl.add (hc.smul hv)) (hc.mul hp)

theorem cutResidual_eventuallyEq {A A' v v' : VelocityField} {p p' : PressureField}
    {z : SpaceTime} (hA : A =ᶠ[𝓝 z] A') (hv : v =ᶠ[𝓝 z] v') (hp : p =ᶠ[𝓝 z] p') :
    cutResidual A v p =ᶠ[𝓝 z] cutResidual A' v' p' := by
  have hAc : SpatialLocalization.cutPotential A =ᶠ[𝓝 z]
      SpatialLocalization.cutPotential A' := by
    filter_upwards [hA] with w hw
    simp only [SpatialLocalization.cutPotential, hw]
  have hvc : SpatialLocalization.cutPotential v =ᶠ[𝓝 z]
      SpatialLocalization.cutPotential v' := by
    filter_upwards [hv] with w hw
    simp only [SpatialLocalization.cutPotential, hw]
  have hpc : SpatialLocalization.cutPressure p =ᶠ[𝓝 z]
      SpatialLocalization.cutPressure p' := by
    filter_upwards [hp] with w hw
    simp only [SpatialLocalization.cutPressure, hw]
  exact ResidualRegularity.residual_eventuallyEq
    ((SolenoidalDiagonal.spatialCurl_eventuallyEq hAc).add hvc) hpc

/-- All three original components have genuine smooth local extensions. -/
def cutResidualExtension {A v : VelocityField} {p : PressureField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (ev : JointResidualLimits.OneSidedExtension v x)
    (ep : JointResidualLimits.OneSidedExtension p x) :
    JointResidualLimits.OneSidedExtension (cutResidual A v p) x where
  value := cutResidual eA.value ev.value ep.value
  domain := (eA.domain ∩ ev.domain) ∩ ep.domain
  isOpen := (eA.isOpen.inter ev.isOpen).inter ep.isOpen
  mem := ⟨⟨eA.mem, ev.mem⟩, ep.mem⟩
  smooth := cutResidual_smoothOn ((eA.isOpen.inter ev.isOpen).inter ep.isOpen)
    (eA.smooth.mono (fun _ h => h.1.1)) (ev.smooth.mono (fun _ h => h.1.2))
    (ep.smooth.mono inter_subset_right)
  agrees := by
    intro z hz
    have hO := (((eA.isOpen.inter ev.isOpen).inter ep.isOpen).inter
      (SpacetimeEndpoint.openPast_isOpen 1))
    apply (cutResidual_eventuallyEq (z := z) ?_ ?_ ?_).self_of_nhds
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact eA.agrees ⟨hw.1.1.1, hw.2⟩
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact ev.agrees ⟨hw.1.1.2, hw.2⟩
    · filter_upwards [hO.mem_nhds hz] with w hw
      exact ep.agrees ⟨hw.1.2, hw.2⟩

theorem cutResidual_awayExtensions {A v : VelocityField} {p : PressureField}
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) :
    JointResidualLimits.AwayExtensions (cutResidual A v p) := by
  intro x hx
  exact ⟨cutResidualExtension (Classical.choice (eA x hx)) (Classical.choice (ev x hx))
    (Classical.choice (ep x hx))⟩

theorem cutResidual_vanishingJointJets {A v : VelocityField} {p : PressureField}
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p)) :
    JointResidualLimits.VanishingJointJets (cutResidual A v p) := by
  intro n
  apply (hz n).congr'
  exact ((SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (cutResidual_eventuallyEq_original A v p (z := (1, 0))
      SpatialLocalization.zero_mem_plateau) n).filter_mono nhdsWithin_le_nhds).symm

/-- The jets of the periodic force at time one: the boundary limits of the
cut residual, read at the representative of each point. At every lattice
copy of the singular point they vanish. -/
def boundaryLimits (A v : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (x : Space) :
    FormalMultilinearSeries ℝ SpaceTime Space :=
  JointResidualLimits.boundaryLimits (cutResidual A v p)
    (cutResidual_awayExtensions eA ev ep) (representative x)

@[simp] theorem boundaryLimits_zero (A v : VelocityField) (p : PressureField)
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p) (n : ℕ) :
    boundaryLimits A v p eA ev ep 0 n = 0 := by
  simp only [boundaryLimits, representative_zero, JointResidualLimits.boundaryLimits_zero]

/-! ## The compact candidate -/

/-- The compact whole-space candidate on the cut fields. Its force is the
Taylor--Borel extension of the cut residual, supported in the cube of
half-width `1/4` at every time, with the boundary limits of the cut residual
as its jets at time one. The two inputs beyond smoothness and the residual
limits, divergence-freeness and unbounded speed of the activated cut velocity,
are supplied by `cutVelocity_divergence_free` and `cutVelocity_speed_unbounded`
in the construction. The compact candidate is recorded in witness data before
periodization and later extracted by
`R3CompactCandidate.selected_compact_candidate`. -/
theorem exists_compact_candidate {A v : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p)
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (TimeLocalization.activatedVelocity (cutVelocity A v)) t x = 0)
    (hunbounded : SpeedUnboundedAtOne (TimeLocalization.activatedVelocity (cutVelocity A v))) :
    ∃ F : VelocityField,
      R3CompactCandidate.Properties (TimeLocalization.activatedVelocity (cutVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.cutPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      PeriodicLocalization.SupportedInCube (1 / 4) F ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (1, x) =
        JointResidualLimits.boundaryLimits (cutResidual A v p)
          (cutResidual_awayExtensions eA ev ep) x n) := by
  have hu : ContDiffOn ℝ ∞ (cutVelocity A v) preSingularDomain :=
    cutVelocity_smoothOn (hA.mono (fun _ h => ⟨h.1.2, h.2⟩)) (hv.mono (fun _ h => ⟨h.1.2, h.2⟩))
  have hpc : ContDiffOn ℝ ∞ (SpatialLocalization.cutPressure p) preSingularDomain :=
    cutPressure_smoothOn (hp.mono (fun _ h => ⟨h.1.2, h.2⟩))
  let L := JointResidualLimits.boundaryLimits (cutResidual A v p)
    (cutResidual_awayExtensions eA ev ep)
  have hlim : CandidateFromLimits.ResidualLimits (cutVelocity A v)
      (SpatialLocalization.cutPressure p) L := by
    intro n
    apply JointResidualLimits.locallyUniform_of_joint_limits
      (F := iteratedFDeriv ℝ n (cutResidual A v p))
    intro x
    simpa only [JointResidualLimits.past_filter] using
      JointResidualLimits.boundaryLimits_joint (cutResidual_vanishingJointJets hz)
        (cutResidual_awayExtensions eA ev ep) n x
  have hus : ∀ t : ℝ, ∀ x : Space, x ∉ SpatialLocalization.supportCylinder →
      cutVelocity A v (t, x) = 0 := fun t x hx => cutVelocity_zero_outside A v t hx
  have hps : ∀ t : ℝ, ∀ x : Space, x ∉ SpatialLocalization.supportCylinder →
      SpatialLocalization.cutPressure p (t, x) = 0 := fun t x hx => cutPressure_zero_outside p t hx
  refine ⟨CandidateFromLimits.force _ _ hu hpc L hlim,
    R3CompactCandidate.of_limits hu hpc SpatialLocalization.isCompact_supportCylinder hus hps
      L hlim hd hunbounded,
    CandidateFromLimits.force_smooth _ _ hu hpc L hlim, ?_,
    CandidateFromLimits.force_boundary_jets _ _ hu hpc L hlim⟩
  exact supportedInCube_of_zero_outside (fun t x hx =>
    CandidateFromLimits.force_zero_outside _ _ hu hpc L hlim
      SpatialLocalization.isClosed_supportCylinder hus hps hx t)

/-! ## Lattice periodization -/

/-- The jets of a periodized field at time one are the jets of one translate. -/
theorem periodize_jets {f : VelocityField} (hf : PeriodicLocalization.SupportedInCube (1 / 4) f)
    (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (PeriodicLocalization.periodize f) (1, x) =
      iteratedFDeriv ℝ n f (1, representative x) := by
  rw [← eq_representative (CompactForceDecay.iteratedFDeriv_periods
    (PeriodicLocalization.unitSpatialPeriodsOn_periodize f univ) n) (mem_univ (1 : ℝ)) x]
  exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (PeriodicLocalization.periodize_eventuallyEq hf (z := (1, representative x))
      (representative_mem_innerCube x)) n).self_of_nhds

/-- Initial data survives the compact-to-periodic localization. -/
theorem periodized_zero_initial {u U : VelocityField}
    (hzero : ∀ x : Space, u (0, x) = 0)
    (hUper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) U)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u) :
    ∀ x : Space, U (0, x) = 0 := by
  intro x
  rw [← eq_representative hUper ⟨le_rfl, zero_lt_one⟩ x,
    (heu (0, representative x) (representative_mem_innerCube x)).self_of_nhds]
  exact hzero _

/-- Future time support survives periodization. -/
theorem periodized_force_time_support {f : VelocityField}
    (hforce : CompactFutureTimeSupport f) :
    CompactFutureTimeSupport (PeriodicLocalization.periodize f) := by
  obtain ⟨T, hT, hz⟩ := hforce
  refine ⟨T, hT, fun t ht x => ?_⟩
  simp [PeriodicLocalization.periodize, PeriodicLocalization.translate, hz t ht]

/-- Divergence-freeness can be checked on the representative copy. -/
theorem periodized_divergence_free {u U : VelocityField}
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hUper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) U)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence U t x = 0 := by
  intro t ht x
  calc spatialDivergence U t x = spatialDivergence U t (representative x) :=
        (eq_representative (spatialDivergence_periodic hUper) ht x).symm
    _ = spatialDivergence u t (representative x) :=
        spatialDivergence_congr (heu (t, representative x) (representative_mem_innerCube x))
    _ = 0 := hdiv t ht _

/-- The equation can be checked on the representative copy. -/
theorem periodized_navier_stokes {u U : VelocityField} {p P : PressureField} {f : VelocityField}
    (hf : PeriodicLocalization.SupportedInCube (1 / 4) f)
    (hns : ∀ t ∈ Ico (0 : ℝ) 1, 0 < t → ∀ x : Space,
      navierStokesResidual u p t x = f (t, x))
    (hUper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) U)
    (hPper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) P)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u)
    (hep : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → P =ᶠ[𝓝 z] p) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      navierStokesResidual U P t x = PeriodicLocalization.periodize f (t, x) := by
  intro t ht x
  have hUo : UnitSpatialPeriodsOn (Ioo (0 : ℝ) 1) U := fun s hs => hUper s ⟨hs.1.le, hs.2⟩
  have hPo : UnitSpatialPeriodsOn (Ioo (0 : ℝ) 1) P := fun s hs => hPper s ⟨hs.1.le, hs.2⟩
  have hper := PeriodicLocalization.unitSpatialPeriodsOn_periodize f univ
  let xr := representative x
  have hresper : navierStokesResidual U P t x = navierStokesResidual U P t xr :=
    (eq_representative (ResidualRegularity.residual_periods isOpen_Ioo hUo hPo) ht x).symm
  have hlocU : U =ᶠ[𝓝 (t, xr)] u := heu (t, xr) (representative_mem_innerCube x)
  have hlocP : P =ᶠ[𝓝 (t, xr)] p := hep (t, xr) (representative_mem_innerCube x)
  have hresloc : navierStokesResidual U P t xr = navierStokesResidual u p t xr := by
    exact ResidualRegularity.residual_congr (z := (t, xr)) hlocU hlocP
  have hcompact : navierStokesResidual u p t xr = f (t, xr) := hns t ⟨ht.1.le, ht.2⟩ ht.1 xr
  have hinner : f (t, xr) = PeriodicLocalization.periodize f (t, xr) :=
    (PeriodicLocalization.periodize_eq_on_innerCube hf (representative_mem_innerCube x) t).symm
  have hforceper : PeriodicLocalization.periodize f (t, xr) =
      PeriodicLocalization.periodize f (t, x) := eq_representative hper (mem_univ t) x
  exact hresper.trans (hresloc.trans (hcompact.trans (hinner.trans hforceper)))

/-- The compact blow-up points already lie in the inner cube by support. -/
theorem periodized_speed_unbounded {u U : VelocityField}
    (hu : PeriodicLocalization.SupportedInCube (1 / 4) u)
    (hspeed : SpeedUnboundedAtOne u)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u) :
    SpeedUnboundedAtOne U := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hspeed M hM δ hδ
  have hx : x ∈ PeriodicLocalization.innerCube (1 / 4) := by
    intro i
    have hne : u (t, x) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlarge
      exact absurd hlarge (not_lt.mpr hM.le)
    have hb : |x i| ≤ 1 / 4 := hu (t, x) hne i
    change |x i| < 1 - 1 / 4
    linarith
  exact ⟨t, x, ht, hnear, by rwa [(heu (t, x) hx).self_of_nhds]⟩

/-- Periodization of a compactly supported candidate. -/
theorem candidate_of_periodization {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : R3CompactCandidate.Properties u p f)
    (hu : PeriodicLocalization.SupportedInCube (1 / 4) u)
    (hf : PeriodicLocalization.SupportedInCube (1 / 4) f)
    {U : VelocityField} {P : PressureField}
    (hU : ContDiffOn ℝ ∞ U preSingularDomain) (hP : ContDiffOn ℝ ∞ P preSingularDomain)
    (hUper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) U)
    (hPper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) P)
    (heu : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → U =ᶠ[𝓝 z] u)
    (hep : ∀ z : SpaceTime, z.2 ∈ PeriodicLocalization.innerCube (1 / 4) → P =ᶠ[𝓝 z] p) :
    CandidateProperties U P (PeriodicLocalization.periodize f) where
  velocity_smooth := hU
  pressure_smooth := hP
  force_smooth := PeriodicLocalization.contDiffOn_periodize hf h.force_smooth
  velocity_periodic := hUper
  pressure_periodic := hPper
  force_periodic := PeriodicLocalization.unitSpatialPeriodsOn_periodize f _
  zero_initial_velocity := periodized_zero_initial h.zero_initial_velocity hUper heu
  force_time_support := periodized_force_time_support h.force_time_support
  divergence_free := periodized_divergence_free h.divergence_free hUper heu
  navier_stokes := periodized_navier_stokes hf h.navier_stokes hUper hPper heu hep
  speed_unbounded := periodized_speed_unbounded hu h.speed_unbounded heu

/-- The periodic candidate: the compact candidate of `exists_compact_candidate`,
periodized. Its force is smooth on all of spacetime and its jets at time one
are `boundaryLimits`. All remaining analytic assumptions concern the incoming
fields. -/
theorem exists_candidate_force {A v : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hd : ∀ t < 1, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    (hz : JointResidualLimits.VanishingJointJets (originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖velocity A v (t, 0)‖) (𝓝[<] 1) atTop) :
    ∃ F : VelocityField,
      CandidateProperties (TimeLocalization.activatedVelocity (periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      (∀ n : ℕ, ∀ x : Space,
        iteratedFDeriv ℝ n F (1, x) = boundaryLimits A v p eA ev ep x n) := by
  have hA' : ContDiffOn ℝ ∞ A preSingularDomain := hA.mono (fun _ h => ⟨h.1.2, h.2⟩)
  have hv' : ContDiffOn ℝ ∞ v preSingularDomain := hv.mono (fun _ h => ⟨h.1.2, h.2⟩)
  have hp' : ContDiffOn ℝ ∞ p preSingularDomain := hp.mono (fun _ h => ⟨h.1.2, h.2⟩)
  obtain ⟨F, hF, hFs, hFc, hjet⟩ := exists_compact_candidate hA hv hp hz eA ev ep
    (TimeLocalization.activatedVelocity_divergence_free _ (cutVelocity_smoothOn hA' hv')
      (fun t ht x => cutVelocity_divergence_free hA hv hd ht.2 x))
    (TimeLocalization.activatedVelocity_speed_unbounded _ (cutVelocity_speed_unbounded haxis))
  refine ⟨PeriodicLocalization.periodize F,
    candidate_of_periodization hF
      (supportedInCube_of_zero_outside (fun t x hx => activated_cutVelocity_zero_outside A v t hx))
      hFc
      (TimeLocalization.activatedVelocity_smooth _ (periodicVelocity_smoothOn hA' hv'))
      (TimeLocalization.activatedPressure_smooth _
        (SpatialLocalization.periodicPressure_smoothOn hp'))
      (TimeLocalization.activatedVelocity_periodic _ _ (periodicVelocity_periodic A v _))
      (TimeLocalization.activatedPressure_periodic _ _
        (SpatialLocalization.periodicPressure_periodic p _))
      (activated_periodicVelocity_eventuallyEq_cut A v)
      (activated_periodicPressure_eventuallyEq_cut p), ?_, ?_⟩
  · have hset : (univ : Set ℝ) ×ˢ (univ : Set Space) = (univ : Set SpaceTime) := by
      ext z
      simp
    exact contDiffOn_univ.mp (by
      simpa [hset] using PeriodicLocalization.contDiffOn_periodize (times := univ) hFc
        hFs.contDiffOn)
  · intro n x
    rw [periodize_jets hFc n x, hjet n (representative x)]
    rfl

end NavierStokes.MixedPeriodicAssembly
