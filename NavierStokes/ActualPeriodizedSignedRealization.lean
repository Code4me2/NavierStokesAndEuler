import NavierStokes.PhysicalSignedWave
import NavierStokes.PeriodizedWaveBounds

/-!
# Actual native-copy realization of the signed reference wave

The primary pulse and signed quotient are fixed.  A periodic reference
coordinate and mask are constructed from the native layout.  The native
copies are summed before curl, and equality with the same reference output
is proved from the periodic-clock identity on their compact supports.
-/

noncomputable section

namespace NavierStokes.ActualPeriodizedSignedRealization

open Set Function Filter
open HarmonicCalculus LinearWaveBounds WeightedClasses
open ProblemStatement
open scoped Topology ContDiff BigOperators InnerProductSpace

abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev Plane := TorusInverse.Plane
abbrev Frequency := TorusInverse.Frequency
abbrev Space := ProblemStatement.Space
abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2

/-- Primitive native geometry and its actual compact mask.  No summed
coefficient or solved-wave identity is a field of this record. -/
structure Layout where
  geometry : ℕ → CommonCoverSolve.Geometry
  window : ℕ → PeriodicPhaseAssembly.ClockWindow
  length : ℕ → ℝ
  length_pos : ∀ n, 0 < length n
  cutoff : ℕ → Plane → ℝ
  cutoff_smooth : ∀ n, ContDiff ℝ ∞ (cutoff n)
  cutoff_support : ∀ n, support (cutoff n) ⊆ (window n).core
  injective : ∀ n, InjOn TorusAverages.quotientPoint
    ((fun z => (geometry n).center + (geometry n).basis z) '' (window n).outer)

namespace Layout

variable (l : Layout)

noncomputable def nativeMask (n : ℕ) (k : Frequency) (Y : Plane) : ℝ :=
  l.cutoff n ((l.geometry n).coordinates k Y)

noncomputable def mask (n : ℕ) (Y : Plane) : ℝ := ∑' k, l.nativeMask n k Y

noncomputable def clock (n : ℕ) (Y : Plane) : ℝ :=
  PeriodicPhaseAssembly.periodicClock (l.geometry n) (l.window n).cutoff Y / l.length n

noncomputable def nativeClock (n : ℕ) (k : Frequency) (Y : Plane) : ℝ :=
  ((l.geometry n).coordinates k Y).2 / l.length n

noncomputable def gaussian (n : ℕ) (Y : Plane) : ℝ := GaussianTailFlat.profile (l.clock n Y)

noncomputable def nativeGaussian (n : ℕ) (k : Frequency) (Y : Plane) : ℝ :=
  GaussianTailFlat.profile (l.nativeClock n k Y)

theorem cutoff_compact (n : ℕ) : HasCompactSupport (l.cutoff n) :=
  HasCompactSupport.of_support_subset_isCompact (l.window n).core_compact (l.cutoff_support n)

theorem mask_summable (n : ℕ) (Y : Plane) : Summable (fun k => l.nativeMask n k Y) := by
  obtain ⟨J, hJ⟩ := (l.geometry n).finite_copy_cutoffs (l.cutoff_compact n) ‖Y‖
  exact summable_of_ne_finset_zero (s := J) (hJ Y le_rfl)

theorem clock_eq_native (n : ℕ) (k : Frequency) (Y : Plane) (hk : l.nativeMask n k Y ≠ 0) :
    l.clock n Y = l.nativeClock n k Y := by
  have h := PeriodicPhaseAssembly.periodicClock_germ (P := Unit)
    (l.geometry n) (l.window n) (l.injective n) k (z := ((), Y)) (l.cutoff_support n hk)
  exact congrArg (fun t => t / l.length n) h.self_of_nhds

theorem gaussian_eq_native (n : ℕ) (k : Frequency) (Y : Plane) (hk : l.nativeMask n k Y ≠ 0) :
    l.gaussian n Y = l.nativeGaussian n k Y :=
  congrArg GaussianTailFlat.profile (l.clock_eq_native n k Y hk)





/-- Actual finite native support justifies the scalar/vector infinite sum.
The Gaussian is inserted once, on each native copy. -/
theorem gaussian_mask_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (Y : Plane) (a : E) :
    (∑' k, l.nativeGaussian n k Y • (l.nativeMask n k Y • a)) =
      l.gaussian n Y • (l.mask n Y • a) := by
  calc
    _ = ∑' k, l.nativeMask n k Y • (l.gaussian n Y • a) := by
      apply tsum_congr
      intro k
      by_cases hk : l.nativeMask n k Y = 0
      · simp only [hk, zero_smul, smul_zero]
      · rw [l.gaussian_eq_native n k Y hk]
        exact smul_comm _ _ _
    _ = l.mask n Y • (l.gaussian n Y • a) := (l.mask_summable n Y).tsum_smul_const _
    _ = _ := smul_comm _ _ _


end Layout

/-! ## The primitive homogeneous pressure is linear in its velocity -/

noncomputable def homogeneousPressure (K : ℝ) (N Ndot : Space) (A : Space →L[ℝ] Space)
    (u : Space) : ℂ :=
  Complex.I * (TangentProjection.pressureCoefficient N Ndot u (A u) 0 : ℂ) / (K : ℂ)

theorem homogeneousPressure_smul (K c : ℝ) (N Ndot : Space) (A : Space →L[ℝ] Space) (u : Space) :
    homogeneousPressure K N Ndot A (c • u) = c • homogeneousPressure K N Ndot A u := by
  simp only [homogeneousPressure, TangentProjection.pressureCoefficient, map_smul,
    inner_smul_right, inner_zero_right, add_zero, Complex.real_smul]
  push_cast
  ring


theorem coefficients_amplitude_at {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (unit Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (j : Fin 2) (n : ℕ) (x : D) :
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).amplitude n x =
      SignedWaveUpdate.signedScalar (D := D) s H T R mask j n x • CurlClassBounds.complexify (unit n x) := by
  simp only [SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    SignedWaveUpdate.signedVector, map_smul]

theorem coefficients_pressure_at {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2) (mask : ℕ → D → ℝ)
    (unit Ndot : ℕ → D → Space) (A : ℕ → D → Space →L[ℝ] Space)
    (j : Fin 2) (n : ℕ) (x : D) :
    (SignedWaveUpdate.coefficients a s d H T R mask unit Ndot A j).pressure n x =
      SignedWaveUpdate.signedScalar (D := D) s H T R mask j n x •
        homogeneousPressure (a.frequency n) (a.normal s d n x) (Ndot n x) (A n x) (unit n x) :=
  homogeneousPressure_smul _ _ _ _ _ _

theorem signedScalar_mul_mask {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (s : StripData D) (H : ℕ → D → Mat2) (T R : ℕ → D → Vec2)
    (mask factor : ℕ → D → ℝ) (j : Fin 2) (n : ℕ) (x : D) :
    SignedWaveUpdate.signedScalar (D := D) s H T R (fun n x => mask n x * factor n x) j n x =
      factor n x * SignedWaveUpdate.signedScalar (D := D) s H T R mask j n x := by
  unfold SignedWaveUpdate.signedScalar
  ring

/-! ## Periodic reference constructed from the same primary data -/

section Reference

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  (B : PhysicalSignedWave.PrimaryData U) (l : Layout)

noncomputable def periodizedPrimary : PhysicalSignedWave.PrimaryData U :=
  {B with
    coordinate := fun n x => ((B.coordinate n x).1, l.clock n x.1.2.2)
    mask := fun n x => B.mask n x * l.mask n x.1.2.2}

@[simp] theorem periodizedPrimary_pulse : (periodizedPrimary B l).pulse = B.pulse := rfl
@[simp] theorem periodizedPrimary_target : (periodizedPrimary B l).target = B.target := rfl
@[simp] theorem periodizedPrimary_matrix : (periodizedPrimary B l).matrix = B.matrix := rfl

/-- All view scales, integer covers, backgrounds, and operators are retained. -/
noncomputable def views {reference : ℕ} (V : B.Views reference) :
    (periodizedPrimary B l).Views reference where
  exponent := V.exponent
  referenceScale := V.referenceScale
  referenceScale_pos := V.referenceScale_pos
  referenceCover := V.referenceCover
  scale := V.scale
  scale_pos := V.scale_pos
  cover := V.cover
  cover_le := V.cover_le
  frequency := V.frequency
  frequency_ne := V.frequency_ne
  strip := V.strip
  directions := V.directions
  background := V.background


/-- Reuse the actual current state, reference state, and their full-fiber
coherence. There is no second signed choice or request. -/
noncomputable def stateData {reference : ℕ} {V : B.Views reference} (D : V.StateData) :
    (views B l V).StateData where
  patch := D.patch
  context := D.context
  referenceContext := D.referenceContext
  current := D.current
  referenceState := D.referenceState
  exponent_pos := D.exponent_pos
  exponent_lt_half := D.exponent_lt_half
  domain := D.domain
  domain_open := D.domain_open
  state_coherent := D.state_coherent
  context_coherent := D.context_coherent
  time_pos := D.time_pos
  fibers := D.fibers
  referenceSlow := D.referenceSlow
  referenceSlow_open := D.referenceSlow_open
  referenceSlow_mem := D.referenceSlow_mem
  reference_theta_smooth := D.reference_theta_smooth
  reference_axial_smooth := D.reference_axial_smooth
  reference_theta_periodic := D.reference_theta_periodic
  reference_axial_periodic := D.reference_axial_periodic

@[simp] theorem stateData_request {reference : ℕ} {V : B.Views reference} (D : V.StateData) :
    (stateData B l D).request = D.request := rfl

@[simp] theorem stateData_referenceRequest {reference : ℕ} {V : B.Views reference} (D : V.StateData) :
    (stateData B l D).referenceRequest = D.referenceRequest := rfl

variable {reference : ℕ} (V : B.Views reference)

noncomputable def sharedMask (n : ℕ) (x : Cylinder) : ℝ := B.mask reference (V.map n x)



noncomputable def commonUnit (j : Fin 2) (n : ℕ) (x : Cylinder) : Space :=
  (periodizedPrimary B l).fundamental j reference (V.map n x)

noncomputable def nativeUnit (j : Fin 2) (k : Frequency) (n : ℕ) (x : Cylinder) : Space :=
  PrimaryPulseBounds.normalizedPulse ((B.pulse j).frame reference)
    ((B.pulse j).lam reference) ((B.pulse j).u reference) ((B.pulse j).L reference)
    ((B.coordinate reference (V.map n x)).1, l.nativeClock reference k (V.map n x).1.2.2)

theorem commonUnit_eq_native (j : Fin 2) (k : Frequency) (n : ℕ) (x : Cylinder)
    (hk : l.nativeMask reference k (V.map n x).1.2.2 ≠ 0) :
    commonUnit B l V j n x = nativeUnit B l V j k n x := by
  change PrimaryPulseBounds.normalizedPulse _ _ _ _ (_, l.clock reference (V.map n x).1.2.2) = _
  rw [l.clock_eq_native reference k (V.map n x).1.2.2 hk]
  rfl

/-- One call to the original homogeneous signed quotient constructor. -/
noncomputable def coefficientsWith (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (mask : ℕ → Cylinder → ℝ) (unit : ℕ → Cylinder → Space) : WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients ((periodizedPrimary B l).viewBase V.background V.frequency (fun n => V.map n) reference)
    V.strip V.directions (fun n x => (periodizedPrimary B l).matrix reference (V.map n x))
    ((periodizedPrimary B l).viewTarget V.strip V.velocity (fun n => V.map n) reference) request mask unit
    (fun n x => (V.normal n * V.clock n) • B.normalMotion reference (V.map n x))
    (fun n x => V.clock n • B.action reference (V.map n x)) j



















/-! ## The literal current-state request and one physical reference -/












end Reference

/-! ## Support-local primitive regularity on the complete reference strip -/

section SupportLocal

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}
  (B : PhysicalSignedWave.PrimaryData U) (l : Layout)

noncomputable def referenceNativeUnit (j : Fin 2) (n : ℕ) (k : Frequency) (x : Cylinder) : Space :=
  PrimaryPulseBounds.normalizedPulse ((B.pulse j).frame n)
    ((B.pulse j).lam n) ((B.pulse j).u n) ((B.pulse j).L n)
    ((B.coordinate n x).1, l.nativeClock n k x.1.2.2)

theorem referenceUnit_eq_native (j : Fin 2) (n : ℕ) (k : Frequency) (x : Cylinder)
    (hk : l.nativeMask n k x.1.2.2 ≠ 0) :
    (periodizedPrimary B l).fundamental j n x = referenceNativeUnit B l j n k x := by
  change PrimaryPulseBounds.normalizedPulse _ _ _ _ (_, l.clock n x.1.2.2) = _
  rw [l.clock_eq_native n k x.1.2.2 hk]
  rfl

noncomputable def referenceScalar (request : ℕ → Cylinder → Vec2) (j : Fin 2)
    (n : ℕ) (x : Cylinder) : ℝ :=
  SignedWaveUpdate.signedScalar B.strip B.matrix B.target request B.mask j n x

theorem reference_raw_formula (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) (x : Cylinder) :
    (periodizedPrimary B l).raw request j n x =
      l.gaussian n x.1.2.2 • (l.mask n x.1.2.2 •
        (referenceScalar B request j n x •
          CurlClassBounds.complexify ((periodizedPrimary B l).fundamental j n x))) := by
  change l.gaussian n x.1.2.2 • ((periodizedPrimary B l).coefficients request j).amplitude n x = _
  rw [PhysicalSignedWave.PrimaryData.coefficients, coefficients_amplitude_at]
  have hs : SignedWaveUpdate.signedScalar (periodizedPrimary B l).strip
      (periodizedPrimary B l).matrix (periodizedPrimary B l).target request
      (periodizedPrimary B l).mask j n x = l.mask n x.1.2.2 * referenceScalar B request j n x := by
    change SignedWaveUpdate.signedScalar B.strip B.matrix B.target request
      (fun n x => B.mask n x * l.mask n x.1.2.2) j n x = _
    exact signedScalar_mul_mask _ _ _ _ _ _ _ _ _
  rw [hs, mul_smul]

theorem reference_raw_eq_sum (request : ℕ → Cylinder → Vec2) (j : Fin 2) (n : ℕ) :
    (periodizedPrimary B l).raw request j n = fun x =>
      ∑' k, l.nativeMask n k x.1.2.2 • (l.nativeGaussian n k x.1.2.2 •
        (referenceScalar B request j n x • CurlClassBounds.complexify (referenceNativeUnit B l j n k x))) := by
  funext x
  rw [reference_raw_formula, ← l.gaussian_mask_sum]
  apply tsum_congr
  intro k
  by_cases hk : l.nativeMask n k x.1.2.2 = 0
  · simp only [hk, zero_smul, smul_zero]
  · rw [referenceUnit_eq_native B l j n k x hk]
    exact smul_comm _ _ _

/-- Every condition is on the original slow data, native pulse, or
native support.  Inactive gaps need no uncut pulse-time hypothesis. -/
structure SupportedRegular (request : ℕ → Cylinder → Vec2) (reference : ℕ) (column : Fin 2) : Prop where
  coordinate : ContDiffOn ℝ ∞ (fun x => (B.coordinate reference x).1) B.strip.domain
  coordinate_mem : ∀ x ∈ B.strip.domain, (B.coordinate reference x).1 ∈ U.carrier reference
  native_time : ∀ k x, x ∈ B.strip.domain →
    (l.geometry reference).coordinates k x.1.2.2 ∈ tsupport (l.cutoff reference) →
      l.nativeClock reference k x.1.2.2 ∈ Ioo (0 : ℝ) 1
  prefactor : ∀ j, PhaseJetBounds.PolynomialJets U (fun n _ => B.prefactor j n)
  target : ∀ j, ContDiffOn ℝ ∞ (fun x => B.target reference x j) B.strip.domain
  request : ∀ j, ContDiffOn ℝ ∞ (fun x => request reference x j) B.strip.domain
  mask : ContDiffOn ℝ ∞ (B.mask reference) B.strip.domain
  cone : ∀ x ∈ B.strip.domain, SmoothCovariance.StrictCone (B.matrix reference x) (B.target reference x)
  phase : ContDiffOn ℝ ∞ (B.base.phase reference) B.strip.domain
  normal_ne : ∀ x ∈ B.strip.domain, B.base.normal B.strip B.directions reference x ≠ 0
  normal_frame : ∀ k x, x ∈ B.strip.domain → l.nativeMask reference k x.1.2.2 ≠ 0 →
    B.base.normal B.strip B.directions reference x =
      ((B.pulse column).frame reference).normal ((B.coordinate reference x).1,
        (B.pulse column).L reference * l.nativeClock reference k x.1.2.2)

namespace SupportedRegular

variable {B l} {request : ℕ → Cylinder → Vec2} {reference : ℕ} {column : Fin 2}
  (R : SupportedRegular B l request reference column)

include R






end SupportedRegular



variable {reference : ℕ} (V : B.Views reference) (D : V.StateData)





end SupportLocal

end NavierStokes.ActualPeriodizedSignedRealization
