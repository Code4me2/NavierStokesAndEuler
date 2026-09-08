import NavierStokes.PeriodizedWaveBounds
import NavierStokes.PhysicalParticularWave
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A periodic phase with the actual native clock germs

An explicit compact smooth cutoff has a plateau around the entire native
core. Its clock-weighted copies are summed on the common cover. The phase
is therefore periodic on the full auxiliary lift and retains the original
clock, with every derivative, on each padded wave core.
-/

noncomputable section

namespace NavierStokes.PeriodicPhaseAssembly

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open CommonCoverSolve TorusInverse TorusAverages

/-- A concrete smooth interval cutoff. Its plateau includes an extra
padding interval on each side of `[a,b]`. -/
noncomputable def intervalCutoff (a b d x : ℝ) : ℝ :=
  Real.smoothTransition ((x - (a - 2 * d)) / d) *
    Real.smoothTransition (((b + 2 * d) - x) / d)

theorem intervalCutoff_contDiff (a b d : ℝ) : ContDiff ℝ ∞ (intervalCutoff a b d) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const d)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const d))

theorem intervalCutoff_one {a b d x : ℝ} (hd : 0 < d)
    (ha : a - d ≤ x) (hb : x ≤ b + d) : intervalCutoff a b d x = 1 := by
  have h1 : 1 ≤ (x - (a - 2 * d)) / d := (le_div_iff₀ hd).2 (by linarith)
  have h2 : 1 ≤ ((b + 2 * d) - x) / d := (le_div_iff₀ hd).2 (by linarith)
  simp only [intervalCutoff, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2, mul_one]

theorem intervalCutoff_support {a b d : ℝ} (hd : 0 < d) :
    support (intervalCutoff a b d) ⊆ Icc (a - 2 * d) (b + 2 * d) := by
  intro x hx
  have hne := mul_ne_zero_iff.mp hx
  constructor
  · by_contra hn
    have harg : (x - (a - 2 * d)) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    exact hne.1 (Real.smoothTransition.zero_of_nonpos harg)
  · by_contra hn
    have harg : ((b + 2 * d) - x) / d ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    exact hne.2 (Real.smoothTransition.zero_of_nonpos harg)

/-- Input geometry for the compact clock cutoff. The full sampled native
path and all wave cutoff supports are placed inside `core`. -/
structure ClockWindow where
  lower : Plane
  upper : Plane
  padding : ℝ
  padding_pos : 0 < padding

namespace ClockWindow

variable (w : ClockWindow)

noncomputable def core : Set Plane :=
  Icc w.lower.1 w.upper.1 ×ˢ Icc w.lower.2 w.upper.2

noncomputable def plateau : Set Plane :=
  Ioo (w.lower.1 - w.padding) (w.upper.1 + w.padding) ×ˢ
    Ioo (w.lower.2 - w.padding) (w.upper.2 + w.padding)

noncomputable def outer : Set Plane :=
  Icc (w.lower.1 - 2 * w.padding) (w.upper.1 + 2 * w.padding) ×ˢ
    Icc (w.lower.2 - 2 * w.padding) (w.upper.2 + 2 * w.padding)

noncomputable def cutoff (z : Plane) : ℝ :=
  intervalCutoff w.lower.1 w.upper.1 w.padding z.1 *
    intervalCutoff w.lower.2 w.upper.2 w.padding z.2

theorem core_compact : IsCompact w.core := isCompact_Icc.prod isCompact_Icc

theorem outer_compact : IsCompact w.outer := isCompact_Icc.prod isCompact_Icc

theorem plateau_open : IsOpen w.plateau := isOpen_Ioo.prod isOpen_Ioo

theorem core_subset_plateau : w.core ⊆ w.plateau := by
  rintro z ⟨⟨hl1, hu1⟩, ⟨hl2, hu2⟩⟩
  have hd := w.padding_pos
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem plateau_subset_outer : w.plateau ⊆ w.outer := by
  rintro z ⟨⟨hl1, hu1⟩, ⟨hl2, hu2⟩⟩
  have hd := w.padding_pos
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem core_subset_outer : w.core ⊆ w.outer :=
  w.core_subset_plateau.trans w.plateau_subset_outer

theorem cutoff_contDiff : ContDiff ℝ ∞ w.cutoff :=
  ((intervalCutoff_contDiff _ _ _).comp contDiff_fst).mul
    ((intervalCutoff_contDiff _ _ _).comp contDiff_snd)

theorem cutoff_support : support w.cutoff ⊆ w.outer := by
  intro z hz
  have hne := mul_ne_zero_iff.mp hz
  exact ⟨intervalCutoff_support w.padding_pos hne.1,
    intervalCutoff_support w.padding_pos hne.2⟩

theorem cutoff_compact : HasCompactSupport w.cutoff :=
  HasCompactSupport.of_support_subset_isCompact w.outer_compact w.cutoff_support

theorem cutoff_one {z : Plane} (hz : z ∈ w.plateau) : w.cutoff z = 1 := by
  simp only [cutoff, intervalCutoff_one w.padding_pos hz.1.1.le hz.1.2.le,
    intervalCutoff_one w.padding_pos hz.2.1.le hz.2.2.le, mul_one]

theorem cutoff_germ {z : Plane} (hz : z ∈ w.core) : w.cutoff =ᶠ[𝓝 z] fun _ => 1 :=
  eventually_of_mem (w.plateau_open.mem_nhds (w.core_subset_plateau hz))
    (fun _ hx => w.cutoff_one hx)


end ClockWindow

/-- The literal lattice sum of a native scalar. -/
noncomputable def periodizeScalar (g : Geometry) (f : Plane → ℝ) (Y : Plane) : ℝ :=
  ∑' k : Frequency, f (g.coordinates k Y)

theorem periodizeScalar_eventually_finite (g : Geometry) {f : Plane → ℝ}
    (hf : HasCompactSupport f) (Y : Plane) :
    ∃ J : Finset Frequency, periodizeScalar g f =ᶠ[𝓝 Y]
      fun Z => ∑ k ∈ J, f (g.coordinates k Z) := by
  classical
  obtain ⟨J, hJ⟩ := g.finite_copy_cutoffs hf (‖Y‖ + 1)
  refine ⟨J, ?_⟩
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
    (show ‖Y‖ < ‖Y‖ + 1 by linarith)] with Z hZ
  exact tsum_eq_sum (fun k hk => hJ Z hZ.le k hk)

theorem periodizeScalar_contDiff (g : Geometry) {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (periodizeScalar g f) := by
  rw [contDiff_iff_contDiffAt]
  intro Y
  obtain ⟨J, hJ⟩ := periodizeScalar_eventually_finite g hc Y
  have hs : ContDiff ℝ ∞ (fun Z => ∑ k ∈ J, f (g.coordinates k Z)) :=
    ContDiff.sum (fun k _ => hf.comp (g.coordinates_contDiff k))
  exact hs.contDiffAt.congr_of_eventuallyEq hJ

theorem periodizeScalar_periodic (g : Geometry) (f : Plane → ℝ) (Y : Plane) (n : Frequency) :
    periodizeScalar g f (Y + latticePoint n) = periodizeScalar g f Y := by
  change PeriodizedWaveBounds.copySum (fun k Y => f (g.coordinates k Y)) (Y + latticePoint n) = _
  apply PeriodizedWaveBounds.copySum_translate _ (fun Z => Z + latticePoint n)
    (Equiv.addRight (coverIndex g.gap n))
  intro k Z
  exact congrArg f (g.coordinates_deck k n Z)

theorem periodizeScalar_refine (g : Geometry) (f : Plane → ℝ) (d : ℕ) (Y : Plane) :
    periodizeScalar (CopySolveCompatibility.refineGeometry g d) f Y =
      periodizeScalar g f (coverPower d Y) :=
  CopySolveCompatibility.native_copy_sum_refine g d f Y

theorem periodizeScalar_transport (g : Geometry) (f : Plane → ℝ) (d : ℕ)
    (shift rate : ℝ) (hrate : rate ≠ 0) (Y : Plane) :
    periodizeScalar (CopySolveCompatibility.transportGeometry g d shift rate hrate)
      (f ∘ CopySolveCompatibility.nativeTimeMap shift rate) Y =
      periodizeScalar g f (coverPower d Y) := by
  unfold periodizeScalar
  apply tsum_congr
  intro k
  simp only [comp_apply, CopySolveCompatibility.transportGeometry,
    CopySolveCompatibility.coordinates_refine, CopySolveCompatibility.coordinates_timeGeometry]

/-- The clock itself is periodicized together with its cutoff. -/
noncomputable def periodicClock (g : Geometry) (χ : Plane → ℝ) : Plane → ℝ :=
  periodizeScalar g (fun z => χ z * z.2)

theorem periodicClock_contDiff (g : Geometry) (w : ClockWindow) :
    ContDiff ℝ ∞ (periodicClock g w.cutoff) :=
  periodizeScalar_contDiff g (w.cutoff_contDiff.mul contDiff_snd) w.cutoff_compact.mul_right

theorem periodicClock_periodic (g : Geometry) (χ : Plane → ℝ) (Y : Plane) (n : Frequency) :
    periodicClock g χ (Y + latticePoint n) = periodicClock g χ Y :=
  periodizeScalar_periodic g _ Y n

theorem periodicClock_refine (g : Geometry) (χ : Plane → ℝ) (d : ℕ) (Y : Plane) :
    periodicClock (CopySolveCompatibility.refineGeometry g d) χ Y =
      periodicClock g χ (coverPower d Y) :=
  periodizeScalar_refine g _ d Y


section Germs

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
/-- Exact clock agreement on a neighborhood of every closed native core.
The geometric input is injectivity of the larger padded support cell. -/
theorem periodicClock_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (k : Frequency) {z : P × Plane} (hz : g.coordinates k z.2 ∈ w.core) :
    (fun x : P × Plane => periodicClock g w.cutoff x.2) =ᶠ[𝓝 z]
      fun x => (g.coordinates k x.2).2 := by
  let K := PeriodizedWaveBounds.nativeCells (P := P) (fun _ => g) (fun _ => w.outer)
    (fun _ => w.outer_compact) (fun _ => hinj)
  let f (j : Frequency) (x : P × Plane) : ℝ :=
    w.cutoff (g.coordinates j x.2) * (g.coordinates j x.2).2
  have hs : ∀ j, support (f j) ⊆ K.carrier 0 j := by
    intro j x hx
    exact w.cutoff_support (mul_ne_zero_iff.mp hx).1
  have he := PeriodizedWaveBounds.copySum_germ K 0 f hs (w.core_subset_outer hz)
  have hc : Continuous (fun x : P × Plane => g.coordinates k x.2) :=
    (g.coordinates_contDiff k).continuous.comp continuous_snd
  filter_upwards [he, hc.continuousAt.preimage_mem_nhds
    (w.plateau_open.mem_nhds (w.core_subset_plateau hz))] with x hx hp
  change (∑' j : Frequency, w.cutoff (g.coordinates j x.2) * (g.coordinates j x.2).2) = _ at hx ⊢
  change _ = w.cutoff (g.coordinates k x.2) * (g.coordinates k x.2).2 at hx
  rw [hx, w.cutoff_one hp, one_mul]


end Germs


/-! ## Actual phases and complete carriers -/

section Phases

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def phase (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (z : P × Plane) : ℝ := A z.1 - periodicClock g χ z.2 * B z.1

noncomputable def nativePhase (g : Geometry) (A B : P → ℝ) (k : Frequency)
    (z : P × Plane) : ℝ := A z.1 - (g.coordinates k z.2).2 * B z.1

theorem phase_contDiff (g : Geometry) (w : ClockWindow) {A B : P → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (phase g w.cutoff A B) :=
  (hA.comp contDiff_fst).sub
    (((periodicClock_contDiff g w).comp contDiff_snd).mul (hB.comp contDiff_fst))


omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem phase_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (p : P) (Y : Plane) (n : Frequency) :
    phase g χ A B (p, Y + latticePoint n) = phase g χ A B (p, Y) := by
  simp only [phase, periodicClock_periodic]

omit [NormedSpace ℝ P] in
theorem phase_germ (g : Geometry) (w : ClockWindow)
    (hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer))
    (A B : P → ℝ) (k : Frequency) {z : P × Plane}
    (hz : g.coordinates k z.2 ∈ w.core) :
    phase g w.cutoff A B =ᶠ[𝓝 z] nativePhase g A B k := by
  filter_upwards [periodicClock_germ g w hinj k hz] with x hx
  simp only [phase, nativePhase, hx]



/-- The angular coordinate is distinct from the auxiliary torus. -/
noncomputable def angularLift (Φ : P × Plane → ℝ) (angular : ℝ)
    (x : (P × ℝ) × Plane) : ℝ := Φ (x.1.1, x.2) + angular * x.1.2

theorem angularLift_contDiff {Φ : P × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (angular : ℝ) :
    ContDiff ℝ ∞ (angularLift Φ angular) :=
  (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)).add
    (contDiff_const.mul contDiff_fst.snd)


omit [NormedSpace ℝ P] in
theorem angularLift_germ {Φ Ψ : P × Plane → ℝ} (angular : ℝ)
    {x : (P × ℝ) × Plane} (hΦ : Φ =ᶠ[𝓝 (x.1.1, x.2)] Ψ) :
    angularLift Φ angular =ᶠ[𝓝 x] angularLift Ψ angular := by
  have ht : Tendsto (fun z : (P × ℝ) × Plane => (z.1.1, z.2))
      (𝓝 x) (𝓝 (x.1.1, x.2)) :=
    (continuous_fst.fst.prodMk continuous_snd).continuousAt
  filter_upwards [ht.eventually hΦ] with y hy
  exact congrArg (fun t => t + angular * y.1.2) hy



omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem fullPhase_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (angular : ℝ) (p : P) (θ : ℝ) (Y : Plane) (n : Frequency) :
    angularLift (phase g χ A B) angular ((p, θ), Y + latticePoint n) =
      angularLift (phase g χ A B) angular ((p, θ), Y) := by
  simp only [angularLift, phase_periodic]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem carrier_periodic (g : Geometry) (χ : Plane → ℝ) (A B : P → ℝ)
    (angular K : ℝ) (p : P) (θ : ℝ) (Y : Plane) (n : Frequency) :
    HarmonicCalculus.carrier K (angularLift (phase g χ A B) angular) ((p, θ), Y + latticePoint n) =
      HarmonicCalculus.carrier K (angularLift (phase g χ A B) angular) ((p, θ), Y) := by
  simp only [HarmonicCalculus.carrier, fullPhase_periodic]




end Phases

/-! ## The manuscript phase in physical slow-coordinate order `(R,(T,Z))` -/

abbrev Parameter := PhysicalParticularWave.Parameter


noncomputable def profileIntercept (ε pz x0 : ℝ) (s : Parameter) : ℝ :=
  (pz / ε) * s.2.2 + x0 * s.1

noncomputable def profileRate (p pz : ℝ) (F G : Parameter → ℝ) (s : Parameter) : ℝ :=
  p * F s + pz * G s

noncomputable def profilePhase (g : Geometry) (χ : Plane → ℝ) (ε p pz x0 : ℝ)
    (F G : Parameter → ℝ) : Parameter × Plane → ℝ :=
  phase g χ (profileIntercept ε pz x0) (profileRate p pz F G)




/-! ## One reference phase under actual clock and common-cover changes -/


section Transport

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Each target band is a view of one fixed reference phase. -/
noncomputable def transportPhase (Φ : P × Plane → ℝ) (φ : Q → P) (gap : ℕ)
    (K Kr : ℝ) (z : Q × Plane) : ℝ :=
  (Kr / K) * Φ (φ z.1, coverPower gap z.2)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem transportPhase_weighted (Φ : P × Plane → ℝ) (φ : Q → P) (gap : ℕ)
    {K : ℝ} (hK : K ≠ 0) (Kr : ℝ) (z : Q × Plane) :
    K * transportPhase Φ φ gap K Kr z = Kr * Φ (φ z.1, coverPower gap z.2) := by
  unfold transportPhase
  field_simp








end Transport

theorem parameterChange_self {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    PhysicalParticularWave.parameterChange h Q Q = id := by
  have hr (a : ℝ) : PhysicalParticularWave.ratioPower Q Q a = 1 :=
    div_self (Real.rpow_pos_of_pos hQ a).ne'
  funext p
  simp only [PhysicalParticularWave.parameterChange, hr, one_mul, id_eq]

/-- A literal harmonic block with one reference phase and one angular
integer. Its amplitudes and pressure coefficients are supplied by the
existing block; its phase is the constructed common-cover view. -/
noncomputable def physicalBlock (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ) :
    CorrectionState.HarmonicBlock (Parameter × Plane) :=
  { b with
    phase := fun n => transportPhase (phase g w.cutoff A B)
      (PhysicalParticularWave.parameterChange h (Q n) (Q reference))
      (gap n) (b.frequency n) (b.frequency reference)
    angularFrequency := fun _ => angular }

theorem physicalBlock_reference (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (hQ : 0 < Q reference) (hgap : gap reference = 0) (hK : b.frequency reference ≠ 0) :
    (physicalBlock b h Q gap reference angular g w A B).phase reference = phase g w.cutoff A B := by
  funext z
  simp only [physicalBlock, transportPhase, hgap, parameterChange_self hQ h, id_eq,
    coverPower, ContinuousLinearEquiv.refl_apply, div_self hK, one_mul]

theorem physicalBlock_weighted (b : CorrectionState.HarmonicBlock (Parameter × Plane))
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (reference : ℕ) (angular : ℤ)
    (g : Geometry) (w : ClockWindow) (A B : Parameter → ℝ)
    (hQ : 0 < Q reference) (hgap : gap reference = 0)
    (hK : ∀ n, b.frequency n ≠ 0) (n : ℕ) (p : Parameter) (Y : Plane) :
    (physicalBlock b h Q gap reference angular g w A B).frequency n *
        (physicalBlock b h Q gap reference angular g w A B).phase n (p, Y) =
      (physicalBlock b h Q gap reference angular g w A B).frequency reference *
        (physicalBlock b h Q gap reference angular g w A B).phase reference
          (PhysicalParticularWave.parameterChange h (Q n) (Q reference) p, coverPower (gap n) Y) := by
  rw [physicalBlock_reference b h Q gap reference angular g w A B hQ hgap (hK reference)]
  exact transportPhase_weighted _ _ _ (hK n) _ _




/-- Assign the constructed phase family to the literal assembly record. -/
noncomputable def periodicAssembly (D : ParticularWaveAssembly.AssemblyData Parameter)
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (angular : ℤ) (w : ClockWindow)
    (A B : Parameter → ℝ) : ParticularWaveAssembly.AssemblyData Parameter :=
  { D with carrierBlock := physicalBlock D.carrierBlock h Q gap D.reference.band angular
               D.reference.geometry w A B }

theorem bandPhase_eq_actualCarrier (D : ParticularWaveAssembly.AssemblyData Parameter)
    (h : ℝ) (Q : ℕ → ℝ) (gap : ℕ → ℕ) (angular : ℤ) (w : ClockWindow)
    (A B : Parameter → ℝ) (hQ : 0 < Q D.reference.band)
    (hgap : gap D.reference.band = 0) (hK : ∀ n, D.carrierBlock.frequency n ≠ 0)
    (n : ℕ) (j : ℤ) (hj : j ≠ 0) :
    PhysicalParticularWave.bandPhase (periodicAssembly D h Q gap angular w A B)
        h (Q n) (Q D.reference.band) (gap n) ((j : ℝ) * D.carrierBlock.frequency n) j =
      fun x => (ParticularWaveAssembly.actualCarrier D.background
        (periodicAssembly D h Q gap angular w A B).carrierBlock j).phase n
          (PhysicalParticularWave.waveEquiv x) := by
  apply PhysicalParticularWave.bandPhase_eq_actualCarrier
    (periodicAssembly D h Q gap angular w A B) h (Q n) (Q D.reference.band) (gap n) n j hj hK
  · exact physicalBlock_weighted D.carrierBlock h Q gap D.reference.band angular
      D.reference.geometry w A B hQ hgap hK n
  · rfl

/-! ## Native support geometry and direct carrier adapters -/



section AdditionalTransport

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]



end AdditionalTransport

section CarrierAdapters

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]









end CarrierAdapters



end NavierStokes.PeriodicPhaseAssembly
