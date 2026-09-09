import NavierStokes.GaugeDebtIncrement
import NavierStokes.ParametricFlatFactor

/-!
# Regularity of covariances of the actual harmonic state

Finite harmonic fields are assembled before taking their actual angular
integral. Smoothness of that integral follows from local compact
domination of its genuine parameter derivatives. No covariance
regularity or covariance formula is an input.
-/

noncomputable section

namespace NavierStokes.WaveStateRegularity

open Set Function Filter MeasureTheory CorrectionState HarmonicFields
open scoped Topology ContDiff BigOperators Interval


variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable def AngularSmooth (Ω : Set D) (u : Oscillation D) : Prop :=
  ∀ n i, ContDiffOn ℝ ∞ (fun p => u n p i) (HarmonicResidual.liftDomain Ω)

theorem AngularSmooth.add {Ω : Set D} {u v : Oscillation D}
    (hu : AngularSmooth Ω u) (hv : AngularSmooth Ω v) : AngularSmooth Ω (u + v) :=
  fun n i => (hu n i).add (hv n i)

/-- Joint local smoothness gives continuous actual parameter jets.
Compactness of the angular interval then supplies their local majorants. -/
theorem compactIntegral_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {F : D × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (HarmonicResidual.liftDomain Ω))
    (a b : ℝ) (hab : a ≤ b) :
    ContDiffOn ℝ ∞ (fun x => ∫ θ in a..b, F (x, θ)) Ω := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hΩ hab
  · intro θ _
    exact hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx, Set.mem_univ θ⟩)
  · intro k
    rintro ⟨x, θ⟩ hp
    have hAt : ContDiffAt ℝ ∞ F (x, θ) :=
      hF.contDiffAt ((HarmonicResidual.liftDomain_open hΩ).mem_nhds ⟨hp.1, Set.mem_univ θ⟩)
    have hSwap : ContDiffAt ℝ ∞ (Function.uncurry (fun θ x => F (x, θ))) (θ, x) :=
      hAt.comp (θ, x) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hj := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
      (fun θ x => F (x, θ)) k θ x hSwap
    exact (hj.comp (x, θ) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt.continuousWithinAt

theorem angularAverage_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {f : OscillatoryScalar D}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (HarmonicResidual.liftDomain Ω)) :
    MeanIncrementBounds.SmoothOn Ω (angularAverage f) := by
  intro n
  exact (compactIntegral_smooth hΩ (hf n) 0 (2 * Real.pi) (by positivity)).div_const (2 * Real.pi)

theorem bilinearCovariance_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {u v : Oscillation D} (hu : AngularSmooth Ω u) (hv : AngularSmooth Ω v) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn Ω (bilinearCovariance u v i j) :=
  angularAverage_smooth hΩ (fun n => (hu n i).mul (hv n j))

theorem covarianceIncrement_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {u w : Oscillation D} (hu : AngularSmooth Ω u) (hw : AngularSmooth Ω w) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn Ω (SignedMeanGain.covarianceIncrement u w i j) :=
  (bilinearCovariance_smooth hΩ (hu.add hw) (hu.add hw) i j).sub
    (bilinearCovariance_smooth hΩ hu hu i j)

/-! ## Smoothness from the actual local harmonic coefficients -/



/-- Primitive local data for every active block. Harmonics are the
actual finite group-algebra coefficients, including harmonic zero. -/
structure LocalData (Ω : Set D) (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D) (C : ℕ → ι → Set D) : Prop where
  patch_open : ∀ n l, l ∈ labels n → IsOpen (C n l)
  coefficient : ∀ n l, l ∈ labels n → ∀ i,
    HarmonicResidual.SmoothCoefficients (Ω ∩ C n l) ((blocks l).velocity n i)
  phase : ∀ n l, l ∈ labels n → ContDiffOn ℝ ∞ ((blocks l).phase n) (Ω ∩ C n l)
  off_patch : ∀ n l, l ∈ labels n → ∀ x, x ∈ Ω → x ∉ C n l →
    ∀ i j, (blocks l).velocity n i j =ᶠ[𝓝 x] fun _ => 0

namespace LocalData

variable {Ω : Set D} {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock D}
  {C : ℕ → ι → Set D}




end LocalData

/-! ## Actual support in the moving radial annulus -/

abbrev Point := GaugeDebtIncrement.Point

noncomputable def WaveSupport {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (a b : ℝ) (u : Oscillation Point) : Prop :=
  ∀ n θ i, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
    U.carrier (fun x => u n (x, θ) i)

theorem WaveSupport.add {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {u v : Oscillation Point} (hu : WaveSupport U a b u) (hv : WaveSupport U a b v) :
    WaveSupport U a b (u + v) := by
  intro n θ i x hx hn
  by_cases hz : u n (x, θ) i = 0
  · exact hv n θ i x hx (fun hv0 => hn (by simp [hz, hv0]))
  · exact hu n θ i x hx hz

theorem angularAverage_supported {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {f : OscillatoryScalar Point}
    (hs : ∀ n θ, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
      U.carrier (fun x => f n (x, θ))) :
    ∀ n, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
      U.carrier (angularAverage f n) := by
  intro n x hx hn
  by_contra hout
  have hz (θ : ℝ) : f n (x, θ) = 0 := by
    by_contra hne
    exact hout (hs n θ x hx hne)
  apply hn
  simp only [angularAverage, hz, intervalIntegral.integral_zero, zero_div]

theorem bilinearCovariance_regular {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    {u v : Oscillation Point}
    (hu : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hv : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) v)
    (hs : WaveSupport U a b u) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (bilinearCovariance u v i j) := by
  refine ⟨bilinearCovariance_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen) hu hv i j, ?_⟩
  apply angularAverage_supported
  intro n θ x hx hn
  exact hs n θ i x hx (left_ne_zero_of_mul hn)

/-- Only the new wave needs annular support: outside it the old
covariance cancels in the literal difference of angular integrals. -/
theorem covarianceIncrement_regular {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    {u w : Oscillation Point}
    (hu : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hw : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) w)
    (hs : WaveSupport U a b w) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (SignedMeanGain.covarianceIncrement u w i j) := by
  refine ⟨covarianceIncrement_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen) hu hw i j, ?_⟩
  intro n x hx hn
  by_contra hout
  have hz (θ : ℝ) (r : Fin 3) : w n (x, θ) r = 0 := by
    by_contra hne
    exact hout (hs n θ r x hx hne)
  apply hn
  simp only [SignedMeanGain.covarianceIncrement, bilinearCovariance, angularAverage,
    Pi.sub_apply, Pi.add_apply, hz, add_zero, sub_self]


omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem field_eq_zero_of_coefficients {c : Coefficients D} (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (x : D) (θ : ℝ) (hz : ∀ j, c j x = 0) : field c k Φ kp (x, θ) = 0 := by
  rw [field_expansion]
  exact Finset.sum_eq_zero (fun j _ => by rw [hz j]; simp)


theorem fieldSum_support {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {labels : ℕ → Finset ι} {u : ι → Oscillation Point}
    (hs : ∀ n l, l ∈ labels n → ∀ θ i,
      VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
        U.carrier (fun x => u l n (x, θ) i)) :
    WaveSupport U a b (LabelSumBounds.fieldSum labels u) := by
  intro n θ i x hx hn
  by_contra hout
  apply hn
  apply Finset.sum_eq_zero
  intro l hl
  by_contra hne
  exact hout (hs n l hl θ i x hx hne)

/-! ## Concrete finite-active state adapters -/

section State

variable {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
  {labels₀ labels₁ : ℕ → Finset ι} {blocks₀ blocks₁ : ι → HarmonicBlock Point}
  {C₀ C₁ : ℕ → ι → Set Point}






end State

end NavierStokes.WaveStateRegularity
