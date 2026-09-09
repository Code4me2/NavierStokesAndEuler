import NavierStokes.HarmonicWaveInteraction
import NavierStokes.SignedWaveUpdate

/-!
# Initial primary residual classes

The primary coefficient and its Gaussian error are the actual cutoff/curl
construction. The improved nonlinear bound uses the exact divergence of that
curl, before projecting the literal residual into its finite harmonics.
-/

noncomputable section

namespace NavierStokes.PrimaryResidualClass

open Set Function Filter HarmonicCalculus HarmonicFields WeightedClasses
open CopyAngularInvariance
open scoped Topology ContDiff BigOperators ComplexConjugate


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The context's literal graph directions lifted to the explicit angle. -/
noncomputable def directions (c : CorrectionState.Context D) :
    LinearWaveBounds.GraphDirections (D × ℝ) where
  radial := (c.operators.eR, 0)
  auxiliary := (c.operators.vR, 0)
  axial := (c.operators.eZ, 0)
  angular := (0, 1)
  slow := (c.operators.eT, 0)
  fast := (c.operators.vT, 0)
  radialScale := c.operators.radialFrequency
  fastScale := c.operators.fastCoefficient
  radialProfile := fun p => c.operators.radialProfile p.1

theorem directions_radial (c : CorrectionState.Context D) (n : ℕ) :
    (directions c).radialField n =
      HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial := by
  funext p
  simp [directions, LinearWaveBounds.GraphDirections.radialField,
    HarmonicResidual.liftDirection, HarmonicResidual.contextFrame, smul_smul]

theorem directions_axial (s : StripData D) (c : CorrectionState.Context D)
    (hε : s.epsilon = c.operators.epsilon) (n : ℕ) :
    (directions c).axialField (HarmonicWaveInteraction.productStrip s) n =
      HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial := by
  funext p
  simp [directions, LinearWaveBounds.GraphDirections.axialField,
    HarmonicResidual.liftDirection, HarmonicResidual.contextFrame,
    HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip, hε]

theorem directions_time (s : StripData D) (c : CorrectionState.Context D)
    (hε : s.epsilon = c.operators.epsilon) (n : ℕ) :
    LinearWaveResidual.timeDirection ((HarmonicWaveInteraction.productStrip s).epsilon n)
      ((directions c).fastField n) (fun _ => (directions c).slow) =
        HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).time := by
  funext p
  simp [directions, LinearWaveBounds.GraphDirections.fastField, LinearWaveResidual.timeDirection,
    HarmonicResidual.liftDirection, HarmonicResidual.contextFrame,
    HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip, hε]

/-- Matching concerns primitive fields, never a residual or a residual bound. -/
structure Matches (s : StripData D) (c : CorrectionState.Context D)
    (a : LinearWaveBounds.WaveCoefficients (D × ℝ)) : Prop where
  epsilon : s.epsilon = c.operators.epsilon
  radius : a.radius = fun _ p => c.operators.radius p.1
  base : ∀ n, LinearWaveResidual.complexBase (a.radius n) (a.radialBase n)
    (a.frequencyBase n) (a.axialBase n) = fun p => HarmonicResidual.contextBase c n p.1

/-- Primitive angular translation data for one primary field. -/
structure AngularData (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) : Prop where
  radius : ∀ n, Invariant ((0 : D), 1) (a.radius n)
  radialBase : ∀ n, Invariant ((0 : D), 1) (a.radialBase n)
  frequencyBase : ∀ n, Invariant ((0 : D), 1) (a.frequencyBase n)
  axialBase : ∀ n, Invariant ((0 : D), 1) (a.axialBase n)
  phase : ∀ n, ∃ m, AffinePhase ((0 : D), 1) m (a.phase n)
  amplitude : ∀ n, Invariant ((0 : D), 1) (a.amplitude n)
  pressure : ∀ n, Invariant ((0 : D), 1) (a.pressure n)
  cutoff : ∀ n, Invariant ((0 : D), 1) (ψ n)

theorem invariant_fst {E : Type} (f : D → E) :
    Invariant ((0 : D), 1) (fun p : D × ℝ => f p.1) := by
  intro p t
  simp

theorem directions_radial_invariant (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1) ((directions c).radialField n) := by
  rw [directions_radial]
  exact invariant_fst (fun x => ((HarmonicResidual.contextFrame c n).radial x, (0 : ℝ)))

theorem AngularData.corrected_amplitude {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (s : StripData D)
    (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1)
      ((a.corrected (HarmonicWaveInteraction.productStrip s) (directions c) ψ).amplitude n) :=
  corrected_amplitude_invariant ψ ha.radius (directions_radial_invariant c)
    (fun _ => Invariant.const _) ha.phase ha.amplitude ha.cutoff n

theorem AngularData.corrected_pressure {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (s : StripData D)
    (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1)
      ((a.corrected (HarmonicWaveInteraction.productStrip s) (directions c) ψ).pressure n) :=
  corrected_pressure_invariant ψ ha.pressure ha.cutoff n

section InvariantOperators

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {θ : X} {R b F G : X → ℝ} {Vr Vθ Vz Vf Vs : X → X}
  {Φ : X → ℝ} {m : ℝ} {a : X → ComplexVector} {p : X → ℂ}

theorem principal_invariant (hR : Invariant θ R) (hF : Invariant θ F)
    (hG : Invariant θ G) (hr : Invariant θ Vr) (hθ : Invariant θ Vθ)
    (hz : Invariant θ Vz) (hf : Invariant θ Vf)
    (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a) (hp : Invariant θ p)
    (ε k : ℝ) : Invariant θ (LinearWaveResidual.principal ε k R F G Vr Vθ Vz Vf Φ a p) := by
  have hN := phaseNormal_invariant hR hr hθ hz hΦ
  intro x t
  funext i
  simp only [LinearWaveResidual.principal, LinearWaveResidual.shear,
    (ha.component i).along hf x t, hF.along hr x t, hG.along hr x t,
    hN x t, hR x t, hF x t, ha x t, hp x t]

theorem remainder_invariant (hR : Invariant θ R) (hb : Invariant θ b)
    (hF : Invariant θ F) (hG : Invariant θ G) (hr : Invariant θ Vr)
    (hθ : Invariant θ Vθ) (hz : Invariant θ Vz) (hf : Invariant θ Vf)
    (hs : Invariant θ Vs) (hΦ : AffinePhase θ m Φ) (ha : Invariant θ a)
    (hp : Invariant θ p) (ε k : ℝ) :
    Invariant θ (LinearWaveResidual.remainder ε k R b F G Vr Vθ Vz Vf Vs Φ a p) := by
  have hN := phaseNormal_invariant hR hr hθ hz hΦ
  have hB := base_invariant hR hb hF hG
  have ht : Invariant θ (LinearWaveResidual.timeDirection ε Vf Vs) :=
    hf.map₂ hs (fun v w => v - ε • w)
  intro x t
  funext i
  simp only [LinearWaveResidual.remainder, LinearWaveResidual.slowTransport,
    LinearWaveResidual.materialPhaseDefect, LinearWaveResidual.baseDerivativeRemainder,
    LinearWaveResidual.strippedPressureGradient, LinearWaveResidual.viscousRemainder,
    (ha.component i).along hs x t, (ha.component i).along hr x t,
    (ha.component i).along hz x t, ((ha.component i).along hr).along hr x t,
    ((ha.component i).along hz).along hz x t, hΦ.along_invariant ht x t,
    hΦ.along_invariant hr x t, hΦ.along_invariant hθ x t, hΦ.along_invariant hz x t,
    hb.along hr x t, (hB.component i).along hz x t, hp.along hr x t, hp.along hz x t,
    (hN.map (fun N => N 0)).along hr x t, (hN.map (fun N => N 2)).along hz x t,
    hR x t, hb x t, hF x t, hG x t, hN x t, ha x t]

end InvariantOperators

theorem AngularData.constructedGood {a : LinearWaveBounds.WaveCoefficients (D × ℝ)}
    {ψ : ℕ → D × ℝ → ℝ} (ha : AngularData a ψ) (s : StripData D)
    (c : CorrectionState.Context D) (n : ℕ) :
    Invariant ((0 : D), 1)
      (a.constructedGood (HarmonicWaveInteraction.productStrip s) (directions c) ψ n) := by
  obtain ⟨m, hm⟩ := ha.phase n
  have hc : Invariant ((0 : D), 1)
      (((a.withCutoff ψ).curlCorrection (HarmonicWaveInteraction.productStrip s) (directions c)) n) :=
    curlRemainder_invariant (ha.radius n) (directions_radial_invariant c n)
      (Invariant.const _) (Invariant.const _)
      (coefficient_invariant (ha.radius n) (directions_radial_invariant c n)
        (Invariant.const _) (Invariant.const _) hm
        ((ha.cutoff n).map₂ (ha.amplitude n) (fun r v => r • v))) (a.frequency n)
  exact (principal_invariant (ha.radius n) (ha.frequencyBase n) (ha.axialBase n)
    (directions_radial_invariant c n) (Invariant.const _) (Invariant.const _)
    (Invariant.const _) hm hc (Invariant.const _) _ _).map₂
      (remainder_invariant (ha.radius n) (ha.radialBase n) (ha.frequencyBase n) (ha.axialBase n)
        (directions_radial_invariant c n) (Invariant.const _) (Invariant.const _)
        (Invariant.const _) (Invariant.const _) hm (ha.corrected_amplitude s c n)
        (ha.corrected_pressure s c n) _ _) (· + ·)

/-- Quantitative and geometric inputs concern the primitive primary wave.
In particular neither a good-residual class nor a residual identity is a field. -/
structure Inputs (s : StripData D) (P : ℕ → D → ℝ) (κ : ℝ)
    (c : CorrectionState.Context D) (a : LinearWaveBounds.WaveCoefficients (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ) : Prop where
  matching : Matches s c a
  operators : MeanIncrementBounds.OperatorBounds s c.operators κ
  loss_le : κ ≤ 1 / 10
  coefficients : LinearWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s)
    (fun n p => P n p.1) (1 / 2) κ (directions c) a
  cutoff : UnweightedClass (HarmonicWaveInteraction.productStrip s) 0 ψ
  angular : AngularData a ψ
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.phase n) (HarmonicWaveInteraction.productStrip s).domain
  phase_split : ∀ n x θ, a.frequency n * a.phase n (x, θ) =
    a.frequency n * a.phase n (x, 0) + (kp n : ℝ) * θ
  frequency_ne : ∀ n, a.frequency n ≠ 0
  angular_ne : ∀ n, kp n ≠ 0
  normal_jets : PhaseJetBounds.PolynomialJets
    (CurlClassBounds.phaseDomain (HarmonicWaveInteraction.productStrip s))
    (a.normal (HarmonicWaveInteraction.productStrip s) (directions c))
  normal_bounds : ∃ b M : ℝ, 0 < b ∧
    (∀ n p, p.1 ∈ s.domain → b ≤ ‖a.normal (HarmonicWaveInteraction.productStrip s) (directions c) n p‖) ∧
    (∀ n p, p.1 ∈ s.domain → ‖a.normal (HarmonicWaveInteraction.productStrip s) (directions c) n p‖ ≤ M)
  inverse_frequency : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
    (fun n => 1 / a.frequency n)
  geometry : ∀ n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
    (a.radius n) ((directions c).radialField n) (fun _ => (directions c).angular)
    ((directions c).axialField (HarmonicWaveInteraction.productStrip s) n)
  tangent : ∀ n p, p.1 ∈ s.domain →
    normalDot (a.normal (HarmonicWaveInteraction.productStrip s) (directions c) n p) (a.amplitude n p) = 0
  principal_zero : ∀ n p, p.1 ∈ s.domain → ψ n p ≠ 0 →
    a.principal (HarmonicWaveInteraction.productStrip s) (directions c) n p = 0
  profile_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ P n x
  profile_le_one : ∀ n x, x ∈ s.domain → P n x ≤ 1
  radius_pos : ∀ x ∈ s.domain, 0 < c.operators.radius x






namespace Inputs

variable {s : StripData D} {P : ℕ → D → ℝ} {κ : ℝ} {c : CorrectionState.Context D}
  {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {ψ : ℕ → D × ℝ → ℝ} {kp : ℕ → ℤ}
  (h : Inputs s P κ c a ψ kp)

include h










end Inputs

noncomputable def realProjection : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

@[simp] theorem realProjection_apply (z : ℂ) : realProjection z = (z.re : ℂ) := rfl

theorem divergence_map {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : ℂ →L[ℝ] ℂ) (R : X → ℝ) (Vr Vθ Vz : X → X)
    {v : X → ComplexVector} {x : X}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    cylindricalDivergence R Vr Vθ Vz (fun y i => L (v y i)) x =
      L (cylindricalDivergence R Vr Vθ Vz v x) := by
  simp only [cylindricalDivergence, LinearWaveResidual.along_map L _ (hv _), map_add, map_smul]


theorem pair_field_of_invariant {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X × ℝ → ℂ} {Φ : X × ℝ → ℝ} (k : ℝ) (kp : ℤ)
    (hf : Invariant ((0 : X), 1) f)
    (hΦ : ∀ x θ, k * Φ (x, θ) = k * Φ (x, 0) + (kp : ℝ) * θ) (p : X × ℝ) :
    field (ErrorHarmonics.conjugatePair 1 (fun x => f (x, 0))) k
      (fun x => Φ (x, 0)) kp p = realProjection (mode k Φ f p) := by
  rw [ErrorHarmonics.field_conjugatePair, ← hΦ p.1 p.2]
  have hc := character_eq_carrier 1 k Φ p
  simp only [Int.cast_one, mul_one] at hc
  rw [hc]
  change ((f (p.1, 0) * carrier k Φ p).re : ℂ) = ((f p * carrier k Φ p).re : ℂ)
  rw [invariant_eq_zeroSlice hf p.1 p.2]


namespace Inputs

variable {s : StripData D} {P : ℕ → D → ℝ} {κ : ℝ} {c : CorrectionState.Context D}
  {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {ψ : ℕ → D × ℝ → ℝ} {kp : ℕ → ℤ}
  (h : Inputs s P κ c a ψ kp)

include h










end Inputs


namespace Inputs

variable {s : StripData D} {P : ℕ → D → ℝ} {κ : ℝ} {c : CorrectionState.Context D}
  {a : LinearWaveBounds.WaveCoefficients (D × ℝ)} {ψ : ℕ → D × ℝ → ℝ} {kp : ℕ → ℤ}
  (h : Inputs s P κ c a ψ kp)

include h


















end Inputs

end NavierStokes.PrimaryResidualClass
