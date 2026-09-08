import NavierStokes.SlowRecursion
import NavierStokes.ActivationHolomorphic
import NavierStokes.TransitionRamp

/-!
# The actual natural/ACT base in the all-order local axis recursion

The finite base functions below are the constructed holomorphic natural/ACT
functions. Every regularity field required by `SlowRecursion` is derived
from those functions. In particular the angular slow coefficient is `C*f`.
-/

noncomputable section

namespace NavierStokes.ActualSlowAxis

open Set Filter
open scoped Topology ContDiff
open ActivationHolomorphic (InitialTube CField signedSquare)
open SlowRecursion (AxisFunction Coefficient)

/-- A conjugation-invariant open neighborhood whose real points remain in
the real profile domain. It retains the entire closed physical window. -/
noncomputable def parameterDomain (Ω : Set ℂ) : Set ℂ :=
  Ω ∩ (starRingEnd ℂ) ⁻¹' Ω ∩ Complex.re ⁻¹' ReferencePath.parameterInterval

theorem parameterDomain_open {Ω : Set ℂ} (hΩ : IsOpen Ω) : IsOpen (parameterDomain Ω) :=
  (hΩ.inter (hΩ.preimage Complex.continuous_conj)).inter
    (ReferencePath.parameterInterval_open.preimage Complex.continuous_re)

theorem parameterDomain_subset (Ω : Set ℂ) : parameterDomain Ω ⊆ Ω := fun _ hz => hz.1.1

theorem parameterDomain_conjugate {Ω : Set ℂ} {z : ℂ} (hz : z ∈ parameterDomain Ω) :
    starRingEnd ℂ z ∈ parameterDomain Ω := by
  exact ⟨⟨hz.1.2, by simpa using hz.1.1⟩, by simpa using hz.2⟩

theorem parameterDomain_real {Ω : Set ℂ}
    (hreal : ∀ eta ∈ Icc (-1 : ℝ) 1, (eta : ℂ) ∈ Ω)
    {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) : (eta : ℂ) ∈ parameterDomain Ω := by
  refine ⟨⟨hreal eta heta, ?_⟩, ?_⟩
  · simpa using hreal eta heta
  · exact NaturalAxisCoefficients.original_interval_interior heta

theorem parameterDomain_real_interval {Ω : Set ℂ} {eta : ℝ}
    (heta : (eta : ℂ) ∈ parameterDomain Ω) : eta ∈ ReferencePath.parameterInterval := heta.2

theorem parameterTube_conjugate (J : AxisCoefficientSpace.Window) {ρ : ℝ} {z : ℂ}
    (hz : z ∈ AxisHolomorphic.parameterTube J ρ) :
    starRingEnd ℂ z ∈ AxisHolomorphic.parameterTube J ρ := by
  rcases hz with ⟨x, hx, hd⟩
  refine ⟨x, hx, ?_⟩
  simpa only [Complex.dist_conj_comm, Complex.conj_ofReal] using hd


theorem histories_congr_below {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    {X eta : ℝ} (hX : 0 ≤ X) (hP0 : P.pressure0 eta = Q.pressure0 eta)
    (hf : ∀ Y ∈ Icc (0 : ℝ) X, P.f (Y, eta) = Q.f (Y, eta))
    (hu : ∀ Y ∈ Icc (0 : ℝ) X, P.U (Y, eta) = Q.U (Y, eta)) :
    P.Ubar (X, eta) = Q.Ubar (X, eta) ∧ P.pressure (X, eta) = Q.pressure (X, eta) := by
  constructor
  · unfold ProfileHistories.Profiles.Ubar ProfileHistories.average
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    exact hu (t * X) ⟨mul_nonneg ht'.1 hX, mul_le_of_le_one_left hX ht'.2⟩
  · unfold ProfileHistories.Profiles.pressure
    rw [hP0]
    congr 1
    unfold ProfileHistories.primitive
    apply intervalIntegral.integral_congr
    intro Y hY
    have hY' : Y ∈ Icc (0 : ℝ) X := by simpa only [uIcc_of_le hX] using hY
    change P.f (Y, eta) ^ 2 = Q.f (Y, eta) ^ 2
    rw [hf Y hY']

section ActualBase

variable {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
variable (E : InitialTube N h P0 R Ω)

include E in
theorem domain {S : ℝ} (hS : 0 < S) : SlowRecursion.Domain S (parameterDomain Ω) h where
  positive := hS
  open_set := parameterDomain_open E.isOpen
  conjugate := fun _ hz => parameterDomain_conjugate hz
  denominator := fun z hz => E.elliptic_ne_zero z hz.1.1

noncomputable def fields (T κ δ : ℝ) : Fin 4 → CField :=
  ![E.f T κ δ, E.U T κ δ, E.Ubar T κ δ, E.Pi T κ δ]

noncomputable def realFields {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) :
    Fin 4 → ProfileHistories.Field :=
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  ![P.f, P.U, P.Ubar, P.pressure]

theorem fields_regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (i : Fin 4) :
    ActivationHolomorphic.Regular univ Ω (signedSquare (fields E T κ δ i)) := by
  obtain ⟨hf, hu, hv, hp⟩ := E.signed_regular hT hδ hδT κ
  fin_cases i
  · exact hf
  · exact hu
  · exact hv
  · exact hp

theorem fields_real {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (i : Fin 4) (x : ℝ) {eta : ℝ} (heta : eta ∈ ReferencePath.parameterInterval) :
    fields E T κ δ i (x, (eta : ℂ)) = (realFields (N := N) hT hδ hδT κ hP0 i (x, eta) : ℂ) := by
  obtain ⟨hf, hu, hv, hp⟩ := E.real_profiles hT hδ hδT κ hP0 x heta
  fin_cases i
  · exact hf
  · exact hu
  · exact hv
  · exact hp

/-- Each base component is an actual member of the compatible function
algebra; no separate jet data or extension hypothesis is supplied. -/
noncomputable def element {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) : AxisFunction S (parameterDomain Ω) :=
  ⟨signedSquare (fields E T κ δ i), {
    smooth := (fields_regular E hT hδ hδT κ i).smooth.mono
      (Set.prod_mono (subset_univ _) (parameterDomain_subset Ω))
    holomorphic := fun r _ => ((fields_regular E hT hδ hδT κ i).holomorphic r (mem_univ r)).mono
      (parameterDomain_subset Ω)
    even := fun z _ r _ => ActivationHolomorphic.signedSquare_even _ z r
    real := by
      intro r _ eta heta
      change (fields E T κ δ i (r ^ 2, (eta : ℂ))).im = 0
      rw [fields_real E hT hδ hδT κ hP0 i _ (parameterDomain_real_interval heta)]
      rfl }⟩

theorem element_complexProfile {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X : ℝ} (hX : 0 ≤ X) (z : ℂ) :
    SlowRecursion.complexProfile (element E hT hδ hδT κ hP0 S i) (X, z) = fields E T κ δ i (X, z) := by
  change fields E T κ δ i (Real.sqrt X ^ 2, z) = _
  rw [Real.sq_sqrt hX]

theorem element_profile {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) (X, eta) =
      realFields (N := N) hT hδ hδT κ hP0 i (X, eta) := by
  have hc := (element_complexProfile E hT hδ hδT κ hP0 S i hX (eta : ℂ)).trans
    (fields_real E hT hδ hδT κ hP0 i X heta)
  exact congrArg Complex.re hc


theorem real_domain_mem (N : ReferencePath.Input) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) : (X, eta) ∈ N.radialDomain.carrier := by
  refine ⟨?_, heta⟩
  have := mul_nonneg N.scale_pos.le hX
  linarith


theorem element_profile_germ {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (S : ℝ) (i : Fin 4) {X eta : ℝ} (hX : 0 < X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowRecursion.profile (element E hT hδ hδT κ hP0 S i) =ᶠ[𝓝 (X, eta)]
      realFields (N := N) hT hδ hδT κ hP0 i := by
  filter_upwards [(isOpen_Ioi.prod ReferencePath.parameterInterval_open).mem_nhds
    (show (X, eta) ∈ Ioi (0 : ℝ) ×ˢ ReferencePath.parameterInterval from ⟨hX, heta⟩)] with p hp
  exact element_profile E hT hδ hδT κ hP0 S i hp.1.le hp.2

noncomputable def base {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) : Coefficient S (parameterDomain Ω) :=
  SlowRecursion.makeBase (domain E hS)
    (SlowRecursion.realConstant S (parameterDomain Ω) C * element E hT hδ hδT κ hP0 S 0)
    (element E hT hδ hδT κ hP0 S 1) (element E hT hδ hδT κ hP0 S 2)
    (element E hT hδ hδT κ hP0 S 3)

theorem base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := base E hT hδ hδT κ hP0 C hS
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (A 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A 3) (X, eta) = P.pressure (X, eta) := by
  have hv (i : Fin 4) := element_profile E hT hδ hδT κ hP0 S i hX heta
  refine ⟨?_, hv 1, ?_, hv 3⟩
  · change ((C : ℂ) * element E hT hδ hδT κ hP0 S 0 (Real.sqrt X, (eta : ℂ))).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (C * ·) (hv 0)
  · change (element E hT hδ hδT κ hP0 S 2 (Real.sqrt X, (eta : ℂ)) -
      element E hT hδ hδT κ hP0 S 1 (Real.sqrt X, (eta : ℂ))).re = _
    exact congrArg₂ (· - ·) (hv 2) (hv 1)

theorem base_beta_value {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {S : ℝ} (hS : 0 < S) {X eta : ℝ} (hX : X ∈ Ioo (0 : ℝ) (S ^ 2))
    (heta : (eta : ℂ) ∈ parameterDomain Ω) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (base E hT hδ hδT κ hP0 C hS 4) (X, eta) =
      SlowDivergence.radialFlux h 0 P.U (X, eta) / X := by
  let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
  let u := element E hT hδ hδT κ hP0 S 1
  let k := element E hT hδ hδT κ hP0 S 2 - u
  have hu : SlowRecursion.profile u =ᶠ[𝓝 (X, eta)] P.U :=
    element_profile_germ E hT hδ hδT κ hP0 S 1 hX.1 (parameterDomain_real_interval heta)
  have hk : SlowRecursion.profile k =ᶠ[𝓝 (X, eta)] PositiveAxisSystem.averageDefect P.U := by
    filter_upwards [(isOpen_Ioi.prod ReferencePath.parameterInterval_open).mem_nhds
      (show (X, eta) ∈ Ioi (0 : ℝ) ×ˢ ReferencePath.parameterInterval from
        ⟨hX.1, parameterDomain_real_interval heta⟩)] with q hq
    change (element E hT hδ hδT κ hP0 S 2 (Real.sqrt q.1, (q.2 : ℂ)) -
      element E hT hδ hδT κ hP0 S 1 (Real.sqrt q.1, (q.2 : ℂ))).re = _
    exact congrArg₂ (· - ·)
      (element_profile E hT hδ hδT κ hP0 S 2 hq.1.le hq.2)
      (element_profile E hT hδ hδT κ hP0 S 1 hq.1.le hq.2)
  have hb := congrArg Complex.re (SlowRecursion.betaOperator_value (domain E hS) 0 u k hX heta)
  have hcompare : PositiveAxisExistence.newBeta h 0 (SlowRecursion.profile u) (SlowRecursion.profile k) (X, eta) =
      PositiveAxisSystem.betaValue h 0 eta (PositiveAxisSystem.actualJet P.U (X, eta))
        (PositiveAxisSystem.actualJet (PositiveAxisSystem.averageDefect P.U) (X, eta)) := by
    simp only [PositiveAxisExistence.newBeta, PositiveAxisSystem.slowPower, Nat.cast_zero, mul_zero, zero_mul,
      PositiveAxisSystem.betaValue, PositiveAxisSystem.actualJet, hu.eq_of_nhds, hk.eq_of_nhds,
      SimilarityProfile.partialEta, hu.fderiv_eq, hk.fderiv_eq]
  exact hb.trans (hcompare.trans (PositiveAxisSystem.betaValue_averageDefect N.radialDomain P.U_smooth h 0
    (real_domain_mem N hX.1.le (parameterDomain_real_interval heta)) hX.1.ne'))

/-- A fixed radial rectangle strictly containing the entire initial collar. -/
noncomputable def axisRadius (N : ReferencePath.Input) (δ : ℝ) : ℝ :=
  Real.sqrt (N.endpoint * Real.exp δ) + 1

theorem axisRadius_pos (N : ReferencePath.Input) (δ : ℝ) : 0 < axisRadius N δ := by
  unfold axisRadius
  positivity

theorem collar_lt_square (N : ReferencePath.Input) (δ : ℝ) :
    N.endpoint * Real.exp δ < axisRadius N δ ^ 2 := by
  have hp : 0 ≤ N.endpoint * Real.exp δ := mul_nonneg N.endpoint_pos.le (Real.exp_pos δ).le
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (N.endpoint * Real.exp δ)
  unfold axisRadius
  nlinarith

noncomputable def hierarchy {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0) (C : ℝ) :=
  let hc := axisRadius_pos N δ
  let c := domain E (SlowRecursion.radius_pos (buffer := 1) hc zero_lt_one 0)
  SlowRecursion.buildLocalHierarchy c hc zero_lt_one C
    (base E hT hδ hδT κ hP0 C (SlowRecursion.radius_pos (buffer := 1) hc zero_lt_one 0))

theorem hierarchy_base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (C : ℝ) {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := hierarchy E hT hδ hδT κ hP0 C
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = P.pressure (X, eta) := by
  dsimp only
  simp only [(hierarchy E hT hδ hδT κ hP0 C).starts]
  exact base_values E hT hδ hδT κ hP0 C _ hX heta



end ActualBase

section NaturalConstruction

variable {h j σ Λ C : ℝ} {g a : ℝ → ℝ} {cap : ℝ} {P0 : ℝ → ℝ}
variable (hp : PressureDatum.Admissible g a cap) (hP0 : P0 = PressureDatum.pressure g a)
variable {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
variable (F : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)
variable (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)

include hp hP0 hsmall hσ in
theorem exists_tube_of_pressure_eq :
    ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 (5 / Λ)
      (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow ρ)) := by
  subst P0
  exact ActivationHolomorphic.exists_initialTube hp F hΛ hsmall hσ

noncomputable def tubeWidth : ℝ := Classical.choose (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)


/-- This witness is obtained from the actual coefficient-space natural
solution and the proved pressure integral, not supplied by the caller. -/
noncomputable def constructedTube : InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 (5 / Λ)
    (AxisHolomorphic.parameterTube ActivationHolomorphic.parameterWindow (tubeWidth hp hP0 F hΛ hsmall hσ)) :=
  Classical.choice (Classical.choose_spec (exists_tube_of_pressure_eq hp hP0 F hΛ hsmall hσ)).2

include hp hP0 in
theorem actualPressure_smooth : ContDiff ℝ ∞ P0 := by
  rw [hP0]
  exact PressureDatum.pressure_contDiff hp

noncomputable def fromNatural {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) :=
  hierarchy (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ (actualPressure_smooth hp hP0) C



theorem fromNatural_base_values {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < ReferencePath.rampLimit) (κ : ℝ) {X eta : ℝ} (hX : 0 ≤ X)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    let A := fromNatural hp hP0 F hΛ hsmall hσ hT hδ hδT κ
    let P := StressActivation.FromReference.histories (ReferenceJetBounds.referenceInput F hΛ)
      hT hδ hδT κ P0 (actualPressure_smooth hp hP0)
    SlowRecursion.profile (A.coefficients 0 0) (X, eta) = C * P.f (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 1) (X, eta) = P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 2) (X, eta) = P.Ubar (X, eta) - P.U (X, eta) ∧
    SlowRecursion.profile (A.coefficients 0 3) (X, eta) = P.pressure (X, eta) :=
  hierarchy_base_values (constructedTube hp hP0 F hΛ hsmall hσ) hT hδ hδT κ
    (actualPressure_smooth hp hP0) C hX heta








end NaturalConstruction

end NavierStokes.ActualSlowAxis
