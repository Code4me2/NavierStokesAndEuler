import NavierStokes.CorrectionStep.MeanComposition

/-!
# Exact field bookkeeping for one correction cycle: cycle invariants

Sixth and last part of `NavierStokes.CorrectionStep`.  It records what one full
cycle preserves: the cycle mean gain, regularity preservation, association
transport and residual grouping, the real coefficient structure, the analytic
invariant, the wave cycle gain, and the derived request gain.
-/

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds
open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section ActualCycleMeanGain

open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest
open scoped ContDiff BigOperators
namespace CycleParameters

/-- One geometric choice is shared by all four literal stages. -/
noncomputable def ofGeometry {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (rank : RankData PressureStream.Plane) : CycleParameters ι where
  gauge := G.gauge
  strip := G.strip
  patch := G.patch
  coordinate := G.coord
  timeExponent := h
  commonIndex := index
  axial := axial
  particular := particular
  signed := signed
  rank := rank

section ActualMean
variable {ι : Type} (G : SignedMeanGain.Geometry) (B : SignedMeanGain.NativeData G)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (r : RankData PressureStream.Plane)
    (v : CycleCoefficients ι) (c : Context CyclePoint) (u : State CyclePoint)
    (primary : ι → HarmonicBlock CyclePoint) (P : ι → ℕ → CyclePoint → ℝ)
    {σ κ : ℝ} (hσ : 1/5 ≤ σ) (N : ℕ)
    (hprimary : ∀ l, (primary l).BandLimited N) (hband : CoefficientBands v)
    (hcp : ∀ l, SameCarrier (v.blocks l) (primary l))


variable (hcs : ∀ l, SameCarrier (v.blocks l) ((ofGeometry G h index axial particular signed r).signedBlock v c u l))
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (17/25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2+σ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).particularBlock v c u l).velocity n i j x))
    (htangent : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2+σ-κ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).signedTangent v c u l).velocity n i j x))
    (hcurl : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1+σ-2*κ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).signedCurl v c u l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ G.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ G.strip.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)

local notation "F" => signedFamily (ofGeometry G h index axial particular signed r) v c u primary P hσ N hprimary hband hcp hcs
  hold hdiff hpart htangent hcurl hP0 hP1 hkp


end ActualMean
end CycleParameters

end ActualCycleMeanGain

section CycleRegularityPreservation

open Set CorrectionState VariableGaugeMean LocalSignedRequest MeanStateRegularity
namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

/-- Primitive regularity is propagated through the literal four-stage
state. The rank geometry is reused from the incoming state; its new
measured-debt smoothness is proved from the updated primitive fields. -/
theorem next_primitive {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (H : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v c u) i j))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u) :
    PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.next v c u) ∧
      reconstructState p.gauge c (p.next v c u) = p.next v c u := by
  have H₁ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterParticular v c u) :=
    H.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u) hX₁
  have H₂ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterSigned v c u) :=
    H₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u) hX₂
  have ht := MeanStageRegularity.temporalStage_primitive H₂ ha hd hell rfl
    p.timeExponent p.commonIndex p.axial
  have hgt := MeanStageRegularity.rankGeometry_for_state ht ha p.gauge.radial.inner_lt_outer hg
  have hr := MeanStageRegularity.rankStage_primitive ht hgt hell p.axial
  exact ⟨⟨hr.operators, hr.base, hr.mean, hr.covariance, hr.virtualTheta, hr.virtualAxial⟩, rfl⟩

theorem next_zeroMassesOn {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (H : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v c u) i j))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u)
    (hlength : ∀ n x, x ∈ U.carrier → p.rank.length n x = qLength coord x)
    (hleft : p.gauge.radial.inner ≤ p.rank.inner) (hright : p.rank.outer ≤ p.gauge.radial.outer)
    (hm : GaugeMassPreservation.ZeroMassesOn U.carrier u) :
    GaugeMassPreservation.ZeroMassesOn U.carrier (p.next v c u) := by
  have H₁ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterParticular v c u) :=
    H.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u) hX₁
  have H₂ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterSigned v c u) :=
    H₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u) hX₂
  have ht := MeanStageRegularity.temporalStage_primitive H₂ ha hd hell rfl
    p.timeExponent p.commonIndex p.axial
  have hgt := MeanStageRegularity.rankGeometry_for_state ht ha p.gauge.radial.inner_lt_outer hg
  have hθ := H₂.theta ha p.gauge.radial.inner_lt_outer
  have hz := H₂.axial_reconstructed ha hd hell rfl
  intro n x hx
  have he := p.next_preserve_masses v c u U ha hd hell H.mean.regular.smooth
    ⟨H.mean.radial.supported,H.mean.angular.supported,H.mean.axial.supported⟩
    hθ.smooth hz.smooth hθ.periodic hz.periodic hθ.supported hz.supported
    hgt hlength hleft hright n hx
  exact ⟨he.1.trans (hm n x hx).1, he.2.trans (hm n x hx).2⟩

end CycleParameters

end CycleRegularityPreservation

section CycleAssociationTransport

open Set WeightedClasses CorrectionState
open scoped BigOperators
section Reindex
variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]






end Reindex

end CycleAssociationTransport

section CycleResidualGrouping

open Set CorrectionState
open scoped BigOperators
namespace CycleRepresentation
variable {ι : Type} {v : CycleCoefficients ι} {u : State CyclePoint} {axis : AxisymmetricAlias}

theorem withAxis (h : CycleRepresentation v u axis) :
    AxisymmetricResidualGrouping.Representation v.labels v.blocks v.gaussian v.aliasCoefficients u axis :=
  ⟨h.velocity, h.pressure, h.gaussian, h.aliasError⟩

theorem fullGoodWaveResidual_grouped (h : CycleRepresentation v u axis)
    {U : Set CyclePoint} (hU : IsOpen U) {c : Context CyclePoint} {n : ℕ}
    (hr : HarmonicResidual.ExtractionRegular U c u v.labels v.blocks v.gaussian v.aliasCoefficients n)
    {x : CyclePoint × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullGoodWaveResidual c u n x i = ∑ l ∈ v.labels n,
      (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients l)).oscillation n x i :=
  AxisymmetricResidualGrouping.stateGoodWaveResidual_grouped hU h.withAxis hr hx i



theorem fullResidual_reconstructed_local (h : CycleRepresentation v u axis)
    {U : Set CyclePoint} (hU : IsOpen U) {c : Context CyclePoint} {n : ℕ}
    (hr : LocalResidualGrouping.ExtractionRegular U c u v.labels v.blocks v.gaussian v.aliasCoefficients n)
    {x : CyclePoint × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    fullResidual c u n x i = (∑ l ∈ v.labels n,
      (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients l)).oscillation n x i) +
      (HarmonicResidual.stateMeanCoefficientValue v.labels v.blocks v.gaussian v.aliasCoefficients c u n x.1 i -
        axis n x.1 i) + u.errors.total n x i :=
  LocalResidualGrouping.stateFullResidual_reconstructed hU h.withAxis hr hx i

end CycleRepresentation

end CycleResidualGrouping

section RealCoefficientStructure
open Set Filter CorrectionState HarmonicFields
open scoped Topology ComplexConjugate

/-- The stored coefficients themselves represent real fields. Retaining
this algebraic invariant lets support of the real projection control the
same coefficients used in the differentiated interaction estimates. -/
structure CycleRealCoefficients {ι : Type} (v : CycleCoefficients ι) : Prop where
  velocity : ∀ l n i, ConjugateSymmetric ((v.blocks l).velocity n i)
  pressure : ∀ l n, ConjugateSymmetric ((v.blocks l).pressure n)
  gaussian : ∀ l n i, ConjugateSymmetric (v.gaussian l n i)

private theorem conjugate_add {D : Type} {a b : Coefficients D}
    (ha : ConjugateSymmetric a) (hb : ConjugateSymmetric b) : ConjugateSymmetric (a+b) := by
  intro j x
  change a (-j) x + b (-j) x = conj (a j x + b j x)
  rw [ha j x, hb j x, map_add]

private theorem conjugate_pull {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : D ≃ₗᵢ[ℝ] E) {a : Coefficients E} (ha : ConjugateSymmetric a) :
    ConjugateSymmetric (StateReindex.coefficients e a) :=
  fun j x => ha j (e x)

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

theorem particularBlock_real (l : ι) : ErrorHarmonics.RealBlock (p.particularBlock v c u l) :=
  ⟨fun n i => conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i),
    fun n => conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).2 n)⟩

theorem signedBlock_real (l : ι) : ErrorHarmonics.RealBlock (p.signedBlock v c u l) :=
  SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _

theorem next_realCoefficients (h : CycleRealCoefficients v) :
    CycleRealCoefficients (p.nextCoefficients v c u) := by
  have hpv l n i : ConjugateSymmetric ((p.particularBlock v c u l).velocity n i) :=
    conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i)
  have hpp l n : ConjugateSymmetric ((p.particularBlock v c u l).pressure n) :=
    conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).2 n)
  have hpg l n i : ConjugateSymmetric ((p.particularGaussianBlock v c u l).velocity n i) :=
    conjugate_pull cycleAssoc ((ParticularWaveAssembly.assembledBlock_real _ _ _ _ _ _).1 n i)
  have hsv l n i : ConjugateSymmetric ((p.signedBlock v c u l).velocity n i) :=
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1 n i
  have hsp l n : ConjugateSymmetric ((p.signedBlock v c u l).pressure n) :=
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).2 n
  have hsg l n i : ConjugateSymmetric ((p.signedGaussianBlock v c u l).velocity n i) :=
    (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1 n i
  exact ⟨fun l n i => conjugate_add (conjugate_add (h.velocity l n i) (hpv l n i)) (hsv l n i),
    fun l n => conjugate_add (conjugate_add (h.pressure l n) (hpp l n)) (hsp l n),
    fun l n i => conjugate_add (conjugate_add (h.gaussian l n i) (hpg l n i)) (hsg l n i)⟩

end CycleParameters

theorem block_velocity_zero_germ_of_inputSupport {U : Set CyclePoint} {S : ℕ → Set CyclePoint}
    (hU : IsOpen U) (hS : ∀ n, IsClosed (S n))
    {b : HarmonicBlock CyclePoint} {G A : HarmonicResidual.BlockCoefficients CyclePoint}
    (hs : HarmonicSourceSupport.InputSupportOn U S b G A)
    (hr : ∀ n i, ConjugateSymmetric (b.velocity n i)) (n : ℕ) {x : CyclePoint}
    (hx : x ∈ U) (hn : x ∉ S n) (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    b.velocity n i j =ᶠ[𝓝 x] fun _ => 0 := by
  apply PeriodizedWaveBounds.zero_germ_of_support (hU.isClosed_compl.union (hS n))
  · have hh := (hs.velocity n i).enlarge j hj
    rw [HarmonicResidual.realCoefficients_eq_self (hr n i)] at hh
    intro z hz
    by_contra hz'
    exact hz (hh z hz')
  · simpa using And.intro hx hn

/-- The genuine input support controls raw nonzero coefficient germs
because their real-projection identity is retained. -/
theorem velocity_zero_germ_of_inputSupport {ι : Type} {v : CycleCoefficients ι}
    {U : Set CyclePoint} {S : ι → ℕ → Set CyclePoint}
    (hU : IsOpen U) (hS : ∀ l n, IsClosed (S l n))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (v.blocks l) (v.gaussian l) (v.aliasCoefficients l))
    (hr : CycleRealCoefficients v) (l : ι) (n : ℕ) {x : CyclePoint}
    (hx : x ∈ U) (hn : x ∉ S l n) (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    (v.blocks l).velocity n i j =ᶠ[𝓝 x] fun _ => 0 := by
  apply PeriodizedWaveBounds.zero_germ_of_support (hU.isClosed_compl.union (hS l n))
  · have hh := ((hs l).velocity n i).enlarge j hj
    rw [HarmonicResidual.realCoefficients_eq_self (hr.velocity l n i)] at hh
    intro z hz
    by_contra hz'
    exact hz (hh z hz')
  · simpa using And.intro hx hn

end RealCoefficientStructure

section AnalyticInvariant

open Set WeightedClasses MeanIncrementBounds CorrectionState LocalSignedRequest
open scoped ContDiff BigOperators

namespace CycleRepresentation
variable {ι : Type} {v : CycleCoefficients ι} {u : State CyclePoint} {axis : AxisymmetricAlias}

theorem alias_eq_lift (h : CycleRepresentation v u axis) (hz : ∀ l, v.aliasCoefficients l = 0) :
    u.errors.aliasError = fun n x => axis n x.1 := by
  funext n x i
  rw [h.aliasError]
  simp only [hz, coefficientField, Pi.zero_apply, HarmonicResidual.field_zero, Complex.zero_re,
    Finset.sum_const_zero, zero_add]

theorem gaussian_angularContinuous (h : CycleRepresentation v u axis) :
    AngularContinuous u.errors.gaussian := by
  let b : ι → HarmonicBlock CyclePoint := fun l =>
    ⟨v.gaussian l, 0, (v.blocks l).frequency, (v.blocks l).phase, (v.blocks l).angularFrequency⟩
  have he : u.errors.gaussian = LabelSumBounds.fieldSum v.labels (fun l => (b l).oscillation) := by
    funext n x i
    exact h.gaussian n x i
  rw [he]
  exact LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _)

end CycleRepresentation

/-- The quantitative and local regularity invariant is stated on the
actual stored fields of `CycleState`, including the independent alias.
Its definition makes no assertion that an arbitrary step preserves it. -/
structure CycleAnalyticInvariant {ι : Type} (G : SignedMeanGain.Geometry)
    (c : Context CyclePoint) (primary : ι → HarmonicBlock CyclePoint)
    (P : ι → ℕ → CyclePoint → ℝ) (labelCarrier : ι → ℕ → Set CyclePoint)
    (σ : ℝ) (x : CycleState ι) : Prop where
  representation : CycleRepresentation x.coefficients x.state x.axisymmetricAlias
  bands : CoefficientBands x.coefficients
  realCoefficients : CycleRealCoefficients x.coefficients
  inputSupport : ∀ l, HarmonicSourceSupport.InputSupportOn G.domain (labelCarrier l)
    (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
  sourceBand : ∀ l, (HarmonicResidual.residualBlock c x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)).BandLimited x.coefficients.residualBand
  zeroVelocity : ∀ l, HarmonicWaveInteraction.ZeroMode (x.coefficients.blocks l)
  zeroPressure : ∀ l n, (x.coefficients.blocks l).pressure n 0 = 0
  carrier : ∀ l, SameCarrier (x.coefficients.blocks l) (primary l)
  phase : ∀ l n, ContDiffOn ℝ ∞ ((x.coefficients.blocks l).phase n) G.strip.domain
  frequency : ∀ l n, (x.coefficients.blocks l).frequency n ≠ 0
  angular : ∀ l n, (x.coefficients.blocks l).angularFrequency n ≠ 0
  coefficientSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    ((x.coefficients.blocks l).velocity n i)
  pressureCoefficientSmooth : ∀ l n, HarmonicResidual.SmoothCoefficients G.domain
    ((x.coefficients.blocks l).pressure n)
  gaussianCoefficientSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (x.coefficients.gaussian l n i)
  solenoidal : ∀ l, HarmonicWaveInteraction.ModeSolenoidal G.strip c (x.coefficients.blocks l)
  wave : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2)
    (fun l n z => (x.coefficients.blocks l).velocity n i j z)
  pressure : ∀ j, LabelSumBounds.UniformWaveClass G.strip P 1
    (fun l n z => (x.coefficients.blocks l).pressure n j z)
  difference : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (17/25)
    (fun l n z => (x.coefficients.blocks l).velocity n i j z - (primary l).velocity n i j z)
  cumulative : CorrectionState.CumulativeBounds G.strip x.state
  covariance : ∀ i j, MeanClass G.strip 1 (x.state.covariance i j)
  residual : UniformHarmonicInteraction.UniformVelocity G.strip P (1/2+σ)
    (fun l => HarmonicResidual.residualBlock c x.state (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
  mean : MeanResidualBounds G.strip σ c x.state
  meanHypotheses : LiftedMeanResidual.MeanHypotheses G.strip.domain c x.state
  debt : DefectBounds G.slowStrip σ c x.state
  primitives : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c x.state
  reconstructed : VariableGaugeMean.reconstructState G.gauge c x.state = x.state
  masses : GaugeMassPreservation.ZeroMassesOn G.region.carrier x.state
  oscillationSmooth : WaveStateRegularity.AngularSmooth G.domain x.state.oscillation
  oscillatoryPressureSmooth : ∀ n, ContDiffOn ℝ ∞ (x.state.oscillatoryPressure n)
    (G.domain ×ˢ (Set.univ : Set ℝ))
  oscillationPeriodic : OscillationPeriodic G.region.carrier x.state.oscillation
  oscillationSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b x.state.oscillation
  gaussianFlat : ∀ β i j, LabelSumBounds.UniformClass G.strip
    (fun _ _ z => Real.sqrt (G.strip.zeta z)) β
    (fun l n z => x.coefficients.gaussian l n i j z)
  gaussianMean : angularMeanVector x.state.errors.gaussian = 0
  aliasCoefficients : ∀ l, x.coefficients.aliasCoefficients l = 0
  axisFlat : ∀ β, MeanClass G.strip β x.axisymmetricAlias
  baseAngular : ∀ n z, z ∈ G.domain → ∀ i,
    Continuous (fun θ : ℝ => x.state.errors.base n (z, θ) i)

namespace CycleAnalyticInvariant
variable {ι : Type} {G : SignedMeanGain.Geometry} {c : Context CyclePoint}
    {primary : ι → HarmonicBlock CyclePoint} {P : ι → ℕ → CyclePoint → ℝ}
    {labelCarrier : ι → ℕ → Set CyclePoint} {σ : ℝ} {x : CycleState ι}

/-- Raw residual classes required by the next signed request are derived
from the good-mean invariant and the actual all-power axis alias. -/
theorem raw_mean_bounds (H : CycleAnalyticInvariant G c primary P labelCarrier σ x) :
    MeanClass G.strip (1+σ) (x.state.thetaResidual c) ∧
    MeanClass G.strip (1+σ) (x.state.axialResidual c) := by
  have ha := H.representation.alias_eq_lift H.aliasCoefficients
  have hca : AngularContinuous x.state.errors.aliasError := by
    rw [ha]
    intro n z i
    change Continuous (fun _ : ℝ => x.axisymmetricAlias n z i)
    exact continuous_const
  have ham : angularMeanVector x.state.errors.aliasError = x.axisymmetricAlias := by
    rw [ha]
    funext n z i
    exact congrFun (congrFun (angularAverage_axisymmetric (fun n z => x.axisymmetricAlias n z i)) n) z
  have he n z hz i := meanGoodResidual_at c x.state n z i
    (H.baseAngular n z (G.strip_subset hz) i)
    (H.representation.gaussian_angularContinuous n z i) (hca n z i)
  have haxis (i : Fin 3) : MeanClass G.strip (1+σ) (fun n z => x.axisymmetricAlias n z i) :=
    (H.axisFlat (1+σ)).map (ContinuousLinearMap.proj i)
  constructor
  · apply class_congr (H.mean.angular.add (haxis 1))
    intro n z hz
    dsimp only
    rw [he n z hz 1, H.gaussianMean, ham]
    change x.state.thetaResidual c n z = x.state.thetaResidual c n z - 0 - x.axisymmetricAlias n z 1 +
      x.axisymmetricAlias n z 1
    ring
  · apply class_congr (H.mean.axial.add (haxis 2))
    intro n z hz
    dsimp only
    rw [he n z hz 2, H.gaussianMean, ham]
    change x.state.axialResidual c n z = x.state.axialResidual c n z - 0 - x.axisymmetricAlias n z 2 +
      x.axisymmetricAlias n z 2
    ring

end CycleAnalyticInvariant

end AnalyticInvariant

section ActualWaveCycleGain
open Set Filter WeightedClasses MeanIncrementBounds CorrectionState
open LabelSumBounds UniformHarmonicInteraction
open scoped ContDiff Topology BigOperators

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

/-- The two constructed linear cancellations give the improved residual
of the literal post-signed state, including both nonlinear wave updates.
The linear estimates are the native equation/jet outputs, not estimates
on either complete updated residual. -/
theorem waveStages_residual_gain {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hσ : 1/5 ≤ σ) (hκsmall : κ ≤ 1/100000)
    (ho : OperatorBounds p.strip c.operators κ)
    (hR : ∀ x ∈ p.strip.domain, 0 < c.operators.radius x)
    (hbase : BaseBounds p.strip c.base)
    (hu : MeanIncrementBounds.CumulativeBounds p.strip u.mean)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hold : ∀ i j, UniformWaveClass p.strip P (1/2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hpart : ∀ i j, UniformWaveClass p.strip P (1/2+σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (hsigned : ∀ i j, UniformWaveClass p.strip P (1/2+σ-κ)
      (fun l n x => (p.signedBlock v c u l).velocity n i j x))
    (hpold : ∀ l n, HarmonicResidual.SmoothCoefficients p.strip.domain ((v.blocks l).pressure n))
    (hppart : ∀ l n, HarmonicResidual.SmoothCoefficients p.strip.domain
      ((p.particularBlock v c u l).pressure n))
    (hpsigned : ∀ l n, HarmonicResidual.SmoothCoefficients p.strip.domain
      ((p.signedBlock v c u l).pressure n))
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l))
    (hband : ∀ l, (v.blocks l).BandLimited v.residualBand)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((v.blocks l).phase n) p.strip.domain)
    (hk : ∀ l n, (v.blocks l).frequency n ≠ 0)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hdiv : ∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (v.blocks l))
    (hdivpart : ∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.particularBlock v c u l))
    (hdivsigned : ∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.signedBlock v c u l))
    {C : ℕ → ι → Set CyclePoint}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted p.strip C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (v.blocks l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1/2))
      (fun n l _ => (v.blocks l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1/2))
      (fun n l _ => ((v.blocks l).angularFrequency n : ℝ)))
    (hzpart : ∀ n l x, x ∈ p.strip.domain → x ∉ C n l → ∀ i j, j ≠ 0 →
      (p.particularBlock v c u l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hzsigned : ∀ n l x, x ∈ p.strip.domain → x ∉ C n l → ∀ i j, j ≠ 0 →
      (p.signedBlock v c u l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ l n x, x ∈ p.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ p.strip.domain → P l n x ≤ 1)
    (hlinearP : ∀ i j, j ≠ 0 → UniformWaveClass p.strip P (1+σ-3*κ)
      (fun l n x =>
        (HarmonicResidual.residualBlock c u (v.blocks l) (v.gaussian l) (v.aliasCoefficients l)).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c (v.blocks l) (p.particularBlock v c u l)
          (p.particularGaussianBlock v c u l).velocity).velocity n i j x))
    (hlinearS : UniformVelocity p.strip P (1+σ-4*κ)
      (fun l => HarmonicWaveInteraction.linearGoodBlock c (p.beforeSignedBlock v c u l)
        (p.signedBlock v c u l) (p.signedGaussianBlock v c u l).velocity)) :
    UniformVelocity p.strip P (1/2+σ+1/10)
      (fun l => HarmonicResidual.residualBlock c (p.afterSigned v c u) (p.finalBlock v c u l)
        ((p.nextCoefficients v c u).gaussian l) (v.aliasCoefficients l)) ∧
      (∀ l, HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.finalBlock v c u l)) := by
  have hκhalf : κ ≤ 1/2 := by linarith
  have hpart0 l := p.particularBlock_zero v c u l
  have hsigned0 l := (p.signed l).exactBlock_zero p.strip (p.signedRequest v c u)
  have hpartc l := p.particular_carrier v c u l
  have hpartdiv l : HarmonicWaveInteraction.ModeSolenoidal p.strip c
      (HarmonicWaveInteraction.withCarrier (v.blocks l) (p.particularBlock v c u l)) := by
    rw [withCarrier_of_same (hpartc l)]
    exact hdivpart l
  have hfirst := waveStage_residual_uniform c ho hκhalf hR u (p.afterParticular v c u)
    (p.afterParticular_mean v c u) (meanIncrement_of_cumulative hu) hbase.smooth
    v.blocks (p.particularBlock v c u) (fun i j _ => hold i j) (fun i j _ => hpart i j)
    hzero hpart0 hband (p.particularBlock_band v c u) hphase hk hkp hdiv hpartdiv
    hNormal hFreq hAng hzpart hP0 hP1 hpold hppart v.gaussian
    (fun l => (p.particularGaussianBlock v c u l).velocity) v.aliasCoefficients v.aliasCoefficients
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hlinearP i j hj).mono_exponent (show 1/2+σ+1/10 ≤ 1+σ-3*κ by linarith))
    (by linarith) (by linarith) (by linarith)
  have hbefore : ∀ i j, UniformWaveClass p.strip P (1/2)
      (fun l n x => (p.beforeSignedBlock v c u l).velocity n i j x) := by
    intro i j
    exact (hold i j).add ((hpart i j).mono_exponent (by linarith))
  have hbzero l : HarmonicWaveInteraction.ZeroMode (p.beforeSignedBlock v c u l) :=
    HarmonicStructurePreservation.zeroMode_addBlock (hzero l) (hpart0 l)
  have hbband l : (p.beforeSignedBlock v c u l).BandLimited v.residualBand := by
    have hb := addBlock_band (hband l) (p.particularBlock_band v c u l)
    simp only [max_self] at hb
    exact hb
  have hbdiv l : HarmonicWaveInteraction.ModeSolenoidal p.strip c (p.beforeSignedBlock v c u l) :=
    HarmonicStructurePreservation.modeSolenoidal_addBlock (hpartc l).frequency (hpartc l).phase
      (hpartc l).angular (fun n i j => (hold i j).smooth l n)
      (fun n i j => (hpart i j).smooth l n) (hphase l) (hdiv l) (hdivpart l)
  have hbpressure l n : HarmonicResidual.SmoothCoefficients p.strip.domain
      ((p.beforeSignedBlock v c u l).pressure n) := by
    intro j
    exact (hpold l n j).add (hppart l n j)
  have hbsame l : SameCarrier (p.beforeSignedBlock v c u l) (p.signedBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  have hsdiv l : HarmonicWaveInteraction.ModeSolenoidal p.strip c
      (HarmonicWaveInteraction.withCarrier (p.beforeSignedBlock v c u l) (p.signedBlock v c u l)) := by
    rw [withCarrier_of_same (hbsame l)]
    exact hdivsigned l
  have hm : (p.afterSigned v c u).mean = (p.afterParticular v c u).mean := by
    rw [p.afterSigned_mean v c u, p.afterParticular_mean v c u]
  have hmean : IncrementBounds p.strip (9/10) (p.afterParticular v c u).mean := by
    rw [p.afterParticular_mean v c u]
    exact meanIncrement_of_cumulative hu
  have hsecond := waveStage_residual_uniform c ho hκhalf hR (p.afterParticular v c u)
    (p.afterSigned v c u) hm hmean hbase.smooth (p.beforeSignedBlock v c u) (p.signedBlock v c u)
    (fun i j _ => hbefore i j) (fun i j _ => hsigned i j) hbzero hsigned0 hbband
    (fun l => (p.signed l).exactBlock_band p.strip (p.signedRequest v c u))
    hphase hk hkp hbdiv hsdiv hNormal hFreq hAng hzsigned hP0 hP1 hbpressure hpsigned
    (fun l => v.gaussian l + (p.particularGaussianBlock v c u l).velocity)
    (fun l => (p.signedGaussianBlock v c u l).velocity) v.aliasCoefficients v.aliasCoefficients
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hfirst i j hj).add ((hlinearS i j hj).mono_exponent
      (show 1/2+σ+1/10 ≤ 1+σ-4*κ by linarith)))
    (by linarith) (by linarith) (by linarith)
  refine ⟨hsecond, ?_⟩
  intro l
  exact HarmonicStructurePreservation.modeSolenoidal_addBlock (hbsame l).frequency (hbsame l).phase
    (hbsame l).angular (fun n i j => (hbefore i j).smooth l n)
    (fun n i j => (hsigned i j).smooth l n) (hphase l) (hbdiv l) (hdivsigned l)

end CycleParameters
end ActualWaveCycleGain

section DerivedRequestGain
open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest
open scoped ContDiff

/-- The actual full signed request is controlled by the current raw
residuals. Their smoothness and support are derived from primitive state
regularity and the actual pressure reconstruction. -/
theorem fullRequest_bounds_of_primitive (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    {α : ℝ} (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) :
    ∀ i, MeanClass (HarmonicWaveInteraction.productStrip G.strip) (α-1)
      (fun n x => fullRequest G.strip G.patch G.coord c u n x i) := by
  have H₀ : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have ht := H.theta G.patch.a_pos G.patch.a_lt_b
  have hz' := H₀.axial_reconstructed G.inner_pos G.exponent_pos G.length_eq hfixed
  have hs : ∀ n, MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (u.axialResidual c n) := by
    simpa only [G.inner_eq, G.outer_eq] using fun n => MeanStateRegularity.MovingField.movingSupport hz' n
  exact fullRequest_class G.strip G.patch G.coord c u
    (normalizedRequest_class G.region G.patch G.left_pos G.right_pos G.epsilon G.slow
      G.epsilon_pos G.epsilon_le_one G.slow_ge_one c u α ht.smooth hz'.smooth (fun n => MeanStateRegularity.MovingField.movingSupport ht n) hs hθ hz)

/-- The first actual wave supplies the current raw residuals and debt
used by the signed request. No post-wave residual estimate is assumed. -/
theorem waveStage_mean_gain (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point) (w : Oscillation Point)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    {σ κ : ℝ} (hσ : 1/5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1/100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (ho : OperatorBounds G.strip c.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hθ : MeanClass G.strip (1+σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1+σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    (hXC : SignedMeanGain.TensorClass G.strip (1+σ)
      (SignedMeanGain.covarianceIncrement u.oscillation w)) :
    let next := SignedMeanGain.waveStage G.gauge c u w q gaussian
    MeanClass G.strip (1+σ-κ) (next.pressure-u.pressure) ∧
      CorrectionState.CumulativeBounds G.strip next ∧
      MeanClass G.strip (1+σ-κ) (next.thetaResidual c) ∧
      MeanClass G.strip (1+σ-κ) (next.axialResidual c) ∧
      DefectBounds G.slowStrip (σ-κ) c next ∧
      (∀ i, MeanClass (HarmonicWaveInteraction.productStrip G.strip) (σ-κ)
        (fun n x => fullRequest G.strip G.patch G.coord c next n x i)) := by
  dsimp only
  have hs : movingStripData G.region G.gauge.radial.inner G.gauge.radial.outer
      G.leftWeight G.rightWeight G.inner_pos G.left_pos G.right_pos
      G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one = G.strip := by
    simp only [SignedMeanGain.Geometry.strip, G.inner_eq, G.outer_eq]
  have H₀ : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have HX : ∀ i j, GaugeDebtIncrement.Regular G.region G.gauge.radial.inner G.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w i j) := by
    simpa only [G.inner_eq, G.outer_eq] using
      (fun i j => MeanStateRegularity.MovingField.regular (hX i j))
  have hf := gaugeWaveStage_mean_from_covariance G.region G.gauge G.inner_pos G.exponent_pos
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one G.length_eq
    c u w q gaussian H.operators.regular H.base.smooth H₀.mean.regular
    (fun i j => MeanStateRegularity.MovingField.regular (H₀.covariance i j)) HX
    (hs.symm ▸ ho) (hs.symm ▸ hXC) hfixed (hs.symm ▸ hb) (hs.symm ▸ hu)
    (show 9/10 ≤ (1+σ)-κ by linarith) le_rfl
    (hs.symm ▸ hθ.mono_exponent (by linarith)) (hs.symm ▸ hz.mono_exponent (by linarith))
    (fun i => (hd i).mono_exponent (by linarith))
  rw [hs] at hf
  obtain ⟨hp, hcum, htheta, haxial, hdebt⟩ := hf
  have Hn := H.waveStage G.gauge w q gaussian hX
  refine ⟨hp, hcum, htheta, haxial, ?_, ?_⟩
  · simpa only [DefectBounds, SignedMeanGain.Geometry.slowStrip,
      show 1+(σ-κ) = 1+σ-κ by ring] using hdebt
  · have hr := fullRequest_bounds_of_primitive G c _ Hn
      (congrArg (fun a : State Point => a.pressure)
        (GaugeMomentBalances.reconstructState_idempotent _ _ _)) htheta haxial
    simpa only [show (1+σ-κ)-1 = σ-κ by ring] using hr

end DerivedRequestGain

section FurtherPreservation
open Set WeightedClasses MeanIncrementBounds CorrectionState
open scoped ContDiff

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

/-- Mean stages and the alias refresh leave the actual wave covariance
unchanged. Both finite wave increments are retained in this identity. -/
theorem next_covariance :
    (p.next v c u).covariance = u.covariance +
      SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) +
      SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v c u) := by
  change bilinearCovariance (p.next v c u).oscillation (p.next v c u).oscillation = _
  rw [p.next_oscillation]
  change bilinearCovariance (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u)
      (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u) =
    bilinearCovariance u.oscillation u.oscillation +
      (bilinearCovariance (u.oscillation + p.particularVelocity v c u)
        (u.oscillation + p.particularVelocity v c u) - bilinearCovariance u.oscillation u.oscillation) +
      (bilinearCovariance (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u)
        (u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u) -
        bilinearCovariance (u.oscillation + p.particularVelocity v c u)
          (u.oscillation + p.particularVelocity v c u))
  abel

theorem next_covariance_mem {α β γ : ℝ}
    (hα : γ ≤ α) (hβ : γ ≤ β)
    (hold : ∀ i j, MeanClass p.strip γ (u.covariance i j))
    (hp : SignedMeanGain.TensorClass p.strip α
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u)))
    (hs : SignedMeanGain.TensorClass p.strip β
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v c u))) :
    ∀ i j, MeanClass p.strip γ ((p.next v c u).covariance i j) := by
  intro i j
  rw [p.next_covariance v c u]
  exact ((hold i j).add ((hp i j).mono_exponent hα)).add ((hs i j).mono_exponent hβ)


/-- The edge weight is retained in all new Gaussian coefficients. -/
theorem next_gaussian_mem {w : ι → ℕ → CyclePoint → ℝ} {β : ℝ}
    (hold : ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => v.gaussian l n i j z))
    (hp : ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => (p.particularGaussianBlock v c u l).velocity n i j z))
    (hs : ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => (p.signedGaussianBlock v c u l).velocity n i j z)) :
    ∀ i j, LabelSumBounds.UniformClass p.strip w β
      (fun l n z => (p.nextCoefficients v c u).gaussian l n i j z) :=
  fun i j => ((hold i j).add (hp i j)).add (hs i j)

theorem next_inputSupport {U : Set CyclePoint} {S : ι → ℕ → Set CyclePoint}
    (hold : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (v.blocks l) (v.gaussian l) (v.aliasCoefficients l))
    (hp : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (p.particularBlock v c u l) (p.particularGaussianBlock v c u l).velocity 0)
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn U (S l)
      (p.signedBlock v c u l) (p.signedGaussianBlock v c u l).velocity 0) :
    ∀ l, HarmonicSourceSupport.InputSupportOn U (S l) ((p.nextCoefficients v c u).blocks l)
      ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l) :=
  fun l => LabelSupportPreservation.inputSupport_two_updates (hold l) (hp l) (hs l)

theorem next_oscillation_smooth {U : Set CyclePoint}
    (hold : WaveStateRegularity.AngularSmooth U u.oscillation)
    (hp : WaveStateRegularity.AngularSmooth U (p.particularVelocity v c u))
    (hs : WaveStateRegularity.AngularSmooth U (p.signedVelocity v c u)) :
    WaveStateRegularity.AngularSmooth U (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact (hold.add hp).add hs

theorem next_oscillation_periodic {U : Set PressureStream.Plane}
    (hold : OscillationPeriodic U u.oscillation)
    (hp : OscillationPeriodic U (p.particularVelocity v c u))
    (hs : OscillationPeriodic U (p.signedVelocity v c u)) :
    OscillationPeriodic U (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact (hold.add hp).add hs

theorem next_oscillation_support {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    (hold : WaveStateRegularity.WaveSupport U a b u.oscillation)
    (hp : WaveStateRegularity.WaveSupport U a b (p.particularVelocity v c u))
    (hs : WaveStateRegularity.WaveSupport U a b (p.signedVelocity v c u)) :
    WaveStateRegularity.WaveSupport U a b (p.next v c u).oscillation := by
  rw [p.next_oscillation]
  exact (hold.add hp).add hs

theorem finalBlock_zero (hold : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l)) :
    ∀ l, HarmonicWaveInteraction.ZeroMode (p.finalBlock v c u l) :=
  fun l => HarmonicStructurePreservation.zeroMode_addBlock
    (HarmonicStructurePreservation.zeroMode_addBlock (hold l) (p.particularBlock_zero v c u l))
    ((p.signed l).exactBlock_zero p.strip (p.signedRequest v c u))

theorem finalBlock_pressure_zero (hold : ∀ l n, (v.blocks l).pressure n 0 = 0) :
    ∀ l n, (p.finalBlock v c u l).pressure n 0 = 0 := by
  intro l
  apply HarmonicStructurePreservation.zeroPressure_addBlock
    (HarmonicStructurePreservation.zeroPressure_addBlock (hold l) ?_)
    ((p.signed l).exactBlock_pressure_zero p.strip (p.signedRequest v c u))
  intro n
  funext x
  exact congrFun ((ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).2 n) (cycleAssoc x)

theorem finalBlock_pressure_cumulative {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hσ : 1/5 ≤ σ) (hκsmall : κ ≤ 1/100000)
    (hold : ∀ j, LabelSumBounds.UniformWaveClass p.strip P 1
      (fun l n z => (v.blocks l).pressure n j z))
    (hp : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1+σ)
      (fun l n z => (p.particularBlock v c u l).pressure n j z))
    (hs : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1+σ-κ)
      (fun l n z => (p.signedBlock v c u l).pressure n j z)) :
    ∀ j, LabelSumBounds.UniformWaveClass p.strip P 1
      (fun l n z => (p.finalBlock v c u l).pressure n j z) :=
  fun j => ((hold j).add ((hp j).mono_exponent (by linarith))).add
    ((hs j).mono_exponent (by linarith))

end CycleParameters
end FurtherPreservation

end NavierStokes.CorrectionStep
