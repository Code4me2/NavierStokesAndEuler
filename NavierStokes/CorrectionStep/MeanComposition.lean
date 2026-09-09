import NavierStokes.CorrectionStep.WaveGains

/-!
# Exact field bookkeeping for one correction cycle: mean composition

Fifth part of `NavierStokes.CorrectionStep`.  It composes the mean stages:
uniform periodized coefficients, the coherent reference particular family, the
constructed mean stages, the uniform particular and signed gains, the
four-stage mean composition, and the moving covariance and Gaussian means.
-/

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds
open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section UniformPeriodizedCoefficients
open Set Filter Function WeightedClasses CorrectionState
open scoped ContDiff Topology
variable {D I ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable def jointRawBackground (a : ι → PeriodizedWaveBounds.CopyData D I) :
    LocalizedWaveBounds.WaveFamily D (ι × I) :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun j =>
    {(a j.1).background with amplitude := 0, pressure := 0})

noncomputable def jointRawCoefficients (a : ι → PeriodizedWaveBounds.CopyData D I) :
    LocalizedWaveBounds.WaveFamily D (ι × I) :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun j => (a j.1).raw j.2)

theorem uniform_localInput_of_coefficients
    (a : ι → PeriodizedWaveBounds.CopyData D I) {s : StripData D}
    {C : ι → ℕ → I → Set D} {W : ι → ℕ → D → ℝ} {α κ : ℝ}
    {d : LinearWaveBounds.GraphDirections D}
    (h : LocalizedWaveBounds.InputBounds s (fun n (j : ι × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) 0 κ d (jointRawBackground a))
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (ha : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x)*W l n x)
      α C (fun l => (a l).amplitude))
    (hp : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x)*W l n x)
      (α+1/2) C (fun l => (a l).pressure)) :
    LocalizedWaveBounds.InputBounds s (fun n (j : ι × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) α κ d (jointRawCoefficients a) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW l n x hx)
  exact ⟨h.loss_nonneg, h.radial_profile, h.radial_scale, h.fast_scale, h.frequency_scale,
    h.radius, h.inverse_radius, h.radial_base, h.frequency_base, h.axial_base,
    h.radial_base_aux, h.frequency_base_aux, h.axial_base_aux, h.normal, h.defect,
    fun j => (LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw ha).map (ContinuousLinearMap.proj j),
    LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw hp⟩

/-- The native solver estimates enter before summation over copies or
spatial labels. All bounds on the background remain local to `C`. -/
theorem uniform_common_bounds_from_raw
    (a : ι → PeriodizedWaveBounds.CopyData D I) (K : ι → PeriodizedWaveBounds.Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} {C : ι → ℕ → I → Set D} {W : ι → ℕ → D → ℝ} {α κ : ℝ}
    {d : LinearWaveBounds.GraphDirections D}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (h : LocalizedWaveBounds.InputBounds s (fun n (j : ι × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) 0 κ d (jointRawBackground a))
    (ha : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x)*W l n x)
      α C (fun l => (a l).amplitude))
    (hp : PeriodizedWaveBounds.UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x)*W l n x)
      (α+1/2) C (fun l => (a l).pressure))
    (hcut : PeriodizedWaveBounds.UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hκ : κ ≤ 1/2) {lo hi : ℝ} (hlo : 0 < lo)
    (hLower : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → lo ≤ ‖(a l).background.normal s d n x‖)
    (hUpper : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → ‖(a l).background.normal s d n x‖ ≤ hi)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s (fun n (j : ι × I) => C j.1 n j.2) (1/2)
      (fun n j _ => 1/(a j.1).background.frequency n))
    (hcover : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∈ C l n i ∨
      (((a l).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((a l).localized i).pressure n =ᶠ[𝓝 x] fun _ => 0)) :
    LabelSumBounds.UniformWaveClass s W α (fun l => (a l).common.amplitude) ∧
    LabelSumBounds.UniformWaveClass s W α (fun l => ((a l).commonCorrected s d).amplitude) ∧
    LabelSumBounds.UniformWaveClass s W (α+1/2) (fun l => (a l).common.pressure) ∧
    LabelSumBounds.UniformWaveClass s W (α+1/2-κ) (fun l => (a l).common.curlCorrection s d) ∧
    LabelSumBounds.UniformWaveClass s W (α+1/2-3*κ) (fun l => (a l).globalGood s d) := by
  have hin := uniform_localInput_of_coefficients a h hW ha hp
  have hout := hin.with_cutoff
    (LocalizedWaveBounds.LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hcut)
  exact LocalizedWaveBounds.uniform_common_bounds_from_supported_native a K hs C hW hout
    hκ hlo hLower hUpper hfreq hcover

namespace PeriodizedSignedParameters
variable (p : ι → PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D×ℝ → SignedWaveUpdate.Vec2)

/-- Literal stored coefficients inherit the joint estimates of the
actual common solves, including the exact-minus-tangent curl. -/
theorem uniform_block_bounds
    {P : ι → ℕ → D → ℝ} {α κ : ℝ}
    (ha : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) α (fun l => ((p l).copyData s request).common.amplitude))
    (he : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) α (fun l =>
        (((p l).copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) (p l).directions).amplitude))
    (hp : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) (α+1/2) (fun l => ((p l).copyData s request).common.pressure))
    (hc : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) (α+1/2-κ) (fun l =>
        ((p l).copyData s request).common.curlCorrection (HarmonicWaveInteraction.productStrip s) (p l).directions))
    (hg : LabelSumBounds.UniformWaveClass (HarmonicWaveInteraction.productStrip s)
      (fun l n x => P l n x.1) (α+1/2-3*κ) (fun l =>
        ((p l).copyData s request).globalGood (HarmonicWaveInteraction.productStrip s) (p l).directions)) :
    (∀ i j, LabelSumBounds.UniformWaveClass s P α (fun l n x => ((p l).tangentBlock s request).velocity n i j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s P α (fun l n x => ((p l).exactBlock s request).velocity n i j x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass s P (α+1/2) (fun l n x => ((p l).exactBlock s request).pressure n j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s P (α+1/2-κ) (fun l n x => ((p l).curlBlock s request).velocity n i j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s P (α+1/2-3*κ) (fun l n x => ((p l).goodBlock s request).velocity n i j x)) := by
  have ht := UniformBlockBounds.blockOfCoefficients_product_uniform
    (fun l => ((p l).copyData s request).common) (fun l => (p l).angularFrequency) ha hp
  have hx := UniformBlockBounds.blockOfCoefficients_product_uniform
    (fun l => ((p l).copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) (p l).directions)
    (fun l => (p l).angularFrequency) he hp
  have hd := UniformBlockBounds.commonCorrected_product_difference_uniform
    (fun l => (p l).copyData s request) (fun l => (p l).directions) (fun l => (p l).angularFrequency) hc
  have hgs := UniformBlockBounds.uniform_slice (s := s)
    (w := fun l n x => Real.sqrt (s.zeta x) * P l n x) hg
  have hgb := UniformBlockBounds.coefficientBlock_uniform
    (fun l => (p l).base.frequency) (fun l n x => (p l).base.phase n (x,0)) (fun l => (p l).angularFrequency)
    hgs (LabelSumBounds.UniformClass.zero (E := ℂ) (α := (0:ℝ)) hgs.weight_nonneg)
  exact ⟨ht.1,hx.1,hx.2,hd,hgb.1⟩

end PeriodizedSignedParameters

end UniformPeriodizedCoefficients

section CoherentReferenceParticular

open Set Filter Function CorrectionState WeightedClasses ParticularWaveAssembly ParticularWaveBounds
open scoped ContDiff Topology BigOperators
namespace ParticularParameters
open TorusInverse
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem common_amplitude (p : ParticularParameters P)
    (c : Context (P×Plane)) (u : State (P×Plane)) (b : HarmonicBlock (P×Plane))
    (G A : HarmonicResidual.BlockCoefficients (P×Plane)) (j : ℤ) (n : ℕ) :
    (p.copyData c u b G A j).common.amplitude n =
      angleLift (ParticularWaveBounds.commonVelocity (p.tangent j n)
        (residualSource c u b G A j n) (p.geometry n) (p.length_pos n).le (p.cutoff n)) := by
  funext z
  rcases z with ⟨⟨x,θ⟩,Y⟩
  apply tsum_congr
  intro k
  exact congrArg (fun w => p.cutoff n ((p.geometry n).coordinates k Y) • w)
    (complexCopyVelocity_angle (p.tangent j n) (residualSource c u b G A j n)
      (p.geometry n) (p.length_pos n).le k x θ Y)

theorem common_pressure (p : ParticularParameters P)
    (c : Context (P×Plane)) (u : State (P×Plane)) (b : HarmonicBlock (P×Plane))
    (G A : HarmonicResidual.BlockCoefficients (P×Plane)) (j : ℤ) (n : ℕ)
    (hk : (j:ℝ)*b.frequency n ≠ 0) :
    (p.copyData c u b G A j).common.pressure n =
      angleLift (ParticularWaveBounds.commonPressure (p.tangent j n)
        (residualSource c u b G A j n) (p.geometry n) (p.length_pos n).le (p.cutoff n)
          ((j:ℝ)*b.frequency n)) := by
  funext z
  rcases z with ⟨⟨x,θ⟩,Y⟩
  apply tsum_congr
  intro k
  exact congrArg (fun w => p.cutoff n ((p.geometry n).coordinates k Y) • w)
    (complexCopyPressure_angle (p.tangent j n) (residualSource c u b G A j n)
      (p.geometry n) (p.length_pos n).le k hk x θ Y)

/-- Every target band uses the same chosen reference tangent, geometry,
clock interval and cutoff. Only the current HR source is supplied at solve time. -/
noncomputable def fromReference
    (D : AssemblyData PhysicalParticularWave.Parameter) (h : ℝ) (gap : ℕ→ℕ) :
    ParticularParameters PhysicalParticularWave.Parameter where
  tangent j n := ScaledTangentTransport.transportTangent (D.reference.tangent j)
    (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)) (gap n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q D.reference.band)
      ((j:ℝ)*D.carrierBlock.frequency n) (PhysicalParticularWave.referenceFrequency D j))
  geometry n := CopySolveCompatibility.transportGeometry D.reference.geometry (gap n) 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
      (CoordinateAlgebra.A h+1/2)).ne'
  length n := D.reference.length /
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band)
  length_pos n := div_pos D.reference.length_pos
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
      (CoordinateAlgebra.A h+1/2))
  cutoff n := D.reference.cutoff ∘ CopySolveCompatibility.nativeTimeMap 0
    (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
  background := D.background
  directions := D.directions





end ParticularParameters

end CoherentReferenceParticular

section ConstructedMeanStages

open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest
open scoped ContDiff BigOperators
section
variable (g : GaugeData PressureStream.Plane) (r : RankData PressureStream.Plane)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    {coord cL cR A B : ℝ} (U : SlowRegion coord)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)
include hd hell
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL
local notation "slowStrip" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL
local notation "signedState" => u
local notation "temporalState" => temporalStageState g h index axial c u
theorem meanStages_constructed {σ κ : ℝ}
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n =
      ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hsigned : CorrectionState.CumulativeBounds stageStrip signedState)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (signedState).mean)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier (signedState).mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) ((signedState).covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier ((signedState).covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ ((signedState).thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ ((signedState).axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((signedState).thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((signedState).axialResidual c n))
    (hsθ : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier ((signedState).thetaResidual c))
    (hsz : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier ((signedState).axialResidual c))
    (hcθ : MeanClass stageStrip (1 + σ - 2 * κ) ((signedState).thetaResidual c))
    (hcz : MeanClass stageStrip (1 + σ - 2 * κ) ((signedState).axialResidual c))
    (hbarθ : MeanClass stageStrip (1 + σ + 17 / 100) (meanBar ((signedState).thetaResidual c)))
    (hbarz : MeanClass stageStrip (1 + σ + 17 / 100) (meanBar ((signedState).axialResidual c)))
    (hdebt : ∀ i : Fin 3, UnweightedClass slowStrip (1 + σ - 2 * κ)
      (fun n x => debt c signedState n x i))
    (hg : LocalRankDefect.RankGeometry g r U.carrier c temporalState)
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer) :
    IncrementBounds stageStrip (1 + σ - 2 * κ) (temporalIncrementState g h index axial c u) ∧
    IncrementBounds stageStrip (1 + σ - 2 * κ) (rankIncrementState g r axial c temporalState) ∧
    MeanClass stageStrip (1 + σ - 2 * κ) ((rankStageState g r axial c temporalState).pressure - u.pressure) ∧
    CorrectionState.CumulativeBounds stageStrip (rankStageState g r axial c temporalState) ∧
    DefectBounds slowStrip (σ + 1 / 10) c (rankStageState g r axial c temporalState) ∧
    MeanClass stageStrip (1 + (σ + 1 / 10)) ((rankStageState g r axial c temporalState).thetaResidual c) ∧
    MeanClass stageStrip (1 + (σ + 1 / 10))
      ((rankStageState g r axial c temporalState).axialResidual c -
        fun n x => temporalAliasState g h index c signedState n (x,0) 2) := by
  have hH : 9 / 10 ≤ 1 + σ - 2 * κ := by linarith
  have hκ : 2 * κ ≤ 9 / 10 := by linarith
  have hβ : 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 1 - 2 * κ := by linarith
  obtain ⟨hi, hp, htCum, htSmooth, htSupport, htTheta, htAxial⟩ :=
    gaugeTemporalStage_constructed U g ha hd hcL hcR ε L hε hεone hL hell
      hh hscale index gap hgap axial c signedState ho.epsilon_eq hv hfast hfixed
      hH hκ hβ ho hb hsigned hop hbase hm hms hW hWs hθ hz hpθ hpz hsθ hsz hcθ hcz
      (hbarθ.mono_exponent (by linarith)) (hbarz.mono_exponent (by linarith))
  have hiSmooth := gaugeTemporalIncrement_smooth U g ha hd hell h index axial
    c signedState hθ hz hpθ hpz hsz
  have hiSupport : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalIncrementState g h index axial c u) := by
    have hs n := temporalIncrementState_supportedGauge U g ha hd hell c signedState
      h index axial n (hz n) (hpz n) (hsz n) (hsθ n)
    exact ⟨fun n => (hs n).1, fun n => (hs n).2.1, fun n => (hs n).2.2⟩
  have hmReg : GaugeDebtIncrement.RegularTriple U g.radial.inner g.radial.outer (signedState).mean :=
    ⟨⟨hm.radial, hms.radial⟩, ⟨hm.angular, hms.angular⟩, ⟨hm.axial, hms.axial⟩⟩
  have hiReg : GaugeDebtIncrement.RegularTriple U g.radial.inner g.radial.outer
      (temporalIncrementState g h index axial c u) :=
    ⟨⟨hiSmooth.radial, hiSupport.radial⟩, ⟨hiSmooth.angular, hiSupport.angular⟩,
      ⟨hiSmooth.axial, hiSupport.axial⟩⟩
  have htDebt := GaugeDebtIncrement.temporalStage_debt_mem U ha g.radial.inner_lt_outer
    hcL hcR ε L hε hεone hL g h index axial c signedState
    hop hbase hmReg hiReg (fun i j => ⟨hW i j, hWs i j⟩) ho hb hsigned.velocity hi hH hκ le_rfl hdebt
  have hcov : (temporalState).covariance = (signedState).covariance :=
    gaugeTemporalStage_covariance g h index axial c signedState
  have htW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) ((temporalState).covariance i j) := by
    simpa only [hcov] using hW
  have htWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier
      ((temporalState).covariance i j) := by simpa only [hcov] using hWs
  let aliasField : ScalarField Point := fun n x =>
    temporalAliasState g h index c signedState n (x,0) 2
  obtain ⟨hrInc, hrPressure, hrCum, _, _, hrTheta, hrAxial⟩ :=
    gaugeRankStage_constructed U g r ha hd hcL hcR ε L hε hεone hL hell
      axial c temporalState hg hparam hB hleft hright hH hκ hβ hv rfl
      ho hb htCum hop hbase htSmooth htSupport htW htWs
      (RankStateBounds.debtClass_of_components _ htDebt) aliasField htTheta htAxial
  have hrDebt := MovingMomentBounds.rankStage_defectBounds U g r ha hcL hcR
    ε L hε hεone hL hell axial c temporalState hg hop hbase htSmooth
    ⟨htSupport.radial, htSupport.angular, htSupport.axial⟩ htW htWs hV hG
    ho hb htCum.velocity hrInc hH (show 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 9 / 10 - 2 * κ by linarith)
  have hpressure : MeanClass stageStrip (1 + σ - 2 * κ)
      ((rankStageState g r axial c temporalState).pressure - u.pressure) := by
    apply class_congr (hp.add hrPressure)
    intro n x hx
    change (rankStageState g r axial c temporalState).pressure n x - u.pressure n x =
      ((temporalState).pressure n x - u.pressure n x) +
        ((rankStageState g r axial c temporalState).pressure n x - (temporalState).pressure n x)
    ring
  exact ⟨hi, hrInc, hpressure, hrCum, hrDebt, hrTheta, hrAxial⟩

end

end ConstructedMeanStages

section UniformParticularGain

open Set Filter Function WeightedClasses CorrectionState ParticularWaveAssembly ParticularWaveBounds
open scoped ContDiff Topology BigOperators
namespace ParticularParameters
open TorusInverse
variable {Q ι : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (p : ι → ParticularParameters Q) (s : StripData (Q×Plane))
    (c : Context (Q×Plane)) (u : State (Q×Plane))
    (b : ι → HarmonicBlock (Q×Plane)) (G A : ι → HarmonicResidual.BlockCoefficients (Q×Plane))
    (N : ℕ)

theorem uniform_assembled_bounds {W : ι → ℕ → (Q×ℝ)×Plane → ℝ} {α κ : ℝ}
    (hW : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ W l n x)
    (ha : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W α
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).amplitude))
    (hp : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α+1/2)
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).pressure))
    (hg : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α+1/2-3*κ)
      (fun l => ((p l).copyData c u (b l) (G l) (A l) j).globalGood (nativeStrip s) (p l).directions)) :
    (∀ i j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0))) α
      (fun l n x => ((p l).updateBlock s c u (b l) (G l) (A l) N).velocity n i j x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0))) (α+1/2)
      (fun l n x => ((p l).updateBlock s c u (b l) (G l) (A l) N).pressure n j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0))) (α+1/2-3*κ)
      (fun l n x => ((p l).goodBlock s c u (b l) (G l) (A l) N).velocity n i j x)) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg ((nativeStrip s).zeta x)) (hW l n x hx)
  have hupdate := UniformBlockBounds.native_assembledBlock_original_uniform (s := s)
    N (fun l => (b l).frequency) (fun l => (b l).phase) (fun l => (b l).angularFrequency) hw ha hp
  have hgood := UniformBlockBounds.native_assembledBlock_original_uniform (s := s)
    N (fun l => (b l).frequency) (fun l => (b l).phase) (fun l => (b l).angularFrequency) hw hg
    (fun _ _ => LabelSumBounds.UniformClass.zero (E := ℂ) (α := (0:ℝ)) hw)
  exact ⟨hupdate.1,hupdate.2,hgood.1⟩

theorem uniform_linearGood_bounds {W : ι → ℕ → (Q×ℝ)×Plane → ℝ} {α κ : ℝ}
    (C : ∀ l j, j ∈ modes N → (p l).NativeControl s c u (b l) (G l) (A l) j (W l) α κ)
    (dyn : ∀ l j hj, NativeDynamics (C l j hj))
    (hκ : κ ≤ 1/2)
    (hW : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ W l n x)
    (hg : ∀ i j, LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0)))
      (α+1/2-3*κ) (fun l n x => ((p l).goodBlock s c u (b l) (G l) (A l) N).velocity n i j x))
    (hN : ∀ l, (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).BandLimited N)
    (hB : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle (p l).directions) (reindexCoefficients angleShuffle (p l).background))
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((b l).phase n) s.domain)
    (hkp : ∀ l n, (b l).angularFrequency n ≠ 0) :
    ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass s (fun l n x => W l n (angleShuffle (x,0)))
      (α+1/2-3*κ) (fun l n x =>
        (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i j x +
        (HarmonicWaveInteraction.linearGoodBlock c (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N)
          ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity).velocity n i j x) := by
  have hb l := (p l).assembled_bounds s c u (b l) (G l) (A l) N (C l) (hW l) hκ
  apply linearGoodBlock_cancel_uniform c b (fun l => (p l).updateBlock s c u (b l) (G l) (A l) N)
    (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l))
    (fun l => (p l).goodBlock s c u (b l) (G l) (A l) N)
    (fun l => ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity)
    hrad (fun _ => contDiffOn_const) hB
    (fun l => HarmonicWaveInteraction.waveBounds_smooth (hb l).1 (assembledBlock_zero _ _ _ _ _ _).1)
    (fun l => pressureBounds_smooth (hb l).2.1 (assembledBlock_zero _ _ _ _ _ _).2)
    hphase hkp (fun l => HarmonicResidual.residualBlock_conjugate _ _ _ _ _)
    (fun _ => (assembledBlock_real _ _ _ _ _ _).1) (fun i j _ => hg i j)
  intro l n x hx θ i
  exact congrFun ((p l).context_linear_cancellation s c u (b l) (G l) (A l) N (C l) (dyn l)
    hκ (hN l) hB hrad (hm l) n (x,θ) hx) i

theorem uniform_residual_gain {W : ι → ℕ → (Q×ℝ)×Plane → ℝ} {α κ : ℝ}
    (C : ∀ l j, j ∈ modes N → (p l).NativeControl s c u (b l) (G l) (A l) j (W l) α κ)
    (dyn : ∀ l j hj, NativeDynamics (C l j hj))
    (hα : 7/10 ≤ α) (hκ : κ ≤ 1/100000)
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (hb : MeanIncrementBounds.BaseBounds s c.base)
    (hu : MeanIncrementBounds.CumulativeBounds s u.mean)
    (v : State (Q×Plane)) (hmean : v.mean = u.mean)
    (hW : ∀ l n x, x ∈ (nativeStrip s).domain → 0 ≤ W l n x)
    (hWone : ∀ l n x, x ∈ s.domain → W l n (angleShuffle (x,0)) ≤ 1)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s)
      (reindexDirections angleShuffle (p l).directions) (reindexCoefficients angleShuffle (p l).background))
    (hcopy : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W α
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).amplitude))
    (hpressure : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α+1/2)
      (fun l => ((p l).wave s c u (b l) (G l) (A l) j).pressure))
    (hgood : ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass (nativeStrip s) W (α+1/2-3*κ)
      (fun l => ((p l).copyData c u (b l) (G l) (A l) j).globalGood (nativeStrip s) (p l).directions))
    (hold : UniformHarmonicInteraction.UniformVelocity s (fun l n x => W l n (angleShuffle (x,0))) (1/2) b)
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    {M : ℕ} (hband : ∀ l, (b l).BandLimited M)
    (hsource : ∀ l, (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).BandLimited N)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((b l).phase n) s.domain)
    (hk : ∀ l n, (b l).frequency n ≠ 0) (hkp : ∀ l n, (b l).angularFrequency n ≠ 0)
    (hdiv : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (b l))
    (hpold : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((b l).pressure n))
    {patch : ℕ → ι → Set (Q×Plane)}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s patch 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (b l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s patch (-(1/2)) (fun n l _ => (b l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s patch (-(1/2))
      (fun n l _ => ((b l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ patch n l → ∀ i j, j ≠ 0 →
      ((p l).updateBlock s c u (b l) (G l) (A l) N).velocity n i j =ᶠ[𝓝 x] fun _ => 0) :
    UniformHarmonicInteraction.UniformVelocity s (fun l n x => W l n (angleShuffle (x,0))) (α+1/10)
      (fun l => HarmonicResidual.residualBlock c v
        (HarmonicWaveInteraction.addBlock (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N))
        (G l + ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity) (A l)) := by
  have hkhalf : κ ≤ 1/2 := by linarith
  have hblocks := uniform_assembled_bounds p s c u b G A N hW hcopy hpressure hgood
  have hlin := uniform_linearGood_bounds p s c u b G A N C dyn hkhalf hW hblocks.2.2
    hsource hb.smooth (operator_radial_smooth ho) hm hphase hkp
  have hnewdiv l : HarmonicWaveInteraction.ModeSolenoidal s c
      (HarmonicWaveInteraction.withCarrier (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N)) := by
    rw [withCarrier_of_same (show SameCarrier (b l) ((p l).updateBlock s c u (b l) (G l) (A l) N) from ⟨rfl,rfl,rfl⟩)]
    exact (p l).modeSolenoidal s c u (b l) (G l) (A l) N (C l) (dyn l) hkhalf (hW l) (hm l) (hphase l) (hkp l)
  exact waveStage_residual_uniform c ho hkhalf hR u v hmean (meanIncrement_of_cumulative hu) hb.smooth
    b (fun l => (p l).updateBlock s c u (b l) (G l) (A l) N) hold (fun i j _ => hblocks.1 i j)
    hzero (fun _ => (assembledBlock_zero _ _ _ _ _ _).1) hband
    (fun l => (p l).updateBlock_band _ _ _ _ _ _ _) hphase hk hkp hdiv hnewdiv hNormal hFreq hAng hz
    (fun l n x hx => hW l n _ hx) hWone hpold (fun l n j => (hblocks.2.1 j).smooth l n)
    G (fun l => ((p l).gaussianBlock c u (b l) (G l) (A l) N).velocity) A A
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hlin i j hj).mono_exponent (by linarith))
    (by linarith) (by linarith) (by linarith)

end ParticularParameters

end UniformParticularGain

section UniformSignedGain

open Set Filter Function WeightedClasses MeanIncrementBounds CorrectionState
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PeriodizedSignedParameters
variable {D I ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (p : ι → PeriodizedSignedParameters D I) (s : StripData D)
    (request : ℕ → D×ℝ → SignedWaveUpdate.Vec2)
    {P : ι → ℕ → D → ℝ} {β κ : ℝ}
    (C : ∀ l, (p l).NativeControl s (P l) κ)
    (dyn : ∀ l, NativeDynamics (C l) request) (i₀ : I)

include i₀

theorem uniform_linearGood_bounds
    (hκ : κ ≤ 1/2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (hkp : ∀ l n, (p l).base.frequency n * (dyn l).slope n = ((p l).angularFrequency n : ℝ))
    (hkpne : ∀ l n, (p l).angularFrequency n ≠ 0)
    (c : Context D) (hB : SmoothTriple s.domain c.base)
    (hrad : ∀ n, ContDiffOn ℝ ∞ (HarmonicResidual.contextFrame c n).radial s.domain)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) (p l).directions (p l).base)
    (a : ι → HarmonicBlock D) (hc : ∀ l, SameCarrier (a l) ((p l).exactBlock s request))
    (hg : UniformHarmonicInteraction.UniformVelocity s P (β+1-3*κ)
      (fun l => (p l).goodBlock s request)) :
    UniformHarmonicInteraction.UniformVelocity s P (β+1-3*κ)
      (fun l => HarmonicWaveInteraction.linearGoodBlock c (a l) ((p l).exactBlock s request)
        ((p l).gaussianBlock s request).velocity) := by
  let z : ι → HarmonicBlock D := fun l => ErrorHarmonics.zeroBlock (a l).frequency (a l).phase (a l).angularFrequency 0
  have hb l := (C l).block_bounds hκ request hR
  have hphase l n : ContDiffOn ℝ ∞ ((a l).phase n) s.domain := by
    rw [← (hc l).phase]
    exact (((dyn l).angular i₀).phase_smooth n).comp (SignedWaveUpdate.zeroSection (D := D)).contDiff.contDiffOn
      (fun x hx => hx)
  have hka l n : (a l).angularFrequency n ≠ 0 := by rw [← (hc l).angular]; exact hkpne l n
  have he := linearGoodBlock_cancel_uniform c a (fun l => (p l).exactBlock s request) z
    (fun l => (p l).goodBlock s request) (fun l => ((p l).gaussianBlock s request).velocity)
    hrad (fun _ => contDiffOn_const) hB
    (fun l => HarmonicWaveInteraction.waveBounds_smooth (hb l).2.1 ((p l).exactBlock_zero s request))
    (fun l => pressureBounds_smooth (hb l).2.2.1 ((p l).exactBlock_pressure_zero s request))
    hphase hka (fun l n i => ErrorHarmonics.zeroBlock_symmetric _ _ _ _ n i)
    (fun _ => (SignedWaveUpdate.coefficientBlock_symmetric _ _ _ _ _).1) hg ?_
  · intro i j hj
    simpa [z, ErrorHarmonics.zeroBlock, HarmonicFields.constantCoefficient, Finsupp.single_apply,
      hj, Ne.symm hj] using he i j hj
  · intro l n x hx θ i
    have hgood : SameCarrier (a l) ((p l).goodBlock s request) :=
      ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
    have hgauss : SameCarrier (a l) ((p l).gaussianBlock s request) :=
      ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
    have hh := congrFun ((dyn l).context_linear_identity i₀ hκ hR (hkp l) c hB hrad (hm l)
      (a l) (hc l) n (x,θ) hx) i
    rw [withCarrier_of_same hgood]
    have heval : (HarmonicFields.field (((p l).gaussianBlock s request).velocity n i)
        ((a l).frequency n) ((a l).phase n) ((a l).angularFrequency n) (x,θ)).re =
        ((p l).gaussianBlock s request).oscillation n (x,θ) i := by
      simp only [HarmonicBlock.oscillation, hgauss.frequency, hgauss.phase, hgauss.angular]
    rw [heval]
    simpa only [z, HarmonicWaveInteraction.withCarrier, ErrorHarmonics.zeroBlock,
      HarmonicBlock.oscillation, HarmonicResidual.field_constant, Pi.zero_apply, Complex.ofReal_zero,
      Complex.zero_re, Pi.add_apply, add_zero] using hh

theorem uniform_residual_gain {B : ℝ}
    (hB : 7/10 ≤ B) (hκ : κ ≤ 1/100000)
    (hRquest : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) (B-1/2-κ) (fun n x => request n x j))
    (geom : ∀ l n, CurlClassBounds.CylindricalGeometry (HarmonicWaveInteraction.productStrip s).domain
      ((p l).base.radius n) ((p l).directions.radialField n) (fun _ => (p l).directions.angular)
      ((p l).directions.axialField (HarmonicWaveInteraction.productStrip s) n))
    (ht : ∀ l n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ (C l).phasePatch n i →
      ⟪(p l).base.normal (HarmonicWaveInteraction.productStrip s) (p l).directions n x,
        (p l).fundamental i n x⟫_ℝ = 0)
    (hkp : ∀ l n, (p l).base.frequency n*(dyn l).slope n = ((p l).angularFrequency n : ℝ))
    (hkpne : ∀ l n, (p l).angularFrequency n ≠ 0)
    (c : Context D) (u v : State D) (hmean : v.mean = u.mean)
    (ho : OperatorBounds s c.operators κ) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (hbase : BaseBounds s c.base) (hu : MeanIncrementBounds.CumulativeBounds s u.mean)
    (hm : ∀ l, WaveFrameMatch c (HarmonicWaveInteraction.productStrip s) (p l).directions (p l).base)
    (a : ι → HarmonicBlock D) (hc : ∀ l, SameCarrier (a l) ((p l).exactBlock s request))
    (ha : UniformHarmonicInteraction.UniformVelocity s P (1/2) a)
    (hnew : UniformHarmonicInteraction.UniformVelocity s P (B-κ) (fun l => (p l).exactBlock s request))
    (hgood : UniformHarmonicInteraction.UniformVelocity s P (B+1/2-4*κ) (fun l => (p l).goodBlock s request))
    (ha0 : ∀ l, HarmonicWaveInteraction.ZeroMode (a l)) {M : ℕ} (hM : ∀ l, (a l).BandLimited M)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((a l).phase n) s.domain)
    (hk : ∀ l n, (a l).frequency n ≠ 0) (hka : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hdiv : ∀ l, HarmonicWaveInteraction.ModeSolenoidal s c (a l))
    (hpold : ∀ l n, HarmonicResidual.SmoothCoefficients s.domain ((a l).pressure n))
    {patch : ℕ → ι → Set D}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted s patch 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (a l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted s patch (-(1/2)) (fun n l _ => (a l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted s patch (-(1/2)) (fun n l _ => ((a l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ patch n l → ∀ i j, j ≠ 0 →
      ((p l).exactBlock s request).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (G A : ι → HarmonicResidual.BlockCoefficients D)
    (hold : UniformHarmonicInteraction.UniformVelocity s P (B+1/10)
      (fun l => HarmonicResidual.residualBlock c u (a l) (G l) (A l))) :
    UniformHarmonicInteraction.UniformVelocity s P (B+1/10)
      (fun l => HarmonicResidual.residualBlock c v
        (HarmonicWaveInteraction.addBlock (a l) ((p l).exactBlock s request))
        (G l+((p l).gaussianBlock s request).velocity) (A l)) := by
  have hkhalf : κ ≤ 1/2 := by linarith
  have hgood' : UniformHarmonicInteraction.UniformVelocity s P ((B-1/2-κ)+1-3*κ)
      (fun l => (p l).goodBlock s request) := by
    convert! hgood using 1
    ring
  have hlin := uniform_linearGood_bounds p s request C dyn i₀ hkhalf hRquest hkp hkpne c hbase.smooth
    (operator_radial_smooth ho) hm a hc hgood'
  have hnewdiv l : HarmonicWaveInteraction.ModeSolenoidal s c
      (HarmonicWaveInteraction.withCarrier (a l) ((p l).exactBlock s request)) := by
    rw [withCarrier_of_same (hc l)]
    exact (dyn l).modeSolenoidal i₀ hkhalf hRquest (geom l) (ht l) (hkp l) (hkpne l) c (hm l)
  exact waveStage_residual_uniform c ho hkhalf hR u v hmean (meanIncrement_of_cumulative hu) hbase.smooth
    a (fun l => (p l).exactBlock s request) ha hnew ha0 (fun l => (p l).exactBlock_zero s request)
    hM (fun l => (p l).exactBlock_band s request) hphase hk hka hdiv hnewdiv hNormal hFreq hAng hz
    (fun l => (C l).envelope_nonneg) hP1 hpold
    (fun l => pressureBounds_smooth ((C l).block_bounds hkhalf request hRquest).2.2.1
      ((p l).exactBlock_pressure_zero s request)) G (fun l => ((p l).gaussianBlock s request).velocity) A A
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _)
    (fun i j hj => (hold i j hj).add ((hlin i j hj).mono_exponent (by linarith)))
    (by linarith) (by linarith) (by linarith)

end PeriodizedSignedParameters

end UniformSignedGain

section CycleUniformComposition

open Set Filter WeightedClasses MeanIncrementBounds CorrectionState
open scoped ContDiff Topology BigOperators

theorem incrementBounds_updated {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {H : ℝ} {a b : Triple D}
    (ha : IncrementBounds s H a) (hb : IncrementBounds s H b) :
    IncrementBounds s H (updated a b) :=
  ⟨ha.radial.add hb.radial, ha.angular.add hb.angular, ha.axial.add hb.axial⟩

theorem updated_assoc {D : Type} (a b c : Triple D) :
    updated (updated a b) c = updated a (updated b c) := by
  apply triple_ext <;> exact add_assoc _ _ _

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

/-- The actual two wave increments retain the cumulative bound and the
difference from the fixed primary family, with constants before labels. -/
theorem finalBlock_uniform_cumulative
    (primary : ι → HarmonicBlock CyclePoint) {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hσ : 1/5 ≤ σ) (hκsmall : κ ≤ 1/100000)
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (17/25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (hsigned : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ-κ)
      (fun l n x => (p.signedBlock v c u l).velocity n i j x)) :
    (∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2)
      (fun l n x => (p.finalBlock v c u l).velocity n i j x)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass p.strip P (17/25)
      (fun l n x => (p.finalBlock v c u l).velocity n i j x - (primary l).velocity n i j x)) := by
  constructor
  · intro i j
    exact ((hold i j).add ((hpart i j).mono_exponent (by linarith))).add
      ((hsigned i j).mono_exponent (by linarith))
  · intro i j
    apply (((hdiff i j).add ((hpart i j).mono_exponent (by linarith))).add
      ((hsigned i j).mono_exponent (by linarith))).congr
    intro l n x hx
    change (v.blocks l).velocity n i j x - (primary l).velocity n i j x +
      (p.particularBlock v c u l).velocity n i j x + (p.signedBlock v c u l).velocity n i j x =
      (v.blocks l).velocity n i j x + (p.particularBlock v c u l).velocity n i j x +
      (p.signedBlock v c u l).velocity n i j x - (primary l).velocity n i j x
    ring

theorem finalBlock_increment_bounds {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hκ : 0 ≤ κ)
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ)
      (fun l n x => (p.particularBlock v c u l).velocity n i j x))
    (hsigned : ∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ-κ)
      (fun l n x => (p.signedBlock v c u l).velocity n i j x))
    (hpp : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1+σ)
      (fun l n x => (p.particularBlock v c u l).pressure n j x))
    (hsp : ∀ j, LabelSumBounds.UniformWaveClass p.strip P (1+σ-κ)
      (fun l n x => (p.signedBlock v c u l).pressure n j x)) :
    (∀ i j, LabelSumBounds.UniformWaveClass p.strip P (1/2+σ-κ)
      (fun l n x => (p.finalBlock v c u l).velocity n i j x - (v.blocks l).velocity n i j x)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass p.strip P (1+σ-κ)
      (fun l n x => (p.finalBlock v c u l).pressure n j x - (v.blocks l).pressure n j x)) := by
  constructor
  · intro i j
    apply (((hpart i j).mono_exponent (by linarith)).add (hsigned i j)).congr
    intro l n x hx
    change (p.particularBlock v c u l).velocity n i j x + (p.signedBlock v c u l).velocity n i j x =
      (v.blocks l).velocity n i j x + (p.particularBlock v c u l).velocity n i j x +
      (p.signedBlock v c u l).velocity n i j x - (v.blocks l).velocity n i j x
    ring
  · intro j
    apply (((hpp j).mono_exponent (by linarith)).add (hsp j)).congr
    intro l n x hx
    change (p.particularBlock v c u l).pressure n j x + (p.signedBlock v c u l).pressure n j x =
      (v.blocks l).pressure n j x + (p.particularBlock v c u l).pressure n j x +
      (p.signedBlock v c u l).pressure n j x - (v.blocks l).pressure n j x
    ring

/-- Apply the complete actual mean increment once to the stored harmonic
residual. The pressure-alias refresh contributes only an angular zero mode. -/
theorem meanStages_residual_gain {P : ι → ℕ → CyclePoint → ℝ} {σ κ : ℝ}
    (hκsmall : κ ≤ 1/100000)
    (ho : OperatorBounds p.strip c.operators κ)
    (hR : ∀ x ∈ p.strip.domain, 0 < c.operators.radius x)
    (hb : SmoothTriple p.strip.domain c.base)
    (hm : SmoothTriple p.strip.domain u.mean)
    (hTemporal : IncrementBounds p.strip (1+σ-2*κ) (p.temporalIncrement v c u))
    (hRank : IncrementBounds p.strip (1+σ-2*κ) (p.rankIncrement v c u))
    (hvelocity : UniformHarmonicInteraction.UniformVelocity p.strip P (1/2) (p.finalBlock v c u))
    {C : ℕ → ι → Set CyclePoint}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted p.strip C 0
      (fun n l x => HarmonicMeanInteraction.slowNormal c ho hR (v.blocks l).phase n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1/2)) (fun n l _ => (v.blocks l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted p.strip C (-(1/2))
      (fun n l _ => ((v.blocks l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ p.strip.domain → x ∉ C n l → ∀ i j, j ≠ 0 →
      (p.finalBlock v c u l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hold : UniformHarmonicInteraction.UniformVelocity p.strip P (1/2+σ+1/10)
      (fun l => HarmonicResidual.residualBlock c (p.afterSigned v c u) (p.finalBlock v c u l)
        ((p.nextCoefficients v c u).gaussian l) (v.aliasCoefficients l))) :
    UniformHarmonicInteraction.UniformVelocity p.strip P (1/2+(σ+1/10))
      (fun l => HarmonicResidual.residualBlock c (p.next v c u) ((p.nextCoefficients v c u).blocks l)
        ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l)) := by
  have hh := incrementBounds_updated hTemporal hRank
  have he : (p.next v c u).mean = updated (p.afterSigned v c u).mean
      (updated (p.temporalIncrement v c u) (p.rankIncrement v c u)) := by
    rw [p.next_mean v c u, p.afterSigned_mean v c u, updated_assoc]
  have hms : SmoothTriple p.strip.domain (p.afterSigned v c u).mean := by
    simpa only [p.afterSigned_mean v c u] using hm
  have hout := meanStage_residual_uniform c ho (by linarith) hR (p.afterSigned v c u) (p.next v c u)
    (updated (p.temporalIncrement v c u) (p.rankIncrement v c u)) he hb hms hh (p.finalBlock v c u)
    hvelocity hNormal hFreq hAng hz ((p.nextCoefficients v c u).gaussian) v.aliasCoefficients v.aliasCoefficients
    (fun _ _ _ => by rw [sub_self]; exact HarmonicResidual.band_zero _) hold (by linarith)
  simp only [add_assoc] at hout ⊢
  exact hout

end CycleParameters

end CycleUniformComposition

section ActualMovingCovariance

open Set MeasureTheory WeightedClasses MeanIncrementBounds CorrectionState LocalSignedRequest
open scoped ContDiff BigOperators

/-- Whole-fiber periodicity of the actual real oscillation. -/
def OscillationPeriodic (U : Set PressureStream.Plane) (w : Oscillation Point) : Prop :=
  ∀ n R s, s ∈ U → ∀ θ, FourierAlias.TorusPeriodic (fun Y => w n ((R,(s,Y)),θ))

theorem OscillationPeriodic.add {U : Set PressureStream.Plane} {u w : Oscillation Point}
    (hu : OscillationPeriodic U u) (hw : OscillationPeriodic U w) : OscillationPeriodic U (u+w) :=
  fun n R s hs θ Y k => congrArg₂ (·+·) (hu n R s hs θ Y k) (hw n R s hs θ Y k)

theorem OscillationPeriodic.bilinearCovariance {U : Set PressureStream.Plane} {u w : Oscillation Point}
    (hu : OscillationPeriodic U u) (hw : OscillationPeriodic U w) (i j : Fin 3) :
    MeanStateRegularity.Periodic U (bilinearCovariance u w i j) := by
  intro n R s hs Y k
  unfold CorrectionState.bilinearCovariance CorrectionState.angularAverage
  apply congrArg (fun t : ℝ => t / (2 * Real.pi))
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact congrArg₂ (· * ·) (congrFun (hu n R s hs θ Y k) i) (congrFun (hw n R s hs θ Y k) j)

theorem OscillationPeriodic.covarianceIncrement {U : Set PressureStream.Plane} {u w : Oscillation Point}
    (hu : OscillationPeriodic U u) (hw : OscillationPeriodic U w) (i j : Fin 3) :
    MeanStateRegularity.Periodic U (SignedMeanGain.covarianceIncrement u w i j) :=
  MeanStateRegularity.Periodic.sub ((hu.add hw).bilinearCovariance (hu.add hw) i j)
    (hu.bilinearCovariance hu i j)

theorem covarianceIncrement_moving {coord a b : ℝ} (U : SlowRegion coord)
    {u w : Oscillation Point}
    (hu : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hw : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) w)
    (hs : WaveStateRegularity.WaveSupport U a b w)
    (hup : OscillationPeriodic U.carrier u) (hwp : OscillationPeriodic U.carrier w) (i j : Fin 3) :
    GaugeMomentBalances.MovingField U a b (SignedMeanGain.covarianceIncrement u w i j) :=
  MeanStateRegularity.MovingField.of_regular (WaveStateRegularity.covarianceIncrement_regular U hu hw hs i j)
    (hup.covarianceIncrement hwp i j)

theorem symmetricCovariance_moving {coord a b : ℝ} (U : SlowRegion coord)
    {u w : Oscillation Point}
    (hu : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hw : WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) w)
    (hs : WaveStateRegularity.WaveSupport U a b w)
    (hup : OscillationPeriodic U.carrier u) (hwp : OscillationPeriodic U.carrier w) (i j : Fin 3) :
    GaugeMomentBalances.MovingField U a b (LabelSumBounds.symmetricCovariance u w i j) := by
  have h₁ : GaugeDebtIncrement.Regular U a b (bilinearCovariance u w i j) := by
    rw [bilinearCovariance_comm u w i j]
    exact WaveStateRegularity.bilinearCovariance_regular U hw hu hs j i
  exact MeanStateRegularity.MovingField.add
    (MeanStateRegularity.MovingField.of_regular h₁ (hup.bilinearCovariance hwp i j))
    (MeanStateRegularity.MovingField.of_regular
      (WaveStateRegularity.bilinearCovariance_regular U hw hu hs i j) (hwp.bilinearCovariance hup i j))

end ActualMovingCovariance

section ActualGaussianMeans

open Set MeasureTheory WeightedClasses MeanIncrementBounds CorrectionState
open scoped ContDiff BigOperators

theorem block_zeroMode_pull {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : D ≃ₗᵢ[ℝ] E) (b : HarmonicBlock E) (hb : HarmonicWaveInteraction.ZeroMode b) :
    HarmonicWaveInteraction.ZeroMode (StateReindex.block e b) := by
  intro n i
  funext x
  change b.velocity n i 0 (e x) = 0
  rw [hb]
  rfl

theorem block_angularMean_zero {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (b : HarmonicBlock D) (hb : HarmonicWaveInteraction.ZeroMode b)
    (hk : ∀ n, b.angularFrequency n ≠ 0) : angularMeanVector b.oscillation = 0 := by
  funext n x i
  change (∫ θ in (0:ℝ)..2*Real.pi,
    (HarmonicFields.field (b.velocity n i) (b.frequency n) (b.phase n) (b.angularFrequency n) (x,θ)).re) /
      (2*Real.pi) = 0
  rw [SignedWaveUpdate.angularAverage_re_field, HarmonicFields.angularMean_field _ _ _ (hk n), hb]
  rfl

theorem fieldSum_angularMean_zero {D ι : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (labels : ℕ → Finset ι) (b : ι → HarmonicBlock D)
    (hb : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hk : ∀ l n, (b l).angularFrequency n ≠ 0) :
    angularMeanVector (LabelSumBounds.fieldSum labels (fun l => (b l).oscillation)) = 0 := by
  funext n x i
  change (∫ θ in (0:ℝ)..2*Real.pi, ∑ l ∈ labels n, (b l).oscillation n (x,θ) i) / (2*Real.pi) = 0
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_div]
    apply Finset.sum_eq_zero
    intro l hl
    exact congrFun (congrFun (congrFun (block_angularMean_zero (b l) (hb l) (hk l)) n) x) i
  · intro l hl
    exact (block_angularContinuous (b l) n x i).intervalIntegrable _ _

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

theorem particularBlock_zero (l : ι) : HarmonicWaveInteraction.ZeroMode (p.particularBlock v c u l) :=
  block_zeroMode_pull _ _ (ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).1

theorem particularGaussianBlock_zero (l : ι) :
    HarmonicWaveInteraction.ZeroMode (p.particularGaussianBlock v c u l) :=
  block_zeroMode_pull _ _ (ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).1

theorem signedGaussianBlock_zero (l : ι) :
    HarmonicWaveInteraction.ZeroMode (p.signedGaussianBlock v c u l) :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient _ _ _ _ _).1

theorem gaussianIncrement_angularMeans
    (hk : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) :
    angularMeanVector (p.particularGaussian v c u) = 0 ∧
    angularMeanVector (p.signedGaussian v c u) = 0 := by
  constructor
  · exact fieldSum_angularMean_zero v.labels (p.particularGaussianBlock v c u)
      (p.particularGaussianBlock_zero v c u) hk
  · apply fieldSum_angularMean_zero v.labels (p.signedGaussianBlock v c u)
      (p.signedGaussianBlock_zero v c u)
    intro l n
    change (p.signedBlock v c u l).angularFrequency n ≠ 0
    rw [(hc l).angular]
    exact hk l n

theorem gaussianIncrement_angularContinuous :
    AngularContinuous (p.particularGaussian v c u) ∧ AngularContinuous (p.signedGaussian v c u) :=
  ⟨LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _),
    LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _)⟩

theorem next_gaussian_angularMean
    (hk : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hu : AngularContinuous u.errors.gaussian) :
    angularMeanVector (p.next v c u).errors.gaussian = angularMeanVector u.errors.gaussian := by
  rw [p.next_gaussian_error v c u]
  have hs := p.gaussianIncrement_angularContinuous v c u
  have hz := p.gaussianIncrement_angularMeans v c u hk hc
  rw [angularMeanVector_add (hu.add hs.1) hs.2, angularMeanVector_add hu hs.1, hz.1, hz.2]
  simp only [add_zero]

theorem next_alias_lift :
    (p.next v c u).errors.aliasError = u.errors.aliasError +
      fun n x => p.nextAxisymmetricAlias v c u 0 n x.1 := by
  rw [p.next_alias_error v c u]
  funext n x i
  simp only [nextAxisymmetricAlias, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, zero_add,
    VariableGaugeMean.temporalAliasState, VariableGaugeMean.pressureAliasState]
  ring

theorem next_alias_angularContinuous (hu : AngularContinuous u.errors.aliasError) :
    AngularContinuous (p.next v c u).errors.aliasError := by
  rw [p.next_alias_lift v c u]
  apply hu.add
  intro n x i
  change Continuous (fun _ : ℝ => p.nextAxisymmetricAlias v c u 0 n x i)
  exact continuous_const

theorem next_alias_angularMean (hu : AngularContinuous u.errors.aliasError) :
    angularMeanVector (p.next v c u).errors.aliasError =
      angularMeanVector u.errors.aliasError + p.nextAxisymmetricAlias v c u 0 := by
  have hs : AngularContinuous (fun n x => p.nextAxisymmetricAlias v c u 0 n x.1) := by
    intro n x i
    change Continuous (fun _ : ℝ => p.nextAxisymmetricAlias v c u 0 n x i)
    exact continuous_const
  rw [p.next_alias_lift v c u, angularMeanVector_add hu hs]
  congr 1
  funext n x i
  exact congrFun (congrFun (angularAverage_axisymmetric
    (fun n x => p.nextAxisymmetricAlias v c u 0 n x i)) n) x

theorem nextAliasIncrement_angular (n : ℕ) (x : CyclePoint) :
    p.nextAxisymmetricAlias v c u 0 n x 1 = 0 := by
  simp only [nextAxisymmetricAlias, Pi.zero_apply, VariableGaugeMean.temporalAliasState,
    VariableGaugeMean.pressureAliasState, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero, sub_self]

theorem nextAliasIncrement_axial (n : ℕ) (x : CyclePoint) :
    p.nextAxisymmetricAlias v c u 0 n x 2 =
      VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
        (p.afterSigned v c u) n (x,0) 2 := by
  simp only [nextAxisymmetricAlias, Pi.zero_apply, VariableGaugeMean.pressureAliasState,
    Matrix.cons_val_two,
    zero_add, add_zero, sub_self]

/-- The actual good mean residual gains the requested exponent. New
Gaussian means vanish exactly, and the new temporal alias is the same
one retained by the mean-stage calculation. -/
theorem next_meanResidualBounds {σ : ℝ}
    (hk : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l))
    (hb : ∀ n x, x ∈ p.strip.domain → ∀ i,
      Continuous (fun θ : ℝ => u.errors.base n (x, θ) i))
    (hg : AngularContinuous u.errors.gaussian)
    (ha : AngularContinuous u.errors.aliasError)
    (hθ : MeanClass p.strip (1+σ) ((p.next v c u).thetaResidual c))
    (hz : MeanClass p.strip (1+σ) ((p.next v c u).axialResidual c - fun n x =>
      VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
        (p.afterSigned v c u) n (x,0) 2))
    (hgθ : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.gaussian n x 1))
    (hgz : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.gaussian n x 2))
    (haθ : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.aliasError n x 1))
    (haz : MeanClass p.strip (1+σ) (fun n x => angularMeanVector u.errors.aliasError n x 2)) :
    CorrectionState.MeanResidualBounds p.strip σ c (p.next v c u) := by
  have hbn : ∀ n x, x ∈ p.strip.domain → ∀ i,
      Continuous (fun θ : ℝ => (p.next v c u).errors.base n (x, θ) i) := by
    simpa only [p.next_base_error v c u] using hb
  have hgn : AngularContinuous (p.next v c u).errors.gaussian := by
    rw [p.next_gaussian_error v c u]
    exact (hg.add (p.gaussianIncrement_angularContinuous v c u).1).add
      (p.gaussianIncrement_angularContinuous v c u).2
  have han := p.next_alias_angularContinuous v c u ha
  have he n x hx i := meanGoodResidual_at c (p.next v c u) n x i
    (hbn n x hx i) (hgn n x i) (han n x i)
  have hgm := p.next_gaussian_angularMean v c u hk hc hg
  have ham := p.next_alias_angularMean v c u ha
  constructor
  · apply class_congr (Class.sub (Class.sub hθ hgθ) haθ)
    intro n x hx
    dsimp only
    rw [he n x hx 1, hgm, ham]
    change (p.next v c u).thetaResidual c n x - angularMeanVector u.errors.gaussian n x 1 -
      (angularMeanVector u.errors.aliasError n x 1 + p.nextAxisymmetricAlias v c u 0 n x 1) = _
    rw [p.nextAliasIncrement_angular v c u, add_zero]
    rfl
  · apply class_congr (Class.sub (Class.sub hz hgz) haz)
    intro n x hx
    dsimp only
    rw [he n x hx 2, hgm, ham]
    change (p.next v c u).axialResidual c n x - angularMeanVector u.errors.gaussian n x 2 -
      (angularMeanVector u.errors.aliasError n x 2 + p.nextAxisymmetricAlias v c u 0 n x 2) = _
    rw [p.nextAliasIncrement_axial v c u]
    change (p.next v c u).axialResidual c n x - angularMeanVector u.errors.gaussian n x 2 -
      (angularMeanVector u.errors.aliasError n x 2 +
        VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
          (p.afterSigned v c u) n (x,0) 2) =
      ((p.next v c u).axialResidual c n x -
        VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c
          (p.afterSigned v c u) n (x,0) 2) - angularMeanVector u.errors.gaussian n x 2 -
        angularMeanVector u.errors.aliasError n x 2
    ring

end CycleParameters

end ActualGaussianMeans

end NavierStokes.CorrectionStep
