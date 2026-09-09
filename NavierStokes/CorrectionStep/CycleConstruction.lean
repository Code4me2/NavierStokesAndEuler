import NavierStokes.CorrectionStep.SignedStages

/-!
# Exact field bookkeeping for one correction cycle: the cycle construction

Third part of `NavierStokes.CorrectionStep`.  It assembles a full cycle from
the signed stages: the cycle parameters, the constructed temporal and rank
stages, mass preservation and mean completion for a cycle, and the native
equations satisfied by the periodized and particular parameter families.
-/

noncomputable section

namespace NavierStokes.CorrectionStep

open Set WeightedClasses MeanIncrementBounds
open scoped ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

section ActualCycle

open CorrectionState VariableGaugeMean

abbrev CyclePoint := LocalSignedRequest.Point
abbrev CycleSlow := ℝ × PressureStream.Plane

noncomputable def cycleAssoc : CyclePoint ≃ₗᵢ[ℝ] (CycleSlow × TorusInverse.Plane) :=
  ParticularWaveBounds.liftAssoc PressureStream.Plane

/-- Finite labeled coefficient data of the current fields. Correct
representation is a separate invariant, not part of the construction.

The generic residual layer (`HarmonicResidual`, `ParticularWaveAssembly`)
also accepts a per-label wave alias coefficient; the cycle never uses
one, so every call below passes `0` in that slot and the axisymmetric
alias is carried separately in `CycleState.axisymmetricAlias`. -/
structure CycleCoefficients (ι : Type) where
  labels : ℕ → Finset ι
  blocks : ι → HarmonicBlock CyclePoint
  gaussian : ι → HarmonicResidual.BlockCoefficients CyclePoint
  residualBand : ℕ

/-- Fixed geometric and primitive solver data for an actual correction
cycle. The only state-dependent source is computed inside the stages. -/
structure CycleParameters (ι : Type) where
  gauge : GaugeData PressureStream.Plane
  strip : StripData CyclePoint
  patch : SignedStressPrimitive.Patch
  coordinate : ℝ
  timeExponent : ℝ
  commonIndex : ℕ → ℕ
  axial : PressureStream.Plane × PressureStream.Plane
  particular : ι → ParticularParameters CycleSlow
  signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency
  rank : RankData PressureStream.Plane

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

noncomputable def particularBlock (l : ι) : HarmonicBlock CyclePoint :=
  StateReindex.block cycleAssoc ((p.particular l).updateBlock
    (ParticularWaveBounds.reindexStrip cycleAssoc.symm p.strip)
    (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
    (StateReindex.block cycleAssoc.symm (v.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm 0) v.residualBand)

noncomputable def particularGaussianBlock (l : ι) : HarmonicBlock CyclePoint :=
  StateReindex.block cycleAssoc ((p.particular l).gaussianBlock
    (StateReindex.context cycleAssoc.symm c) (StateReindex.state cycleAssoc.symm u)
    (StateReindex.block cycleAssoc.symm (v.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (v.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm 0) v.residualBand)

noncomputable def particularVelocity : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.particularBlock v c u l).oscillation)

noncomputable def particularPressure : OscillatoryScalar CyclePoint :=
  fun n x => ∑ l ∈ v.labels n, (p.particularBlock v c u l).oscillatoryPressure n x

noncomputable def particularGaussian : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.particularGaussianBlock v c u l).oscillation)

noncomputable def afterParticular : State CyclePoint :=
  gaugeWaveStage p.gauge c u (p.particularVelocity v c u) (p.particularPressure v c u)
    ⟨0, p.particularGaussian v c u, 0⟩

/-- The signed request is recomputed from the actual state after the
particular solve; it is not supplied independently. -/
noncomputable def signedRequest : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2 :=
  LocalSignedRequest.fullRequest p.strip p.patch p.coordinate c (p.afterParticular v c u)

noncomputable def signedBlock (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).exactBlock p.strip (p.signedRequest v c u)

noncomputable def signedGaussianBlock (l : ι) : HarmonicBlock CyclePoint :=
  (p.signed l).gaussianBlock p.strip (p.signedRequest v c u)

noncomputable def signedVelocity : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.signedBlock v c u l).oscillation)

noncomputable def signedPressure : OscillatoryScalar CyclePoint :=
  fun n x => ∑ l ∈ v.labels n, (p.signedBlock v c u l).oscillatoryPressure n x

noncomputable def signedGaussian : Oscillation CyclePoint :=
  LabelSumBounds.fieldSum v.labels (fun l => (p.signedGaussianBlock v c u l).oscillation)

noncomputable def afterSigned : State CyclePoint :=
  gaugeWaveStage p.gauge c (p.afterParticular v c u)
    (p.signedVelocity v c u) (p.signedPressure v c u) ⟨0, p.signedGaussian v c u, 0⟩

noncomputable def temporalIncrement : Triple CyclePoint :=
  temporalIncrementState p.gauge p.timeExponent p.commonIndex p.axial c (p.afterSigned v c u)

noncomputable def afterTemporal : State CyclePoint :=
  temporalStageState p.gauge p.timeExponent p.commonIndex p.axial c (p.afterSigned v c u)

noncomputable def rankIncrement : Triple CyclePoint :=
  rankIncrementState p.gauge p.rank p.axial c (p.afterTemporal v c u)

noncomputable def afterRank : State CyclePoint :=
  rankStageState p.gauge p.rank p.axial c (p.afterTemporal v c u)

/-- Four literal updates followed by replacement of the obsolete radial
pressure alias. The current radial alias is recorded exactly once. -/
noncomputable def next : State CyclePoint :=
  gaugeRefreshPressureAlias p.gauge c u (p.afterRank v c u)

noncomputable def finalBlock (l : ι) : HarmonicBlock CyclePoint :=
  addBlock (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l)

theorem particularBlock_band (l : ι) : (p.particularBlock v c u l).BandLimited v.residualBand :=
  StateReindex.block_bandLimited cycleAssoc ((p.particular l).updateBlock_band _ _ _ _ _ _ _)

theorem particularGaussianBlock_band (l : ι) :
    (p.particularGaussianBlock v c u l).BandLimited v.residualBand :=
  StateReindex.block_bandLimited cycleAssoc ((p.particular l).gaussianBlock_band _ _ _ _ _ _)

theorem finalBlock_band {N : ℕ} (hb : ∀ l, (v.blocks l).BandLimited N) (l : ι) :
    (p.finalBlock v c u l).BandLimited (max (max N v.residualBand) 1) :=
  twoWaveUpdates_band (hb l) (p.particularBlock_band v c u l)
    ((p.signed l).exactBlock_band p.strip (p.signedRequest v c u))

theorem next_oscillation :
    (p.next v c u).oscillation = u.oscillation + p.particularVelocity v c u + p.signedVelocity v c u := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, add_zero]

theorem next_oscillatoryPressure :
    (p.next v c u).oscillatoryPressure =
      u.oscillatoryPressure + p.particularPressure v c u + p.signedPressure v c u := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, add_zero]

theorem next_mean :
    (p.next v c u).mean = updated (updated u.mean (p.temporalIncrement v c u)) (p.rankIncrement v c u) := by
  change updated (updated (p.afterSigned v c u).mean (p.temporalIncrement v c u))
    (p.rankIncrement v c u) = _
  have he : (p.afterSigned v c u).mean = u.mean := by
    simp only [afterSigned, afterParticular, gaugeWaveStage, reconstructState, State.addIncrement,
      updated_zeroTriple]
  rw [he]

theorem next_base_error : (p.next v c u).errors.base = u.errors.base := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, ExcludedErrors.add, ExcludedErrors.zero, add_zero]

theorem next_gaussian_error :
    (p.next v c u).errors.gaussian =
      u.errors.gaussian + p.particularGaussian v c u + p.signedGaussian v c u := by
  simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, afterTemporal,
    temporalStageState, afterSigned, afterParticular, gaugeWaveStage, reconstructState,
    State.addIncrement, ExcludedErrors.add, ExcludedErrors.zero, add_zero]

theorem next_alias_error :
    (p.next v c u).errors.aliasError = u.errors.aliasError +
      temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) +
      (pressureAliasState p.gauge c (p.afterRank v c u) - pressureAliasState p.gauge c u) := by
  change (p.afterRank v c u).errors.aliasError + _ = _
  have he : (p.afterRank v c u).errors.aliasError = u.errors.aliasError +
      temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) := by
    simp only [afterRank, rankStageState, afterTemporal, temporalStageState, afterSigned, afterParticular,
      gaugeWaveStage, reconstructState, State.addIncrement, ExcludedErrors.add, ExcludedErrors.zero, add_zero]
  rw [he]

theorem next_reconstructed :
    (reconstructState p.gauge c (p.next v c u)).pressure = (p.next v c u).pressure := rfl

end CycleParameters
end ActualCycle



section ConstructedTemporalStage

open CorrectionState VariableGaugeMean LocalSignedRequest

variable {coord cL cR : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

include hd hell
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL

/-- Full mean-step bound for the constructed temporal inverse and stream.
The increment and pressure-change classes are conclusions. -/
theorem gaugeTemporalStage_constructed
    {h H κ β : ℝ} (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ L n)
    (index : ℕ → ℕ) (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (axial : PressureStream.Plane × PressureStream.Plane) (c : Context Point) (u : State Point)
    (heps : c.operators.epsilon = ε)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10) (hβ : β ≤ H + 1 - 2 * κ)
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsθ : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.thetaResidual c))
    (hsz : GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.axialResidual c))
    (hcθ : MeanClass stageStrip H (u.thetaResidual c))
    (hcz : MeanClass stageStrip H (u.axialResidual c))
    (hbarθ : MeanClass stageStrip β (meanBar (u.thetaResidual c)))
    (hbarz : MeanClass stageStrip β (meanBar (u.axialResidual c))) :
    IncrementBounds stageStrip H (temporalIncrementState g h index axial c u) ∧
    MeanClass stageStrip H (gaugeTemporalPressureChange g h index axial c u) ∧
    CorrectionState.CumulativeBounds stageStrip (temporalStageState g h index axial c u) ∧
    SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (temporalStageState g h index axial c u).mean ∧
    GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalStageState g h index axial c u).mean ∧
    MeanClass stageStrip β ((temporalStageState g h index axial c u).thetaResidual c) ∧
    MeanClass stageStrip β (fun n x => (temporalStageState g h index axial c u).axialResidual c n x -
      temporalAliasState g h index c u n (x,0) 2) := by
  obtain ⟨hR, hT, hZ⟩ := temporalIncrementState_classes U g ha hd hcL hcR ε L hε hεone hL hell
    hh hscale index gap hgap axial c u heps hθ hz hpθ hpz hsz hcθ hcz
  have hi : IncrementBounds stageStrip H (temporalIncrementState g h index axial c u) := ⟨hR, hT, hZ⟩
  have him := gaugeTemporalIncrement_smooth U g ha hd hell h index axial c u hθ hz hpθ hpz hsz
  have his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (temporalIncrementState g h index axial c u) := by
    have hs n := temporalIncrementState_supportedGauge U g ha hd hell c u h index axial n
      (hz n) (hpz n) (hsz n) (hsθ n)
    exact ⟨fun n => (hs n).1, fun n => (hs n).2.1, fun n => (hs n).2.2⟩
  have hp := gaugeTemporalStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell
    h index axial c u hfixed hH hκ ho hb hu hi hop hbase hm him hms his hW hWs
  have hgain := gaugeTemporalStage_mean_gain (s := stageStrip) U.isOpen (fun _ hx => hx.1) g h index axial c u
    hv hfast ho hb hu hi hp (fun i j n => (hW i j n).mono (fun _ hx => hx.1))
    hbarθ hbarz hθ hz hpθ hpz hH hβ
  exact ⟨hi, hp, gaugeTemporalStage_cumulative g h index axial c u hu hi hp hH,
    smooth_updated hm him, hms.updated his, hgain⟩

end ConstructedTemporalStage
section ConstructedRankStage

open CorrectionState VariableGaugeMean LocalSignedRequest
variable {coord cL cR A B : ℝ} (U : SlowRegion coord) (g : GaugeData PressureStream.Plane)
    (r : RankData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)

include hd hell
local notation "stageStrip" => movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL

/-- The actual rank increment and its pressure change are derived from the
measured debt. The previous temporal alias stays subtracted. -/
theorem gaugeRankStage_constructed
    (axial : PressureStream.Plane × PressureStream.Plane) (c : Context Point) (u : State Point)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier) (hB : B ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    {H κ β : ℝ} (hH : 9 / 10 ≤ H) (hκ : 2 * κ ≤ 9 / 10) (hβ : β ≤ H + 1 - 2 * κ)
    (hfast : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfixed : (reconstructState g c u).pressure = u.pressure)
    (ho : OperatorBounds stageStrip c.operators κ) (hb : BaseBounds stageStrip c.base)
    (hu : CorrectionState.CumulativeBounds stageStrip u)
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hW : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, GaugeSupported g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j))
    (hdebt : UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      H (debt c u))
    (aliasField : ScalarField Point)
    (hθ : MeanClass stageStrip β (u.thetaResidual c))
    (hz : MeanClass stageStrip β (u.axialResidual c - aliasField)) :
    IncrementBounds stageStrip H (rankIncrementState g r axial c u) ∧
    MeanClass stageStrip H (gaugeRankPressureChange g r axial c u) ∧
    CorrectionState.CumulativeBounds stageStrip (rankStageState g r axial c u) ∧
    SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (rankStageState g r axial c u).mean ∧
    GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankStageState g r axial c u).mean ∧
    MeanClass stageStrip β ((rankStageState g r axial c u).thetaResidual c) ∧
    MeanClass stageStrip β ((rankStageState g r axial c u).axialResidual c - aliasField) := by
  have heps : BandBound stageStrip 1 c.operators.epsilon := by
    rw [ho.epsilon_eq]
    simpa only [Real.rpow_one] using bandBound_rpow stageStrip 1
  have hi := RankStateBounds.rankIncrementState_bounds U g r ha hcL hcR ε L hε hεone hL
    c u hg hparam hB hleft hright axial heps hdebt
  obtain ⟨a, b, L₀, ha₀, hab, _, _, hLo, hHi, _⟩ := qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hleft₀ (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : a ≤ r.length n x * r.inner := by
    rw [hparam.length n x hx]
    exact (hLo x hx).trans (mul_le_mul_of_nonneg_left hleft.le
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos x hx)).le)
  have hright₀ (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ b := by
    rw [hparam.length n x hx]
    exact (mul_le_mul_of_nonneg_left hright.le
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos x hx)).le).trans (hHi x hx)
  have hil := hg.increment_localTriple ha₀ hab U.isOpen hleft₀ hright₀ axial
  have his : GaugeSupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankIncrementState g r axial c u) := by
    have hsup n := hg.increment_supportedGauge ha₀ hab U.isOpen hleft₀ hright₀ axial n
    have enlarge {f : Point → ℝ} (n : ℕ) (hf : SupportedGauge r.inner r.outer (r.length n) U.carrier f) :
        SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier f := by
      intro x hx hn
      have hs := hf x hx hn
      rw [hparam.length n x.2.1 hx] at hs
      have hq := (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos x.2.1 hx)).le
      exact ⟨(mul_le_mul_of_nonneg_left hleft.le hq).trans hs.1,
        hs.2.trans (mul_le_mul_of_nonneg_left hright.le hq)⟩
    exact ⟨fun n => enlarge n (hsup n).1, fun n => enlarge n (hsup n).2.1,
      fun n => enlarge n (hsup n).2.2⟩
  have hp := gaugeRankStage_pressure_change_mem U g ha hd hcL hcR ε L hε hεone hL hell
    r axial c u hfixed hH hκ ho hb hu hi hop hbase hm hil.smooth hms his hW hWs
  have hgain := gaugeRankStage_mean_gain (s := stageStrip) U.isOpen (fun _ hx => hx.1) g r axial c u hg ha₀ hab
    hleft₀ hright₀ (TorusInverse.vector .temporal) hfast ho hb hu hi hp
    (fun i j n => (hW i j n).mono (fun _ hx => hx.1)) aliasField hθ hz hH hβ
  exact ⟨hi, hp, gaugeRankStage_cumulative g r axial c u hu hi hp hH,
    smooth_updated hm hil.smooth, hms.updated his, hgain⟩

end ConstructedRankStage


section CycleMassPreservation

open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest
open scoped ContDiff BigOperators

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

theorem afterParticular_mean : (p.afterParticular v c u).mean = u.mean :=
  gaugeWaveStage_mean _ _ _ _ _ _

theorem afterSigned_mean : (p.afterSigned v c u).mean = u.mean :=
  (gaugeWaveStage_mean _ _ _ _ _ _).trans (p.afterParticular_mean v c u)

/-- Both actual conserved masses survive all four stages. All radial
integrals are evaluated on the valid local slow region. -/
theorem next_preserve_masses {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (hm : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier u.mean)
    (hθ : ∀ n, ContDiffOn ℝ ∞ ((p.afterSigned v c u).thetaResidual c n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ ((p.afterSigned v c u).axialResidual c n)
      (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((p.afterSigned v c u).thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier ((p.afterSigned v c u).axialResidual c n))
    (hsθ : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      ((p.afterSigned v c u).thetaResidual c))
    (hsz : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      ((p.afterSigned v c u).axialResidual c))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c (p.afterTemporal v c u))
    (hrlength : ∀ n x, x ∈ U.carrier → p.rank.length n x = qLength coord x)
    (hleft : p.gauge.radial.inner ≤ p.rank.inner) (hright : p.rank.outer ≤ p.gauge.radial.outer)
    (n : ℕ) {x : PressureStream.Plane} (hx : x ∈ U.carrier) :
    radialMoment 2 (p.next v c u).mean.angular n x = radialMoment 2 u.mean.angular n x ∧
    radialMoment 1 (p.next v c u).mean.axial n x = radialMoment 1 u.mean.axial n x := by
  have hmid : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (p.afterSigned v c u).mean := by
    rw [p.afterSigned_mean v c u]
    exact hm
  have hi := gaugeTemporalIncrement_smooth U p.gauge ha hd hell p.timeExponent p.commonIndex p.axial
    c (p.afterSigned v c u) hθ hz hpθ hpz hsz
  have him : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) (p.afterTemporal v c u).mean :=
    smooth_updated hmid hi
  have his : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      (p.temporalIncrement v c u) := by
    have hs k := temporalIncrementState_supportedGauge U p.gauge ha hd hell c (p.afterSigned v c u)
      p.timeExponent p.commonIndex p.axial k (hz k) (hpz k) (hsz k) (hsθ k)
    exact ⟨fun k => (hs k).1, fun k => (hs k).2.1, fun k => (hs k).2.2⟩
  have hmidd : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      (p.afterSigned v c u).mean := by
    rw [p.afterSigned_mean v c u]
    exact hms
  have hmids : GaugeSupportedTriple p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier
      (p.afterTemporal v c u).mean := hmidd.updated his
  have ht := GaugeMassPreservation.temporalStage_preserve_masses_on U p.gauge ha hd hell
    p.timeExponent p.commonIndex p.axial c (p.afterSigned v c u)
    (fun k => (hmid.angular k).continuousOn) (fun k => (hmid.axial k).continuousOn)
    hθ hz hpθ hpz hsz n hx
  change radialMoment 2 (p.afterTemporal v c u).mean.angular n x =
      radialMoment 2 (p.afterSigned v c u).mean.angular n x ∧
    radialMoment 1 (p.afterTemporal v c u).mean.axial n x =
      radialMoment 1 (p.afterSigned v c u).mean.axial n x at ht
  rw [p.afterSigned_mean v c u] at ht
  obtain ⟨a, b, L, ha₀, hab, _, _, hLo, hHi, _⟩ := qLength_reference_bounds U ha p.gauge.radial.inner_lt_outer
  have hrl (k : ℕ) (y : PressureStream.Plane) (hy : y ∈ U.carrier) : a ≤ p.rank.length k y * p.rank.inner := by
    rw [hrlength k y hy]
    exact (hLo y hy).trans (mul_le_mul_of_nonneg_left hleft
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos y hy)).le)
  have hrr (k : ℕ) (y : PressureStream.Plane) (hy : y ∈ U.carrier) : p.rank.length k y * p.rank.outer ≤ b := by
    rw [hrlength k y hy]
    exact (mul_le_mul_of_nonneg_left hright
      (qLength_pos U.coord_pos U.coord_lt_one (U.time_pos y hy)).le).trans (hHi y hy)
  have localize {f : ScalarField Point}
      (hf : GaugeSupported p.gauge.radial.inner p.gauge.radial.outer (qLength coord) U.carrier f) :
      ∀ k, PhysicalMeanDomain.SupportedOn a b U.carrier (f k) := by
    intro k y hy hn
    exact ⟨(hLo _ hy).trans (hf k y hy hn).1, (hf k y hy hn).2.trans (hHi _ hy)⟩
  have hml : LocalRankDefect.LocalTriple a b U.carrier (p.afterTemporal v c u).mean :=
    ⟨⟨him.radial, localize hmids.radial⟩, ⟨him.angular, localize hmids.angular⟩,
      ⟨him.axial, localize hmids.axial⟩⟩
  have hr := hg.preserve_masses ha₀ hab U.isOpen hrl hrr p.axial hml n hx
  exact ⟨hr.1.trans ht.1, hr.2.trans ht.2⟩

end CycleParameters

end CycleMassPreservation

section CycleMeanCompletion

open Set WeightedClasses MeanIncrementBounds CorrectionState VariableGaugeMean LocalSignedRequest
open scoped ContDiff BigOperators

namespace CycleParameters
variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)
    {coord cL cR A B : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, p.gauge.length n = qLength coord)

include hd hell
local notation "stageStrip" => movingStripData U p.gauge.radial.inner p.gauge.radial.outer cL cR ha hcL hcR ε L hε hεone hL
local notation "slowStrip" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL
local notation "signedState" => p.afterSigned v c u
local notation "temporalState" => p.afterTemporal v c u


end CycleParameters

end CycleMeanCompletion


section PeriodizedNativeBounds

open Set Filter WeightedClasses CorrectionState
open scoped ContDiff Topology

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Only primitive background fields remain in this native family. Its
amplitude and pressure are zero, so its bounds assume no constructed output. -/
noncomputable def nativeBackground (a : LinearWaveBounds.WaveCoefficients D) :
    LocalizedWaveBounds.WaveFamily D I :=
  LocalizedWaveBounds.WaveFamily.ofCoefficients (fun _ =>
    { a with amplitude := 0, pressure := 0 })

theorem localInput_of_coefficients
    (a : PeriodizedWaveBounds.CopyData D I) {s : StripData D}
    {K : ℕ → I → Set D} {P : ℕ → D → ℝ} {α κ : ℝ}
    {d : LinearWaveBounds.GraphDirections D}
    (h : LocalizedWaveBounds.InputBounds s K (fun n _ => P n) 0 κ d
      (nativeBackground a.background))
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (ha : PeriodizedWaveBounds.LocalJets s (fun n x => Real.sqrt (s.zeta x) * P n x)
      α K a.amplitude)
    (hp : PeriodizedWaveBounds.LocalJets s (fun n x => Real.sqrt (s.zeta x) * P n x)
      (α + 1 / 2) K a.pressure) :
    LocalizedWaveBounds.InputBounds s K (fun n _ => P n) α κ d
      (LocalizedWaveBounds.rawFamily a) := by
  have hw n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hP n x hx)
  exact ⟨h.loss_nonneg, h.radial_profile, h.radial_scale, h.fast_scale, h.frequency_scale,
    h.radius, h.inverse_radius, h.radial_base, h.frequency_base, h.axial_base,
    h.radial_base_aux, h.frequency_base_aux, h.axial_base_aux, h.normal, h.defect,
    fun j => (LocalizedWaveBounds.LocalClass.of_localJets hw ha).map (ContinuousLinearMap.proj j),
    LocalizedWaveBounds.LocalClass.of_localJets hw hp⟩

namespace PeriodizedSignedParameters

variable (p : PeriodizedSignedParameters D I) (s : StripData D)

/-- Uniform native-copy input data for the signed quotient. The current
request is deliberately absent; it is supplied from the measured residual. -/
structure NativeControl (P : ℕ → D → ℝ) (κ : ℝ) where
  cells : PeriodizedWaveBounds.Cells (D × ℝ) I
  phasePatch : ℕ → I → Set (D × ℝ)
  background : LocalizedWaveBounds.InputBounds (HarmonicWaveInteraction.productStrip s)
    phasePatch (fun n _ x => P n x.1) 0 κ p.directions (nativeBackground p.base)
  covariance : SignedCopyBounds.NativeCovariance (HarmonicWaveInteraction.productStrip s)
    phasePatch p.matrix p.target
  mask : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s) (fun _ _ => 1)
    0 phasePatch (fun n i => p.mask i n)
  fundamental : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun n x => P n x.1) 0 phasePatch (fun n i => p.fundamental i n)
  normalMotion : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun _ _ => 1) 0 phasePatch (fun n i => p.normalMotion i n)
  action : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun _ _ => 1) 0 phasePatch (fun n i => p.action i n)
  cutoff : PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
    (fun _ _ => 1) 0 phasePatch (fun n i => p.cutoff i n)
  cutoff_support : ∀ n i, Function.support (p.cutoff i n) ⊆ cells.carrier n i
  phase_cover : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ cells.carrier n i →
    x ∈ phasePatch n i ∨ (p.cutoff i n =ᶠ[𝓝 x] fun _ => 0) ∨ (p.mask i n =ᶠ[𝓝 x] fun _ => 0)
  envelope_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ P n x
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  normal_lower : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ phasePatch n i →
    lower ≤ ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖
  normal_upper : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ phasePatch n i →
    ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ≤ upper
  inverse_frequency : BandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
    (fun n => 1 / p.base.frequency n)

variable {p s} {P : ℕ → D → ℝ} {κ β : ℝ}

theorem raw_zero_of_mask (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (n : ℕ) (i : I) (x : D × ℝ) (hm : p.mask i n x = 0) :
    (p.copyData s request).amplitude n i x = 0 ∧ (p.copyData s request).pressure n i x = 0 := by
  simp [copyData, native, SignedParameters.coefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, SignedWaveUpdate.signedVector, SignedWaveUpdate.signedScalar,
    hm, ParticularWaveBounds.projectedPressure, TangentProjection.pressureCoefficient]

theorem localized_zero_of_mask (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    {n : ℕ} {i : I} {x : D × ℝ} (hm : p.mask i n =ᶠ[𝓝 x] fun _ => 0) :
    ((p.copyData s request).localized i).amplitude n =ᶠ[𝓝 x] (fun _ => 0) ∧
    ((p.copyData s request).localized i).pressure n =ᶠ[𝓝 x] (fun _ => 0) := by
  constructor
  · filter_upwards [hm] with y hy
    change p.cutoff i n y • (p.copyData s request).amplitude n i y = 0
    rw [(raw_zero_of_mask request n i y hy).1, smul_zero]
  · filter_upwards [hm] with y hy
    change (p.cutoff i n y : ℂ) * (p.copyData s request).pressure n i y = 0
    rw [(raw_zero_of_mask request n i y hy).2, mul_zero]

theorem NativeControl.raw_jets (h : p.NativeControl s P κ)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j)) :
    PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
      (fun n x => Real.sqrt (s.zeta x.1) * P n x.1) (β + 1 / 2) h.phasePatch
      (p.copyData s request).amplitude ∧
    PeriodizedWaveBounds.LocalJets (HarmonicWaveInteraction.productStrip s)
      (fun n x => Real.sqrt (s.zeta x.1) * P n x.1) (β + 1) h.phasePatch
      (p.copyData s request).pressure := by
  have hK : UniformPrimaryWeights.UniformBandBound (HarmonicWaveInteraction.productStrip s)
      (1 / 2) (fun (_ : I) n => 1 / p.base.frequency n) := by
    obtain ⟨C, hC, q, hb⟩ := h.inverse_frequency
    exact ⟨C, hC, q, fun _ n => hb n⟩
  exact SignedCopyBounds.coefficients_jets (a := fun _ => p.base) (d := fun _ => p.directions)
    h.covariance (fun j => PeriodizedWaveBounds.LocalJets.of_memClass (hR j))
    h.mask h.fundamental (fun n x hx => h.envelope_nonneg n x.1 hx)
    h.background.normal.to_localJets h.normalMotion h.action h.lower_pos
    h.normal_lower h.normal_upper hK p.column

/-- All five full-lift classes are obtained from the actual quotient and
uniform native data. Background estimates are used only on the cells. -/
theorem NativeControl.global_bounds (h : p.NativeControl s P κ) (hκ : κ ≤ 1 / 2)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j)) :
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 / 2)
      (p.copyData s request).common.amplitude ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 / 2)
      ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions).amplitude ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1)
      (p.copyData s request).common.pressure ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 - κ)
      ((p.copyData s request).common.curlCorrection (HarmonicWaveInteraction.productStrip s) p.directions) ∧
    WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 - 3 * κ)
      ((p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s) p.directions) := by
  obtain ⟨ha, hp⟩ := h.raw_jets request hR
  have hinput := localInput_of_coefficients (p.copyData s request) h.background
    (fun n x hx => h.envelope_nonneg n x.1 hx) ha
    (by simp only [show β + 1 / 2 + 1 / 2 = β + 1 by ring]; exact hp)
  have hcover : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.cells.carrier n i →
      x ∈ h.phasePatch n i ∨
      (((p.copyData s request).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((p.copyData s request).localized i).pressure n =ᶠ[𝓝 x] fun _ => 0) := by
    intro n i x hx hi
    rcases h.phase_cover n i x hx hi with hp | hcut | hmask
    · exact Or.inl hp
    · exact Or.inr ((p.copyData s request).localized_zero_germs hcut)
    · exact Or.inr (localized_zero_of_mask request hmask)
  have hh := LocalizedWaveBounds.common_bounds_from_supported_native (p.copyData s request)
    h.cells h.cutoff_support h.phasePatch (fun n x hx => h.envelope_nonneg n x.1 hx)
    (hinput.with_cutoff (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff))
    hκ h.lower_pos h.normal_lower h.normal_upper
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency) hcover
  simpa only [show β + 1 / 2 + 1 / 2 = β + 1 by ring] using hh

theorem NativeControl.block_bounds (h : p.NativeControl s P κ) (hκ : κ ≤ 1 / 2)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j)) :
    (p.tangentBlock s request).WaveBounds s P (β + 1 / 2) ∧
    (p.exactBlock s request).WaveBounds s P (β + 1 / 2) ∧
    (p.exactBlock s request).PressureBounds s P (β + 1) ∧
    (p.curlBlock s request).WaveBounds s P (β + 1 - κ) ∧
    (p.goodBlock s request).WaveBounds s P (β + 1 - 3 * κ) := by
  obtain ⟨ha, he, hp, hc, hg⟩ := h.global_bounds hκ request hR
  have ht := SignedWaveUpdate.blockOfCoefficients_classes (p.copyData s request).common p.angularFrequency ha hp
  have hx := SignedWaveUpdate.blockOfCoefficients_classes
    ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions)
    p.angularFrequency he hp
  have hd : WaveClass (HarmonicWaveInteraction.productStrip s) (fun n x => P n x.1) (β + 1 - κ)
      (fun n x => ((p.copyData s request).commonCorrected
        (HarmonicWaveInteraction.productStrip s) p.directions).amplitude n x -
        (p.copyData s request).common.amplitude n x) := by
    apply LinearWaveBounds.class_congr hc
    intro n x hx
    simp only [PeriodizedWaveBounds.CopyData.commonCorrected,
      LinearWaveBounds.WaveCoefficients.addAmplitude, add_sub_cancel_left]
  have hd' := blockOfCoefficients_difference_mem _ _ p.angularFrequency hd
  have hg' := SignedWaveUpdate.class_zeroSection hg
  rw [sectionStrip_productStrip] at ht hx hd' hg'
  exact ⟨ht.1, hx.1, hx.2, hd', (SignedWaveUpdate.coefficientBlock_classes
    p.base.frequency (fun n x => p.base.phase n (x,0)) p.angularFrequency hg'
      (MemClass.zero (α := (0 : ℝ)) hg'.weight_nonneg)).1⟩

end PeriodizedSignedParameters

namespace ParticularParameters

open CommonCoverSolve TorusInverse

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (j : ℤ)

noncomputable def nativeTangent : ℕ → TangentData (Q × ℝ) ProblemStatement.Space :=
  fun n => ParticularWaveAssembly.angleTangent (p.tangent j n)

/-- Input bounds for the actual complex Volterra solve on all of its
native cells. The modal forcing is the literal current residual source. -/
structure NativeControl (W : ℕ → (Q × ℝ) × Plane → ℝ) (α κ : ℝ) where
  cells : PeriodizedWaveBounds.Cells ((Q × ℝ) × Plane) Frequency
  phasePatch : ℕ → Frequency → Set ((Q × ℝ) × Plane)
  background : LocalizedWaveBounds.InputBounds (nativeStrip s) phasePatch
    (fun n _ => W n) 0 κ p.directions (nativeBackground (p.copyData c u b G A j).background)
  frame : ℕ → PrimaryODE.FrameData ((Q × ℝ) × ℝ)
  envelope : ℕ → ℝ → ℝ
  realControl : ParticularCopyBounds.ModalControl (nativeStrip s) α frame
    (fun n => ParticularWaveBounds.realData (p.nativeTangent j n) ((p.copyData c u b G A j).source n))
    j p.geometry p.length envelope phasePatch
  imagControl : ParticularCopyBounds.ModalControl (nativeStrip s) α frame
    (fun n => ParticularWaveBounds.imagData (p.nativeTangent j n) ((p.copyData c u b G A j).source n))
    j p.geometry p.length envelope phasePatch
  envelope_nonneg : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x
  envelope_compare : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    envelope n ((p.geometry n).coordinates i x.2).2 ≤ W n x
  normal : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (fun n i x => (p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x))
  normalMotion : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (fun n i x => (p.nativeTangent j n).normalDot (ParticularWaveBounds.nativePoint (p.geometry n) i x))
  action : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (fun n i x => (p.nativeTangent j n).action (ParticularWaveBounds.nativePoint (p.geometry n) i x))
  source : PeriodizedWaveBounds.LocalJets (nativeStrip s)
    (fun n x => Real.sqrt ((nativeStrip s).zeta x) * W n x) α phasePatch
    (fun n _ => (p.copyData c u b G A j).source n)
  cutoff : PeriodizedWaveBounds.LocalJets (nativeStrip s) (fun _ _ => 1) 0 phasePatch
    (p.copyData c u b G A j).cutoff
  cutoff_support : ∀ n i, Function.support ((p.copyData c u b G A j).cutoff n i) ⊆ cells.carrier n i
  phase_cover : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ cells.carrier n i →
    x ∈ phasePatch n i ∨ ∀ᶠ y in 𝓝 x,
      ((p.geometry n).coordinates i y.2).2 ∈ Icc 0 (p.length n) ∧
      ∀ v ∈ Icc 0 (p.length n), (p.copyData c u b G A j).source n
        (y.1, (p.geometry n).path i y.2 v) = 0
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  normal_lower : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    lower ≤ ‖(p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x)‖
  normal_upper : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    ‖(p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x)‖ ≤ upper
  normal_match : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ phasePatch n i →
    (p.copyData c u b G A j).background.normal (nativeStrip s) p.directions n x =
      (p.nativeTangent j n).normal (ParticularWaveBounds.nativePoint (p.geometry n) i x)
  inverse_frequency : BandBound (nativeStrip s) (1 / 2)
    (fun n => 1 / (p.copyData c u b G A j).background.frequency n)

variable {p s c u b G A j} {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}

theorem raw_zero_of_source_path {n : ℕ} {i : Frequency} {x : (Q × ℝ) × Plane}
    (hf : ∀ᶠ y in 𝓝 x,
      ((p.geometry n).coordinates i y.2).2 ∈ Icc 0 (p.length n) ∧
      ∀ v ∈ Icc 0 (p.length n), (p.copyData c u b G A j).source n
        (y.1, (p.geometry n).path i y.2 v) = 0) :
    (p.copyData c u b G A j).amplitude n i =ᶠ[𝓝 x] (fun _ => 0) ∧
    (p.copyData c u b G A j).pressure n i =ᶠ[𝓝 x] (fun _ => 0) ∧
    (p.copyData c u b G A j).source n =ᶠ[𝓝 x] (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hf] with y hy
    exact ParticularWaveBounds.complexCopyVelocity_zero_of_path (p.nativeTangent j n)
      ((p.copyData c u b G A j).source n) (p.geometry n) (p.length_pos n).le i y.1 y.2 hy.2
  · filter_upwards [hf] with y hy
    exact ParticularWaveBounds.complexCopyPressure_zero_of_path (p.nativeTangent j n)
      ((p.copyData c u b G A j).source n) (p.geometry n) (p.length_pos n).le i
      ((p.copyData c u b G A j).background.frequency n) y.1 y.2 hy.2 hy.1
  · filter_upwards [hf] with y hy
    simpa only [Geometry.path_current, Prod.mk.eta] using hy.2 _ hy.1

theorem localized_zero_of_source_path {n : ℕ} {i : Frequency} {x : (Q × ℝ) × Plane}
    (hf : ∀ᶠ y in 𝓝 x,
      ((p.geometry n).coordinates i y.2).2 ∈ Icc 0 (p.length n) ∧
      ∀ v ∈ Icc 0 (p.length n), (p.copyData c u b G A j).source n
        (y.1, (p.geometry n).path i y.2 v) = 0) :
    ((p.copyData c u b G A j).localized i).amplitude n =ᶠ[𝓝 x] (fun _ => 0) ∧
    ((p.copyData c u b G A j).localized i).pressure n =ᶠ[𝓝 x] (fun _ => 0) := by
  obtain ⟨ha, hp, _⟩ := raw_zero_of_source_path hf
  constructor
  · filter_upwards [ha] with y hy
    change _ • (p.copyData c u b G A j).amplitude n i y = 0
    rw [hy, smul_zero]
  · filter_upwards [hp] with y hy
    change _ * (p.copyData c u b G A j).pressure n i y = 0
    rw [hy, mul_zero]

theorem NativeControl.raw_jets (h : p.NativeControl s c u b G A j W α κ) :
    PeriodizedWaveBounds.LocalJets (nativeStrip s)
      (fun n x => Real.sqrt ((nativeStrip s).zeta x) * W n x) α h.phasePatch
      (p.copyData c u b G A j).amplitude ∧
    PeriodizedWaveBounds.LocalJets (nativeStrip s)
      (fun n x => Real.sqrt ((nativeStrip s).zeta x) * W n x) (α + 1 / 2) h.phasePatch
      (p.copyData c u b G A j).pressure :=
  ParticularCopyBounds.coefficients_jets (p.copyData c u b G A j).background
    (p.nativeTangent j) (p.copyData c u b G A j).source p.geometry p.length p.length_pos
    h.envelope W h.frame j h.phasePatch h.realControl h.imagControl h.envelope_nonneg
    h.envelope_compare h.normal h.normalMotion h.action h.source h.lower_pos h.normal_lower
    h.normal_upper h.inverse_frequency

/-- The global amplitude, pressure, exact curl, and retained linear error
are derived from native modal inputs for the same actual residual solve. -/
theorem NativeControl.global_bounds (h : p.NativeControl s c u b G A j W α κ) (hκ : κ ≤ 1 / 2) :
    WaveClass (nativeStrip s) W α (p.copyData c u b G A j).common.amplitude ∧
    WaveClass (nativeStrip s) W α (p.wave s c u b G A j).amplitude ∧
    WaveClass (nativeStrip s) W (α + 1 / 2) (p.copyData c u b G A j).common.pressure ∧
    WaveClass (nativeStrip s) W (α + 1 / 2 - κ)
      ((p.copyData c u b G A j).common.curlCorrection (nativeStrip s) p.directions) ∧
    WaveClass (nativeStrip s) W (α + 1 / 2 - 3 * κ)
      ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions) := by
  obtain ⟨ha, hp⟩ := h.raw_jets
  have hin := localInput_of_coefficients (p.copyData c u b G A j) h.background h.envelope_nonneg ha hp
  exact LocalizedWaveBounds.common_bounds_from_supported_native (M := h.upper)
    (p.copyData c u b G A j) h.cells h.cutoff_support h.phasePatch h.envelope_nonneg
    (hin.with_cutoff (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff))
    hκ h.lower_pos
    (fun n i x hx hi => by
      rw [h.normal_match n i x hx hi]
      exact h.normal_lower n i x hx hi)
    (fun n i x hx hi => by
      rw [h.normal_match n i x hx hi]
      exact h.normal_upper n i x hx hi)
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency)
    (fun n i x hx hi => (h.phase_cover n i x hx hi).imp_right localized_zero_of_source_path)

theorem sectionStrip_nativeStrip (s : StripData (Q × Plane)) :
    ParticularWaveAssembly.sectionStrip (nativeStrip s) = s := by
  cases s
  rfl

theorem assembled_bounds (p : ParticularParameters Q) (s : StripData (Q × Plane))
    (c : Context (Q × Plane)) (u : State (Q × Plane)) (b : HarmonicBlock (Q × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Q × Plane)) (N : ℕ)
    {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (C : ∀ j ∈ ParticularWaveAssembly.modes N, p.NativeControl s c u b G A j W α κ)
    (hW : ∀ n x, x ∈ (nativeStrip s).domain → 0 ≤ W n x) (hκ : κ ≤ 1 / 2) :
    (p.updateBlock s c u b G A N).WaveBounds s
      (fun n x => W n (ParticularWaveAssembly.angleShuffle (x,0))) α ∧
    (p.updateBlock s c u b G A N).PressureBounds s
      (fun n x => W n (ParticularWaveAssembly.angleShuffle (x,0))) (α + 1 / 2) ∧
    (p.goodBlock s c u b G A N).WaveBounds s
      (fun n x => W n (ParticularWaveAssembly.angleShuffle (x,0))) (α + 1 / 2 - 3 * κ) := by
  have hu := ParticularWaveAssembly.assembledBlock_classes
    (s := ParticularWaveAssembly.sectionStrip (nativeStrip s)) N b.frequency b.phase b.angularFrequency
    (fun n x hx => hW n _ hx)
    (fun j hj => ParticularWaveAssembly.nativeSlice_waveClass ((C j hj).global_bounds hκ).2.1)
    (fun j hj => ParticularWaveAssembly.nativeSlice_waveClass ((C j hj).global_bounds hκ).2.2.1)
  have hg := ParticularWaveAssembly.assembledBlock_classes
    (s := ParticularWaveAssembly.sectionStrip (nativeStrip s)) (γ := (0 : ℝ)) N
    b.frequency b.phase b.angularFrequency (fun n x hx => hW n _ hx)
    (fun j hj => ParticularWaveAssembly.nativeSlice_waveClass ((C j hj).global_bounds hκ).2.2.2.2)
    (fun _ _ => MemClass.zero (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n _ hx)))
  rw [sectionStrip_nativeStrip] at hu hg
  exact ⟨hu.1, hu.2, hg.1⟩

end ParticularParameters

end PeriodizedNativeBounds

section NativeEquations

open Set Filter WeightedClasses HarmonicCalculus CorrectionState
open scoped ContDiff Topology

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem localClass_contDiffOn_inter {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {C : ℕ → I → Set D} {w : ℕ → I → D → ℝ} {α : ℝ}
    {f : ℕ → I → D → E} (hf : LocalizedWaveBounds.LocalClass s C w α f)
    (hC : ∀ n i, IsOpen (C n i)) (n : ℕ) (i : I) :
    ContDiffOn ℝ ∞ (f n i) (s.domain ∩ C n i) :=
  (s.isOpen_domain.inter (hC n i)).contDiffOn_iff.mpr
    (fun x hx => hf.smooth n i x hx.1 hx.2)

/-- Angular and radial geometry of the actual raw copies. The analytic
bounds on the normal and material defect remain restricted to `C`. -/
structure NativeAngularGeometry (a : PeriodizedWaveBounds.CopyData D I) (s : StripData D)
    (d : LinearWaveBounds.GraphDirections D) (C : ℕ → I → Set D) : Prop where
  open_patch : ∀ n i, IsOpen (C n i)
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (a.background.phase n) s.domain
  radius_nonzero : ∀ n i x, x ∈ s.domain → x ∈ C n i → a.background.radius n x ≠ 0
  radial_radius : ∀ n i x, x ∈ s.domain → x ∈ C n i →
    along (d.radialField n) (a.background.radius n) x = 1
  radius : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.radius n)
  radial_base : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.radialBase n)
  frequency_base : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.frequencyBase n)
  axial_base : ∀ n, CopyAngularInvariance.Invariant d.angular (a.background.axialBase n)
  radial_field : ∀ n, CopyAngularInvariance.Invariant d.angular (d.radialField n)
  phase : ∀ n, ∃ m, CopyAngularInvariance.AffinePhase d.angular m (a.background.phase n)
  amplitude : ∀ i n, CopyAngularInvariance.Invariant d.angular (a.amplitude n i)
  pressure : ∀ i n, CopyAngularInvariance.Invariant d.angular (a.pressure n i)
  cutoff : ∀ i n, CopyAngularInvariance.Invariant d.angular (a.cutoff n i)

theorem NativeAngularGeometry.exactOn
    {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
    {d : LinearWaveBounds.GraphDirections D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α κ lower upper : ℝ}
    (g : NativeAngularGeometry a s d C)
    (h : LocalizedWaveBounds.InputBounds s C P α κ d (LocalizedWaveBounds.rawFamily a))
    (hψ : LocalizedWaveBounds.LocalUnweighted s C 0 a.cutoff)
    (hκ : κ ≤ 1 / 2) (hlower : 0 < lower)
    (hlo : ∀ n i x, x ∈ s.domain → x ∈ C n i → lower ≤ ‖a.background.normal s d n x‖)
    (hhi : ∀ n i x, x ∈ s.domain → x ∈ C n i → ‖a.background.normal s d n x‖ ≤ upper)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s C (1 / 2)
      (fun n _ _ => 1 / a.background.frequency n)) (n : ℕ) (i : I) :
    LocalizedWaveBounds.ExactOn (a.corrected s d i) s d n (s.domain ∩ C n i) := by
  have hn := h.with_cutoff hψ
  have hc := hn.curlCorrection_class hlower hlo hhi hfreq
  have he := hn.add_curl_amplitude hκ (fun j => hc.map (ContinuousLinearMap.proj j))
  have ha i n := CopyAngularInvariance.corrected_amplitude_invariant
    (a := a.raw i) (s := s) (d := d) (fun n => a.cutoff n i) g.radius g.radial_field
    (fun _ => CopyAngularInvariance.Invariant.const _) g.phase (g.amplitude i) (g.cutoff i) n
  have hp i n := CopyAngularInvariance.corrected_pressure_invariant
    (a := a.raw i) (s := s) (d := d) (fun n => a.cutoff n i) (g.pressure i) (g.cutoff i) n
  refine ⟨s.isOpen_domain.inter (g.open_patch n i),
    localClass_contDiffOn_inter h.radial_profile g.open_patch n i,
    (g.phase_smooth n).mono inter_subset_left,
    (fun j => localClass_contDiffOn_inter (he.amplitude j) g.open_patch n i),
    (fun x hx => (h.radius.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (h.radial_base.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (h.frequency_base.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (h.axial_base.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => (he.pressure.smooth n i x hx.1 hx.2).differentiableAt (by simp)),
    (fun x hx => g.radius_nonzero n i x hx.1 hx.2),
    (fun x hx => g.radial_radius n i x hx.1 hx.2), ?_, ?_, ?_, ?_⟩
  · intro x hx j
    exact ((CopyAngularInvariance.base_invariant (g.radius n) (g.radial_base n)
      (g.frequency_base n) (g.axial_base n)).component j).along_zero x
  · intro j x hx
    exact ((ha i n).component j).along_zero x
  · obtain ⟨m, hm⟩ := g.phase n
    exact ⟨m, fun x hx => hm.directional_eq
      (((g.phase_smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx.1)).differentiableAt (by simp))⟩
  · intro x hx
    exact (hp i n).along_zero x

/-- The generic local identity is applied only after the primitive raw
principal equation has been proved by its actual ODE constructor. -/
theorem native_cancellation_of_principal
    {a : PeriodizedWaveBounds.CopyData D I} {s : StripData D}
    {d : LinearWaveBounds.GraphDirections D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α κ lower upper : ℝ}
    (g : NativeAngularGeometry a s d C)
    (h : LocalizedWaveBounds.InputBounds s C P α κ d (LocalizedWaveBounds.rawFamily a))
    (hψ : LocalizedWaveBounds.LocalUnweighted s C 0 a.cutoff)
    (hκ : κ ≤ 1 / 2) (hlower : 0 < lower)
    (hlo : ∀ n i x, x ∈ s.domain → x ∈ C n i → lower ≤ ‖a.background.normal s d n x‖)
    (hhi : ∀ n i x, x ∈ s.domain → x ∈ C n i → ‖a.background.normal s d n x‖ ≤ upper)
    (hfreq : LocalizedWaveBounds.LocalUnweighted s C (1 / 2)
      (fun n _ _ => 1 / a.background.frequency n))
    (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ C n i)
    (hsolve : (a.raw i).principal s d n x = -a.source n x) :
    (a.corrected s d i).harmonicResidual s d n x +
        (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
      (fun j => (a.localGood s d n i x j + a.localGaussian d n i x j) *
        carrier (a.background.frequency n) (a.background.phase n) x) := by
  have hc := (h.with_cutoff hψ).curlCorrection_class hlower hlo hhi hfreq
  exact LocalizedWaveBounds.harmonicResidual_eq_good_add_excluded_on (a.raw i) s d
    (fun n => a.cutoff n i) ((a.localized i).curlCorrection s d) a.source n
    (g.exactOn h hψ hκ hlower hlo hhi hfreq n i) ⟨hx,hi⟩
    (fun j => (h.amplitude j).smooth n i x hx hi |>.differentiableAt (by simp))
    ((hψ.smooth n i x hx hi).differentiableAt (by simp))
    (fun j => (hc.map (ContinuousLinearMap.proj j)).smooth n i x hx hi |>.differentiableAt (by simp))
    hsolve

theorem harmonicResidual_zero_germ
    (a : LinearWaveBounds.WaveCoefficients D) (s : StripData D)
    (d : LinearWaveBounds.GraphDirections D) {n : ℕ} {x : D}
    (ha : a.amplitude n =ᶠ[𝓝 x] fun _ => 0) (hp : a.pressure n =ᶠ[𝓝 x] fun _ => 0) :
    a.harmonicResidual s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have hv : vectorMode (a.frequency n) (a.phase n) (a.amplitude n) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ha] with y hy
    ext j
    simp only [vectorMode, mode, hy, Pi.zero_apply, zero_mul]
  have hpr : mode (a.frequency n) (a.phase n) (a.pressure n) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hp] with y hy
    simp only [mode, hy, zero_mul]
  have hh := ParticularWaveAssembly.linearResidual_germ hv hpr (s.epsilon n) (a.radius n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (LinearWaveResidual.timeDirection (s.epsilon n) (d.fastField n) (fun _ => d.slow))
    (LinearWaveResidual.complexBase (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n))
  simp only [PeriodizedWaveBounds.linearResidual_zero] at hh
  exact hh

theorem local_cancellation_of_zero_germs
    (a : PeriodizedWaveBounds.CopyData D I) (s : StripData D)
    (d : LinearWaveBounds.GraphDirections D) {n : ℕ} {i : I} {x : D}
    (ha : (a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0)
    (hp : (a.localized i).pressure n =ᶠ[𝓝 x] fun _ => 0)
    (hg : a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0)
    (hf : a.source n =ᶠ[𝓝 x] fun _ => 0) :
    (a.corrected s d i).harmonicResidual s d n x +
        (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) =
      (fun j => (a.localGood s d n i x j + a.localGaussian d n i x j) *
        carrier (a.background.frequency n) (a.background.phase n) x) := by
  have hz := (LocalizedWaveBounds.nativeFamily a).outputs_zero_germs s d ha hp
  have hcor : (a.corrected s d i).amplitude n =ᶠ[𝓝 x] fun _ => 0 := hz.2.1
  have hgood : a.localGood s d n i =ᶠ[𝓝 x] fun _ => 0 := hz.2.2
  have hres := harmonicResidual_zero_germ (a.corrected s d i) s d hcor hp
  rw [hres.self_of_nhds, hf.self_of_nhds, hgood.self_of_nhds, hg.self_of_nhds]
  ext j
  simp

namespace PeriodizedSignedParameters

variable {p : PeriodizedSignedParameters D I} {s : StripData D}
    {P : ℕ → D → ℝ} {κ β : ℝ} (h : p.NativeControl s P κ)
    (request : ℕ → D × ℝ → SignedWaveUpdate.Vec2)

/-- Primitive angular identities and the fixed unit fundamental's ODE.
The signed principal equation and every cutoff/curl identity are derived. -/
structure NativeDynamics where
  slope : ℕ → ℝ
  angular : ∀ i, SignedWaveUpdate.AngularInputs (HarmonicWaveInteraction.productStrip s)
    p.directions p.base (p.matrix i) (p.target i) request (p.mask i) (p.fundamental i)
    (p.normalMotion i) (p.action i) (p.cutoff i) slope
  open_patch : ∀ n i, IsOpen (h.phasePatch n i)
  radius_nonzero : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    x ∈ h.phasePatch n i → p.base.radius n x ≠ 0
  radial_radius : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain →
    x ∈ h.phasePatch n i → along (p.directions.radialField n) (p.base.radius n) x = 1
  matrix_frozen : ∀ i, SignedWaveUpdate.FrozenAlong p.directions.fast (p.matrix i)
  target_frozen : ∀ i, SignedWaveUpdate.FrozenAlong p.directions.fast (p.target i)
  request_frozen : SignedWaveUpdate.FrozenAlong p.directions.fast request
  mask_frozen : ∀ i, SignedWaveUpdate.FrozenAlong p.directions.fast (p.mask i)
  frequency_nonzero : ∀ n, p.base.frequency n ≠ 0
  ode : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
    along (p.directions.fastField n) (p.fundamental i n) x =
      TangentProjection.projectedRhs
        (p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x)
        (p.normalMotion i n x) (p.fundamental i n x) (p.action i n x (p.fundamental i n x)) 0
        (s.epsilon n * p.base.frequency n ^ 2 *
          ‖p.base.normal (HarmonicWaveInteraction.productStrip s) p.directions n x‖ ^ 2)
  action_eq : ∀ n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ h.phasePatch n i →
    CurlClassBounds.complexify (p.action i n x (p.fundamental i n x)) =
      LinearWaveResidual.shear (p.base.radius n) (p.base.frequencyBase n) (p.base.axialBase n)
        (p.directions.radialField n) (fun y => CurlClassBounds.complexify (p.fundamental i n y)) x

variable {h request}

theorem NativeDynamics.angularGeometry (d : NativeDynamics h request) (i₀ : I) :
    NativeAngularGeometry (p.copyData s request) (HarmonicWaveInteraction.productStrip s)
      p.directions h.phasePatch :=
  ⟨d.open_patch, (d.angular i₀).phase_smooth, d.radius_nonzero, d.radial_radius,
    (d.angular i₀).radius, (d.angular i₀).radial_base, (d.angular i₀).frequency_base,
    (d.angular i₀).axial_base, (d.angular i₀).radialField,
    fun n => ⟨d.slope n, (d.angular i₀).phase n⟩,
    fun i => (d.angular i).amplitude p.column, fun i => (d.angular i).pressure p.column,
    fun i => (d.angular i).cutoff⟩

theorem NativeDynamics.principal (d : NativeDynamics h request)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (n : ℕ) (i : I) {x : D × ℝ} (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain)
    (hi : x ∈ h.phasePatch n i) :
    ((p.copyData s request).raw i).principal (HarmonicWaveInteraction.productStrip s) p.directions n x = 0 :=
  NativePrincipalEquations.signed_coefficients_principal_at (a := fun _ => p.base)
    (dirs := fun _ => p.directions) h.covariance
    (fun j => PeriodizedWaveBounds.LocalJets.of_memClass (hR j)) h.mask h.fundamental
    p.column n i hx hi (d.matrix_frozen i) (d.target_frozen i) d.request_frozen (d.mask_frozen i)
    (d.frequency_nonzero n) (d.ode n i x hx hi) (d.action_eq n i x hx hi)

theorem NativeDynamics.local_equation (d : NativeDynamics h request) (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (n : ℕ) (i : I) {x : D × ℝ} (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain)
    (hi : x ∈ h.phasePatch n i) :
    ((p.copyData s request).corrected (HarmonicWaveInteraction.productStrip s) p.directions i).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions n x +
        (fun j => (p.copyData s request).source n x j * carrier (p.base.frequency n) (p.base.phase n) x) =
      (fun j => ((p.copyData s request).localGood (HarmonicWaveInteraction.productStrip s) p.directions n i x j +
        (p.copyData s request).localGaussian p.directions n i x j) * carrier (p.base.frequency n) (p.base.phase n) x) := by
  obtain ⟨ha, hp⟩ := h.raw_jets request hR
  have hin := localInput_of_coefficients (p.copyData s request) h.background
    (fun n x hx => h.envelope_nonneg n x.1 hx) ha
    (by simp only [show β + 1 / 2 + 1 / 2 = β + 1 by ring]; exact hp)
  exact native_cancellation_of_principal (d.angularGeometry i) hin
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    hκ h.lower_pos h.normal_lower h.normal_upper
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency) n i hx hi
    (by simpa only [copyData, Pi.zero_apply, neg_zero] using d.principal hR n i hx hi)

/-- The literal signed common curl has its actual retained good term and
Gaussian derivative tail on the entire lift. Native ODE input is needed
only on the supported phase patches. -/
theorem NativeDynamics.common_equation (d : NativeDynamics h request) (hκ : κ ≤ 1 / 2)
    (hR : ∀ j, MeanClass (HarmonicWaveInteraction.productStrip s) β (fun n x => request n x j))
    (n : ℕ) {x : D × ℝ} (hx : x ∈ (HarmonicWaveInteraction.productStrip s).domain) :
    ((p.copyData s request).commonCorrected (HarmonicWaveInteraction.productStrip s) p.directions).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions n x =
      (fun j => ((p.copyData s request).globalGood (HarmonicWaveInteraction.productStrip s) p.directions n x j +
        (p.copyData s request).globalGaussian p.directions n x j) * carrier (p.base.frequency n) (p.base.phase n) x) := by
  let a := p.copyData s request
  have hzsource (m : ℕ) (y : D × ℝ) : a.source m =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hl : ∀ m i y, y ∈ (HarmonicWaveInteraction.productStrip s).domain → y ∈ h.cells.carrier m i →
      (a.corrected (HarmonicWaveInteraction.productStrip s) p.directions i).harmonicResidual
        (HarmonicWaveInteraction.productStrip s) p.directions m y +
        (fun j => a.source m y j * carrier (a.background.frequency m) (a.background.phase m) y) =
      (fun j => (a.localGood (HarmonicWaveInteraction.productStrip s) p.directions m i y j +
        a.localGaussian p.directions m i y j) * carrier (a.background.frequency m) (a.background.phase m) y) := by
    intro m i y hy hi
    rcases h.phase_cover m i y hy hi with hC | hcut | hmask
    · exact d.local_equation hκ hR m i hy hC
    · have hz := a.localized_zero_germs hcut
      have hg : a.localGaussian p.directions m i =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [a.localTail_zero_germ p.directions hcut] with z hz
        rw [a.localGaussian_eq, hz]
        simp only [a, copyData, smul_zero, add_zero]
      exact local_cancellation_of_zero_germs a _ _ hz.1 hz.2 hg (hzsource m y)
    · have hz := localized_zero_of_mask (s := s) request hmask
      have hu : a.amplitude m i =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hmask] with z hz
        exact (raw_zero_of_mask request m i z hz).1
      exact local_cancellation_of_zero_germs a _ _ hz.1 hz.2
        (a.localGaussian_zero_of_fields p.directions hu (hzsource m y)) (hzsource m y)
  have he := a.common_cancellation h.cells h.cutoff_support
    (HarmonicWaveInteraction.productStrip s) p.directions hl n hx
  have hz : (fun j => a.source n x j * carrier (a.background.frequency n) (a.background.phase n) x) = 0 := by
    ext j
    exact zero_mul _
  simp only [hz, add_zero] at he
  exact he

end PeriodizedSignedParameters

namespace ParticularParameters

open CommonCoverSolve TorusInverse ParticularWaveAssembly CopyAngularInvariance

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {p : ParticularParameters Q} {s : StripData (Q × Plane)}
    {c : Context (Q × Plane)} {u : State (Q × Plane)} {b : HarmonicBlock (Q × Plane)}
    {G A : HarmonicResidual.BlockCoefficients (Q × Plane)} {j : ℤ}
    {W : ℕ → (Q × ℝ) × Plane → ℝ} {α κ : ℝ}
    (h : p.NativeControl s c u b G A j W α κ)

structure NativeDynamics : Prop where
  background : BackgroundControl (nativeStrip s) p.directions p.background b j
  open_patch : ∀ n i, IsOpen (h.phasePatch n i)
  frequency_nonzero : ∀ n, (j : ℝ) * b.frequency n ≠ 0
  damping : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ h.phasePatch n i →
    (p.nativeTangent j n).damping (ParticularWaveBounds.nativePoint (p.geometry n) i x) =
      s.epsilon n * ((j : ℝ) * b.frequency n) ^ 2 *
        ‖(p.copyData c u b G A j).background.normal (nativeStrip s) p.directions n x‖ ^ 2
  fast : ∀ n, p.directions.fastScale n • p.directions.fast =
    ((0 : Q × ℝ), ParticularWaveBounds.slotDirection (p.geometry n))
  action : ∀ n i x, x ∈ (nativeStrip s).domain → x ∈ h.phasePatch n i → ∀ z : ProblemStatement.Space,
    CurlClassBounds.complexify ((p.nativeTangent j n).action
      (ParticularWaveBounds.nativePoint (p.geometry n) i x) z) =
      LinearWaveResidual.shear (p.background.radius n) (p.background.frequencyBase n)
        (p.background.axialBase n) (p.directions.radialField n) (fun _ => CurlClassBounds.complexify z) x

variable {h}

theorem NativeDynamics.angularGeometry (d : NativeDynamics h) :
    NativeAngularGeometry (p.copyData c u b G A j) (nativeStrip s) p.directions h.phasePatch := by
  refine ⟨d.open_patch, d.background.phase_smooth,
    (fun n _ x hx _ => d.background.radius_ne n x hx),
    (fun n _ x hx _ => d.background.radial_radius n x hx),
    d.background.radius_invariant, d.background.radial_base_invariant,
    d.background.frequency_base_invariant, d.background.axial_base_invariant,
    d.background.radial_invariant, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [d.background.angular]
    exact ⟨_, actualCarrier_affine p.background b j n⟩
  · intro i n
    rw [d.background.angular]
    exact complexCopyVelocity_invariant (angleTangent_invariant _) (angleLift_invariant _)
      (p.geometry n) (p.length_pos n).le i
  · intro i n
    rw [d.background.angular]
    exact complexCopyPressure_invariant (angleTangent_invariant _) (angleLift_invariant _)
      (p.geometry n) (p.length_pos n).le i _
  · intro i n
    rw [d.background.angular]
    exact nativeCutoff_invariant ((0 : Q), (1 : ℝ)) (p.geometry n) (p.cutoff n) i

theorem NativeDynamics.principal (d : NativeDynamics h)
    (n : ℕ) (i : Frequency) {x : (Q × ℝ) × Plane}
    (hx : x ∈ (nativeStrip s).domain) (hi : x ∈ h.phasePatch n i) :
    ((p.copyData c u b G A j).raw i).principal (nativeStrip s) p.directions n x =
      -(p.copyData c u b G A j).source n x :=
  NativePrincipalEquations.complexCopyCoefficients_principal_at
    (p.copyData c u b G A j).background p.length_pos h.realControl h.imagControl n i hx hi
    (d.frequency_nonzero n) (h.normal_match n i x hx hi) (d.damping n i x hx hi)
    (d.fast n) (d.action n i x hx hi)

theorem NativeDynamics.local_equation (d : NativeDynamics h) (hκ : κ ≤ 1 / 2)
    (n : ℕ) (i : Frequency) {x : (Q × ℝ) × Plane}
    (hx : x ∈ (nativeStrip s).domain) (hi : x ∈ h.phasePatch n i) :
    ((p.copyData c u b G A j).corrected (nativeStrip s) p.directions i).harmonicResidual
        (nativeStrip s) p.directions n x +
        (fun k => (p.copyData c u b G A j).source n x k *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) =
      (fun k => ((p.copyData c u b G A j).localGood (nativeStrip s) p.directions n i x k +
        (p.copyData c u b G A j).localGaussian p.directions n i x k) *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) := by
  obtain ⟨ha, hp⟩ := h.raw_jets
  have hin := localInput_of_coefficients (p.copyData c u b G A j) h.background h.envelope_nonneg ha hp
  exact native_cancellation_of_principal d.angularGeometry hin
    (LocalizedWaveBounds.LocalClass.of_localJets (fun _ _ _ => zero_le_one) h.cutoff)
    hκ h.lower_pos
    (fun n i x hx hi => by rw [h.normal_match n i x hx hi]; exact h.normal_lower n i x hx hi)
    (fun n i x hx hi => by rw [h.normal_match n i x hx hi]; exact h.normal_upper n i x hx hi)
    (LocalizedWaveBounds.LocalClass.band_const h.inverse_frequency) n i hx hi (d.principal n i hx hi)

/-- The actual inhomogeneous common wave cancels the literal HR source
on the whole lift, including the uncovered-source term in its Gaussian. -/
theorem NativeDynamics.common_equation (d : NativeDynamics h) (hκ : κ ≤ 1 / 2)
    (n : ℕ) {x : (Q × ℝ) × Plane} (hx : x ∈ (nativeStrip s).domain) :
    (p.wave s c u b G A j).harmonicResidual (nativeStrip s) p.directions n x +
        (fun k => (p.copyData c u b G A j).source n x k *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) =
      (fun k => ((p.copyData c u b G A j).globalGood (nativeStrip s) p.directions n x k +
        (p.copyData c u b G A j).globalGaussian p.directions n x k) *
          carrier ((j : ℝ) * b.frequency n) ((actualCarrier p.background b j).phase n) x) := by
  apply (p.copyData c u b G A j).common_cancellation h.cells h.cutoff_support (nativeStrip s) p.directions _ n hx
  intro m i y hy hi
  rcases h.phase_cover m i y hy hi with hC | hpath
  · exact d.local_equation hκ m i hy hC
  · have hz := localized_zero_of_source_path (p := p) (c := c) (u := u) (b := b) (G := G) (A := A) (j := j) hpath
    have hr := raw_zero_of_source_path (p := p) (c := c) (u := u) (b := b) (G := G) (A := A) (j := j) hpath
    exact local_cancellation_of_zero_germs _ _ _ hz.1 hz.2
      ((p.copyData c u b G A j).localGaussian_zero_of_fields p.directions hr.1 hr.2.2) hr.2.2

end ParticularParameters

end NativeEquations

end NavierStokes.CorrectionStep
