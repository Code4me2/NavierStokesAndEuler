import NavierStokes.ActualCycleParameters
import NavierStokes.CyclePhysicalPrefixes
import NavierStokes.CycleStateCoherence
import NavierStokes.ActualInitialMeanEquation
import NavierStokes.ActualIterationLedger
import NavierStokes.ActualCarrierGeometry
import NavierStokes.ActualMeanPhysicalData
import NavierStokes.ActualMeanStageData
import NavierStokes.MixedCandidateAssembly

/-!
# The same initialized correction sequence and its physical prefixes

Every state below comes from the actual initialized primary choice and the
fixed actual cycle parameters. The finite labels, phase carriers, base error,
and current pressure alias are retained through the literal recurrence.
-/

noncomputable section

namespace NavierStokes.ActualCandidateConstruction

open Set Function Filter ProblemStatement
open CorrectionState CorrectionStep
open CorrectionInitialization.ActualPrimary
open scoped ContDiff Topology BigOperators

universe u

abbrev Index := ActualInitialization.Index
abbrev Point := CorrectionStep.CyclePoint
abbrev Full := Point × ℝ

noncomputable def parameters (B N0 : ℕ) : CycleParameters (Index B N0) :=
  ActualCycleParameters.fixedParameters B N0

noncomputable def parameterSequence (B N0 : ℕ) : ℕ → CycleParameters (Index B N0) :=
  fun _ => parameters B N0

noncomputable def cycle (B N0 : ℕ) : ℕ → CycleState (Index B N0) :=
  CycleState.iterate (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0)




theorem cycle_carrier (B N0 j : ℕ) (l : Index B N0) :
    SameCarrier ((cycle B N0 j).coefficients.blocks l) (ActualInitialization.tangentBlock l) := by
  induction j with
  | zero => exact ActualInitialization.primary_tangent_carrier l
  | succ j ih => exact ⟨ih.frequency, ih.phase, ih.angular⟩


theorem cycle_signed_carrier (B N0 j : ℕ) (l : Index B N0) :
    SameCarrier ((cycle B N0 j).coefficients.blocks l)
      ((parameters B N0).signedBlock (cycle B N0 j).coefficients (commonContext B)
        (cycle B N0 j).state l) :=
  ActualCycleParameters.fixedParameters_signed_carrier _ _ l (cycle_carrier B N0 j l)

theorem cycle_representation (B N0 j : ℕ) :
    CycleRepresentation (cycle B N0 j).coefficients (cycle B N0 j).state
      (cycle B N0 j).axisymmetricAlias :=
  CycleState.iterate_representation (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) (ActualInitialization.initialCycleState_represents B N0)
    (cycle_signed_carrier B N0) j








/-- One positive band floor is retained for every physical stage. -/
noncomputable def firstBand (B N0 : ℕ) : ℕ := max 4 (ActualCycleParameters.bandFloor B N0)

theorem firstBand_four (B N0 : ℕ) : 4 ≤ firstBand B N0 := le_max_left _ _




noncomputable def qbig (B N0 : ℕ) : ℝ := ChartScales.Q (firstBand B N0)

theorem qbig_pos (B N0 : ℕ) : 0 < qbig B N0 := ChartScales.Q_pos _


/-- One extra comparison band keeps every native point with `q/Q < 2`
inside the original raw field's validity domain. -/
noncomputable def residualBand (B N0 : ℕ) : ℕ := firstBand B N0 + 1


theorem firstBand_le_residualBand (B N0 : ℕ) : firstBand B N0 ≤ residualBand B N0 := Nat.le_succ _

theorem twice_residual_scale (B N0 : ℕ) :
    2 * ChartScales.Q (residualBand B N0) = qbig B N0 := by
  change 2 * (2 : ℝ) ^ (-((firstBand B N0 + 1 : ℕ) : ℝ)) =
    (2 : ℝ) ^ (-(firstBand B N0 : ℝ))
  rw [Nat.cast_add, Nat.cast_one, neg_add,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg_one]
  ring


noncomputable def physicalDomain (B N0 : ℕ) : Set SpaceTime :=
  CutStageEstimates.physicalSublevel h (qbig B N0)



/-! ## One selected initialization -/

noncomputable def selectedBudget : ℕ := 0

noncomputable def selectedThreshold : ℕ := ActualCarrierGeometry.startingThreshold 0

theorem selectedThreshold_geometry : ActualCarrierGeometry.geometricThreshold ≤ selectedThreshold :=
  ActualCarrierGeometry.geometricThreshold_le_startingThreshold 0






/-! ## Exact finite physical prefixes in any valid polar chart -/

noncomputable def graph (n : ℕ) : PhysicalResidualBridge.ScaledGraph :=
  PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CorrectionInitialization.CommonWindow.index h n)

noncomputable def basePressure (B n : ℕ) : Full → ℝ :=
  ActualBaseResidual.basePressure certificate modulation upper B n




noncomputable def chartPressureStages (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ → PressureField :=
  CyclePhysicalPrefixes.pressureStages (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n (basePressure B n)

noncomputable def chartPotentialParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ → VelocityField :=
  CyclePhysicalPrefixes.potentialParts (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n

noncomputable def chartDirectStages (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : ℕ → VelocityField :=
  CyclePhysicalPrefixes.directStages (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) a i (graph n) n




/-! The global physical representatives need only agree with an individual
chart on its open validity set. Finite summation and the genuine residual
preserve precisely this local agreement. -/






/-! ## The actual mean fields, with one common physical representative

The selector defining this atlas depends on the physical point and the
fixed validity strip. It is independent of the scalar being represented.
Consequently sums and differences retain the original absolute mean and
pressure; no new integration constant or choice enters a later stage. -/

noncomputable def meanAtlas (B N0 : ℕ) :=
  ActualMeanPhysicalData.initialAtlas (firstBand B N0)

noncomputable def meanField (B N0 : ℕ) (degree : ℝ)
    (f : ActualMeanPhysicalData.Scalar) : PressureField :=
  (meanAtlas B N0).physical standardRegion.carrier degree f ∘
    PhysicalMeanJetBounds.physicalPoint h

noncomputable def meanAngularField (B N0 : ℕ) (degree : ℝ)
    (f : ActualMeanPhysicalData.Scalar) : VelocityField :=
  fun w => meanField B N0 degree f w •
    PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection w)





noncomputable def angularNativeStages (B N0 : ℕ) : ℕ → ActualMeanPhysicalData.Scalar :=
  fun k => Nat.casesOn k (cycle B N0 0).state.mean.angular
    (fun j => (cycle B N0 (j + 1)).state.mean.angular - (cycle B N0 j).state.mean.angular)

noncomputable def pressureNativeStages (B N0 : ℕ) : ℕ → ActualMeanPhysicalData.Scalar :=
  fun k => Nat.casesOn k (cycle B N0 0).state.pressure
    (fun j => (cycle B N0 (j + 1)).state.pressure - (cycle B N0 j).state.pressure)

noncomputable def angularMeanStages (B N0 : ℕ) : ℕ → VelocityField :=
  fun j => meanAngularField B N0 (CoordinateAlgebra.A h) (angularNativeStages B N0 j)

noncomputable def pressureMeanStages (B N0 : ℕ) : ℕ → PressureField :=
  fun j => meanField B N0 (2 * CoordinateAlgebra.A h) (pressureNativeStages B N0 j)

theorem angularNativeStages_succ (B N0 j : ℕ) :
    angularNativeStages B N0 (j + 1) =
      ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state).angular +
      ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state).angular := by
  change ((parameters B N0).next (cycle B N0 j).coefficients
    (commonContext B) (cycle B N0 j).state).mean.angular -
      (cycle B N0 j).state.mean.angular = _
  rw [CycleParameters.next_mean]
  change (_ + _) + _ - _ = _
  abel




noncomputable def temporalNative (B N0 j : ℕ) : ActualMeanPhysicalData.Scalar :=
  VariableGaugeMean.temporalPotential (parameters B N0).gauge (parameters B N0).timeExponent
    (parameters B N0).commonIndex (commonContext B)
    ((parameters B N0).afterSigned (cycle B N0 j).coefficients
      (commonContext B) (cycle B N0 j).state)

noncomputable def rankNative (B N0 j : ℕ) : ActualMeanPhysicalData.Scalar :=
  VariableGaugeMean.rankPotential (parameters B N0).gauge (parameters B N0).rank (commonContext B)
    ((parameters B N0).afterTemporal (cycle B N0 j).coefficients
      (commonContext B) (cycle B N0 j).state)

noncomputable def streamNativeStages (B N0 : ℕ) : ℕ → ActualMeanPhysicalData.Scalar :=
  fun k => Nat.casesOn k
    (ActualMeanPhysicalData.initialTemporalScalar B N0 + ActualMeanPhysicalData.initialRankScalar B N0)
    (fun j => temporalNative B N0 j + rankNative B N0 j)

noncomputable def streamMeanStages (B N0 : ℕ) : ℕ → VelocityField :=
  fun j => meanAngularField B N0 (CoordinateAlgebra.A h - 1 / 2) (streamNativeStages B N0 j)

theorem streamMeanStages_zero (B N0 : ℕ) :
    streamMeanStages B N0 0 =
      (ActualMeanPhysicalData.initialStreamFamily B N0 (firstBand B N0)).angularField := rfl

theorem angularMeanStages_zero (B N0 : ℕ) :
    angularMeanStages B N0 0 =
      (ActualMeanPhysicalData.initialAngularFamily B N0 (firstBand B N0)).angularField := rfl

theorem pressureMeanStages_zero (B N0 : ℕ) :
    pressureMeanStages B N0 0 =
      (ActualMeanPhysicalData.initialPressureFamily B N0 (firstBand B N0)).field := rfl

abbrev MeanCycleInput (B N0 : ℕ) :=
  ActualMeanPhysicalData.InitialCycleInput B N0 (firstBand B N0) (parameterSequence B N0)


theorem streamMeanStages_succ {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    streamMeanStages B N0 (j + 1) =
      ((ActualMeanPhysicalData.initialCycleData H).streamFamily j).angularField := rfl

theorem angularMeanStages_succ {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    angularMeanStages B N0 (j + 1) =
      ((ActualMeanPhysicalData.initialCycleData H).angularIncrementFamily j).angularField := rfl

theorem pressureMeanStages_succ {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    pressureMeanStages B N0 (j + 1) =
      ((ActualMeanPhysicalData.initialCycleData H).pressureIncrementFamily j).field := rfl

noncomputable def chartMeanPressureParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n j : ℕ) : PressureField :=
  CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (fun x => pressureNativeStages B N0 j n x.1))

noncomputable def chartStreamParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n : ℕ) : ℕ → VelocityField :=
  fun k => Nat.casesOn k
    (CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (CyclePhysicalPrefixes.meridionalComponents (cycle B N0 0).state.mean n)))
    (fun j => CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n +
       CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n)))

theorem angularNativeStages_overlap {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    (meanAtlas B N0).OverlapLaw standardRegion.carrier (CoordinateAlgebra.A h)
      (angularNativeStages B N0 j) := by
  cases j with
  | zero => exact (ActualMeanPhysicalData.initialized_overlap B N0 (firstBand B N0)).angular
  | succ j =>
      exact (((ActualMeanPhysicalData.initialCycleData H).state_overlap (j + 1)).angular).sub
        (((ActualMeanPhysicalData.initialCycleData H).state_overlap j).angular)

theorem pressureNativeStages_overlap {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    (meanAtlas B N0).OverlapLaw standardRegion.carrier (2 * CoordinateAlgebra.A h)
      (pressureNativeStages B N0 j) := by
  cases j with
  | zero => exact (ActualMeanPhysicalData.initialized_overlap B N0 (firstBand B N0)).pressure
  | succ j =>
      exact (((ActualMeanPhysicalData.initialCycleData H).state_overlap (j + 1)).pressure).sub
        (((ActualMeanPhysicalData.initialCycleData H).state_overlap j).pressure)

theorem angularNativeStages_chart (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n j : ℕ) :
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (fun x => ![0, angularNativeStages B N0 j n x.1, 0])) =
      chartDirectStages B N0 a i n j := by
  cases j with
  | zero => rfl
  | succ j =>
      change CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
        (fun x => ![0, angularNativeStages B N0 (j + 1) n x.1, 0])) =
        CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
          (CyclePhysicalPrefixes.angularComponents
            ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
              (commonContext B) (cycle B N0 j).state) n +
           CyclePhysicalPrefixes.angularComponents
            ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
              (commonContext B) (cycle B N0 j).state) n))
      congr 2
      rw [angularNativeStages_succ]
      funext x q
      fin_cases q <;> simp [CyclePhysicalPrefixes.angularComponents]

theorem angularMeanStages_on_chart {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ) (hn : firstBand B N0 ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    angularMeanStages B N0 j w = chartDirectStages B N0 a i n j w := by
  have he := (meanAtlas B N0).angular_field (angularNativeStages_overlap H j) ha i n hn ht hu hw
  change angularMeanStages B N0 j w =
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (fun x => ![0, angularNativeStages B N0 j n x.1, 0])) w at he
  rw [angularNativeStages_chart] at he
  exact he

theorem pressureMeanStages_on_chart {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ) (hn : firstBand B N0 ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    pressureMeanStages B N0 j w = chartMeanPressureParts B N0 a i n j w :=
  (meanAtlas B N0).pressure_field (pressureNativeStages_overlap H j) ha i n hn ht hu hw

theorem streamMeanStages_curl_on_chart {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ)
    {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ) (hn : firstBand B N0 ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((meanAtlas B N0).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    SpatialCurl.spatialCurl (streamMeanStages B N0 j) w = chartStreamParts B N0 a i n j w := by
  cases j with
  | zero => exact ActualMeanPhysicalData.initialStream_curl B N0 (firstBand B N0) n hn ha i ht hu hw
  | succ j => exact ActualMeanPhysicalData.cycleStream_curl H j n hn ha i ht hu hw

noncomputable def chartBaseVelocity (B : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : VelocityField :=
  CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
    (PhysicalResidualBridge.baseComponents (commonContext B) n))

noncomputable def chartBasePressure (B : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) : PressureField :=
  CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (basePressure B n))

noncomputable def chartWaveParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n : ℕ) : ℕ → VelocityField :=
  fun k => Nat.casesOn k
    (CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      ((cycle B N0 0).state.oscillation n)))
    (fun j => CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      ((parameters B N0).particularVelocity (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n +
        (parameters B N0).signedVelocity (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n)))

noncomputable def chartWavePressureParts (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index)
    (n : ℕ) : ℕ → PressureField :=
  fun k => Nat.casesOn k
    (CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      ((cycle B N0 0).state.oscillatoryPressure n)))
    (fun j => CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      ((parameters B N0).particularPressure (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n +
        (parameters B N0).signedPressure (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state n)))

theorem chartPotentialParts_zero (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPotentialParts B N0 a i n 0 = chartBaseVelocity B a i n +
      chartWaveParts B N0 a i n 0 + chartStreamParts B N0 a i n 0 := by
  change CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
    (PhysicalResidualBridge.baseComponents (commonContext B) n +
      CyclePhysicalPrefixes.meridionalComponents (cycle B N0 0).state.mean n +
        (cycle B N0 0).state.oscillation n)) =
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (PhysicalResidualBridge.baseComponents (commonContext B) n)) +
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      ((cycle B N0 0).state.oscillation n)) +
    CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
      (CyclePhysicalPrefixes.meridionalComponents (cycle B N0 0).state.mean n))
  simp only [map_add]
  abel

theorem chartPotentialParts_succ (B N0 j : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPotentialParts B N0 a i n (j + 1) =
      chartWaveParts B N0 a i n (j + 1) + chartStreamParts B N0 a i n (j + 1) := by
  change CyclePhysicalPrefixes.polarVelocityMap a i (CyclePhysicalPrefixes.velocityMap (graph n)
    (((parameters B N0).particularVelocity (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n +
      (parameters B N0).signedVelocity (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n) +
      CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).temporalIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n +
      CyclePhysicalPrefixes.meridionalComponents
        ((parameters B N0).rankIncrement (cycle B N0 j).coefficients
          (commonContext B) (cycle B N0 j).state) n)) = _
  simp only [chartWaveParts, chartStreamParts, map_add]
  abel

theorem chartPressureParts_zero (B N0 : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPressureStages B N0 a i n 0 = chartBasePressure B a i n +
      chartWavePressureParts B N0 a i n 0 + chartMeanPressureParts B N0 a i n 0 := by
  change CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (basePressure B n + (cycle B N0 0).state.totalPressureIncrement n)) =
    CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n) (basePressure B n)) +
    CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      ((cycle B N0 0).state.oscillatoryPressure n)) +
    CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
      (fun x => (cycle B N0 0).state.pressure n x.1))
  have he : (cycle B N0 0).state.totalPressureIncrement n =
      (fun x => (cycle B N0 0).state.pressure n x.1) + (cycle B N0 0).state.oscillatoryPressure n := rfl
  rw [he]
  simp only [map_add]
  abel

theorem chartPressureParts_succ (B N0 j : ℕ) (a : ℝ) (i : PolarCharts.Index) (n : ℕ) :
    chartPressureStages B N0 a i n (j + 1) = chartWavePressureParts B N0 a i n (j + 1) +
      chartMeanPressureParts B N0 a i n (j + 1) := by
  have he : CyclePhysicalPrefixes.stepPressureComponents (parameters B N0)
      (cycle B N0 j).coefficients (commonContext B) (cycle B N0 j).state n =
      ((parameters B N0).particularPressure (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n +
       (parameters B N0).signedPressure (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state n) +
      (fun x => pressureNativeStages B N0 (j + 1) n x.1) := by
    funext x
    unfold CyclePhysicalPrefixes.stepPressureComponents pressureNativeStages
    change _ = _ + _ +
      (((parameters B N0).afterRank (cycle B N0 j).coefficients
        (commonContext B) (cycle B N0 j).state).pressure n x.1 -
        (cycle B N0 j).state.pressure n x.1)
    ring
  change CyclePhysicalPrefixes.polarPressureMap a i (CyclePhysicalPrefixes.pressureMap (graph n)
    (CyclePhysicalPrefixes.stepPressureComponents (parameters B N0)
      (cycle B N0 j).coefficients (commonContext B) (cycle B N0 j).state n)) = _
  rw [he]
  simp only [chartWavePressureParts, chartMeanPressureParts, map_add]

/-! ## The fixed physical base in the same chart

Both normalizations below are computed from the actual graph map. In
particular the pressure factor is the square of the velocity factor. -/

theorem graph_cylinderPoint (n : ℕ) (z : SpaceTime) :
    ActualBaseResidual.cylinderPoint h (ChartScales.Q n)
      (PhysicalResidualTZ.graphMapTZ (graph n) z) = z := by
  have hQ := ChartScales.Q_pos n
  have hs : Real.sqrt (ChartScales.Q n) * ChartScales.Q n ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ]
    norm_num
  have hd : ChartScales.Q n ^ CoordinateAlgebra.D h * ChartScales.Q n ^ (-CoordinateAlgebra.D h) = 1 := by
    rw [← Real.rpow_add hQ]
    simp
  have ht : ChartScales.Q n * ChartScales.Q n ^ (-1 : ℝ) = 1 := by
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hQ.ne']
  have htime : (graph n).velocityScale * (graph n).radialScale * (graph n).epsilon =
      ChartScales.Q n ^ (-1 : ℝ) :=
    PhysicalResidualBridge.commonGraph_slowTimeScale hQ h _
  have haxial : (graph n).radialScale * (graph n).epsilon =
      ChartScales.Q n ^ (-CoordinateAlgebra.D h) :=
    PhysicalResidualBridge.commonGraph_axialScale hQ h _
  apply Prod.ext
  · change 1 - ChartScales.Q n *
      ((graph n).velocityScale * (graph n).radialScale * (graph n).epsilon * (1 - z.1)) = z.1
    rw [htime, ← mul_assoc, ht]
    ring
  · ext j
    fin_cases j
    · simp only [ActualBaseResidual.cylinderPoint]
      simp only [AxisymmetricResidual.pack, ProblemStatement.coordinateVector,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
      norm_num
      simp only [show (0 : Fin 3) ≠ 2 by decide, ite_false, add_zero]
      change Real.sqrt (ChartScales.Q n) * (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0) = z.2 0
      rw [← mul_assoc, hs, one_mul]
    · simp [ActualBaseResidual.cylinderPoint, AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PhysicalResidualTZ.graphMapTZ, PhysicalResidualBridge.ScaledGraph.map,
        PhysicalResidualTZ.swapCylinder_apply]
    · simp only [ActualBaseResidual.cylinderPoint]
      simp only [AxisymmetricResidual.pack, ProblemStatement.coordinateVector,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
      norm_num
      change ChartScales.Q n ^ CoordinateAlgebra.D h *
        ((graph n).radialScale * (graph n).epsilon * z.2 2) = z.2 2
      rw [haxial, ← mul_assoc, hd, one_mul]

theorem graph_physicalPoint (n : ℕ) (z : SpaceTime) :
    ActualBaseResidual.physicalPoint h (ChartScales.Q n)
      (PhysicalResidualTZ.graphMapTZ (graph n) z) = (z.1, CylindricalResidual.chart z.2) := by
  unfold ActualBaseResidual.physicalPoint
  rw [graph_cylinderPoint]

theorem graph_mem_baseDomain (n : ℕ) {z : SpaceTime} (ht : z.1 < 1) (hr : 0 < z.2 0) :
    PhysicalResidualTZ.graphMapTZ (graph n) z ∈ ActualBaseResidual.domain := by
  constructor
  · change 0 < ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0
    exact mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr
  · change 0 < (graph n).velocityScale * (graph n).radialScale * (graph n).epsilon * (1 - z.1)
    have htime : (graph n).velocityScale * (graph n).radialScale * (graph n).epsilon =
        ChartScales.Q n ^ (-1 : ℝ) :=
      PhysicalResidualBridge.commonGraph_slowTimeScale (ChartScales.Q_pos n) h _
    rw [htime]
    exact mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) (sub_pos.mpr ht)

theorem base_velocity_on_cylinder (B n : ℕ) {z : SpaceTime} (ht : z.1 < 1) (hr : 0 < z.2 0) :
    CyclePhysicalPrefixes.velocityMap (graph n) (PhysicalResidualBridge.baseComponents (commonContext B) n) z =
      CylindricalResidual.frame (-(z.2 1))
        (FinalSlowBase.velocity certificate modulation upper B (z.1, CylindricalResidual.chart z.2)) := by
  have hb := ActualBaseResidual.velocityAtScale_eq_baseComponents certificate modulation upper B
    (CorrectionInitialization.CommonWindow.index h) n (graph_mem_baseDomain n ht hr)
  change ActualBaseResidual.velocityAtScale certificate modulation upper B (ChartScales.Q n)
    (PhysicalResidualTZ.graphMapTZ (graph n) z) =
    PhysicalResidualBridge.baseComponents (commonContext B) n
      (PhysicalResidualTZ.graphMapTZ (graph n) z) at hb
  ext j
  simp only [CyclePhysicalPrefixes.velocityMap, LinearMap.coe_mk, AddHom.coe_mk,
    PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
    PhysicalResidualBridge.baseComponents (commonContext B) n
      (PhysicalResidualTZ.graphMapTZ (graph n) z) j = _
  rw [← hb]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) * (ChartScales.Q n ^ CoordinateAlgebra.A h *
    (CylindricalResidual.frame (-(z.2 1))
      (FinalSlowBase.velocity certificate modulation upper B
        (ActualBaseResidual.physicalPoint h (ChartScales.Q n)
          (PhysicalResidualTZ.graphMapTZ (graph n) z)))) j) = _
  rw [graph_physicalPoint, ← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n)]
  simp

theorem base_pressure_on_cylinder (B n : ℕ) (z : SpaceTime) :
    CyclePhysicalPrefixes.pressureMap (graph n) (basePressure B n) z =
      FinalSlowBase.pressure certificate modulation upper B (z.1, CylindricalResidual.chart z.2) := by
  change (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) ^ 2 *
    (ChartScales.Q n ^ (2 * CoordinateAlgebra.A h) *
      FinalSlowBase.pressure certificate modulation upper B
        (ActualBaseResidual.physicalPoint h (ChartScales.Q n)
          (PhysicalResidualTZ.graphMapTZ (graph n) z))) = _
  rw [graph_physicalPoint, pow_two, ← mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n),
    ← Real.rpow_add (ChartScales.Q_pos n)]
  have he : -CoordinateAlgebra.A h + -CoordinateAlgebra.A h + 2 * CoordinateAlgebra.A h = 0 := by ring
  rw [he, Real.rpow_zero, one_mul]

theorem chartBaseVelocity_eq (B : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime} (ht : w.1 < 1) (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    chartBaseVelocity B a i n w = FinalSlowBase.velocity certificate modulation upper B w := by
  let z := PhysicalCurlCovariance.polarCoordinates a i w
  have hr : 0 < z.2 0 := (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw).1
  have hangle : z.2 1 = (PhysicalCurlCovariance.polarInput a i w).2 := by
    simp only [z, PhysicalCurlCovariance.polarCoordinates, AxisymmetricResidual.pack_one]
  unfold chartBaseVelocity
  simp only [CyclePhysicalPrefixes.polarVelocityMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hangle]
  change CylindricalResidual.frame (z.2 1)
    (CyclePhysicalPrefixes.velocityMap (graph n)
      (PhysicalResidualBridge.baseComponents (commonContext B) n) z) = _
  rw [base_velocity_on_cylinder B n (z := z) ht hr, CylindricalResidual.frame_inverse']
  exact congrArg (FinalSlowBase.velocity certificate modulation upper B)
    (ActualMeanPotentialRealization.polarCoordinates_back ha i hw)

theorem chartBasePressure_eq (B : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime} (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    chartBasePressure B a i n w = FinalSlowBase.pressure certificate modulation upper B w := by
  change CyclePhysicalPrefixes.pressureMap (graph n) (basePressure B n)
    (PhysicalCurlCovariance.polarCoordinates a i w) = _
  rw [base_pressure_on_cylinder]
  exact congrArg (FinalSlowBase.pressure certificate modulation upper B)
    (ActualMeanPotentialRealization.polarCoordinates_back ha i hw)

theorem basePotential_curl_on_chart (B : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {w : SpaceTime} (ht : w.1 < 1) (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    SpatialCurl.spatialCurl (TailGaugePotential.finalPotential certificate modulation upper B) w =
      chartBaseVelocity B a i n w :=
  (TailGaugePotential.finalPotential_sameCurl certificate modulation upper B ht).trans
    (chartBaseVelocity_eq B ha i n ht hw).symm

/-! ## Constructed direct angular and mean-stream stage data -/

noncomputable def directData {B N0 : ℕ} (H : MeanCycleInput B N0) :
    ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h (qbig B N0)) :=
  fun k => Nat.casesOn k
    (ActualMeanStageData.initialAngularData B N0 (firstBand B N0) (qbig B N0) le_rfl)
    (fun j => ActualMeanStageData.cycleAngularData H j (qbig B N0) le_rfl)

noncomputable def streamData {B N0 : ℕ} (H : MeanCycleInput B N0) :
    ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain h (qbig B N0)) :=
  fun k => Nat.casesOn k
    (ActualMeanStageData.initialStreamData B N0 (firstBand B N0) (qbig B N0) le_rfl)
    (fun j => ActualMeanStageData.cycleStreamData H j (qbig B N0) le_rfl)

noncomputable def meanStreamSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedAxisPreservation.AngularSupport (MixedAxisPreservation.localDomain h (qbig B N0)) :=
  MixedAxisPreservation.AngularSupport.ofAngularData (streamData H j) (fun _ hw => hw)

theorem directData_field {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    LocalAngularDiagonal.rawSeries (directData H) j = angularMeanStages B N0 j := by
  cases j with
  | zero =>
      exact (ActualMeanStageData.initialAngularData_field B N0 (firstBand B N0) (qbig B N0) le_rfl).trans
        (angularMeanStages_zero B N0).symm
  | succ j =>
      exact (ActualMeanStageData.cycleAngularData_field H j (qbig B N0) le_rfl).trans
        (angularMeanStages_succ H j).symm

theorem streamData_field {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    DirectAngularDiagonal.angularField (streamData H j).scalar = streamMeanStages B N0 j := by
  cases j with
  | zero =>
      exact (ActualMeanStageData.initialStreamData_field B N0 (firstBand B N0) (qbig B N0) le_rfl).trans
        (streamMeanStages_zero B N0).symm
  | succ j =>
      exact (ActualMeanStageData.cycleStreamData_field H j (qbig B N0) le_rfl).trans
        (streamMeanStages_succ H j).symm

theorem meanStreamSupport_field {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    (meanStreamSupport H j).field = streamMeanStages B N0 j := streamData_field H j


theorem streamMeanStages_smooth {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    ContDiffOn ℝ ∞ (streamMeanStages B N0 j) (physicalDomain B N0) := by
  rw [← streamData_field H j]
  exact (streamData H j).field_smooth
    (LocalAngularDiagonal.localSlowDomain_open outgoing.data.h_pos outgoing.data.h_lt_half _)

theorem angularMeanStages_shrinkingSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (qbig B N0) (angularMeanStages B N0 j) := by
  cases j with
  | zero =>
      have hh := (ActualMeanStageData.initial_shrinkingSupport B N0 (firstBand B N0) (qbig B N0) le_rfl).1
      erw [ActualMeanStageData.initialAngularSupport_field] at hh
      simp only [angularMeanStages_zero]
      exact hh
  | succ j =>
      have hh := (ActualMeanStageData.cycle_shrinkingSupport H j (qbig B N0) le_rfl).1
      erw [ActualMeanStageData.cycleAngularSupport_field] at hh
      simp only [angularMeanStages_succ H]
      exact hh

theorem streamMeanStages_shrinkingSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (qbig B N0) (streamMeanStages B N0 j) := by
  cases j with
  | zero =>
      have hh := (ActualMeanStageData.initial_shrinkingSupport B N0 (firstBand B N0) (qbig B N0) le_rfl).2.2.2
      erw [ActualMeanStageData.initialStreamSupport_field] at hh
      simp only [streamMeanStages_zero]
      exact hh
  | succ j =>
      have hh := (ActualMeanStageData.cycle_shrinkingSupport H j (qbig B N0) le_rfl).2.2.2
      erw [ActualMeanStageData.cycleStreamSupport_field] at hh
      simp only [streamMeanStages_succ H]
      exact hh

theorem pressureMeanStages_shrinkingSupport {B N0 : ℕ} (H : MeanCycleInput B N0) (j : ℕ) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
      (qbig B N0) (pressureMeanStages B N0 j) := by
  cases j with
  | zero =>
      rw [pressureMeanStages_zero]
      exact (PhysicalStageSupport.actual_coherent_support
        (ActualMeanPhysicalData.initialPressureFamily B N0 (firstBand B N0))
        (ActualMeanStageData.nativeSupport_of_moving _
          (ActualMeanPhysicalData.initial_pressure_moving B N0)) le_rfl).1
  | succ j =>
      rw [pressureMeanStages_succ H]
      have hs : (VariableGaugeMean.reconstructState ActualMeanPhysicalData.initialGeometry.gauge
          (commonContext B) (ActualInitialization.initialCycleState B N0).state).pressure =
          (ActualInitialization.initialCycleState B N0).state.pressure := by
        rw [ActualMeanPhysicalData.initialGeometry_gauge]
        rfl
      exact (PhysicalStageSupport.actual_coherent_support
        ((ActualMeanPhysicalData.initialCycleData H).pressureIncrementFamily j)
        (ActualMeanStageData.nativeSupport_of_moving _
          ((ActualMeanPhysicalData.initialCycleData H).pressureIncrement_moving hs j)) le_rfl).1

/-! The stage constructors retain the actual copy data. The wave producers
supply these records; the mean field is fixed by the same cycle above. -/

noncomputable def initialPotentialStage (B N0 : ℕ)
    (wave : MixedAxisPreservation.CopyPotential.{u} h) :
    MixedAxisPreservation.PotentialStage.{u} h (MixedAxisPreservation.localDomain h (qbig B N0)) where
  waveCount := 1
  waves _ := wave
  streamCount := 1
  streams _ := ActualMeanStageData.initialStreamSupport B N0 (firstBand B N0) (qbig B N0) le_rfl


theorem initialPotentialStage_field (B N0 : ℕ)
    (wave : MixedAxisPreservation.CopyPotential.{u} h) :
    (initialPotentialStage B N0 wave).field = wave.field + streamMeanStages B N0 0 := by
  funext w
  change (∑ _ : Fin 1, wave.field w) +
    (∑ _ : Fin 1, (ActualMeanStageData.initialStreamSupport B N0 (firstBand B N0)
      (qbig B N0) le_rfl).field w) = _
  simp [streamMeanStages_zero]
  erw [ActualMeanStageData.initialStreamSupport_field]


end NavierStokes.ActualCandidateConstruction
