import NavierStokes.PhysicalStageBounds
import NavierStokes.ActualBaseVelocityBounds
import NavierStokes.MixedFiniteBackground

/-!
# Initial physical velocity bounds from the actual base and native data

The base potential is the anchored `TailGaugePotential.finalPotential`.
Its curl is the constructed `FinalSlowBase.velocity`.  Only the finite
initialization potential pays the derivative used by the curl estimate;
no growth estimate on the base potential or its gauge is required.
-/

noncomputable section

namespace NavierStokes.InitializedPhysicalBackground

open Set Filter ProblemStatement DiagonalResidual PhysicalStageBounds
open scoped Topology ContDiff BigOperators

/-- The loss for the actual finite initialization potential, before curl.
The offsets absorb its own native homogeneity, without a positivity
assumption on the initialization gain. -/
noncomputable def seedPotentialLoss (h waveAlpha waveShift meanAlpha : ℝ) (m : ℕ) : ℝ :=
  potentialLoss h (-(h * waveAlpha + waveShift)) (-(h * meanAlpha)) m

noncomputable def seedDirectLoss (h meanAlpha : ℝ) (m : ℕ) : ℝ :=
  directLoss h (-(h * meanAlpha)) m

/-- This loss depends only on fixed initialization data and derivative
order. It has no later correction-stage parameter. -/
noncomputable def initialLoss (h waveAlpha waveShift potentialAlpha directAlpha : ℝ)
    (m : ℕ) : ℝ :=
  max (ActualBaseVelocityBounds.heatLoss m)
    (max (seedPotentialLoss h waveAlpha waveShift potentialAlpha (m + 1))
      (seedDirectLoss h directAlpha m))


theorem endpoint_sublevel {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) :
    ∀ᶠ w in ActualBaseVelocityBounds.endpoint,
      w ∈ CutStageEstimates.physicalSublevel h qbig := by
  have ht := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  filter_upwards [ActualBaseVelocityBounds.endpoint_past,
    ht.eventually (gt_mem_nhds hqbig)] with w hw hqw
  exact ⟨hw, hqw⟩

theorem spatialCurl_add_on {U : Set SpaceTime} (hU : IsOpen U)
    {A B : VelocityField} (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    EqOn (SpatialCurl.spatialCurl (fun w => A w + B w))
      (fun w => SpatialCurl.spatialCurl A w + SpatialCurl.spatialCurl B w) U := by
  intro w hw
  have ha := ResidualStability.spatialSlice_differentiable hU hA hw
  have hb := ResidualStability.spatialSlice_differentiable hU hB hw
  change SpatialCurl.curlLinear
    (fderiv ℝ (fun y => A (w.1, y) + B (w.1, y)) w.2) = _
  rw [fderiv_fun_add ha hb, map_add]
  rfl

theorem spatialCurl_smoothOn {U : Set SpaceTime} (hU : IsOpen U)
    {A : VelocityField} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl A) U := by
  intro w hw
  exact (SpatialCurl.contDiffAt_spatialCurl (hA.contDiffAt (hU.mem_nhds hw))
    (by simp)).contDiffWithinAt

section NativeInitialization

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

/-- This applies the actual native-copy estimate at initialization, where
the positive-stage `RawStageBounds` interface is not available. -/
theorem potentialIncrement_rate (WA : WaveData h D I K (Fin 3))
    (MA : MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqbig : 0 < qbig) (hq : qbig ≤ ChartScales.Q MA.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (potentialIncrement WA MA) m
      (-seedPotentialLoss h WA.alpha WA.shift MA.alpha m) := by
  obtain ⟨C, hC, hb⟩ := potentialIncrement_bound
    (g := 0) (waveOffset := -(h * WA.alpha + WA.shift)) (meanOffset := -(h * MA.alpha))
    WA MA hh hh1 hq (by linarith) (by linarith) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  simpa only [seedPotentialLoss, zero_sub] using hb w hw hqw.2

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem directIncrement_rate (MB : MeanData h (CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqbig : 0 < qbig) (hq : qbig ≤ ChartScales.Q MB.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      MB.family.angularField m (-seedDirectLoss h MB.alpha m) := by
  obtain ⟨C, hC, hb⟩ := MB.angular_bound_with_gain
    (g := 0) (delta := -(h * MB.alpha)) hh hh1 hq (by linarith) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  simpa only [seedDirectLoss, directLoss, zero_sub] using hb w hw hqw.2

end NativeInitialization

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

noncomputable def initializedPotential (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2)) : VelocityField :=
  fun w => TailGaugePotential.finalPotential H v upper B w + potentialIncrement WA MA w

/-- Literal curl of the initialized potential plus the direct angular
initialization. The latter is not differentiated as a potential. -/
noncomputable def initializedVelocity (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h)) : VelocityField :=
  fun w => SpatialCurl.spatialCurl (initializedPotential H v upper B WA MA) w +
    MB.family.angularField w


/-- The only use of the anchored gauge is its proved equality of curls. -/
theorem initializedVelocity_decomposition (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q MA.firstBand) :
    EqOn (initializedVelocity H v upper B WA MA MB)
      (fun w => FinalSlowBase.velocity H v upper B w +
        SpatialCurl.spatialCurl (potentialIncrement WA MA) w + MB.family.angularField w)
      (CutStageEstimates.physicalSublevel F.data.h qbig) := by
  have hbase : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential H v upper B)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
    (TailGaugePotential.finalPotential_smooth H v upper B).mono
      (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hinc := potentialIncrement_smooth WA MA F.data.h_pos F.data.h_lt_half hq
  intro w hw
  unfold initializedVelocity initializedPotential
  rw [spatialCurl_add_on (CutStageEstimates.physicalSublevel_open F.data.h_pos
    F.data.h_lt_half qbig) hbase hinc hw]
  dsimp only
  rw [TailGaugePotential.finalPotential_sameCurl H v upper B hw.1]


/-- Initial physical velocity bound from native initialization data and
the actual constructed base. There is no initial-velocity rate premise. -/
theorem initializedVelocity_rate (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (initializedVelocity H v upper B WA MA MB) m
      (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
  let qbig := min (ChartScales.Q MA.firstBand) (ChartScales.Q MB.firstBand)
  have hqbig : 0 < qbig := lt_min (ChartScales.Q_pos _) (ChartScales.Q_pos _)
  have hqA : qbig ≤ ChartScales.Q MA.firstBand := min_le_left _ _
  have hqB : qbig ≤ ChartScales.Q MB.firstBand := min_le_right _ _
  let U := CutStageEstimates.physicalSublevel F.data.h qbig
  have hU : IsOpen U := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U :=
    endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hq := ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half
  have hsBase : ContDiffOn ℝ ∞ (FinalSlowBase.velocity H v upper B) U :=
    (FinalSlowBase.velocity_smooth H v upper B).mono (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hsInc : ContDiffOn ℝ ∞ (potentialIncrement WA MA) U :=
    potentialIncrement_smooth WA MA F.data.h_pos F.data.h_lt_half hqA
  have hsDirect : ContDiffOn ℝ ∞ MB.family.angularField U :=
    MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB
  have hsCurl := spatialCurl_smoothOn hU hsInc
  have hbase := (ActualBaseVelocityBounds.velocity_rate H v upper B m).weaken hq
    (neg_le_neg (le_max_left (ActualBaseVelocityBounds.heatLoss m)
      (max (seedPotentialLoss F.data.h WA.alpha WA.shift MA.alpha (m + 1))
        (seedDirectLoss F.data.h MB.alpha m))))
  have hinc : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (SpatialCurl.spatialCurl (potentialIncrement WA MA)) m
      (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
    apply ((potentialIncrement_rate WA MA F.data.h_pos F.data.h_lt_half hqbig hqA
      (m + 1)).spatialCurl hU hlU hsInc).weaken hq
    exact neg_le_neg ((le_max_left _ _).trans (le_max_right _ _))
  have hdirect : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      MB.family.angularField m (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
    apply (directIncrement_rate MB F.data.h_pos F.data.h_lt_half hqbig hqB m).weaken hq
    exact neg_le_neg ((le_max_right _ _).trans (le_max_right _ _))
  have hsum := (hbase.add hinc hU hlU hsBase hsCurl).add hdirect hU hlU
    (hsBase.add hsCurl) hsDirect
  exact hsum.congr_on hU hlU
    (initializedVelocity_decomposition H v upper B WA MA MB hqA).symm




/-- An exact representation adapter for initialization assembled elsewhere.
Its inputs identify the literal potential and direct angular field on an
eventual open neighborhood; no bound on either initialized velocity or
the base gauge is assumed. -/
theorem represented_initial_rate (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h))
    {A Bdirect : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U)
    (hA : EqOn (A 0) (initializedPotential H v upper B WA MA) U)
    (hB : EqOn (Bdirect 0) MB.family.angularField U) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity A Bdirect 0) m
      (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
  apply (initializedVelocity_rate H v upper B WA MA MB m).congr_on hU hlU
  intro w hw
  have he : A 0 =ᶠ[𝓝 w] initializedPotential H v upper B WA MA := by
    filter_upwards [hU.mem_nhds hw] with y hy
    exact hA hy
  rw [MixedFiniteBackground.uncutVelocity_zero]
  change SpatialCurl.spatialCurl (initializedPotential H v upper B WA MA) w +
    MB.family.angularField w = SpatialCurl.spatialCurl (A 0) w + Bdirect 0 w
  rw [SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq he, hB hw]


end ActualBase

end NavierStokes.InitializedPhysicalBackground
