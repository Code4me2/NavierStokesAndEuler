import NavierStokes.PhysicalMeanJetBounds
import NavierStokes.MixedDiagonalSchedule
import NavierStokes.TailGaugePotential
import NavierStokes.WithTopLemmas

/-!
# Raw physical stage estimates from native wave and mean data

The data below describe the actual copy families and coherent native mean
fields. Physical derivative estimates are consequences of their native
classes, support and chart identities. No `RawStageBounds` is an input.
-/

noncomputable section

namespace NavierStokes.PhysicalStageBounds

open Set Function Filter ProblemStatement
open scoped Topology ContDiff BigOperators

/-- Small physical q automatically restricts time to the interval on which
the existing physical-copy estimates are uniform. -/
theorem abs_time_le_one {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ 1) : |w.1| ≤ 1 := by
  have ha : 0 < 2 * h := by positivity
  have ha1 : 2 * h < 1 := by linarith
  have he := SimilarityCoordinates.coordinateQ_spec ha ha1
    (p := (1 - w.1, w.2 2)) (sub_pos.mpr hw)
  have hn : 0 ≤ (w.2 2) ^ 2 *
      SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) ^ (2 * h) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg he.1.le _)
  change SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) ≤ 1 at hq
  have heq : SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) -
      (w.2 2) ^ 2 * SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) ^ (2 * h) =
      1 - w.1 := he.2
  change w.1 < 1 at hw
  apply abs_le.mpr
  constructor <;> linarith

section Waves

variable (h : ℝ) (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D]
  (I K J : Type*)

/-- A native source and its actual physical copy representation. All
regularity is confined to the valid native patches. The number of
harmonics and the cover gap may vary between stages. -/
structure WaveData where
  lowerRadius : ℝ
  upperRadius : ℝ
  nativeWidth : ℝ
  slowBound : ℝ
  frequencyBound : ℝ
  alpha : ℝ
  shift : ℝ
  harmonics : ℕ
  gapBound : ℕ
  lower_pos : 0 < lowerRadius
  width_nonneg : 0 ≤ nativeWidth
  slow_nonneg : 0 ≤ slowBound
  frequency_one_le : 1 ≤ frequencyBound
  strip : WeightedClasses.StripData D
  weight : I → ℕ → D → ℝ
  source : I → ℕ → D → ℂ
  source_bounds : LocalPhysicalCopyBounds.LocalSourceBounds strip h alpha weight source
  copies : J → PhysicalCopyBounds.CopyFamily harmonics K
  cells : ∀ i, PhysicalCopyBounds.SupportCells (copies i)
  chart : ∀ i, LocalPhysicalCopyBounds.CommonChart (copies i) (cells i)
    lowerRadius upperRadius h nativeWidth shift source
  chart_maps : ∀ i k L, MapsTo ((chart i).map k L) ((chart i).domain k L) strip.domain
  carrier : ∀ i, PhysicalCopyBounds.CarrierBounds (copies i) (cells i)
    lowerRadius upperRadius h nativeWidth
  support : ∀ i, LocalPhysicalCopyBounds.SupportData (copies i)
    lowerRadius upperRadius h nativeWidth slowBound gapBound
  smooth : ∀ i, LocalPhysicalCopyBounds.SmoothData (copies i) lowerRadius h nativeWidth
  frequencies : ∀ i k L, |((copies i).carrier k L).angular| ≤ frequencyBound ∧
    |((copies i).carrier k L).axial| ≤ frequencyBound ∧
    |((copies i).carrier k L).radial| ≤ frequencyBound

variable {h D I K J}

noncomputable def WaveData.scalar (W : WaveData h D I K J) (i : J) : SpaceTime → ℂ :=
  (W.copies i).sum W.lowerRadius h W.nativeWidth

theorem WaveData.scalar_smooth (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1 / 2) (i : J) :
    ContDiffOn ℝ ∞ (W.scalar i) PhysicalWaveSum.preterminal :=
  (W.support i).sum_smooth (W.smooth i) (W.cells i) W.lower_pos hh hh1

/-- The physical exponent and loss are obtained from the native weighted
source and actual chart map, not from a physical-bound hypothesis. -/
theorem WaveData.scalar_bound (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1 / 2) (i : J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (W.scalar i) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m) := by
  obtain ⟨C, hC, hb⟩ := LocalPhysicalCopyBounds.physical_sum_jet_bound_of_weighted
    W.source_bounds (W.chart i) (W.chart_maps i) (W.carrier i) (W.support i) (W.smooth i)
    hh hh1 W.lower_pos W.slow_nonneg W.width_nonneg W.frequency_one_le (W.frequencies i) m
  exact ⟨C, hC, fun w hw hq => hb w hw (abs_time_le_one hh hh1 hw hq)⟩

noncomputable def WaveData.vector (W : WaveData h D I K (Fin 3)) : VelocityField :=
  PhysicalCopyBounds.vectorSum W.copies W.lowerRadius h W.nativeWidth

theorem WaveData.vector_smooth (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ W.vector PhysicalWaveSum.preterminal :=
  LocalPhysicalCopyBounds.vectorSum_smooth W.support W.smooth W.cells W.lower_pos hh hh1

theorem WaveData.vector_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m) := by
  obtain ⟨C, hC, hb⟩ := LocalPhysicalCopyBounds.physical_vector_sum_jet_bound_of_weighted
    W.source_bounds W.cells W.chart W.chart_maps W.carrier W.support W.smooth
    hh hh1 W.lower_pos W.slow_nonneg W.width_nonneg W.frequency_one_le W.frequencies m
  exact ⟨C, hC, fun w hw hq => hb w hw (abs_time_le_one hh hh1 hw hq)⟩

noncomputable def WaveData.pressure (W : WaveData h D I K Unit) : PressureField :=
  fun w => (W.scalar () w).re

theorem WaveData.pressure_smooth (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ W.pressure PhysicalWaveSum.preterminal :=
  Complex.reCLM.contDiff.comp_contDiffOn (W.scalar_smooth hh hh1 ())

theorem WaveData.pressure_bound (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m) := by
  obtain ⟨C, hC, hb⟩ := W.scalar_bound hh hh1 () m
  refine ⟨‖Complex.reCLM‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro w hw hq
  have hs := ((W.scalar_smooth hh hh1 ()).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hw)).of_le (natCast_le_infty m)
  have hc := PhysicalWaveSum.norm_jet_linear_comp_at hs Complex.reCLM
  exact hc.trans ((mul_le_mul_of_nonneg_left (hb w hw hq) (norm_nonneg _)).trans_eq (by ring))

end Waves

/-- Actual coherent mean fields with native local-band classes. The
construction keeps a single physical field represented by all valid bands. -/
structure MeanData (h degree : ℝ) where
  firstBand : ℕ
  gapBound : ℕ
  region : Set PhysicalGraphBounds.Plane
  lowerRadius : ℝ
  upperRadius : ℝ
  alpha : ℝ
  slow : ℕ → ℝ
  family : PhysicalMeanJetBounds.CoherentFamily h degree firstBand gapBound region ℝ
  band_four : 4 ≤ firstBand
  lower_pos : 0 < lowerRadius
  radii_lt : lowerRadius < upperRadius
  region_open : IsOpen region
  region_covers : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ region
  smooth : ∀ n ≥ firstBand, ContDiffOn ℝ ∞ (family.native n) (PhysicalMeanDomain.slowDomain region)
  support : PhysicalMeanJetBounds.NativeSupport h lowerRadius upperRadius firstBand region family.native
  slow_nonneg : ∀ n ≥ firstBand, 0 ≤ slow n
  slow_growth : ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n ≥ firstBand, slow n ≤ C * ChartScales.S n ^ p
  native_class : PhysicalMeanDomain.LocalBandJets region (ChartScales.epsilon h) slow alpha family.native






section GainComparison

private theorem norm_bound_mono_loss {E : Type*} [NormedAddCommGroup E] {v : E}
    {C q g l₁ l₂ : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hl : l₁ ≤ l₂) (hv : ‖v‖ ≤ C * q ^ (g - l₁)) :
    ‖v‖ ≤ C * q ^ (g - l₂) :=
  hv.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 (sub_le_sub_left hl g)) hC)

variable {h g delta : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

theorem WaveData.vector_bound_with_gain (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hg : g ≤ h * W.alpha + W.shift + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (g - (PhysicalGraphBounds.waveLoss h m + delta)) := by
  obtain ⟨C, hC, hb⟩ := W.vector_bound hh hh1 m
  refine ⟨C, hC, fun w hw hq => (hb w hw hq).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq
  unfold PhysicalClassBounds.physicalLoss
  linarith

theorem WaveData.pressure_bound_with_gain (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hg : g ≤ h * W.alpha + W.shift + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (g - (PhysicalGraphBounds.waveLoss h m + delta)) := by
  obtain ⟨C, hC, hb⟩ := W.pressure_bound hh hh1 m
  refine ⟨C, hC, fun w hw hq => (hb w hw hq).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq
  unfold PhysicalClassBounds.physicalLoss
  linarith



end GainComparison

section Assembly

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}



/-- These losses depend only on fixed physical parameters and jet order.
The five offsets are fixed once for the whole stage sequence. -/
noncomputable def potentialLoss (h waveOffset meanOffset : ℝ) (m : ℕ) : ℝ :=
  max (PhysicalGraphBounds.waveLoss h m + waveOffset)
    (PhysicalMeanJetBounds.loss (CoordinateAlgebra.A h - 1 / 2) m + meanOffset)

noncomputable def directLoss (h meanOffset : ℝ) (m : ℕ) : ℝ :=
  PhysicalMeanJetBounds.loss (CoordinateAlgebra.A h) m + meanOffset

noncomputable def pressureLoss (h waveOffset meanOffset : ℝ) (m : ℕ) : ℝ :=
  max (PhysicalGraphBounds.waveLoss h m + waveOffset)
    (PhysicalMeanJetBounds.loss (2 * CoordinateAlgebra.A h) m + meanOffset)

private theorem norm_add_jet_le {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (natCast_le_infty m)) (hg.of_le (natCast_le_infty m))]
  exact norm_add_le _ _





end Assembly

section InitializedStages

variable {X V : Type*} [Add V]

/-- The zeroth increment is the base plus finite initialization. Positive
indices keep the supplied correction increments exactly. -/
noncomputable def addBaseAtZero (base : X → V) (increments : ℕ → X → V) (j : ℕ) (x : X) : V :=
  if j = 0 then base x + increments 0 x else increments j x


theorem addBaseAtZero_pos (base : X → V) (increments : ℕ → X → V) {j : ℕ} (hj : 1 ≤ j) :
    addBaseAtZero base increments j = increments j := by
  funext x
  simp only [addBaseAtZero, ite_eq_right (by omega : j ≠ 0)]

end InitializedStages

section Sequences

variable {h qbig : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}









private theorem exists_raw_constants {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℕ → SpaceTime → V} {g L : ℕ → ℝ}
    (hb : ∀ j, 1 ≤ j → ∀ m, ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ CutStageEstimates.physicalSublevel h qbig, PhysicalWaveSum.physicalQ h w ≤ 1 →
        ‖iteratedFDeriv ℝ m (F j) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (g j - L m)) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F g L C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  have he : ∀ j m, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j →
      ∀ w ∈ CutStageEstimates.physicalSublevel h qbig, PhysicalWaveSum.physicalQ h w ≤ 1 →
        ‖iteratedFDeriv ℝ m (F j) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (g j - L m)) := by
    intro j m
    by_cases hj : 1 ≤ j
    · obtain ⟨C, hC, hc⟩ := hb j hj m
      exact ⟨C, hC, fun _ => hc⟩
    · exact ⟨0, le_rfl, fun hj' => False.elim (hj hj')⟩
  choose C hC hb using he
  refine ⟨C, hC, fun j hj m w hw hq => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hb j m hj w hw.2 hq




end Sequences

section JointInputs

variable {h qbig : ℝ}
  {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}


end JointInputs

section RepresentationTransfer

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]




end RepresentationTransfer

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {d : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness d)



end ActualBase

end NavierStokes.PhysicalStageBounds
