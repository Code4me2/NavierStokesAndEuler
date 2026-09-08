import NavierStokes.PhysicalStageBounds
import NavierStokes.MixedCandidateAssembly
import NavierStokes.ActualInitialization

/-!
# A common shrinking support for actual physical increments

Native outer radii, bounded by one fixed patch radius, give one physical
outer-support constant for every stage. Coherent means are represented in
a comparable native band; no physical support property is an input.
The zeroth support assertion concerns the finite initialization increment.
-/

noncomputable section

universe u

namespace NavierStokes.PhysicalStageSupport

open Set Function Filter ProblemStatement PhysicalStageBounds
open MixedDiagonalExtensions
open scoped Topology ContDiff BigOperators

section SupportAlgebra

variable {V : Type*} [NormedAddCommGroup V]

theorem support_mono {h C D qbig : ℝ} {f : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f) (hCD : C ≤ D) :
    SublevelShrinkingSupport h D qbig f := by
  intro w ht hq hn
  exact (hf w ht hq hn).trans (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _))


theorem support_map_zero {E : Type*} [NormedAddCommGroup E]
    {h C qbig : ℝ} {f : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f)
    (T : SpaceTime → V → E) (hT : ∀ w, T w 0 = 0) :
    SublevelShrinkingSupport h C qbig (fun w => T w (f w)) := by
  intro w ht hq hn
  apply hf w ht hq
  intro hz
  exact hn (by simpa only [hz] using hT w)

theorem support_add {h C qbig : ℝ} {f g : SpaceTime → V}
    (hf : SublevelShrinkingSupport h C qbig f)
    (hg : SublevelShrinkingSupport h C qbig g) :
    SublevelShrinkingSupport h C qbig (fun w => f w + g w) := by
  intro w ht hq hn
  by_cases hz : f w = 0
  · apply hg w ht hq
    intro hgz
    exact hn (by simp only [hz, hgz, add_zero])
  · exact hf w ht hq hz


end SupportAlgebra

/-- This constant is shared by the entire stage sequence. -/
noncomputable def outerConstant (R : ℝ) : ℝ := 4 * R * Real.sqrt 2


section Waves

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K J : Type*}

theorem wave_scalar_support (W : WaveData h D I K J) (i : J) {qbig R : ℝ}
    (hR : W.upperRadius ≤ 2 * R) :
    SublevelShrinkingSupport h (outerConstant R) qbig (W.scalar i) := by
  apply support_mono
    (SublevelShrinkingSupport.of_global (localCopy_sum_support (W.support i)))
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem wave_vector_support (W : WaveData h D I K (Fin 3)) {qbig R : ℝ}
    (hR : W.upperRadius ≤ 2 * R) :
    SublevelShrinkingSupport h (outerConstant R) qbig W.vector := by
  apply support_mono
    (SublevelShrinkingSupport.of_global (localCopy_vector_support W.support))
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem wave_pressure_support (W : WaveData h D I K Unit) {qbig R : ℝ}
    (hR : W.upperRadius ≤ 2 * R) :
    SublevelShrinkingSupport h (outerConstant R) qbig W.pressure :=
  support_map_zero (wave_scalar_support W () hR) (fun _ z => z.re) (fun _ => rfl)

end Waves

section Means

variable {h degree : ℝ}



end Means

section CoherentMeans

variable {h degree : ℝ} {N gap : ℕ} {U : Set PhysicalGraphBounds.Plane}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The selected comparable band lies in the actual open normalized
window `(1/2,2)`. No enlargement of the native mean domain is required. -/
theorem comparable_graph_mem (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (ht : w.1 < 1)
    (hlo : PhysicalWaveSum.physicalQ h w ≤ ChartScales.Q n)
    (hhi : ChartScales.Q n < 2 * PhysicalWaveSum.physicalQ h w) :
    (PhysicalMeanJetBounds.graph h n d w).2.1 ∈
      PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 := by
  refine ⟨PhysicalMeanJetBounds.graph_time_pos h n d ht, ?_⟩
  rw [PhysicalMeanJetBounds.graph_q_eq hh hh1 n d ht]
  have hQ := ChartScales.Q_pos n
  constructor
  · apply (lt_div_iff₀ hQ).mpr
    linarith
  · apply (div_lt_iff₀ hQ).mpr
    linarith

theorem coherent_field_support (D : PhysicalMeanJetBounds.CoherentFamily h degree N gap U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b qbig R : ℝ}
    (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    (hq : qbig ≤ ChartScales.Q N) (hR : b ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig D.field := by
  intro w ht hqw hn
  have hqpos := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  obtain ⟨n, hnN, hqn, hnq⟩ := PhysicalMeanJetBounds.exists_comparable_band
    N hqpos (hqw.le.trans hq)
  have hlo : PhysicalWaveSum.physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
  have hu := hcover (comparable_graph_mem hh hh1 n (D.gap n) ht hqn hnq)
  have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hnN ht hu hlo hnq.le
    (subset_tsupport _ hn)
  have hb := AnnularEndpoint.radius_le_of_scaled_annulus hann hnq.le
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  dsimp only [outerConstant]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem coherent_angular_support (D : PhysicalMeanJetBounds.CoherentFamily h degree N gap U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) {a b qbig R : ℝ}
    (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hs : PhysicalMeanJetBounds.NativeSupport h a b N U D.native)
    (hq : qbig ≤ ChartScales.Q N) (hR : b ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig D.angularField :=
  support_map_zero (coherent_field_support D hh hh1 ha hab hU hcover hs hq hR)
    (fun w c => c • PhysicalMeanJetBounds.angularVector (PhysicalGraphBounds.radialProjection w))
    (fun _ => zero_smul _ _)

end CoherentMeans

section Increments

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}



end Increments

section Families

variable {h : ℝ}
  {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- Numeric bounds on the native radial endpoints. The same `R` occurs
at every stage, including stage zero. -/
structure NativeOuterBounds (R : ℝ)
    (WA : ℕ → WaveData h DA IA KA (Fin 3))
    (MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (MB : ℕ → MeanData h (CoordinateAlgebra.A h))
    (WP : ℕ → WaveData h DP IP KP Unit)
    (MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h)) : Prop where
  potentialWave : ∀ j, (WA j).upperRadius ≤ 2 * R
  potentialMean : ∀ j, (MA j).upperRadius ≤ R
  directMean : ∀ j, (MB j).upperRadius ≤ R
  pressureWave : ∀ j, (WP j).upperRadius ≤ 2 * R
  pressureMean : ∀ j, (MP j).upperRadius ≤ R

variable
  (WA : ℕ → WaveData h DA IA KA (Fin 3))
  (MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
  (MB : ℕ → MeanData h (CoordinateAlgebra.A h))
  (WP : ℕ → WaveData h DP IP KP Unit)
  (MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h))

theorem NativeOuterBounds.radius_pos {R : ℝ}
    (H : NativeOuterBounds R WA MA MB WP MP) : 0 < R :=
  ((MA 0).lower_pos.trans (MA 0).radii_lt).trans_le (H.potentialMean 0)




end Families

section InitializedSequences

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}





end InitializedSequences

section FixedPatch

noncomputable def geometryOuterConstant (G : SignedMeanGain.Geometry) : ℝ :=
  outerConstant G.patch.b


/-- The concrete common constant for the manuscript's fixed actual patch. -/
noncomputable def actualOuterConstant : ℝ := geometryOuterConstant ActualInitialization.geometry


theorem actualOuterConstant_eq :
    actualOuterConstant = 4 * PrimaryTargetBounds.rightRadius
      CorrectionInitialization.ActualPrimary.nominal * Real.sqrt 2 := rfl

/-- A literal coherent family on the fixed actual mean domain has the
same outer constant as the wave increments. -/
theorem actual_coherent_support {degree : ℝ} {N gap : ℕ}
    (D : PhysicalMeanJetBounds.CoherentFamily CorrectionInitialization.ActualPrimary.h degree N gap
      CorrectionInitialization.ActualPrimary.standardRegion.carrier ℝ)
    (hs : PhysicalMeanJetBounds.NativeSupport CorrectionInitialization.ActualPrimary.h
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b N
      CorrectionInitialization.ActualPrimary.standardRegion.carrier D.native)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) :
    SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig D.field ∧
    SublevelShrinkingSupport CorrectionInitialization.ActualPrimary.h actualOuterConstant qbig D.angularField := by
  have hcover : PhysicalMeanDomain.normalizedSlowDomain
      (2 * CorrectionInitialization.ActualPrimary.h) (1 / 2) 2 ⊆
      CorrectionInitialization.ActualPrimary.standardRegion.carrier := fun _ hx => hx
  exact ⟨coherent_field_support D
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
      CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      ActualInitialization.geometry.patch.a_pos ActualInitialization.geometry.patch.a_lt_b
      CorrectionInitialization.ActualPrimary.standardRegion.isOpen hcover hs hq le_rfl,
    coherent_angular_support D
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
      CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      ActualInitialization.geometry.patch.a_pos ActualInitialization.geometry.patch.a_lt_b
      CorrectionInitialization.ActualPrimary.standardRegion.isOpen hcover hs hq le_rfl⟩

variable {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}





end FixedPatch

end NavierStokes.PhysicalStageSupport
