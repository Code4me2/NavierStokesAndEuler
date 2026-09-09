import NavierStokes.PhysicalClassBounds
import NavierStokes.PeriodizedWaveBounds
import NavierStokes.WithTopLemmas

/-!
# Physical bounds for locally finite native copies

Each native copy retains its own center and its own full oscillatory carrier.
We sum these waves, not their amplitudes under one unwrapped phase.  Closed,
locally finite, disjoint native cells give an actual single-copy germ.  The
physical estimate is then the center-independent single-carrier estimate,
followed by the existing bounded overlap estimate for the outer labels.
-/

noncomputable section

namespace NavierStokes.PhysicalCopyBounds

open Set Function Filter ProblemStatement PhysicalWaveSum
open scoped Topology ContDiff BigOperators

section Germs

variable {X Y E I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E]

/-- Pull back the native cells only near the evaluation point.  Global
continuity of the physical graph at the axis is not needed. -/
theorem copySum_pullback_germ (K : PeriodizedWaveBounds.Cells Y I) (n : ℕ)
    (φ : X → Y) (f : I → X → E)
    (hs : ∀ i x, f i x ≠ 0 → φ x ∈ K.carrier n i)
    {x : X} (hφ : ContinuousAt φ x) {i : I} (hi : φ x ∈ K.carrier n i) :
    (fun y => ∑' k, f k y) =ᶠ[𝓝 x] f i := by
  classical
  have hn := hφ ((K.locallyFinite n).iInter_compl_mem_nhds (K.closed n) (φ x))
  filter_upwards [hn] with y hy
  apply tsum_eq_single i
  intro j hji
  have hxj : φ x ∉ K.carrier n j := fun hxj => hji (K.unique n j i (φ x) hxj hi)
  by_contra hne
  exact (mem_iInter₂.mp hy j hxj) (hs j y hne)

theorem copySum_pullback_zero_germ (K : PeriodizedWaveBounds.Cells Y I) (n : ℕ)
    (φ : X → Y) (f : I → X → E)
    (hs : ∀ i x, f i x ≠ 0 → φ x ∈ K.carrier n i)
    {x : X} (hφ : ContinuousAt φ x) (hi : ∀ i, φ x ∉ K.carrier n i) :
    (fun y => ∑' k, f k y) =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  have hn := hφ ((K.locallyFinite n).iInter_compl_mem_nhds (K.closed n) (φ x))
  filter_upwards [hn] with y hy
  suffices hz : ∀ i, f i y = 0 by simp only [hz, tsum_zero]
  intro i
  by_contra hne
  exact (mem_iInter₂.mp hy i (hi i)) (hs i y hne)

theorem copySum_pullback_germ_cover (K : PeriodizedWaveBounds.Cells Y I) (n : ℕ)
    (φ : X → Y) (f : I → X → E)
    (hs : ∀ i x, f i x ≠ 0 → φ x ∈ K.carrier n i)
    {x : X} (hφ : ContinuousAt φ x) :
    (∃ i, φ x ∈ K.carrier n i ∧ (fun y => ∑' k, f k y) =ᶠ[𝓝 x] f i) ∨
      (fun y => ∑' k, f k y) =ᶠ[𝓝 x] fun _ => 0 := by
  classical
  by_cases hx : ∃ i, φ x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := hx
    exact Or.inl ⟨i, hi, copySum_pullback_germ K n φ f hs hφ hi⟩
  · exact Or.inr (copySum_pullback_zero_germ K n φ f hs hφ (not_exists.mp hx))

end Germs

/-- The lattice copy is a separate index.  In particular, neither the center
nor the phase profiles have to agree between different copies. -/
structure CopyFamily (H : ℕ) (K : Type*) where
  gap : BandLabel → ℕ
  carrier : K → BandLabel → CarrierData
  amplitude : K → WaveIndex H → LiftPoint → ℂ

noncomputable def CopyFamily.copy {H : ℕ} {K : Type*} (f : CopyFamily H K) (k : K) :
    WaveFamily H := ⟨f.gap, f.carrier k, f.amplitude k⟩

noncomputable def CopyFamily.term {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a h r0 : ℝ) (I : WaveIndex H) (k : K) : SpaceTime → ℂ :=
  (f.copy k).term a h r0 I

/-- Sum full local carriers, including their individual phases. -/
noncomputable def CopyFamily.periodized {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a h r0 : ℝ) (I : WaveIndex H) (w : SpaceTime) : ℂ :=
  ∑' k, f.term a h r0 I k w

noncomputable def CopyFamily.sum {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a h r0 : ℝ) (w : SpaceTime) : ℂ :=
  ∑ᶠ I, f.periodized a h r0 I w

/-- The old single-copy regularity hypotheses are imposed separately on
each actual copy.  No support condition is imposed using one center for the
whole periodized amplitude. -/
structure RegularFamily {H : ℕ} {K : Type*} (f : CopyFamily H K)
    (a b h r0 Z : ℝ) (Δ : ℕ) : Prop where
  copy : ∀ k, PhysicalWaveSum.RegularFamily (f.copy k) a b h r0 Z Δ

/-- Native support cells can depend on the outer label.  Their index is
independent of both the harmonic and the physical point. -/
structure SupportCells {H : ℕ} {K : Type*} (f : CopyFamily H K) where
  cells : BandLabel → PeriodizedWaveBounds.Cells LiftPoint K
  support : ∀ I k, support (f.amplitude k I) ⊆ (cells I.1).carrier I.1.val.1 k

variable {H Δ : ℕ} {K : Type*} {f : CopyFamily H K} {a b h r0 Z : ℝ}


theorem SupportCells.term_mem (hc : SupportCells f) (I : WaveIndex H) (k : K)
    (w : SpaceTime) (hw : f.term a h r0 I k w ≠ 0) :
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k :=
  hc.support I k (globalWave_ne_zero_amp hw)


theorem commonLift_continuousAt_of_annulus (ha : 0 < a) (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b) :
    ContinuousAt (commonLift h n d) w := by
  apply (commonLift_smoothAt h n d ?_).continuousAt
  exact PhysicalGraphBounds.scaledRadial_ne_zero
    (PhysicalGraphBounds.annulus_axisFree ha hw)









/-- Closed-cell membership holds at every point where a copy can have a
nonzero jet, including the boundary of its amplitude support. -/
theorem SupportCells.term_tsupport_mem (hc : SupportCells f)
    (ha : 0 < a) (I : WaveIndex H) (k : K) {w : SpaceTime}
    (hann : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b)
    (hw : w ∈ tsupport (f.term a h r0 I k)) :
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k :=
  closed_property_on_tsupport isOpen_univ (mem_univ w)
    (commonLift_continuousAt_of_annulus ha _ _ hann) ((hc.cells I.1).closed _ k)
    (fun y _ hy => hc.term_mem I k y hy) hw

/-- Only native jets on a copy's own closed cell are used.  No bounds for
uncut data far from that copy are required. -/
structure LocalStrippedClass (f : CopyFamily H K) (hc : SupportCells f)
    (a b h r0 P A B g eAmp eBase : ℝ) (m : ℕ) : Prop where
  parameters : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
    |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P
  amplitude : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.amplitude k I) (commonLift h I.1.val.1 (f.gap I.1) w)‖ ≤
      A * ChartScales.Q I.1.val.1 ^ g * ChartScales.S I.1.val.1 ^ eAmp
  base_F : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier k I.1).F
      (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
        (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w)).1‖ ≤ B * ChartScales.S I.1.val.1 ^ eBase
  base_G : ∀ k (I : WaveIndex H) (w : SpaceTime), w ∈ preterminal →
    physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) w ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart →
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f.carrier k I.1).G
      (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
        (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
        (PhysicalGraphBounds.physicalLift h I.1.val.1 w)).1‖ ≤ B * ChartScales.S I.1.val.1 ^ eBase


section WeightedInputs

open WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type*}

/-- Actual cutoff amplitudes, pulled from their weighted native coefficient
through the common-coordinate map.  Only the map's positive jets are bounded;
its values and the copy centers may be unbounded. -/
structure CommonChart (f : CopyFamily H K) (hc : SupportCells f)
    (a b h σ : ℝ) (source : ι → ℕ → D → ℂ) where
  sourceIndex : K → WaveIndex H → ι
  map : K → WaveIndex H → LiftPoint → D
  domain : K → WaveIndex H → Set LiftPoint
  open_domain : ∀ k I, IsOpen (domain k I)
  smooth : ∀ k I, ContDiffOn ℝ ∞ (map k I) (domain k I)
  positive_jets : ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
    ∀ k I x, x ∈ domain k I → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (map k I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q
  amplitude_eq : ∀ k I, f.amplitude k I = fun x =>
    (ChartScales.Q I.1.val.1 ^ σ) • source (sourceIndex k I) I.1.val.1 (map k I x)
  contains : ∀ k I z, z ∈ preterminal →
    physicalParams h z ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ (hc.cells I.1).carrier I.1.val.1 k →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ domain k I


noncomputable def copyBandDomain {V : Type*} [NormedAddCommGroup V]
    (U : K → BandLabel → Set V) (hU : ∀ k L, IsOpen (U k L)) :
    PhaseJetBounds.Domain (K × BandLabel) V where
  scale i := ChartScales.S i.2.val.1
  carrier i := U i.1 i.2
  isOpen i := hU i.1 i.2
  one_le_scale i := PhysicalGraphBounds.S_ge_one (by have := i.2.property; omega)

/-- The carrier profiles are estimated on their actual local slow regions.
The regions need contain a point only when that point belongs to this copy. -/
structure CarrierBounds (f : CopyFamily H K) (hc : SupportCells f) (a b h r0 : ℝ) where
  region : K → BandLabel → Set PhysicalGraphBounds.Slow
  open_region : ∀ k L, IsOpen (region k L)
  jets : PhaseJetBounds.PolynomialJets (copyBandDomain region open_region)
    (fun i x => ((f.carrier i.1 i.2).F x, (f.carrier i.1 i.2).G x))
  contains : ∀ k (I : WaveIndex H) z, z ∈ preterminal →
    physicalParams h z ∈ labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    commonLift h I.1.val.1 (f.gap I.1) z ∈ (hc.cells I.1).carrier I.1.val.1 k →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PolarCharts.chartDomain a chart →
    (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h I.1.val.1) (f.carrier k I.1).center r0
      (PhysicalGraphBounds.physicalLift h I.1.val.1 z)).1 ∈ region k I.1

theorem CarrierBounds.profile_bound {hc : SupportCells f}
    (hb : CarrierBounds f hc a b h r0) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ p : ℕ, ∀ k L x, x ∈ hb.region k L → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f.carrier k L).F x‖ ≤ B * ChartScales.S L.val.1 ^ p ∧
      ‖iteratedFDeriv ℝ j (f.carrier k L).G x‖ ≤ B * ChartScales.S L.val.1 ^ p := by
  obtain ⟨B, hB, p, hp⟩ := hb.jets.bound m
  refine ⟨B, hB, p, ?_⟩
  intro k L x hx j hj
  have hpair := (hb.jets.smooth (k, L)).contDiffAt ((hb.open_region k L).mem_nhds hx)
  have he := hp (k, L) j hj x hx
  rw [PhysicalGraphBounds.iteratedFDeriv_pair
    (hpair.fst.of_le (natCast_le_infty j)) (hpair.snd.of_le (natCast_le_infty j)),
    ContinuousMultilinearMap.opNorm_prod] at he
  exact ⟨(le_max_left _ _).trans he, (le_max_right _ _).trans he⟩



end WeightedInputs

/-! ## Literal native cells and their lattice centers -/

section NativeCells

open CommonCoverSolve

noncomputable def nativeCenter (g : Geometry) (k : TorusInverse.Frequency) : Plane :=
  g.center + TorusAverages.latticePoint k

/-- The center used by a copy is its own lattice translate. -/
theorem native_offset (g : Geometry) (k : TorusInverse.Frequency) (Y : Plane) :
    coverPower g.gap Y - nativeCenter g k = g.basis (g.coordinates k Y) := by
  rw [Geometry.coordinates, ContinuousLinearEquiv.apply_symm_apply]
  unfold nativeCenter
  abel

theorem nativeGraph_eq_cover_commonLift (h : ℝ) (n d : ℕ) (w : SpaceTime) :
    PhysicalGraphBounds.nativeGraph h n w = coverPower d (commonLift h n d w).2 := by
  change PhysicalGraphBounds.nativeGraph h n w =
    coverPower d ((coverPower d).symm (PhysicalGraphBounds.nativeGraph h n w))
  rw [ContinuousLinearEquiv.apply_symm_apply]



variable {F : CopyFamily H TorusInverse.Frequency}

/-- Build the abstract support cells from the actual native affine lattice
charts.  Compactness gives local finiteness; quotient injectivity gives
disjointness, both through `PeriodizedWaveBounds.nativeCells`. -/
noncomputable def nativeSupportCells (g : BandLabel → Geometry) (U : BandLabel → Set Plane)
    (hU : ∀ L, IsCompact (U L))
    (hinj : ∀ L, InjOn TorusAverages.quotientPoint
      ((fun z => (g L).center + (g L).basis z) '' U L))
    (hs : ∀ k I x, F.amplitude k I x ≠ 0 → (g I.1).coordinates k x.2 ∈ U I.1) :
    SupportCells F where
  cells L := PeriodizedWaveBounds.nativeCells (P := PhysicalGraphBounds.ChartPoint)
    (fun _ => g L) (fun _ => U L) (fun _ => hU L) (fun _ => hinj L)
  support I k x hx := hs k I x hx




end NativeCells

/-! ## Exact support and vector-valued consequences -/

theorem CopyFamily.sum_nonzero_term (f : CopyFamily H K) {a h r0 : ℝ} {w : SpaceTime}
    (hw : f.sum a h r0 w ≠ 0) : ∃ I k, f.term a h r0 I k w ≠ 0 := by
  classical
  by_contra! hn
  have hp : ∀ I, f.periodized a h r0 I w = 0 := by
    intro I
    simp only [CopyFamily.periodized, hn, tsum_zero]
  exact hw (by simp only [CopyFamily.sum, hp, finsum_zero])


noncomputable def vectorSum (f : Fin 3 → CopyFamily H K) (a h r0 : ℝ)
    (w : SpaceTime) : Space := ∑ i : Fin 3, realCoordinate i ((f i).sum a h r0 w)




section WeightedVector

open WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι : Type*}


end WeightedVector

end NavierStokes.PhysicalCopyBounds
