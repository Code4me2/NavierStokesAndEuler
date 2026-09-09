import NavierStokes.PhysicalCopyBounds
import NavierStokes.SimilarityApproach
import NavierStokes.TailGaugePotential

/-!
# Terminal extensions from a common shrinking outer support

The actual similarity coordinate tends jointly to zero at a terminal point
whose axial coordinate is zero.  A family supported inside a common multiple
of its square root therefore vanishes on one common open past neighborhood
of every nonzero such point.  This argument applies before summing or taking
the spatial curl, and requires neither a lower support radius nor estimates
on the individual summands.
-/

noncomputable section

namespace NavierStokes.AnnularEndpoint

open Set Filter Function
open scoped Topology ContDiff BigOperators

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

/-- The actual Cartesian distance to the symmetry axis. -/
noncomputable def radius (w : SpaceTime) : ℝ :=
  PolarCharts.radius (PhysicalGraphBounds.radialProjection w)

theorem radius_continuous : Continuous radius :=
  PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous

theorem radius_nonneg (w : SpaceTime) : 0 ≤ radius w :=
  PolarCharts.radius_nonneg _

theorem radius_pos_at_terminal {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    0 < radius (1, x) := by
  have hs := SlowBaseEndpoint.radialEnergy_pos_of_nonzero_of_axial_zero hx hz
  apply Real.sqrt_pos.mpr
  change 0 < x 0 ^ 2 + x 1 ^ 2
  dsimp only [AxisymmetricFields.radialEnergy] at hs
  linarith

/-- The support radius uses the same physical similarity coordinate as the
wave construction, rather than a separately postulated scale. -/
noncomputable def outerRadius (h C : ℝ) (w : SpaceTime) : ℝ :=
  C * Real.sqrt (PhysicalWaveSum.physicalQ h w)

theorem physicalQ_tendsto_zero {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : Space} (hz : x 2 = 0) :
    Tendsto (PhysicalWaveSum.physicalQ h) (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0) := by
  apply SimilarityApproach.physical_q_tendsto_zero hh hh1
  · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · change Tendsto (fun w : SpaceTime => w.2 2)
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0)
    have hc : Tendsto (fun w : SpaceTime => w.2 2) (𝓝 (1, x)) (𝓝 (x 2)) :=
      ((AxisymmetricFields.projection 2).continuous.comp continuous_snd).tendsto (1, x)
    rw [hz] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact hw.1

theorem outerRadius_tendsto_zero {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) {x : Space} (hz : x 2 = 0) :
    Tendsto (outerRadius h C) (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 0) := by
  have he := tendsto_const_nhds (x := C) |>.mul (Real.continuous_sqrt.continuousAt.tendsto.comp
      (physicalQ_tendsto_zero hh hh1 hz))
  simp only [Real.sqrt_zero, mul_zero] at he ⊢
  exact he


/-- One geometric neighborhood works for every member of any family with
the same outer support constant.  No sign or size assumption on `C` is needed. -/
theorem exists_separating_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      ∀ w ∈ U, w.1 < 1 → outerRadius h C w < radius w := by
  have hr := radius_pos_at_terminal hx hz
  have hout := (outerRadius_tendsto_zero hh hh1 C hz).eventually
    (gt_mem_nhds (half_pos hr))
  have hin := (radius_continuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := SpacetimeEndpoint.openPast 1))).eventually
      (lt_mem_nhds (half_lt_self hr))
  have he : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] (1, x),
      outerRadius h C w < radius w := by
    filter_upwards [hout, hin] with w ho hi
    exact ho.trans hi
  obtain ⟨U, hU, hxU, hsep⟩ := mem_nhdsWithin.mp he
  exact ⟨U, hU, hxU, fun w hw ht => hsep ⟨hw, ht, mem_univ _⟩⟩

section Support

variable {V : Type*} [Zero V]

/-- A pointwise physical support invariant.  It contains no endpoint or
derivative assertion. -/
def ShrinkingSupport (h C : ℝ) (f : SpaceTime → V) : Prop :=
  ∀ w, w.1 < 1 → f w ≠ 0 → radius w ≤ outerRadius h C w

theorem ShrinkingSupport.zero_of_separated {h C : ℝ} {f : SpaceTime → V}
    (hf : ShrinkingSupport h C f) {w : SpaceTime} (ht : w.1 < 1)
    (hs : outerRadius h C w < radius w) : f w = 0 := by
  by_contra hn
  exact (not_lt_of_ge (hf w ht hn)) hs

/-- Zero-preserving pointwise reconstructions, including real parts and
vector-valued coefficient maps, preserve the physical support invariant. -/
theorem ShrinkingSupport.map_zero {W : Type*} [Zero W] {h C : ℝ}
    {f : SpaceTime → V} (hf : ShrinkingSupport h C f)
    (T : SpaceTime → V → W) (hT : ∀ w, T w 0 = 0) :
    ShrinkingSupport h C (fun w => T w (f w)) := by
  intro w ht hn
  apply hf w ht
  intro hz
  exact hn (by simpa only [hz] using hT w)



end Support

section Sums

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]



omit [NormedSpace ℝ V] in
theorem ShrinkingSupport.finset_sum {ι : Type*} {h C : ℝ} {f : ι → SpaceTime → V}
    (s : Finset ι) (hf : ∀ i ∈ s, ShrinkingSupport h C (f i)) :
    ShrinkingSupport h C (fun w => ∑ i ∈ s, f i w) := by
  intro w ht hn
  by_contra hs
  apply hn
  apply Finset.sum_eq_zero
  intro i hi
  exact (hf i hi).zero_of_separated ht (lt_of_not_ge hs)




end Sums

section WaveSupport

/-- The normalized annulus and the actual dyadic-mask comparison imply a
uniform physical outer radius.  The product norm costs a factor of two. -/
theorem radius_le_of_scaled_annulus {a b q : ℝ} {n : ℕ} {w : SpaceTime}
    (hw : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b)
    (hQ : ChartScales.Q n ≤ 2 * q) :
    radius w ≤ (2 * b * Real.sqrt 2) * Real.sqrt q := by
  have hn : ‖PhysicalGraphBounds.scaledRadial n w‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1
  have hb : 0 ≤ b := (norm_nonneg _).trans hn
  have hr : PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) ≤ 2 * b :=
    (PolarCharts.radius_le_two_norm _).trans (mul_le_mul_of_nonneg_left hn (by norm_num))
  have he : radius w = Real.sqrt (ChartScales.Q n) *
      PolarCharts.radius (PhysicalGraphBounds.scaledRadial n w) := by
    unfold radius
    rw [← PhysicalGraphBounds.unscale_radial n w,
      PolarCharts.radius_smul (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _),
      ← Real.sqrt_eq_rpow]
  calc
    radius w ≤ Real.sqrt (ChartScales.Q n) * (2 * b) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 * q) * (2 * b) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hQ) (mul_nonneg (by norm_num) hb)
    _ = (2 * b * Real.sqrt 2) * Real.sqrt q := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem shrinkingSupport_of_normalized_annulus {V : Type*} [Zero V]
    {a b h : ℝ} {f : SpaceTime → V}
    (hf : ∀ w, w.1 < 1 → f w ≠ 0 → ∃ n : ℕ,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b ∧
      ChartScales.Q n ≤ 2 * PhysicalWaveSum.physicalQ h w) :
    ShrinkingSupport h (2 * b * Real.sqrt 2) f := by
  intro w ht hn
  obtain ⟨n, ha, hq⟩ := hf w ht hn
  exact radius_le_of_scaled_annulus ha hq






end WaveSupport

section Extensions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]





/-- The extension is the literal zero function on an actual ambient open
neighborhood, not only a limiting boundary value. -/
noncomputable def zeroExtension {f : SpaceTime → V} {x : Space} {U : Set SpaceTime}
    (hU : IsOpen U) (hxU : (1, x) ∈ U)
    (hf : EqOn f (fun _ => 0) (U ∩ SpacetimeEndpoint.openPast 1)) :
    JointResidualLimits.OneSidedExtension f x where
  value := fun _ => 0
  domain := U
  isOpen := hU
  mem := hxU
  smooth := contDiffOn_const
  agrees := hf.symm







end Extensions

section Curl



end Curl

section Diagonal





end Diagonal


section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)



end FinalBase

end NavierStokes.AnnularEndpoint
