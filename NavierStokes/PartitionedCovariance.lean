import NavierStokes.SquaredPartition
import NavierStokes.TorusAverages
import NavierStokes.PhaseCalculus
import NavierStokes.ParametricODE
import NavierStokes.PhaseEstimates

/-!
# Leading covariance of actual partitioned, separated slot fields

The fields are periodized native pulse components times actual angular cosines.
The off-diagonal label products vanish by the constructed rational slots, not
by an independence assumption about their angular frequencies.
-/

noncomputable section

namespace NavierStokes.PartitionedCovariance

open Set Function Filter MeasureTheory Matrix
open scoped BigOperators Topology ContDiff

abbrev Plane := TorusInverse.Plane
abbrev Vec2 := SmoothCovariance.Vec2
abbrev Mat2 := SmoothCovariance.Mat2

noncomputable def cutoff (r : ℝ) : ℝ → ℝ := SquaredPartition.gridMask r 0

theorem cutoff_continuous (r : ℝ) : Continuous (cutoff r) :=
  (SquaredPartition.gridMask_smooth r 0).continuous

theorem cutoff_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoff r) :=
  SquaredPartition.gridMask_compactSupport r hr 0

theorem cutoff_support {r : ℝ} (hr : 0 < r) : support (cutoff r) = Ioo (-r) r := by
  simpa [cutoff] using SquaredPartition.gridMask_support r hr (0 : ℤ)

theorem cutoff_sq_integral_pos {r : ℝ} (hr : 0 < r) : 0 < ∫ ξ : ℝ, cutoff r ξ ^ 2 := by
  have hc : HasCompactSupport (fun ξ => cutoff r ξ ^ 2) := by
    apply (cutoff_compact hr).mono
    intro ξ hξ hz
    exact hξ (by simp [hz])
  have hi : Integrable (fun ξ => cutoff r ξ ^ 2) :=
    ((cutoff_continuous r).pow 2).integrable_of_hasCompactSupport hc
  apply (integral_pos_iff_support_of_nonneg (fun ξ => sq_nonneg (cutoff r ξ)) hi).mpr
  have hs : support (fun ξ => cutoff r ξ ^ 2) = Ioo (-r) r := by
    ext ξ
    rw [← cutoff_support hr]
    simp only [mem_support, ne_eq, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]
  rw [hs]
  exact isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr (by linarith))

noncomputable def nativePrefactor (vr vt : Plane) (r : ℝ) : ℝ :=
  (|vr.1 * vt.2 - vr.2 * vt.1| / 2) * ∫ ξ : ℝ, cutoff r ξ ^ 2

theorem nativePrefactor_pos {vr vt : Plane} {r : ℝ}
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (hr : 0 < r) :
    0 < nativePrefactor vr vt r :=
  mul_pos (div_pos (abs_pos.mpr hdet) (by norm_num)) (cutoff_sq_integral_pos hr)

/-- The actual scalar radial and two tangent pulse components. All analytic
hypotheses concern these functions, not their covariance integrals. -/
structure Pulse where
  ψ : ℝ → ℝ
  x : ℝ → ℝ
  t : ℝ → Vec2
  ψ_continuous : Continuous ψ
  x_continuous : Continuous x
  t_continuous : Continuous t
  ψ_compact : HasCompactSupport ψ

noncomputable def Pulse.column (P : Pulse) (ci : ℝ) : Vec2 :=
  PulseCovariance.actualColumn ci P.ψ P.x P.t

noncomputable def Pulse.radialProfile (P : Pulse) (r : ℝ) (z : Plane) : ℝ :=
  cutoff r z.1 * P.ψ z.2 * P.x z.2

noncomputable def Pulse.tangentProfile (P : Pulse) (r : ℝ) (i : Fin 2) (z : Plane) : ℝ :=
  cutoff r z.1 * P.ψ z.2 * P.t z.2 i

noncomputable def nativePulse (vr vt center : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (ci r : ℝ) (f : Plane → ℝ) : Plane → ℝ :=
  TorusAverages.nativeField (TorusAverages.slotChart vr vt hdet) center
    (TorusAverages.transverseStretch ci r f)

noncomputable def covered (n : ℕ) (f : Plane → ℝ) (Y : Plane) : ℝ :=
  TorusAverages.periodize f (TorusAverages.covering^[n] Y)

noncomputable def wave (amplitude : ℝ) (n : ℕ) (f : Plane → ℝ) (mode : ℤ)
    (phase : Plane → ℝ) (Y : Plane) (θ : ℝ) : ℝ :=
  amplitude * covered n f Y * Real.cos ((mode : ℝ) * θ + phase Y)

noncomputable def doubleAverage (f : Plane → ℝ → ℝ) : ℝ :=
  TorusAverages.squareAverage (fun Y => SmoothLoop.angularMean (f Y))

theorem doubleAverage_const_mul (a : ℝ) (f : Plane → ℝ → ℝ) :
    doubleAverage (fun Y θ => a * f Y θ) = a * doubleAverage f := by
  simp only [doubleAverage, SmoothLoop.angularMean_const_mul]
  exact TorusAverages.squareAverage_const_mul a _

theorem nativePulse_mul (vr vt center : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (ci r : ℝ) (f g : Plane → ℝ) :
    (fun Y => nativePulse vr vt center hdet ci r f Y * nativePulse vr vt center hdet ci r g Y) =
      nativePulse vr vt center hdet ci r (fun z => f z * g z) := rfl

theorem Pulse.profile_product (P : Pulse) (r : ℝ) (i : Fin 2) :
    (fun z => P.radialProfile r z * P.tangentProfile r i z) =
      TorusAverages.pulseProfile (cutoff r) P.ψ P.x P.t i := by
  funext z
  unfold Pulse.radialProfile Pulse.tangentProfile TorusAverages.pulseProfile
  ring

/-- This evaluates the covariance of the two actual periodized velocity
components. Slot injectivity removes all cross-copy terms before averaging. -/
theorem Pulse.wave_covariance (P : Pulse) (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r : ℝ) (hci : 0 < ci) (hr : 0 < r)
    (S : Set Plane) (hS : InjOn TorusAverages.quotientPoint S)
    (hR : support (nativePulse vr vt center hdet ci r (P.radialProfile r)) ⊆ S)
    (hT : ∀ i, support (nativePulse vr vt center hdet ci r (P.tangentProfile r i)) ⊆ S)
    (a : ℝ) (n : ℕ) (phase : Plane → ℝ) (mode : ℤ) (hmode : mode ≠ 0) (i : Fin 2) :
    doubleAverage (fun Y θ =>
      wave a n (nativePulse vr vt center hdet ci r (P.radialProfile r)) mode phase Y θ *
      wave a n (nativePulse vr vt center hdet ci r (P.tangentProfile r i)) mode phase Y θ) =
      a ^ 2 * nativePrefactor vr vt r * P.column ci i := by
  have hp (Y : Plane) :
      covered n (nativePulse vr vt center hdet ci r (P.radialProfile r)) Y *
        covered n (nativePulse vr vt center hdet ci r (P.tangentProfile r i)) Y =
      covered n (nativePulse vr vt center hdet ci r
        (TorusAverages.pulseProfile (cutoff r) P.ψ P.x P.t i)) Y := by
    unfold covered
    rw [TorusAverages.periodize_mul_of_injective_support hS hR (hT i), nativePulse_mul,
      P.profile_product]
  have heq : (fun Y θ =>
      wave a n (nativePulse vr vt center hdet ci r (P.radialProfile r)) mode phase Y θ *
      wave a n (nativePulse vr vt center hdet ci r (P.tangentProfile r i)) mode phase Y θ) =
      fun Y θ => a ^ 2 * (covered n (nativePulse vr vt center hdet ci r
        (TorusAverages.pulseProfile (cutoff r) P.ψ P.x P.t i)) Y *
          Real.cos ((mode : ℝ) * θ + phase Y) ^ 2) := by
    funext Y θ
    unfold wave
    rw [show (a * covered n (nativePulse vr vt center hdet ci r (P.radialProfile r)) Y *
        Real.cos ((mode : ℝ) * θ + phase Y)) *
      (a * covered n (nativePulse vr vt center hdet ci r (P.tangentProfile r i)) Y *
        Real.cos ((mode : ℝ) * θ + phase Y)) = a ^ 2 *
      (covered n (nativePulse vr vt center hdet ci r (P.radialProfile r)) Y *
        covered n (nativePulse vr vt center hdet ci r (P.tangentProfile r i)) Y *
          Real.cos ((mode : ℝ) * θ + phase Y) ^ 2) by ring]
    rw [hp]
  rw [heq, doubleAverage_const_mul]
  have havg := TorusAverages.primary_covariance_average vr vt center hdet ci r hci
    (cutoff_continuous r) P.ψ_continuous P.x_continuous P.t_continuous
    (cutoff_compact hr) P.ψ_compact i n phase mode hmode
  change a ^ 2 * doubleAverage _ = _
  change doubleAverage _ = nativePrefactor vr vt r * P.column ci i at havg
  calc
    _ = a ^ 2 * (nativePrefactor vr vt r * P.column ci i) :=
      congrArg (fun z : ℝ => a ^ 2 * z) havg
    _ = _ := by ring


/-! ## The actual rational slot system and vanishing cross-label products -/

theorem cover_power_eq_iterate (n : ℕ) (Y : Plane) :
    (SlotGeometry.cover ^ n) Y = TorusAverages.covering^[n] Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', _root_.mul_apply_eq_comp, ih, Function.iterate_succ_apply']
      simp only [SlotGeometry.cover_apply, TorusAverages.covering]

theorem torusEq_lattice_add (k : TorusInverse.Frequency) (z : Plane) :
    SlotGeometry.torusEq z (TorusAverages.latticePoint k + z) := by
  refine ⟨⟨-k.1, ?_⟩, ⟨-k.2, ?_⟩⟩ <;>
    simp [TorusAverages.latticePoint]

theorem quotient_eq_torusEq {x y : Plane}
    (h : TorusAverages.quotientPoint x = TorusAverages.quotientPoint y) :
    SlotGeometry.torusEq x y := by
  have h1 : ((x.1 - y.1 : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrArg Prod.fst h)
  have h2 : ((x.2 - y.2 : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrArg Prod.snd h)
  obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
  obtain ⟨b, hb⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · simpa only [zsmul_eq_mul, mul_one, Prod.fst_sub] using ha
  · simpa only [zsmul_eq_mul, mul_one, Prod.snd_sub] using hb

theorem covered_support {f : Plane → ℝ} {S : Set Plane} (hf : support f ⊆ S) (n : ℕ) :
    support (covered n f) ⊆ SlotGeometry.liftedSupport n S := by
  intro Y hY
  have hsome : ∃ k : TorusInverse.Frequency,
      f (TorusAverages.latticePoint k + TorusAverages.covering^[n] Y) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hY (by simp [covered, TorusAverages.periodize, hnone])
  obtain ⟨k, hk⟩ := hsome
  refine ⟨TorusAverages.latticePoint k + TorusAverages.covering^[n] Y, hf hk, ?_⟩
  rw [cover_power_eq_iterate]
  exact torusEq_lattice_add k _

noncomputable def slotCenter (h : ℝ) (L : SlotColoring.Label) : Plane :=
  SlotGeometry.center (Fintype.card SlotColoring.Palette) (SlotColoring.nativeGap h)
    (SlotColoring.color L)

noncomputable def slotSet (h r : ℝ) (vr vt : Plane) (L : SlotColoring.Label) : Set Plane :=
  SlotGeometry.orientedRectangle (slotCenter h L) vr vt (2 * r)

/-- All separation and quotient-injectivity fields below are constructed by
`exists_slotSystem` from the explicit rational centers. -/
structure SlotSystem (D h : ℝ) (vr vt : Plane) where
  radius : ℝ
  radius_pos : 0 < radius
  injective : ∀ L, InjOn TorusAverages.quotientPoint (slotSet h radius vr vt L)
  disjoint : ∀ L M, SlotColoring.Adj D L M →
    Disjoint
      (SlotGeometry.liftedSupport (SlotColoring.nativeIndex h L.1) (slotSet h radius vr vt L))
      (SlotGeometry.liftedSupport (SlotColoring.nativeIndex h M.1) (slotSet h radius vr vt M))

theorem exists_slotSystem (D h : ℝ) (hh : 0 ≤ h) (vr vt : Plane) :
    Nonempty (SlotSystem D h vr vt) := by
  obtain ⟨r, hr, hsep, hinj⟩ := SlotGeometry.exists_oriented_slots
    (Fintype.card SlotColoring.Palette) (SlotColoring.nativeGap h) vr vt
  refine ⟨⟨r, hr, ?_, ?_⟩⟩
  · intro L x hx y hy hxy
    exact hinj 0 (Nat.zero_le _) (SlotColoring.color L) x hx y hy
      (by simpa using quotient_eq_torusEq hxy)
  · intro L M hLM
    have hc := SlotColoring.color_proper D hLM
    have hd := SlotColoring.nativeIndex_gap h hh hLM.left_positive hLM.right_positive
      hLM.left_level_le hLM.right_level_le
    rcases le_total (SlotColoring.nativeIndex h L.1) (SlotColoring.nativeIndex h M.1) with hle | hle
    · have he := hsep (SlotColoring.nativeIndex h L.1)
        (SlotColoring.nativeIndex h M.1 - SlotColoring.nativeIndex h L.1)
        (by omega) (SlotColoring.color L) (SlotColoring.color M) (Or.inr hc)
      have hsum : SlotColoring.nativeIndex h L.1 +
          (SlotColoring.nativeIndex h M.1 - SlotColoring.nativeIndex h L.1) =
          SlotColoring.nativeIndex h M.1 := by omega
      simpa only [hsum, slotSet, slotCenter] using he
    · have he := hsep (SlotColoring.nativeIndex h M.1)
        (SlotColoring.nativeIndex h L.1 - SlotColoring.nativeIndex h M.1)
        (by omega) (SlotColoring.color M) (SlotColoring.color L) (Or.inr hc.symm)
      have hsum : SlotColoring.nativeIndex h M.1 +
          (SlotColoring.nativeIndex h L.1 - SlotColoring.nativeIndex h M.1) =
          SlotColoring.nativeIndex h L.1 := by omega
      simpa only [hsum, slotSet, slotCenter] using he.symm

/-- The native cutoffs fit inside the padded rectangles used by the slot
construction. Only support of the actual transverse cutoff is required. -/
theorem native_cutoff_support (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {ci r : ℝ} (hci : 0 < ci) (hr : 0 < r)
    {ψ f : ℝ → ℝ} (hψ : support ψ ⊆ Icc 0 (2 * r / ci)) :
    support (nativePulse vr vt center hdet ci r (fun z => cutoff r z.1 * ψ z.2 * f z.2)) ⊆
      SlotGeometry.orientedRectangle center vr vt (2 * r) := by
  intro z hz
  let w := (TorusAverages.slotChart vr vt hdet).symm (z - center)
  let v := (w.2 + r) / ci
  have hp : (cutoff r w.1 * ψ v) * f v ≠ 0 := hz
  have hχ := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1
  have hψv := hψ (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2
  have hξ : |w.1| ≤ 2 * r := by
    have hm : w.1 ∈ support (cutoff r) := hχ
    rw [cutoff_support hr] at hm
    rw [abs_le]
    constructor <;> linarith [hm.1, hm.2]
  have hη : |w.2| ≤ 2 * r := by
    have hl : 0 ≤ w.2 + r := by simpa only [zero_mul] using (le_div_iff₀ hci).mp hψv.1
    have hu : w.2 + r ≤ 2 * r := (div_le_div_iff_of_pos_right hci).mp hψv.2
    rw [abs_le]
    constructor <;> linarith
  refine ⟨w.1, w.2, hξ, hη, ?_⟩
  have hw := (TorusAverages.slotChart vr vt hdet).apply_symm_apply (z - center)
  change TorusAverages.slotChart vr vt hdet w = z - center at hw
  rw [TorusAverages.slotChart_apply] at hw
  calc
    z = center + (z - center) := by abel
    _ = center + w.1 • vr + w.2 • vt := by
      rw [← hw]
      abel

noncomputable def physicalMask (D : ℝ) (L : SlotColoring.Label) (q : ℝ) (x : SlotColoring.Position) : ℝ :=
  SquaredPartition.dyadicMask (L.1 : ℤ) q * SquaredPartition.physicalSlowMask D L.1 L.2.1 x

theorem masks_force_adjacency {D q : ℝ} {x : SlotColoring.Position} {L M : SlotColoring.Label}
    (hq : 0 < q) (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    (hmL : physicalMask D L q x ≠ 0) (hmM : physicalMask D M q x ≠ 0) :
    SlotColoring.Adj D L M := by
  obtain ⟨hdL, hsL⟩ := mul_ne_zero_iff.mp hmL
  obtain ⟨hdM, hsM⟩ := mul_ne_zero_iff.mp hmM
  have hl : SquaredPartition.logCoordinate q ∈ support (SquaredPartition.lineMask (L.1 : ℤ)) := by
    rwa [SquaredPartition.dyadicMask_eq_line _ hq] at hdL
  have hm : SquaredPartition.logCoordinate q ∈ support (SquaredPartition.lineMask (M.1 : ℤ)) := by
    rwa [SquaredPartition.dyadicMask_eq_line _ hq] at hdM
  rw [SquaredPartition.lineMask_support] at hl hm
  simp only [Int.cast_natCast] at hl hm
  have hLM : L.1 ≤ M.1 + 4 := by
    have he : (L.1 : ℝ) ≤ (M.1 : ℝ) + 4 := by
      linarith [hl.1, hm.2]
    exact_mod_cast he
  have hML : M.1 ≤ L.1 + 4 := by
    have he : (M.1 : ℝ) ≤ (L.1 : ℝ) + 4 := by
      linarith [hm.1, hl.2]
    exact_mod_cast he
  exact ⟨hL, hM, hne, hLM, hML, x,
    SquaredPartition.physicalSlowMask_tsupport_subset_physicalBox D hL L.2.1 L.2.2
      (subset_tsupport _ hsL),
    SquaredPartition.physicalSlowMask_tsupport_subset_physicalBox D hM M.2.1 M.2.2
      (subset_tsupport _ hsM)⟩

theorem SlotSystem.cross_product_zero {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    {L M : SlotColoring.Label} (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    {f g : Plane → ℝ} (hf : support f ⊆ slotSet h sys.radius vr vt L)
    (hg : support g ⊆ slotSet h sys.radius vr vt M) {q : ℝ} (hq : 0 < q)
    (x : SlotColoring.Position) (Y : Plane) :
    (physicalMask D L q x * covered (SlotColoring.nativeIndex h L.1) f Y) *
      (physicalMask D M q x * covered (SlotColoring.nativeIndex h M.1) g Y) = 0 := by
  by_cases hmL : physicalMask D L q x = 0
  · simp [hmL]
  by_cases hmM : physicalMask D M q x = 0
  · simp [hmM]
  have hdis := sys.disjoint L M (masks_force_adjacency hq hL hM hne hmL hmM)
  by_cases hfY : covered (SlotColoring.nativeIndex h L.1) f Y = 0
  · simp [hfY]
  have hgY : covered (SlotColoring.nativeIndex h M.1) g Y = 0 := by
    by_contra hneY
    exact Set.disjoint_left.mp hdis (covered_support hf _ hfY) (covered_support hg _ hneY)
  simp [hgY]

/-! ## Actual pulse columns and the positive inverse solve -/








noncomputable def pairMatrix (vr vt : Plane) (r : ℝ) (ci : Vec2) (P : Fin 2 → Pulse) : Mat2 :=
  fun i j => nativePrefactor vr vt r * (P j).column (ci j) i



noncomputable def amplitude (ε mask : ℝ) (H : Mat2) (T : Vec2) (j : Fin 2) : ℝ :=
  Real.sqrt ε * SmoothCovariance.amplitudes H T j * mask

theorem amplitude_sq (ε mask : ℝ) (hε : 0 ≤ ε) (H : Mat2) (T : Vec2) (j : Fin 2) :
    amplitude ε mask H T j ^ 2 = ε * mask ^ 2 * SmoothCovariance.amplitudes H T j ^ 2 := by
  unfold amplitude
  rw [mul_pow, mul_pow, Real.sq_sqrt hε]
  ring

theorem amplitudes_are_inverse_weights {H : Mat2} {T : Vec2}
    (h : SmoothCovariance.StrictCone H T) (j : Fin 2) :
    0 < (H⁻¹.mulVec T) j ∧ SmoothCovariance.amplitudes H T j = Real.sqrt ((H⁻¹.mulVec T) j) := by
  rw [SmoothCovariance.inverse_formula H T h.det_ne_zero]
  exact ⟨h.weights_pos j, rfl⟩

theorem weighted_columns_reconstruct (ε mask : ℝ) (hε : 0 ≤ ε) {H : Mat2} {T : Vec2}
    (hcone : SmoothCovariance.StrictCone H T) (i : Fin 2) :
    (∑ j : Fin 2, amplitude ε mask H T j ^ 2 * H i j) = ε * mask ^ 2 * T i := by
  have hrec := congrFun (SmoothCovariance.reconstruct_amplitudes hcone) i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hrec
  simp only [Fin.sum_univ_two, amplitude_sq ε mask hε]
  calc
    _ = ε * mask ^ 2 * (H i 0 * SmoothCovariance.amplitudes H T 0 ^ 2 +
        H i 1 * SmoothCovariance.amplitudes H T 1 ^ 2) := by ring
    _ = _ := by rw [hrec]

/-! ## Finite sums of the actual velocity components -/

theorem angularMean_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ a ∈ s, Continuous (f a)) :
    SmoothLoop.angularMean (fun θ => ∑ a ∈ s, f a θ) =
      ∑ a ∈ s, SmoothLoop.angularMean (f a) := by
  unfold SmoothLoop.angularMean
  rw [intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _)]
  exact Finset.sum_div _ _ _

theorem squareAverage_sum {ι : Type*} (s : Finset ι) (f : ι → Plane → ℝ)
    (hf : ∀ a ∈ s, Continuous (f a)) :
    TorusAverages.squareAverage (fun Y => ∑ a ∈ s, f a Y) =
      ∑ a ∈ s, TorusAverages.squareAverage (f a) := by
  have hsum := continuous_finsetSum s hf
  rw [TorusAverages.squareAverage_eq_setIntegral hsum]
  have hi (a) (ha : a ∈ s) : IntegrableOn (f a) TorusAverages.fundamentalSquare := by
    exact ((hf a ha).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  rw [MeasureTheory.integral_finsetSum s hi]
  apply Finset.sum_congr rfl
  intro a ha
  exact (TorusAverages.squareAverage_eq_setIntegral (hf a ha)).symm

theorem doubleAverage_sum {ι : Type*} (s : Finset ι) (f : ι → Plane → ℝ → ℝ)
    (hθ : ∀ a ∈ s, ∀ Y, Continuous (f a Y))
    (hY : ∀ a ∈ s, Continuous (fun Y => SmoothLoop.angularMean (f a Y))) :
    doubleAverage (fun Y θ => ∑ a ∈ s, f a Y θ) = ∑ a ∈ s, doubleAverage (f a) := by
  unfold doubleAverage
  simp_rw [angularMean_sum s _ (fun a ha => hθ a ha _)]
  exact squareAverage_sum s _ hY

theorem sum_product_diagonal {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hcross : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → f a * g b = 0) :
    (∑ a ∈ s, f a) * (∑ a ∈ s, g a) = ∑ a ∈ s, f a * g a := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · intro b hb hba
    exact hcross a ha b hb hba.symm
  · exact fun h => (h ha).elim

theorem Pulse.radialProfile_continuous (P : Pulse) (r : ℝ) : Continuous (P.radialProfile r) :=
  ((cutoff_continuous r).comp continuous_fst).mul
    (P.ψ_continuous.comp continuous_snd) |>.mul (P.x_continuous.comp continuous_snd)

theorem Pulse.tangentProfile_continuous (P : Pulse) (r : ℝ) (i : Fin 2) :
    Continuous (P.tangentProfile r i) :=
  (((cutoff_continuous r).comp continuous_fst).mul
    (P.ψ_continuous.comp continuous_snd)).mul
      (((continuous_apply i).comp P.t_continuous).comp continuous_snd)

theorem Pulse.radialProfile_compact (P : Pulse) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (P.radialProfile r) := by
  have h := TorusAverages.productProfile_hasCompactSupport (cutoff_compact hr)
    (P.ψ_compact.mul_right (f' := P.x))
  change HasCompactSupport (fun z : Plane => cutoff r z.1 * P.ψ z.2 * P.x z.2)
  simpa only [Pi.mul_apply, mul_assoc] using h

theorem Pulse.tangentProfile_compact (P : Pulse) {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    HasCompactSupport (P.tangentProfile r i) := by
  have h := TorusAverages.productProfile_hasCompactSupport (cutoff_compact hr)
    (P.ψ_compact.mul_right (f' := fun v => P.t v i))
  change HasCompactSupport (fun z : Plane => cutoff r z.1 * P.ψ z.2 * P.t z.2 i)
  simpa only [Pi.mul_apply, mul_assoc] using h

theorem nativePulse_continuous (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {ci r : ℝ} (hci : ci ≠ 0)
    {f : Plane → ℝ} (hf : Continuous f) : Continuous (nativePulse vr vt center hdet ci r f) :=
  TorusAverages.nativeField_continuous _ _ (TorusAverages.transverseStretch_continuous ci r hci hf)

theorem nativePulse_compact (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {ci r : ℝ} (hci : ci ≠ 0)
    {f : Plane → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (nativePulse vr vt center hdet ci r f) :=
  TorusAverages.nativeField_hasCompactSupport _ _ (TorusAverages.transverseStretch_hasCompactSupport ci r hci hf)

theorem covered_continuous {f : Plane → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (n : ℕ) :
    Continuous (covered n f) :=
  (TorusAverages.periodize_continuous hf hc).comp (TorusAverages.covering_continuous.iterate n)

theorem wave_continuous_theta (a : ℝ) (n : ℕ) (f : Plane → ℝ) (mode : ℤ)
    (phase : Plane → ℝ) (Y : Plane) : Continuous (wave a n f mode phase Y) :=
  continuous_const.mul (Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const))

theorem angularMean_wave_product (a : ℝ) (n : ℕ) (f g : Plane → ℝ) (mode : ℤ)
    (hmode : mode ≠ 0) (phase : Plane → ℝ) (Y : Plane) :
    SmoothLoop.angularMean (fun θ => wave a n f mode phase Y θ * wave a n g mode phase Y θ) =
      (a ^ 2 * covered n f Y * covered n g Y) * (1 / 2) := by
  have heq : (fun θ => wave a n f mode phase Y θ * wave a n g mode phase Y θ) =
      fun θ => (a ^ 2 * covered n f Y * covered n g Y) *
        Real.cos ((mode : ℝ) * θ + phase Y) ^ 2 := by
    funext θ
    unfold wave
    ring
  rw [heq, SmoothLoop.angularMean_const_mul, TorusAverages.angularMean_cos_sq_harmonic mode hmode]

theorem angularMean_wave_product_continuous (a : ℝ) (n : ℕ) {f g : Plane → ℝ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (hg : Continuous g) (hcg : HasCompactSupport g)
    (mode : ℤ) (hmode : mode ≠ 0) (phase : Plane → ℝ) :
    Continuous (fun Y => SmoothLoop.angularMean
      (fun θ => wave a n f mode phase Y θ * wave a n g mode phase Y θ)) := by
  simp_rw [angularMean_wave_product a n f g mode hmode phase]
  exact ((continuous_const.mul (covered_continuous hf hcf n)).mul
    (covered_continuous hg hcg n)).mul continuous_const

theorem SlotSystem.wave_cross_zero {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt)
    {L M : SlotColoring.Label} (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    {f g : Plane → ℝ} (hf : support f ⊆ slotSet h sys.radius vr vt L)
    (hg : support g ⊆ slotSet h sys.radius vr vt M) {q : ℝ} (hq : 0 < q)
    (x : SlotColoring.Position) (Y : Plane) (θ a b : ℝ) (modeL modeM : ℤ)
    (phaseL phaseM : Plane → ℝ) :
    wave (a * physicalMask D L q x) (SlotColoring.nativeIndex h L.1) f modeL phaseL Y θ *
      wave (b * physicalMask D M q x) (SlotColoring.nativeIndex h M.1) g modeM phaseM Y θ = 0 := by
  have hz := sys.cross_product_zero hL hM hne hf hg hq x Y
  unfold wave
  calc
    _ = (a * b * Real.cos ((modeL : ℝ) * θ + phaseL Y) *
          Real.cos ((modeM : ℝ) * θ + phaseM Y)) *
        ((physicalMask D L q x * covered (SlotColoring.nativeIndex h L.1) f Y) *
          (physicalMask D M q x * covered (SlotColoring.nativeIndex h M.1) g Y)) := by ring
    _ = 0 := by rw [hz, mul_zero]

abbrev UnsignedLabel := ℕ × SlotColoring.Grid

noncomputable def signedLabel (U : UnsignedLabel) (j : Fin 2) : SlotColoring.Label :=
  (U.1, U.2, if j = 0 then false else true)

theorem signedLabel_injective (U : UnsignedLabel) : Function.Injective (signedLabel U) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [signedLabel]

noncomputable def mask (D : ℝ) (U : UnsignedLabel) (q : ℝ) (x : SlotColoring.Position) : ℝ :=
  physicalMask D (signedLabel U 0) q x


structure PairData {D h : ℝ} {vr vt : Plane} (sys : SlotSystem D h vr vt) (U : UnsignedLabel) where
  pulses : Fin 2 → Pulse
  ci : Vec2
  ci_pos : ∀ j, 0 < ci j
  fits : ∀ j, support (pulses j).ψ ⊆ Icc 0 (2 * sys.radius / ci j)
  modes : Fin 2 → ℤ
  modes_ne : ∀ j, modes j ≠ 0
  phases : Fin 2 → Plane → ℝ

noncomputable def PairData.matrix {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {U : UnsignedLabel}
    (P : PairData sys U) : Mat2 := pairMatrix vr vt sys.radius P.ci P.pulses

noncomputable def PairData.rawRadial {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {U : UnsignedLabel}
    (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) : Plane → ℝ :=
  nativePulse vr vt (slotCenter h (signedLabel U j)) hdet (P.ci j) sys.radius
    ((P.pulses j).radialProfile sys.radius)

noncomputable def PairData.rawTangent {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {U : UnsignedLabel}
    (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j i : Fin 2) : Plane → ℝ :=
  nativePulse vr vt (slotCenter h (signedLabel U j)) hdet (P.ci j) sys.radius
    ((P.pulses j).tangentProfile sys.radius i)

theorem PairData.rawRadial_support {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    support (P.rawRadial hdet j) ⊆ slotSet h sys.radius vr vt (signedLabel U j) :=
  native_cutoff_support vr vt _ hdet (P.ci_pos j) sys.radius_pos (P.fits j)

theorem PairData.rawTangent_support {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j i : Fin 2) :
    support (P.rawTangent hdet j i) ⊆ slotSet h sys.radius vr vt (signedLabel U j) :=
  native_cutoff_support vr vt (slotCenter h (signedLabel U j)) hdet
    (ψ := (P.pulses j).ψ) (f := fun v => (P.pulses j).t v i)
    (P.ci_pos j) sys.radius_pos (P.fits j)

theorem PairData.rawRadial_continuous {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    Continuous (P.rawRadial hdet j) :=
  nativePulse_continuous vr vt _ hdet (P.ci_pos j).ne' ((P.pulses j).radialProfile_continuous _)

theorem PairData.rawTangent_continuous {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j i : Fin 2) :
    Continuous (P.rawTangent hdet j i) :=
  nativePulse_continuous vr vt _ hdet (P.ci_pos j).ne' ((P.pulses j).tangentProfile_continuous _ i)

theorem PairData.rawRadial_compact {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j : Fin 2) :
    HasCompactSupport (P.rawRadial hdet j) :=
  nativePulse_compact vr vt _ hdet (P.ci_pos j).ne' ((P.pulses j).radialProfile_compact sys.radius_pos)

theorem PairData.rawTangent_compact {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (j i : Fin 2) :
    HasCompactSupport (P.rawTangent hdet j i) :=
  nativePulse_compact vr vt _ hdet (P.ci_pos j).ne' ((P.pulses j).tangentProfile_compact sys.radius_pos i)


noncomputable def PairData.radialWave {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {U : UnsignedLabel}
    (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) : Plane → ℝ → ℝ :=
  wave (outer * amplitude ε (mask D U q x) P.matrix T j)
    (SlotColoring.nativeIndex h U.1) (P.rawRadial hdet j) (P.modes j) (P.phases j)

noncomputable def PairData.tangentWave {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {U : UnsignedLabel}
    (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) : Plane → ℝ → ℝ :=
  wave (outer * amplitude ε (mask D U q x) P.matrix T j)
    (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j)

theorem PairData.diagonal_covariance {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (T : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) :
    doubleAverage (fun Y θ => P.radialWave hdet outer ε T q x j Y θ *
      P.tangentWave hdet outer ε T q x j i Y θ) =
      (outer * amplitude ε (mask D U q x) P.matrix T j) ^ 2 * P.matrix i j := by
  have h := (P.pulses j).wave_covariance vr vt (slotCenter h (signedLabel U j)) hdet
    (P.ci j) sys.radius (P.ci_pos j) sys.radius_pos
    (slotSet h sys.radius vr vt (signedLabel U j)) (sys.injective _)
    (P.rawRadial_support hdet j) (fun i => P.rawTangent_support hdet j i)
    (outer * amplitude ε (mask D U q x) P.matrix T j)
    (SlotColoring.nativeIndex h U.1) (P.phases j) (P.modes j) (P.modes_ne j) i
  simpa only [PairData.radialWave, PairData.tangentWave, PairData.rawRadial, PairData.rawTangent,
    PairData.matrix, pairMatrix, mul_assoc] using h

theorem PairData.diagonal_pair_reconstruct {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (hε : 0 ≤ ε) {T : Vec2} (hcone : SmoothCovariance.StrictCone P.matrix T)
    (q : ℝ) (x : SlotColoring.Position) (i : Fin 2) :
    (∑ j : Fin 2, doubleAverage (fun Y θ => P.radialWave hdet outer ε T q x j Y θ *
      P.tangentWave hdet outer ε T q x j i Y θ)) =
      outer ^ 2 * ε * mask D U q x ^ 2 * T i := by
  simp_rw [P.diagonal_covariance, mul_pow]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, weighted_columns_reconstruct ε (mask D U q x) hε hcone i]
  ring

/-! ## The actual physical partition and the physical covariance scale -/

theorem mask_locallyFinite (D : ℝ) :
    LocallyFinite fun U : UnsignedLabel =>
      support (fun z : Ioi (0 : ℝ) × SlotColoring.Position => mask D U z.1 z.2) := by
  have hn : LocallyFinite fun n : ℕ =>
      support (fun q : Ioi (0 : ℝ) => SquaredPartition.dyadicMask (n : ℤ) q) :=
    SquaredPartition.dyadicMask_locallyFinite.comp_injective Int.ofNat_injective
  have ho := hn.preimage_continuous
    (continuous_fst : Continuous (Prod.fst : Ioi (0 : ℝ) × SlotColoring.Position → Ioi (0 : ℝ)))
  have hi (n : ℕ) : LocallyFinite fun k : SlotColoring.Grid =>
      (Prod.snd : Ioi (0 : ℝ) × SlotColoring.Position → SlotColoring.Position) ⁻¹'
        support (SquaredPartition.physicalSlowMask D n k) :=
    (SquaredPartition.physicalSlowMask_locallyFinite D n).preimage_continuous continuous_snd
  have hh := SquaredPartition.locallyFinite_pair_inter ho hi
  convert! hh using 1
  funext U
  ext z
  simp only [mem_support, mask, physicalMask, signedLabel, mul_ne_zero_iff, mem_inter_iff, mem_preimage]

noncomputable def tailLabel (N : ℕ) (U : UnsignedLabel) : UnsignedLabel := (U.1 + N, U.2)

theorem tailLabel_injective (N : ℕ) : Function.Injective (tailLabel N) := by
  intro U V h
  apply Prod.ext
  · exact Nat.add_right_cancel (congrArg Prod.fst h)
  · simpa only [tailLabel] using congrArg (fun z : UnsignedLabel => z.2) h

theorem finite_active_masks (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) :
    (support (fun U : UnsignedLabel => mask D (tailLabel N U) q x)).Finite :=
  ((mask_locallyFinite D).point_finite (⟨q, hq⟩, x)).preimage (tailLabel_injective N).injOn

theorem physical_mask_tail_sum_sq (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q)
    (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) :
    (∑ᶠ U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2) = 1 := by
  have hf : (support (fun U : UnsignedLabel => mask D (tailLabel N U) q x ^ 2)).Finite := by
    apply (finite_active_masks D N hq x).subset
    intro U hU hz
    exact hU (by simp [hz])
  rw [SquaredPartition.finsum_pair_eq hf]
  have hrow (n : ℕ) :
      (∑ᶠ k : SlotColoring.Grid, mask D (tailLabel N (n, k)) q x ^ 2) =
        SquaredPartition.dyadicMask ((n + N : ℕ) : ℤ) q ^ 2 := by
    have hk : (support (fun k : SlotColoring.Grid =>
        SquaredPartition.physicalSlowMask D (n + N) k x ^ 2)).Finite := by
      apply ((SquaredPartition.physicalSlowMask_locallyFinite D (n + N)).point_finite x).subset
      intro k hk hz
      exact hk (by simp [hz])
    simp only [mask, physicalMask, signedLabel, tailLabel, mul_pow]
    rw [← mul_finsum _ _, SquaredPartition.physicalSlowMask_sum_sq, mul_one]
  simp_rw [hrow]
  exact SquaredPartition.dyadicMask_tail_sum_sq N hq hqN

noncomputable def velocityExponent (h : ℝ) : ℝ := 1 / 2 + h



noncomputable def constructedSlotSystem (D h : ℝ) (hh : 0 ≤ h) (vr vt : Plane) : SlotSystem D h vr vt :=
  Classical.choice (exists_slotSystem D h hh vr vt)




noncomputable def assembledRadial {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (Y : Plane) (θ : ℝ) : ℝ :=
  ∑ᶠ a : UnsignedLabel × Fin 2, (P a.1).radialWave hdet (outer a.1) (ε a.1) (T a.1) q x a.2 Y θ

noncomputable def assembledTangent {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (i : Fin 2) (Y : Plane) (θ : ℝ) : ℝ :=
  ∑ᶠ a : UnsignedLabel × Fin 2, (P a.1).tangentWave hdet (outer a.1) (ε a.1) (T a.1) q x a.2 i Y θ


noncomputable def physicalOuter (h : ℝ) (N : ℕ) (U : UnsignedLabel) : ℝ :=
  ChartScales.Q (U.1 + N) ^ (-velocityExponent h)

noncomputable def physicalViscosity (h : ℝ) (N : ℕ) (U : UnsignedLabel) : ℝ :=
  ChartScales.epsilon h (U.1 + N)

noncomputable def chartTarget (h q : ℝ) (N : ℕ) (T0 : Vec2) (U : UnsignedLabel) : Vec2 :=
  (ChartScales.Q (U.1 + N) / q) ^ (velocityExponent h + 1 / 2) • T0


/-! ## Instantiation by the actual pulse and rounding interfaces -/






theorem actual_carrier_ne_zero (h : ℝ) (n : ℕ) : (ChartScales.carrier h n : ℝ) ≠ 0 :=
  (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h n)).ne'


end NavierStokes.PartitionedCovariance
