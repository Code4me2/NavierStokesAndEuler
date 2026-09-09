import NavierStokes.LabelSumBounds
import NavierStokes.WeightedRadialPrimitive
import NavierStokes.LocalSignedRequest
import NavierStokes.SpatialCurl
import NavierStokes.WithTopLemmas

/-!
# Uniform weighted coefficients and physical wave sums

The constants below are selected before the label and the band.  The first
step absorbs the actual two flat edges, including every inverse-edge power.
Global smoothness and support then extend the estimate across the boundary.
The final passage uses genuine common-coordinate compositions and the
physical carrier estimates of `PhysicalWaveSum`.
-/

noncomputable section

namespace NavierStokes.PhysicalClassBounds

open Set Function Filter WeightedClasses LabelSumBounds
open scoped Topology ContDiff BigOperators


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

/-- Explicit fixed flat-edge geometry, pulled back through any radial
coordinate.  This is an equality of the weights, not a bound on them. -/
structure FlatGeometry (s : StripData D) (cL cR L : ℝ) (ρ : D → ℝ) : Prop where
  left_pos : 0 < cL
  right_pos : 0 < cR
  position : ∀ x ∈ s.domain, ρ x ∈ Ioo 0 L
  delta_eq : ∀ x ∈ s.domain, s.delta x = WeightedRadialPrimitive.delta L (ρ x)
  zeta_eq : ∀ x ∈ s.domain, s.zeta x = WeightedRadialPrimitive.zeta cL cR L (ρ x)

theorem edge_rpow {x : ℝ} (hx : 0 < x) (a c : ℝ) :
    FlatCutoff.edge a x ^ c = FlatCutoff.edge (c * a) x := by
  rw [FlatCutoff.edge_of_pos a hx, FlatCutoff.edge_of_pos (c * a) hx,
    ← Real.exp_mul]
  congr 1
  ring

theorem zeta_rpow {L x : ℝ} (hx : x ∈ Ioo 0 L) (cL cR c : ℝ) :
    WeightedRadialPrimitive.zeta cL cR L x ^ c = WeightedRadialPrimitive.zeta (c * cL) (c * cR) L x := by
  rw [WeightedRadialPrimitive.zeta, Real.mul_rpow (FlatCutoff.edge_nonneg _ _)
    (FlatCutoff.edge_nonneg _ _), edge_rpow hx.1,
    edge_rpow (sub_pos.mpr hx.2), WeightedRadialPrimitive.zeta]

/-- Exponential flatness absorbs any fixed inverse-edge power, uniformly
at both endpoints and for every positive fractional power of the weight. -/
theorem flat_edge_uniform {cL cR c : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hc : 0 < c) (L : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioo (0 : ℝ) L,
      (max 1 (WeightedRadialPrimitive.delta L x)⁻¹) ^ m * WeightedRadialPrimitive.zeta cL cR L x ^ c ≤ K := by
  obtain ⟨K, hK, hb⟩ := WeightedRadialPrimitive.weight_uniform_bound (mul_pos hc hcL) (mul_pos hc hcR) L m
  refine ⟨K, hK, ?_⟩
  intro x hx
  have hd : 1 ≤ (WeightedRadialPrimitive.delta L x)⁻¹ :=
    (one_le_inv₀ (WeightedRadialPrimitive.delta_pos hx)).mpr (WeightedRadialPrimitive.delta_le_one L x)
  rw [max_eq_right hd, zeta_rpow hx]
  simpa only [WeightedRadialPrimitive.weight, div_eq_mul_inv, inv_pow, mul_comm] using hb x hx

theorem FlatGeometry.uniform {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ s.domain,
      (max 1 (s.delta x)⁻¹) ^ m * s.zeta x ^ c ≤ K := by
  obtain ⟨K, hK, hb⟩ := flat_edge_uniform hg.left_pos hg.right_pos hc L m
  refine ⟨K, hK, fun x hx => ?_⟩
  rw [hg.delta_eq x hx, hg.zeta_eq x hx]
  exact hb (ρ x) (hg.position x hx)


theorem movingStrip_flatGeometry {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) :
    FlatGeometry (LocalSignedRequest.movingStripData U a b cL cR ha hcL hcR ε S hε hεone hS)
      cL cR (WeightedRadialPrimitive.logLength a b)
      (fun x => WeightedRadialPrimitive.logPosition a (LocalSignedRequest.profileMap coord x).1) := by
  refine ⟨hcL, hcR, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  intro x hx
  exact WeightedRadialPrimitive.logPosition_mem ha
    ((LocalSignedRequest.movingStrip_domain U a b cL cR ha hcL hcR ε S hε hεone hS x).mp hx).2

/-- Remove the edge growth from an actual uniform coefficient class.  The
input envelope may depend on the label and band; its domination is uniform. -/
theorem UniformClass.edge_absorbed {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {c α : ℝ} (hc : 0 < c)
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformClass s w α f)
    (hw : ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ A * s.epsilon n ^ α * s.slow n ^ p := by
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  obtain ⟨K, hK, hKx⟩ := hg.uniform hc p
  refine ⟨C * K, mul_nonneg hC hK, p, ?_⟩
  intro l n x hx j hj
  have he : 0 ≤ s.epsilon n ^ α := (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le
  have hs : 0 ≤ s.slow n ^ p := pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _
  calc
    _ ≤ majorant s (w l) α C p n x := hb l n x hx j hj
    _ ≤ C * s.epsilon n ^ α * s.growth n x ^ p * s.zeta x ^ c :=
      mul_le_mul_of_nonneg_left (hw l n x hx)
        (mul_nonneg (mul_nonneg hC he) (pow_nonneg (s.growth_nonneg n x) _))
    _ = (C * s.epsilon n ^ α * s.slow n ^ p) *
        ((max 1 (s.delta x)⁻¹) ^ p * s.zeta x ^ c) := by
      rw [StripData.growth, mul_pow]
      ring
    _ ≤ (C * s.epsilon n ^ α * s.slow n ^ p) * K :=
      mul_le_mul_of_nonneg_left (hKx x hx) (mul_nonneg (mul_nonneg hC he) hs)
    _ = _ := by ring








/-- Primitive input for the physical bridge.  In particular, `uniform`
places its constants before the label, and `support` concerns the actual
coefficient, not a prescribed bound for its derivatives. -/
structure SourceBounds (s : StripData D) (h α : ℝ)
    (w : ι → ℕ → D → ℝ) (f : ι → ℕ → D → E) : Prop where
  uniform : UniformClass s w α f
  flat_geometry : ∃ cL cR L : ℝ, ∃ ρ : D → ℝ, FlatGeometry s cL cR L ρ
  weight_le : ∃ c : ℝ, 0 < c ∧ ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c
  epsilon_eq : ∀ n, s.epsilon n = ChartScales.epsilon h n
  slow_le : ∃ K : ℝ, 1 ≤ K ∧ ∃ q : ℕ,
    ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q
  smooth : ∀ l n, ContDiff ℝ ∞ (f l n)
  support : ∀ l n, tsupport (f l n) ⊆ closure s.domain





section CommonCoordinates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A local form of the genuine higher chain-rule estimate.  Only positive
derivatives of the coordinate map are needed; the map's values may be unbounded. -/
theorem composition_jet_bound {g : D → E} {φ : X → D} {U : Set X}
    (hg : ContDiff ℝ ∞ g) (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U)
    {x : X} (hx : x ∈ U) (m : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (φ x)‖ ≤ A)
    (hφb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i φ x‖ ≤ B) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (g ∘ φ) x‖ ≤ (m.factorial : ℝ) * A * B ^ m := by
  intro j hj
  have hb := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hφ (natCast_le_infty j)
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ φ U) hx
    (C := A) (D := B)
    (fun i hi => by rw [iteratedFDerivWithin_univ]; exact hgb i (hi.trans hj))
    (fun i hi hij => by
      rw [iteratedFDerivWithin_of_isOpen i hU hx]
      exact (hφb i hi (hij.trans hj)).trans (by simpa using pow_le_pow_right₀ hB hi))
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hb
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA)
    (pow_le_pow_right₀ hB hj) (by positivity) (by positivity))

/-- The common-chart identity for actual amplitudes.  This records only
the source formula and the coordinate map's jets, before any physical graph
or carrier has been differentiated. -/
structure CommonChart {H : ℕ} (F : PhysicalWaveSum.WaveFamily H)
    (a b h r0 σ : ℝ) (f : ι → ℕ → D → ℂ) where
  sourceIndex : PhysicalWaveSum.WaveIndex H → ι
  map : PhysicalWaveSum.WaveIndex H → PhysicalWaveSum.LiftPoint → D
  domain : PhysicalWaveSum.WaveIndex H → Set PhysicalWaveSum.LiftPoint
  open_domain : ∀ I, IsOpen (domain I)
  smooth : ∀ I, ContDiffOn ℝ ∞ (map I) (domain I)
  positive_jets : ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
    ∀ I x, x ∈ domain I → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (map I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q
  amplitude_eq : ∀ I, F.amplitude I = fun x =>
    (ChartScales.Q I.1.val.1 ^ σ) • f (sourceIndex I) I.1.val.1 (map I x)
  contains : ∀ I z, z ∈ PhysicalWaveSum.preterminal →
    PhysicalWaveSum.physicalParams h z ∈
      PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    PhysicalWaveSum.commonLift h I.1.val.1 (F.gap I.1) z ∈ domain I


end CommonCoordinates

/-- The natural slow scale for a band label is at least one because the
physical sum starts at band four. -/
noncomputable def bandDomain {V : Type} [NormedAddCommGroup V]
    (U : PhysicalWaveSum.BandLabel → Set V) (hU : ∀ L, IsOpen (U L)) :
    PhaseJetBounds.Domain PhysicalWaveSum.BandLabel V where
  scale L := ChartScales.S L.val.1
  carrier := U
  isOpen := hU
  one_le_scale L := PhysicalGraphBounds.S_ge_one (by have := L.property; omega)

/-- Polynomial jets of the actual two base profiles entering the phase,
on open slow-coordinate regions containing every relevant chart point. -/
structure CarrierBounds {H : ℕ} (F : PhysicalWaveSum.WaveFamily H) (a b h r0 : ℝ) where
  region : PhysicalWaveSum.BandLabel → Set PhysicalGraphBounds.Slow
  open_region : ∀ L, IsOpen (region L)
  jets : PhaseJetBounds.PolynomialJets (bandDomain region open_region)
    (fun L x => ((F.carrier L).F x, (F.carrier L).G x))
  contains : ∀ (I : PhysicalWaveSum.WaveIndex H) z,
    z ∈ PhysicalWaveSum.preterminal →
    PhysicalWaveSum.physicalParams h z ∈
      PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PolarCharts.chartDomain a chart →
    (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h I.1.val.1) (F.carrier I.1).center r0
      (PhysicalGraphBounds.physicalLift h I.1.val.1 z)).1 ∈ region I.1



/-- The derivative loss includes the displayed physical field rescaling.
It depends on the derivative order and fixed scaling parameters only. -/
noncomputable def physicalLoss (h σ : ℝ) (m : ℕ) : ℝ :=
  PhysicalGraphBounds.waveLoss h m - σ




/-- Inclusion of a spatial direction into a joint spacetime direction. -/
noncomputable def spatialInclusion : ProblemStatement.Space →L[ℝ] ProblemStatement.SpaceTime :=
  (0 : ProblemStatement.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ProblemStatement.Space)

/-- A fixed continuous linear map takes the spatial curl from a joint
Jacobian.  Its norm is independent of every band and correction stage. -/
noncomputable def jointCurl : (ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.Space) →L[ℝ]
    ProblemStatement.Space :=
  SpatialCurl.curlLinear.comp
    ((ContinuousLinearMap.compL ℝ ProblemStatement.Space ProblemStatement.SpaceTime
      ProblemStatement.Space).flip spatialInclusion)

theorem spatialCurl_eq_joint {A : ProblemStatement.VelocityField} {z : ProblemStatement.SpaceTime}
    (hA : DifferentiableAt ℝ A z) :
    SpatialCurl.spatialCurl A z = jointCurl (fderiv ℝ A z) := by
  have hi : HasFDerivAt (fun y : ProblemStatement.Space => (z.1, y)) spatialInclusion z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hd := (hA.hasFDerivAt.comp z.2 hi).fderiv
  change SpatialCurl.curlLinear (fderiv ℝ (fun y => A (z.1, y)) z.2) =
    SpatialCurl.curlLinear ((fderiv ℝ A z).comp spatialInclusion)
  exact congrArg SpatialCurl.curlLinear hd



@[simp] theorem physicalLoss_potential (h : ℝ) (m : ℕ) :
    physicalLoss h (-h) m = PhysicalGraphBounds.waveLoss h m + h := by
  simp [physicalLoss]

@[simp] theorem physicalLoss_velocity (h : ℝ) (m : ℕ) :
    physicalLoss h (-CoordinateAlgebra.A h) m =
      PhysicalGraphBounds.waveLoss h m + CoordinateAlgebra.A h := by
  simp [physicalLoss]

@[simp] theorem physicalLoss_pressure (h : ℝ) (m : ℕ) :
    physicalLoss h (-(2 * CoordinateAlgebra.A h)) m =
      PhysicalGraphBounds.waveLoss h m + 2 * CoordinateAlgebra.A h := by
  simp [physicalLoss]

/-! ### The actual Cartesian-to-cylindrical coefficient map -/

abbrev CylindricalPoint := ℝ × ((ℝ × ℝ) × PhysicalGraphBounds.Plane)

noncomputable def cartesianRadius (y : PhysicalGraphBounds.Plane) : ℝ :=
  Real.sqrt (y.1 ^ 2 + y.2 ^ 2)

theorem cartesianRadius_smooth :
    ContDiffOn ℝ ∞ cartesianRadius {y : PhysicalGraphBounds.Plane | y ≠ 0} := by
  intro y hy
  exact (((contDiffAt_fst.pow 2).add (contDiffAt_snd.pow 2)).sqrt
    (PhysicalGraphBounds.sum_sq_pos hy).ne').contDiffWithinAt

/-- Slow order `(T,Z)` and the actual common auxiliary coordinate. -/
noncomputable def slowFast : PhysicalWaveSum.LiftPoint →L[ℝ]
    ((ℝ × ℝ) × PhysicalGraphBounds.Plane) :=
  (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp PhysicalGraphBounds.liftZT).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp PhysicalGraphBounds.liftZT)).prod
    (ContinuousLinearMap.snd ℝ PhysicalGraphBounds.ChartPoint PhysicalGraphBounds.Plane)

@[simp] theorem slowFast_apply (x : PhysicalWaveSum.LiftPoint) :
    slowFast x = ((x.1.1, x.1.2.2.2), x.2) := rfl

theorem norm_slowFast_le : ‖slowFast‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [one_mul, slowFast_apply]
  change max (max ‖x.1.1‖ ‖x.1.2.2.2‖) ‖x.2‖ ≤ ‖x‖
  exact max_le (max_le
    ((le_max_left ‖x.1.1‖ ‖x.1.2‖).trans (le_max_left _ _))
    ((le_max_right ‖x.1.2.2.1‖ ‖x.1.2.2.2‖).trans
      ((le_max_right ‖x.1.2.1‖ ‖x.1.2.2‖).trans
        ((le_max_right ‖x.1.1‖ ‖x.1.2‖).trans (le_max_left _ _)))))
    (le_max_right _ _)

noncomputable def cylindricalMap (x : PhysicalWaveSum.LiftPoint) : CylindricalPoint :=
  (cartesianRadius (PhysicalGraphBounds.liftXY x), slowFast x)

noncomputable def cylindricalDomain (a b : ℝ) : Set PhysicalWaveSum.LiftPoint :=
  (fun x => ‖PhysicalGraphBounds.liftXY x‖) ⁻¹' Ioo (a / 2) (b + 1)

theorem cylindricalDomain_open (a b : ℝ) : IsOpen (cylindricalDomain a b) :=
  isOpen_Ioo.preimage PhysicalGraphBounds.liftXY.continuous.norm

theorem cylindricalDomain_axisFree {a b : ℝ} (ha : 0 < a)
    {x : PhysicalWaveSum.LiftPoint} (hx : x ∈ cylindricalDomain a b) :
    PhysicalGraphBounds.liftXY x ≠ 0 := by
  intro he
  have hp : a / 2 < ‖PhysicalGraphBounds.liftXY x‖ := hx.1
  rw [he, norm_zero] at hp
  linarith

theorem cylindricalMap_smooth {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ cylindricalMap (cylindricalDomain a b) :=
  (cartesianRadius_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
    (fun _ hx => cylindricalDomain_axisFree ha hx)).prodMk slowFast.contDiff.contDiffOn

/-- All positive jets of the actual radius map are uniformly bounded on
a fixed padded annulus, regardless of slow or auxiliary coordinates. -/
theorem cylindricalMap_positiveJets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ cylindricalDomain a b, ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j cylindricalMap x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PhysicalGraphBounds.compact_jet_bound
    PhysicalGraphBounds.axisFree_open cartesianRadius_smooth
    (PhysicalGraphBounds.isCompact_annulus (a / 2) (b + 1))
    (PhysicalGraphBounds.annulus_axisFree (half_pos ha)) m
  refine ⟨B, hB, ?_⟩
  intro x hx j hj hjm
  have haxis := cylindricalDomain_axisFree ha hx
  have hann : PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 2) (b + 1) := by
    refine ⟨?_, hx.1.le⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le
  have hrad : ContDiffAt ℝ ∞ (cartesianRadius ∘ PhysicalGraphBounds.liftXY) x :=
    (cartesianRadius_smooth.contDiffAt (PhysicalGraphBounds.axisFree_open.mem_nhds haxis)).comp x
      PhysicalGraphBounds.liftXY.contDiff.contDiffAt
  have hrb : ‖iteratedFDeriv ℝ j (cartesianRadius ∘ PhysicalGraphBounds.liftXY) x‖ ≤ B := by
    exact (PhysicalGraphBounds.norm_jet_comp_linear PhysicalGraphBounds.axisFree_open
      cartesianRadius_smooth PhysicalGraphBounds.liftXY haxis j).trans
      ((mul_le_mul (hb j hjm _ hann)
        (pow_le_one₀ (norm_nonneg _) PhysicalGraphBounds.norm_liftXY_le)
        (by positivity) (zero_le_one.trans hB)).trans_eq (mul_one B))
  change ‖iteratedFDeriv ℝ j
    (fun y => ((cartesianRadius ∘ PhysicalGraphBounds.liftXY) y, slowFast y)) x‖ ≤ B
  rw [PhysicalGraphBounds.iteratedFDeriv_pair (hrad.of_le (natCast_le_infty j))
    (slowFast.contDiff.contDiffAt.of_le (natCast_le_infty j)), ContinuousMultilinearMap.opNorm_prod]
  exact max_le hrb ((PhysicalGraphBounds.norm_positive_jet_linear_le slowFast x hj).trans
    (norm_slowFast_le.trans hB))

@[simp] theorem liftXY_commonLift (h : ℝ) (n d : ℕ) (z : ProblemStatement.SpaceTime) :
    PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d z) =
      PhysicalGraphBounds.scaledRadial n z := by
  change PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h n z) = _
  exact PhysicalGraphBounds.liftXY_physicalLift h n z

/-- The actual common graph has the expected cylindrical radius, scaled
slow variables, and inverse-covered auxiliary coordinate. -/
theorem cylindricalMap_commonLift (h : ℝ) (n d : ℕ) (z : ProblemStatement.SpaceTime) :
    cylindricalMap (PhysicalWaveSum.commonLift h n d z) =
      (cartesianRadius (PhysicalGraphBounds.scaledRadial n z),
        (((1 - z.1) / ChartScales.Q n, ChartScales.Q n ^ (-CoordinateAlgebra.D h) * z.2 2),
          (CommonCoverSolve.coverPower d).symm (PhysicalGraphBounds.nativeGraph h n z))) := by
  rw [cylindricalMap, liftXY_commonLift, slowFast_apply]
  simp only [PhysicalWaveSum.commonLift, Function.comp_apply, PhysicalWaveSum.downLift_apply,
    PhysicalGraphBounds.physicalLift, PhysicalGraphBounds.physicalChart_time]
  simp [PhysicalGraphBounds.physicalChart, PhysicalGraphBounds.chartLinear_apply]

theorem commonLift_mem_cylindricalDomain {a b : ℝ} (ha : 0 < a)
    (h : ℝ) (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (hz : PhysicalGraphBounds.scaledRadial n z ∈ PhysicalGraphBounds.annulus a b) :
    PhysicalWaveSum.commonLift h n d z ∈ cylindricalDomain a b := by
  change a / 2 < ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d z)‖ ∧
    ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d z)‖ < b + 1
  rw [liftXY_commonLift]
  have hlo : a ≤ ‖PhysicalGraphBounds.scaledRadial n z‖ := hz.2
  have hhi : ‖PhysicalGraphBounds.scaledRadial n z‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  constructor <;> linarith


end NavierStokes.PhysicalClassBounds
