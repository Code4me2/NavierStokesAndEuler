import NavierStokes.AnnularEndpoint
import NavierStokes.VariableGaugeMean
import NavierStokes.PeriodicPhaseAssembly

/-!
# Primitive correction formulas at a nonzero axial endpoint

The positive stable branch of the similarity coordinate continues across
`T = 0` when `Z ≠ 0`.  This file uses that branch in the actual moving-radius
mean operations.  Agreement of primitive data is on whole slow fibers,
because radial and torus integrals are nonlocal on each such fiber.
-/

noncomputable section

namespace NavierStokes.OffplaneCorrectionExtensions

open Set Filter Function
open scoped Topology ContDiff BigOperators

abbrev Slow := PressureStream.Plane
abbrev Lift := PressureStream.Lift Slow
abbrev Model := MeanRankUpdate.ModelPoint × PressureStream.Plane

noncomputable def stableQ (coord : ℝ) (s : Slow) : ℝ :=
  (PositiveRepresentatives.stableInverse coord s).1

noncomputable def stableLength (coord : ℝ) (s : Slow) : ℝ := Real.sqrt (stableQ coord s)

theorem stableQ_pos {coord : ℝ} {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) : 0 < stableQ coord s :=
  (PositiveRepresentatives.stableInverse_spec hs).1.1

theorem stableQ_contDiffAt {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) : ContDiffAt ℝ ∞ (stableQ coord) s :=
  (PositiveRepresentatives.stableInverse_smoothAt hc.le hc1.le hs).fst

theorem stableLength_pos {coord : ℝ} {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) : 0 < stableLength coord s :=
  Real.sqrt_pos.mpr (stableQ_pos hs)

theorem stableLength_contDiffAt {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) {s : Slow}
    (hs : s ∈ PositiveRepresentatives.stableTarget coord) :
    ContDiffAt ℝ ∞ (stableLength coord) s :=
  (stableQ_contDiffAt hc hc1 hs).sqrt (stableQ_pos hs).ne'

theorem stableLength_contDiffOn {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1) :
    ContDiffOn ℝ ∞ (stableLength coord) (PositiveRepresentatives.stableTarget coord) :=
  fun _ hs => (stableLength_contDiffAt hc hc1 hs).contDiffWithinAt

theorem stableQ_eq_coordinateQ {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Slow} (hs : 0 < s.1) : stableQ coord s = SimilarityCoordinates.coordinateQ coord s := by
  exact congrArg Prod.fst (PositiveRepresentatives.stableInverse_eq_inverseMap hc hc1 hs)

theorem stableLength_eq_qLength {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {s : Slow} (hs : 0 < s.1) : stableLength coord s = VariableGaugeMean.qLength coord s := by
  exact congrArg Real.sqrt (stableQ_eq_coordinateQ hc hc1 hs)

/-- A neighborhood on which the moving radial interval has fixed positive
inner and finite outer bounds.  These bounds are constructed from the
actual stable branch below. -/
structure Window (coord a b : ℝ) where
  carrier : Set Slow
  isOpen : IsOpen carrier
  stable : carrier ⊆ PositiveRepresentatives.stableTarget coord
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  left : ∀ s ∈ carrier, lower ≤ stableLength coord s * a
  right : ∀ s ∈ carrier, stableLength coord s * b ≤ upper



namespace Window

variable {coord a b : ℝ} (W : Window coord a b)

theorem length_pos {s : Slow} (hs : s ∈ W.carrier) : 0 < stableLength coord s :=
  stableLength_pos (W.stable hs)

theorem length_smooth (hc : 0 < coord) (hc1 : coord < 1) :
    ContDiffOn ℝ ∞ (stableLength coord) W.carrier :=
  (stableLength_contDiffOn hc hc1).mono W.stable

theorem fixed_support {f : Lift → ℝ}
    (hf : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    PhysicalMeanDomain.SupportedOn W.lower W.upper W.carrier f := by
  intro p hp hn
  exact ⟨(W.left _ hp).trans (hf p hp hn).1, (hf p hp hn).2.trans (W.right _ hp)⟩

end Window

/-- Positive time is restricted only in the agreement assertion.  The
continued formulas themselves are defined on the full stable neighborhood. -/
noncomputable def positiveSlow : Set Slow := {s | 0 < s.1}

theorem positiveSlow_open : IsOpen positiveSlow := isOpen_lt continuous_const continuous_fst

def FiberAgreement {V : Type*} (U : Set Slow) (F f : Lift → V) : Prop :=
  EqOn F f (PhysicalMeanDomain.slowDomain (U ∩ positiveSlow))

theorem FiberAgreement.fiber {V : Type*} {U : Set Slow} {F f : Lift → V}
    (h : FiberAgreement U F f) {s : Slow} (hs : s ∈ U) (ht : 0 < s.1) :
    ∀ r Y, F (r, (s, Y)) = f (r, (s, Y)) :=
  fun _ _ => h ⟨hs, ht⟩

theorem FiberAgreement.eventuallyEq {V : Type*} {U : Set Slow} (hU : IsOpen U) {F f : Lift → V}
    (h : FiberAgreement U F f) {p : Lift} (hp : p.2.1 ∈ U) (ht : 0 < p.2.1.1) :
    F =ᶠ[𝓝 p] f := by
  filter_upwards [(PhysicalMeanDomain.slowDomain_open (hU.inter positiveSlow_open)).mem_nhds
    (show p ∈ PhysicalMeanDomain.slowDomain (U ∩ positiveSlow) from ⟨hp, ht⟩)] with z hz
  exact h hz


noncomputable def physicalModel (coord : ℝ) (p : Lift) : Model :=
  ((SimilarityCoordinates.coordinateQ coord p.2.1, (p.1, p.2.1.2)), p.2.2)






noncomputable def physicalSource (coord : ℝ) (F : Model → ℝ) : Lift → ℝ :=
  F ∘ physicalModel coord







namespace Window

variable {coord a b : ℝ} (W : Window coord a b)
    (hc : 0 < coord) (hc1 : coord < 1)

include hc hc1

theorem compactPrimitive_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.compactPrimitive d a b M (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) :=
  VariableGaugeMean.compactPrimitive_contDiffOn W.lower_pos W.lower_lt_upper ha hab hd v
    W.isOpen (W.length_smooth hc hc1) (fun _ hs => W.length_pos hs) W.left W.right hf hs

theorem pressureSource_smooth (hab : a < b) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.pressureSource a b hab (stableLength coord) f)
      (PhysicalMeanDomain.slowDomain W.carrier) :=
  hf.sub ((VariableGaugeMean.density_contDiffOn hab (W.length_smooth hc hc1)
    (fun _ hs => W.length_pos hs)).mul
      (PhysicalMeanDomain.liftedPressureMass_contDiffOn W.isOpen hf (W.fixed_support hs)))

theorem meanPressure_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.meanPressure d a b M hab (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) :=
  W.compactPrimitive_smooth hc hc1 ha hab hd M v
    (W.pressureSource_smooth hc hc1 hab hf hs)
    (VariableGaugeMean.pressureSource_supported hab (fun _ hs => W.length_pos hs) hs)

theorem streamPotential_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.streamPotential d a b M (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hws : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier
      (PressureStream.weightedSource f) := fun p hp hn => hs p hp (right_ne_zero_of_mul hn)
  have hwf : ContDiffOn ℝ ∞ (PressureStream.weightedSource f)
      (PhysicalMeanDomain.slowDomain W.carrier) := contDiffOn_fst.mul hf
  have hI := W.compactPrimitive_smooth hc hc1 ha hab hd M v hwf hws
  have hIs := VariableGaugeMean.compactPrimitive_supportedGauge (M := M) ha hab hd
    (stableLength coord) v W.isOpen (fun _ hs => W.length_pos hs) hwf hws
  exact VariableGaugeMean.divideRadius_contDiffOn W.lower_pos W.isOpen hI (W.fixed_support hIs)

theorem compactAlias_smooth (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d)
    (M : ℝ) (v : Slow) {f : Lift → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain W.carrier))
    (hs : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier f) :
    ContDiffOn ℝ ∞ (VariableGaugeMean.compactAlias d a b M (stableLength coord) v f)
      (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hC := VariableGaugeMean.cutoffRadialDerivative_contDiffOn ha d b
    (W.length_smooth hc hc1) (fun _ hs => W.length_pos hs)
  have hJ := VariableGaugeMean.physicalTotal_contDiffOn (M := M)
    W.lower_pos W.lower_lt_upper hd v W.isOpen hf (W.fixed_support hs)
  apply (hC.mul hJ).congr
  intro p hp
  exact VariableGaugeMean.compactAlias_reference W.lower_pos ha hab hd (stableLength coord) v
    (fun _ hs => W.length_pos hs) W.left hs p hp

end Window

section ExactAgreement

variable {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {U : Set Slow} {F f : Lift → ℝ} (he : FiberAgreement U F f)

include hc hc1 he

theorem compactPrimitive_agreement (d a b M : ℝ) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.compactPrimitive d a b M (stableLength coord) v F)
      (VariableGaugeMean.compactPrimitive d a b M (VariableGaugeMean.qLength coord) v f) := by
  intro p hp
  dsimp only [VariableGaugeMean.compactPrimitive]
  rw [stableLength_eq_qLength hc hc1 hp.2]
  exact PhysicalMeanDomain.physicalCompact_fiberLocal d _ _ M v F f p.2.1
    (he.fiber hp.1 hp.2) p.1 p.2.2

theorem pressureSource_agreement (a b : ℝ) (hab : a < b) :
    FiberAgreement U (VariableGaugeMean.pressureSource a b hab (stableLength coord) F)
      (VariableGaugeMean.pressureSource a b hab (VariableGaugeMean.qLength coord) f) := by
  intro p hp
  have hm : PressureStream.pressureMass F p.2.1 = PressureStream.pressureMass f p.2.1 :=
    PhysicalMeanDomain.liftedPressureMass_fiberLocal F f p.2.1 (he.fiber hp.1 hp.2) p.1 p.2.2
  dsimp only [VariableGaugeMean.pressureSource, VariableGaugeMean.density,
    VariableGaugeMean.radialRatio]
  rw [he hp, hm, stableLength_eq_qLength hc hc1 hp.2]

theorem meanPressure_agreement (d a b M : ℝ) (hab : a < b) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.meanPressure d a b M hab (stableLength coord) v F)
      (VariableGaugeMean.meanPressure d a b M hab (VariableGaugeMean.qLength coord) v f) :=
  compactPrimitive_agreement hc hc1 (pressureSource_agreement hc hc1 he a b hab) d a b M v

theorem streamPotential_agreement (d a b M : ℝ) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.streamPotential d a b M (stableLength coord) v F)
      (VariableGaugeMean.streamPotential d a b M (VariableGaugeMean.qLength coord) v f) := by
  have hw : FiberAgreement U (PressureStream.weightedSource F) (PressureStream.weightedSource f) := by
    intro p hp
    exact congrArg (fun t => p.1 * t) (he hp)
  intro p hp
  exact congrArg (fun t => t / p.1) (compactPrimitive_agreement hc hc1 hw d a b M v hp)

theorem compactAlias_agreement (d a b M : ℝ) (v : Slow) :
    FiberAgreement U (VariableGaugeMean.compactAlias d a b M (stableLength coord) v F)
      (VariableGaugeMean.compactAlias d a b M (VariableGaugeMean.qLength coord) v f) := by
  intro p hp
  dsimp only [VariableGaugeMean.compactAlias]
  rw [stableLength_eq_qLength hc hc1 hp.2]
  exact PhysicalMeanDomain.physicalAlias_fiberLocal d _ _ M v F f p.2.1
    (he.fiber hp.1 hp.2) p.1 p.2.2

omit hc hc1 in
theorem temporalAtIndex_agreement (h : ℝ) (n i : ℕ) :
    FiberAgreement U (MeanChartCompatibility.temporalAtIndex h n i F)
      (MeanChartCompatibility.temporalAtIndex h n i f) := by
  intro p hp
  exact VariableGaugeMean.temporalAtIndex_fiberLocal h n i F f p.2.1
    (he.fiber hp.1 hp.2) p.1 p.2.2

end ExactAgreement

/-- A full-fiber primitive continuation.  Constructors below obtain such
data from explicit positive-q models, then preserve it through the actual
nonlocal mean operations. -/
structure SupportedContinuation {coord a b : ℝ} (W : Window coord a b) (f : Lift → ℝ) where
  value : Lift → ℝ
  smooth : ContDiffOn ℝ ∞ value (PhysicalMeanDomain.slowDomain W.carrier)
  supported : VariableGaugeMean.SupportedGauge a b (stableLength coord) W.carrier value
  agrees : FiberAgreement W.carrier value f

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b} (hc : 0 < coord) (hc1 : coord < 1)


noncomputable def primitive {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.compactPrimitive d a b M (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.compactPrimitive d a b M (stableLength coord) v e.value
  smooth := W.compactPrimitive_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := VariableGaugeMean.compactPrimitive_supportedGauge ha hab hd (stableLength coord) v
    W.isOpen (fun _ hs => W.length_pos hs) e.smooth e.supported
  agrees := compactPrimitive_agreement hc hc1 e.agrees d a b M v

noncomputable def pressure {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.meanPressure d a b M hab (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.meanPressure d a b M hab (stableLength coord) v e.value
  smooth := W.meanPressure_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := VariableGaugeMean.compactPrimitive_supportedGauge ha hab hd (stableLength coord) v
    W.isOpen (fun _ hs => W.length_pos hs) (W.pressureSource_smooth hc hc1 hab e.smooth e.supported)
    (VariableGaugeMean.pressureSource_supported hab (fun _ hs => W.length_pos hs) e.supported)
  agrees := meanPressure_agreement hc hc1 e.agrees d a b M hab v

noncomputable def stream {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.streamPotential d a b M (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.streamPotential d a b M (stableLength coord) v e.value
  smooth := W.streamPotential_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := VariableGaugeMean.streamPotential_supportedGauge ha hab hd (stableLength coord) v
    W.isOpen (fun _ hs => W.length_pos hs) e.smooth e.supported
  agrees := streamPotential_agreement hc hc1 e.agrees d a b M v

noncomputable def aliasField {f : Lift → ℝ} (e : SupportedContinuation W f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℝ) (v : Slow) :
    SupportedContinuation W
      (VariableGaugeMean.compactAlias d a b M (VariableGaugeMean.qLength coord) v f) where
  value := VariableGaugeMean.compactAlias d a b M (stableLength coord) v e.value
  smooth := W.compactAlias_smooth hc hc1 ha hab hd M v e.smooth e.supported
  supported := by
    intro p hp hn
    exact RadialPullback.physicalAlias_supported (mul_pos (W.length_pos hp) ha)
      (mul_lt_mul_of_pos_left hab (W.length_pos hp)) hd M ((0 : Slow), v) e.value hn
  agrees := compactAlias_agreement hc hc1 e.agrees d a b M v

omit hc hc1 in
noncomputable def temporal {f : Lift → ℝ} (e : SupportedContinuation W f)
    (h : ℝ) (n i : ℕ) (hp : PhysicalMeanDomain.PeriodicOn W.carrier e.value) :
    SupportedContinuation W (MeanChartCompatibility.temporalAtIndex h n i f) where
  value := MeanChartCompatibility.temporalAtIndex h n i e.value
  smooth := VariableGaugeMean.temporalAtIndex_contDiffOn h n i W.isOpen e.smooth hp
  supported := VariableGaugeMean.temporalAtIndex_supportedGauge h n i e.supported
  agrees := temporalAtIndex_agreement e.agrees h n i

end SupportedContinuation

namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b}






end SupportedContinuation

section ReferenceODE

variable {P Q V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]






end ReferenceODE

section ContinuedReferenceODE

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]











end ContinuedReferenceODE

section ContinuedPhase


end ContinuedPhase

section FullReferenceCarrier

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]




end FullReferenceCarrier

section RankModels





end RankModels

section PhysicalFields

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

noncomputable def physicalSlow (w : SpaceTime) : Slow := (1 - w.1, w.2 2)

theorem physicalSlow_contDiff : ContDiff ℝ ∞ physicalSlow :=
  (contDiff_const.sub contDiff_fst).prodMk
    ((AxisymmetricFields.projection 2).contDiff.comp contDiff_snd)

/-- The actual radial/slow/native-graph restriction of a full-fiber mean
field.  The common covering level remains the supplied `n`. -/
noncomputable def physicalLift (h : ℝ) (n : ℕ) (w : SpaceTime) : Lift :=
  (AnnularEndpoint.radius w, (physicalSlow w, PhysicalGraphBounds.nativeGraph h n w))

noncomputable def physicalDomain (U : Set Slow) : Set SpaceTime := physicalSlow ⁻¹' U

theorem physicalDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (physicalDomain U) :=
  hU.preimage physicalSlow_contDiff.continuous




noncomputable def physicalScalar (h : ℝ) (n : ℕ) (f : Lift → ℝ) : SpaceTime → ℝ :=
  f ∘ physicalLift h n



/-- `streamPotential` is already the azimuthal component of the vector
potential, including its division by the radial variable. -/
noncomputable def azimuthalPotential (h : ℝ) (n : ℕ) (f : Lift → ℝ) (w : SpaceTime) : Space :=
  (-w.2 1 / AnnularEndpoint.radius w * physicalScalar h n f w) • ProblemStatement.coordinateVector 0 +
    (w.2 0 / AnnularEndpoint.radius w * physicalScalar h n f w) • ProblemStatement.coordinateVector 1

/-- A direct angular velocity uses the same Cartesian multiplication by
`e_theta`.  This definition does not apply a curl or a radial primitive. -/
noncomputable def angularField (h : ℝ) (n : ℕ) (f : Lift → ℝ) : SpaceTime → Space :=
  azimuthalPotential h n f


namespace SupportedContinuation

variable {coord a b : ℝ} {W : Window coord a b} {f : Lift → ℝ}




end SupportedContinuation






end PhysicalFields

section DiagonalCutoffs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def physicalQExtension (h : ℝ) (w : SpaceTime) : ℝ :=
  (EndpointCoordinates.cartesianExtension h w).1

theorem physicalQExtension_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : physicalQExtension h w = PhysicalWaveSum.physicalQ h w :=
  congrArg Prod.fst (EndpointCoordinates.cartesianExtension_eq_physical hh hh1 ht)

/-- Only finitely many stages survive near a positive-q endpoint.  Their
extensions are combined with the same scalar cutoffs and the same schedule.
The preceding model/mean constructors supply the finite-stage extensions. -/
theorem diagonal_extension {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {F : ℕ → SpaceTime → V}
    {x : Space} (hx : x 2 ≠ 0)
    (he : ∀ j, Nonempty (JointResidualLimits.OneSidedExtension (F j) x)) :
    Nonempty (JointResidualLimits.OneSidedExtension
      (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F) x) := by
  classical
  obtain ⟨U, hU, hxU, hUD, _, _, hqU⟩ := EndpointCoordinates.cartesian_endpoint_neighborhood hh hh1 hx
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha
    (EndpointCoordinates.endpointRoot_pos (2 * h) hx)
  let e : ∀ j, JointResidualLimits.OneSidedExtension (F j) x := fun j => Classical.choice (he j)
  let D : Set SpaceTime := U ∩ ⋂ j ∈ Finset.range N, (e j).domain
  have hD : IsOpen D := hU.inter (isOpen_biInter_finset fun j _ => (e j).isOpen)
  have hxD : (1, x) ∈ D := ⟨hxU, mem_iInter.mpr fun j => mem_iInter.mpr fun _ => (e j).mem⟩
  have hsub (j : ℕ) (hj : j ∈ Finset.range N) : D ⊆ (e j).domain :=
    fun w hw => mem_iInter.mp (mem_iInter.mp hw.2 j) hj
  have hq : ContDiffOn ℝ ∞ (physicalQExtension h) D :=
    (EndpointCoordinates.cartesianExtension_smoothOn hh hh1).fst.mono (fun _ hw => hUD hw.1)
  refine ⟨{
    value := fun w => ∑ j ∈ Finset.range N,
      SmoothCutoffs.scaledCutoff (a j) (physicalQExtension h w) • (e j).value w
    domain := D
    isOpen := hD
    mem := hxD
    smooth := ?_
    agrees := ?_ }⟩
  · apply ContDiffOn.sum
    intro j hj
    exact ((SmoothCutoffs.scaledCutoff_contDiff (a j)).comp_contDiffOn hq).smul
      ((e j).smooth.mono (hsub j hj))
  · intro w hw
    have hqt := physicalQExtension_eq hh hh1 hw.2.1
    have hlow : EndpointCoordinates.endpointRoot (2 * h) (x 2) / 2 < PhysicalWaveSum.physicalQ h w := by
      rw [← hqt]
      exact (hqU w hw.1.1).1
    have hsum : SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) F w =
        ∑ j ∈ Finset.range N, SolenoidalDiagonal.cutStage a (PhysicalWaveSum.physicalQ h) F j w := by
      apply tsum_eq_sum
      intro j hj
      simp only [SolenoidalDiagonal.cutStage, hN j
        (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)) _ hlow, zero_smul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    change SmoothCutoffs.scaledCutoff (a j) (physicalQExtension h w) • (e j).value w =
      SmoothCutoffs.scaledCutoff (a j) (PhysicalWaveSum.physicalQ h w) • F j w
    rw [hqt, (e j).agrees ⟨hsub j hj hw.1, hw.2⟩]

end DiagonalCutoffs



end NavierStokes.OffplaneCorrectionExtensions
