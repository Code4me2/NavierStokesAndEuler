import Euler.EulerProof.Foundations

/-!
# The lifted gradient space and metric transport

The `L^2` theory on the periodic lift, the pressure solve there, and the
transport calculus built on top of it:

* `EulerLiftedGradientSpace`, `EulerLiftedPressure` -- the lifted `L^2` space,
  its gradient subspace and the coercive pressure solver on it.
* `EulerMetricTransport`, `EulerTransportDerivatives` -- transport fields on the
  lift and differentiation of the transported quantities.
* `EulerPressureSpatialRegularity`, `EulerLiftedWeakDerivative`,
  `EulerSpatialSobolevInverse` -- spatial regularity of the pressure, weak
  derivatives on the lift, and the jet calculus (`SmoothCoefficient`,
  `SpatialJet`, `CoefficientJet`) inverting the spatial Sobolev estimates.
* `EulerLiftedCurl`, `EulerNoncompactTransport` -- curl identities and transport
  on the noncompact factor.
* `EulerMetricEnergyEvolution`, `EulerRepresentativeMetricEvolution`,
  `EulerPressureJetIdentities`, `EulerJetProductBounds` -- energy evolution for
  metric solutions and the jet product bounds it needs.

This is part 2 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

/-!
An actual L² realization of the lifted pressure-gradient space on R³ × (R / period Z).
The generating vectors are L² representatives of Dφ, for smooth compactly supported
scalar test functions φ.  Smoothness is expressed through local lifts to R³ × R.
The angular measure here has total mass `period`; renormalizing it changes only a
fixed scalar in the L² norm and not the gradient subspace or projection.
-/


namespace EulerLiftedGradientSpace

open MeasureTheory InnerProductSpace
open scoped ContDiff ENNReal Topology

/-- Three dimensional real Euclidean vectors. -/
abbrev Vector3 := EuclideanSpace ℝ (Fin 3)
/-- The spatial cylinder with one periodic angle coordinate. -/
abbrev LiftDomain (period : ℝ) := Vector3 × AddCircle period
/-- The four dimensional real covering space of the cylinder. -/
abbrev LiftTangent := Vector3 × ℝ

variable (period : ℝ) [Fact (0 < period)]

/-- Product Lebesgue and angle Haar measure on the cylinder. -/
def liftMeasure : Measure (LiftDomain period) :=
  (volume : Measure Vector3).prod (volume : Measure (AddCircle period))

instance liftMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (liftMeasure period) := by
  unfold liftMeasure
  infer_instance

/-- The genuine Hilbert space of square integrable vector fields on the cylinder. -/
abbrev LiftL2 := Lp Vector3 2 (liftMeasure period)

/-- The scalar field pulled back to covering coordinates centered at x. -/
def localLift (φ : LiftDomain period → ℝ) (x : LiftDomain period) : LiftTangent → ℝ :=
  fun h => φ (x.1 + h.1, x.2 + (h.2 : AddCircle period))

/-- The quotient covering map from the real tangent space to the cylinder. -/
def coveringMap : LiftTangent → LiftDomain period :=
  fun z => (z.1, (z.2 : AddCircle period))

omit [Fact (0 < period)] in
theorem coveringMap_isOpenQuotient : IsOpenQuotientMap (coveringMap period) :=
  IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk

omit [Fact (0 < period)] in
theorem localLift_cover (φ : LiftDomain period → ℝ) (z : LiftTangent) :
    localLift period φ (coveringMap period z) = fun h => localLift period φ 0 (z + h) := by
  funext h
  simp [localLift, coveringMap]

omit [Fact (0 < period)] in
theorem fderiv_localLift_cover (φ : LiftDomain period → ℝ) (z : LiftTangent) :
    fderiv ℝ (localLift period φ (coveringMap period z)) 0 =
      fderiv ℝ (localLift period φ 0) z := by
  rw [localLift_cover, fderiv_comp_add_left, add_zero]

/-- The actual differential expression `κ ∇_y φ + m ∂_θ φ`. -/
def liftedGradient (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (x : LiftDomain period) : Vector3 :=
  WithLp.toLp 2 fun i =>
    κ * fderiv ℝ (localLift period φ x) 0 (EuclideanSpace.single i 1, 0) +
      m i * fderiv ℝ (localLift period φ x) 0 (0, 1)

omit [Fact (0 < period)] in
theorem liftedGradient_continuous (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    Continuous (liftedGradient period κ m φ) := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have hd : Continuous (fderiv ℝ (localLift period φ 0)) :=
    (hφ 0).continuous_fderiv (by simp)
  have hcomp : liftedGradient period κ m φ ∘ coveringMap period =
      fun z => WithLp.toLp 2 fun i =>
        κ * fderiv ℝ (localLift period φ 0) z (EuclideanSpace.single i 1, 0) +
          m i * fderiv ℝ (localLift period φ 0) z (0, 1) := by
    funext z
    simp only [Function.comp_def, liftedGradient, fderiv_localLift_cover]
  rw [hcomp]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul (hd.clm_apply continuous_const)).add
    (continuous_const.mul (hd.clm_apply continuous_const))

omit [Fact (0 < period)] in
theorem liftedGradient_zero_of_notMem_tsupport (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (x : LiftDomain period) (hx : x ∉ tsupport φ) :
    liftedGradient period κ m φ x = 0 := by
  have hc : Continuous (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) :=
    (continuous_const.add continuous_fst).prodMk
      (continuous_const.add ((AddCircle.continuous_mk' period).comp continuous_snd))
  have ht : Filter.Tendsto (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : LiftTangent)
  have hz : localLift period φ x =ᶠ[𝓝 0] (fun _ : LiftTangent => (0 : ℝ)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto ht
  have hd : fderiv ℝ (localLift period φ x) 0 = 0 := by
    rw [hz.fderiv_eq]
    simp
  simp [liftedGradient, hd]
  rfl

omit [Fact (0 < period)] in
theorem liftedGradient_hasCompactSupport (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (liftedGradient period κ m φ) :=
  HasCompactSupport.intro hφ (liftedGradient_zero_of_notMem_tsupport period κ m φ)

/-- Every smooth compact test has an actual L² lifted gradient. -/
theorem liftedGradient_memLp (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    MemLp (liftedGradient period κ m φ) 2 (liftMeasure period) := by
  exact (liftedGradient_continuous period κ m φ hφ.2).memLp_of_hasCompactSupport
    (liftedGradient_hasCompactSupport period κ m φ hφ.1)

/-- Translation of a scalar test function on the cylinder. -/
def translatedTest (a : LiftDomain period) (φ : LiftDomain period → ℝ) :
    LiftDomain period → ℝ := fun x => φ (x + a)

omit [Fact (0 < period)] in
@[simp]
theorem localLift_translated (a x : LiftDomain period) (φ : LiftDomain period → ℝ) :
    localLift period (translatedTest period a φ) x = localLift period φ (x + a) := by
  funext h
  change φ (x.1 + h.1 + a.1, x.2 + (h.2 : AddCircle period) + a.2) =
    φ (x.1 + a.1 + h.1, x.2 + a.2 + (h.2 : AddCircle period))
  congr 1
  exact Prod.ext (add_right_comm _ _ _) (add_right_comm _ _ _)

omit [Fact (0 < period)] in
theorem smoothCompactTest_translated (a : LiftDomain period) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    HasCompactSupport (translatedTest period a φ) ∧
      ∀ x, ContDiff ℝ ∞ (localLift period (translatedTest period a φ) x) := by
  refine ⟨hφ.1.comp_homeomorph (Homeomorph.addRight a), fun x => ?_⟩
  rw [localLift_translated]
  exact hφ.2 (x + a)

omit [Fact (0 < period)] in
@[simp]
theorem liftedGradient_translated (κ : ℝ) (m : Vector3) (a x : LiftDomain period)
    (φ : LiftDomain period → ℝ) :
    liftedGradient period κ m (translatedTest period a φ) x =
      liftedGradient period κ m φ (x + a) := by
  simp only [liftedGradient, localLift_translated]

theorem measurePreserving_translation (a : LiftDomain period) :
    MeasurePreserving (fun x : LiftDomain period => x + a)
      (liftMeasure period) (liftMeasure period) := by
  exact (measurePreserving_add_right (volume : Measure Vector3) a.1).prod
    (measurePreserving_add_right (volume : Measure (AddCircle period)) a.2)

/-- The measure preserving translation isometry on the actual L² space. -/
def translation (a : LiftDomain period) : LiftL2 period →ₗᵢ[ℝ] LiftL2 period :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain period => x + a)
    (measurePreserving_translation period a)

theorem translation_ae (a : LiftDomain period) (f : LiftL2 period) :
    translation period a f =ᵐ[liftMeasure period] fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translation period a)

theorem translation_norm (a : LiftDomain period) (f : LiftL2 period) :
    ‖translation period a f‖ = ‖f‖ :=
  (translation period a).norm_map f

theorem translation_add (a b : LiftDomain period) (f : LiftL2 period) :
    translation period a (translation period b f) = translation period (a + b) f := by
  apply Lp.ext
  filter_upwards [translation_ae period a (translation period b f),
    (measurePreserving_translation period a).quasiMeasurePreserving.ae
      (translation_ae period b f), translation_ae period (a + b) f] with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃, add_assoc]

@[simp]
theorem translation_zero (f : LiftL2 period) : translation period 0 f = f := by
  apply Lp.ext
  filter_upwards [translation_ae period 0 f] with x hx
  simpa only [add_zero] using hx

/-- The L² element represented by an actual smooth compact test gradient. -/
def testGradientLp (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) : LiftL2 period :=
  (liftedGradient_memLp period κ m φ hφ).toLp (liftedGradient period κ m φ)

theorem testGradientLp_ae (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    testGradientLp period κ m φ hφ =ᵐ[liftMeasure period] liftedGradient period κ m φ :=
  (liftedGradient_memLp period κ m φ hφ).coeFn_toLp

theorem testGradientLp_mem_generators (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    testGradientLp period κ m φ hφ ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}) :=
  ⟨φ, hφ, testGradientLp_ae period κ m φ hφ⟩

/-- Closure of the span of genuine smooth test gradients in the concrete L² space. -/
def gradientSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}))).topologicalClosure

theorem gradientSpace_closed (κ : ℝ) (m : Vector3) :
    IsClosed (gradientSpace period κ m : Set (LiftL2 period)) :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}))).isClosed_topologicalClosure

instance gradientSpace_complete (κ : ℝ) (m : Vector3) :
    CompleteSpace (gradientSpace period κ m) :=
  (gradientSpace_closed period κ m).completeSpace_coe

/-- Orthogonal projection onto the closed lifted gradient subspace. -/
def gradientProjection (κ : ℝ) (m : Vector3) : LiftL2 period →L[ℝ] LiftL2 period :=
  (gradientSpace period κ m).starProjection



theorem testGradient_mem (κ : ℝ) (m : Vector3) {g : LiftL2 period}
    (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) : g ∈ gradientSpace period κ m :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}))).le_topologicalClosure
    (Submodule.subset_span hg)

theorem gradientGenerators_translated (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {g : LiftL2 period} (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) :
    translation period a g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}) := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  refine ⟨translatedTest period a φ, smoothCompactTest_translated period a φ hφ, ?_⟩
  filter_upwards [translation_ae period a g,
    (measurePreserving_translation period a).quasiMeasurePreserving.ae hgφ] with x hx₁ hx₂
  rw [hx₁, hx₂, liftedGradient_translated]

theorem gradientSpace_translation_mem (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {g : LiftL2 period} (hg : g ∈ gradientSpace period κ m) :
    translation period a g ∈ gradientSpace period κ m := by
  let τ := (translation period a).toContinuousLinearMap
  have hspan : Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) ≤
      (gradientSpace period κ m).comap τ.toLinearMap := by
    apply Submodule.span_le.2
    intro f hf
    exact testGradient_mem period κ m (gradientGenerators_translated period κ m a hf)
  have hclosed : IsClosed ((gradientSpace period κ m).comap τ.toLinearMap : Set (LiftL2 period)) :=
    (gradientSpace_closed period κ m).preimage τ.continuous
  exact (Submodule.topologicalClosure_minimal _ hspan hclosed) hg

theorem gradientSpace_map_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period) :
    (gradientSpace period κ m).map (translation period a).toLinearMap =
      gradientSpace period κ m := by
  apply le_antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact gradientSpace_translation_mem period κ m a hf
  · intro g hg
    refine ⟨translation period (-a) g, gradientSpace_translation_mem period κ m (-a) hg, ?_⟩
    change translation period a (translation period (-a) g) = g
    rw [translation_add, add_neg_cancel, translation_zero]

/-- Orthogonal pressure projection commutes with every spatial or angular translation. -/
theorem gradientProjection_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    (f : LiftL2 period) :
    translation period a (gradientProjection period κ m f) =
      gradientProjection period κ m (translation period a f) := by
  have hmap := gradientSpace_map_translation period κ m a
  let : ((gradientSpace period κ m).map (translation period a).toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  simpa only [gradientProjection, hmap] using
    (translation period a).map_starProjection (gradientSpace period κ m) f

/-- The concrete L² weak divergence-free subspace. -/
def divergenceFreeSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (gradientSpace period κ m).orthogonal

/-- Pressure cancellation in the concrete lifted L² space. -/
theorem pressure_pairing_zero (κ : ℝ) (m : Vector3) {p e : LiftL2 period}
    (hp : p ∈ gradientSpace period κ m) (he : e ∈ divergenceFreeSpace period κ m) :
    ⟪p, e⟫_ℝ = 0 := he p hp

theorem testGradient_pairing_zero (κ : ℝ) (m : Vector3) {g e : LiftL2 period}
    (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) (he : e ∈ divergenceFreeSpace period κ m) :
    ⟪g, e⟫_ℝ = 0 :=
  pressure_pairing_zero period κ m (testGradient_mem period κ m hg) he

/-- Orthogonality is the actual weak-divergence integral against every smooth compact test. -/
theorem weak_divergence_test_integral (κ : ℝ) (m : Vector3) {e : LiftL2 period}
    (he : e ∈ divergenceFreeSpace period κ m) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    ∫ x, ⟪liftedGradient period κ m φ x, e x⟫_ℝ ∂liftMeasure period = 0 := by
  have hz := testGradient_pairing_zero period κ m
    (testGradientLp_mem_generators period κ m φ hφ) he
  rw [MeasureTheory.L2.inner_def] at hz
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [testGradientLp_ae period κ m φ hφ] with x hx
  rw [hx]

end EulerLiftedGradientSpace

end

section

/-!
Pointwise bounded coefficient fields act on genuine L² functions.  Their
pointwise positive quadratic bound supplies the Hilbert-space coercivity used
by the lifted pressure solver.  No multiplication operator is assumed.
-/


namespace EulerLiftedPressure

open MeasureTheory InnerProductSpace EulerCoerciveProjection EulerLiftedGradientSpace
open scoped ENNReal NNReal

section Multiplication

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coefficientApply_memLp (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    MemLp (fun x => A x (f x)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := (C : ℝ))
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable f))
  · exact Filter.Eventually.of_forall fun x =>
      ((A x).le_opNorm (f x)).trans
        (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

/-- Pointwise bounded coefficient application represented as an L² element. -/
def coefficientApply (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) : Lp V 2 μ :=
  (coefficientApply_memLp A hA C hbound f).toLp (fun x => A x (f x))

theorem coefficientApply_ae (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    coefficientApply A hA C hbound f =ᵐ[μ] fun x => A x (f x) :=
  (coefficientApply_memLp A hA C hbound f).coeFn_toLp

/-- The linear map induced by pointwise coefficient multiplication. -/
def coefficientLinearMap (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 μ →ₗ[ℝ] Lp V 2 μ where
  toFun := coefficientApply A hA C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coefficientApply_ae A hA C hbound (f + g),
      coefficientApply_ae A hA C hbound f, coefficientApply_ae A hA C hbound g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (coefficientApply A hA C hbound f) (coefficientApply A hA C hbound g)]
      with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp only [Pi.add_apply] at hx₄ hx₅
    rw [hx₁, hx₅, hx₂, hx₃, hx₄, map_add]
  map_smul' r f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [coefficientApply_ae A hA C hbound (r • f),
      coefficientApply_ae A hA C hbound f, Lp.coeFn_smul r f,
      Lp.coeFn_smul r (coefficientApply A hA C hbound f)] with x hx₁ hx₂ hx₃ hx₄
    simp only [Pi.smul_apply] at hx₃ hx₄
    rw [hx₁, hx₄, hx₂, hx₃, map_smul]

theorem coefficientApply_norm_le (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    ‖coefficientApply A hA C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coefficientApply_ae A hA C hbound f] with x hx
  rw [hx]
  exact ((A x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

/-- The bounded operator induced by the actual coefficient field. -/
def coefficientOperator (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  (coefficientLinearMap A hA C hbound).mkContinuous C
    (coefficientApply_norm_le A hA C hbound)

theorem coefficientOperator_ae (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    coefficientOperator A hA C hbound f =ᵐ[μ] fun x => A x (f x) :=
  coefficientApply_ae A hA C hbound f

theorem coefficientOperator_norm_le (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) :
    ‖coefficientOperator A hA C hbound‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    (coefficientApply_norm_le A hA C hbound)

/-- Pointwise coercivity yields the actual integral L² coercivity. -/
theorem coefficientOperator_coercive (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : Lp V 2 μ) :
    c * ‖f‖ ^ 2 ≤ ⟪coefficientOperator A hA C hbound f, f⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner f f).const_mul c)
    (L2.integrable_inner (coefficientOperator A hA C hbound f) f)
  filter_upwards [coefficientOperator_ae A hA C hbound f] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
  exact hpositive x (f x)

theorem coefficientOperator_comp_apply (A B : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (C D : ℝ≥0) (hA_bound : ∀ x, ‖A x‖ ≤ C) (hB_bound : ∀ x, ‖B x‖ ≤ D)
    (hAB : ∀ x v, A x (B x v) = v) (f : Lp V 2 μ) :
    coefficientOperator A hA C hA_bound (coefficientOperator B hB D hB_bound f) = f := by
  apply Lp.ext
  filter_upwards [coefficientOperator_ae A hA C hA_bound
      (coefficientOperator B hB D hB_bound f),
    coefficientOperator_ae B hB D hB_bound f] with x hx₁ hx₂
  rw [hx₁, hx₂, hAB]

/-- Pointwise symmetry gives symmetry of the actual L² multiplication operator. -/
theorem coefficientOperator_inner_swap (A : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C)
    (hsym : ∀ x v w, ⟪A x v, w⟫_ℝ = ⟪v, A x w⟫_ℝ) (f g : Lp V 2 μ) :
    ⟪coefficientOperator A hA C hbound f, g⟫_ℝ =
      ⟪f, coefficientOperator A hA C hbound g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae A hA C hbound f,
    coefficientOperator_ae A hA C hbound g] with x hx₁ hx₂
  rw [hx₁, hx₂, hsym]

end Multiplication

section LiftedSolver

variable (period : ℝ) [Fact (0 < period)]



/-- Exact metric-pressure cancellation for pointwise inverse symmetric coefficient fields. -/
theorem metric_pressure_cancellation (κ : ℝ) (m : Vector3)
    (K G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period))
    (hG : AEStronglyMeasurable G (liftMeasure period))
    (C D : ℝ≥0) (hK_bound : ∀ x, ‖K x‖ ≤ C) (hG_bound : ∀ x, ‖G x‖ ≤ D)
    (hK_sym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hKG : ∀ x v, K x (G x v) = v) {e p : LiftL2 period}
    (he : e ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m) :
    ⟪coefficientOperator K hK C hK_bound e,
      coefficientOperator G hG D hG_bound p⟫_ℝ = 0 := by
  rw [coefficientOperator_inner_swap K hK C hK_bound hK_sym,
    coefficientOperator_comp_apply K G hK hG C D hK_bound hG_bound hKG]
  rw [real_inner_comm]
  exact pressure_pairing_zero period κ m hp he

end LiftedSolver

end EulerLiftedPressure

end

section

/-!
Transport integration by parts on the actual lifted cylinder.  Compactly
supported smooth energy fields are tested against the concrete weak-divergence
condition; boundary terms are eliminated by that proved weak formulation.
-/


namespace EulerMetricTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A field pulled back to real covering coordinates centered at a cylinder point. -/
def localFieldLift {W : Type*} (f : LiftDomain period → W) (x : LiftDomain period) :
    LiftTangent → W := fun h => f (x.1 + h.1, x.2 + (h.2 : AddCircle period))

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [Fact (0 < period)] [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_cover (f : LiftDomain period → W) (z : LiftTangent) :
    localFieldLift period f (coveringMap period z) =
      fun h => localFieldLift period f 0 (z + h) := by
  funext h
  simp [localFieldLift, coveringMap]

omit [Fact (0 < period)] in
theorem fderiv_localFieldLift_cover (f : LiftDomain period → W) (z : LiftTangent) :
    fderiv ℝ (localFieldLift period f (coveringMap period z)) 0 =
      fderiv ℝ (localFieldLift period f 0) z := by
  rw [localFieldLift_cover, fderiv_comp_add_left, add_zero]

omit [Fact (0 < period)] in
theorem smoothField_continuous (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) : Continuous f := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have heq : f ∘ coveringMap period = localFieldLift period f 0 := by
    funext z
    simp [localFieldLift, coveringMap]
  rw [heq]
  exact (hf 0).continuous

omit [Fact (0 < period)] in
theorem localFDeriv_continuous (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    Continuous (fun x => fderiv ℝ (localFieldLift period f x) 0) := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have heq : (fun x => fderiv ℝ (localFieldLift period f x) 0) ∘ coveringMap period =
      fderiv ℝ (localFieldLift period f 0) := by
    funext z
    exact fderiv_localFieldLift_cover period f z
  rw [heq]
  exact (hf 0).continuous_fderiv (by simp)

end Fields

/-- The covering-space direction corresponding to one lifted gradient component. -/
def coordinateDirection (κ : ℝ) (m : Vector3) (i : Fin 3) : LiftTangent :=
  (κ • EuclideanSpace.single i 1, m i)

/-- The actual four dimensional transport vector associated with a lifted velocity. -/
def transportDirection (κ : ℝ) (m v : Vector3) : LiftTangent :=
  (κ • v, ⟪m, v⟫_ℝ)

/-- The vector of a scalar differential evaluated on the lifted coordinate directions. -/
def vectorOfLinear (κ : ℝ) (m : Vector3) (L : LiftTangent →L[ℝ] ℝ) : Vector3 :=
  WithLp.toLp 2 fun i => L (coordinateDirection κ m i)

theorem coordinateDirections_sum (κ : ℝ) (m v : Vector3) :
    ∑ i : Fin 3, v i • coordinateDirection κ m i = transportDirection κ m v := by
  have hrepr : ∑ i : Fin 3, v i • EuclideanSpace.single i 1 = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  apply Prod.ext
  · change (∑ i : Fin 3, v i • coordinateDirection κ m i).1 = κ • v
    calc
      (∑ i : Fin 3, v i • coordinateDirection κ m i).1 =
          ∑ i : Fin 3, v i • (κ • EuclideanSpace.single i 1) := by
            simp [Prod.fst_sum, coordinateDirection]
      _ = κ • ∑ i : Fin 3, v i • EuclideanSpace.single i 1 := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_comm _ _ _
      _ = κ • v := by rw [hrepr]
  · change (∑ i : Fin 3, v i • coordinateDirection κ m i).2 = ⟪m, v⟫_ℝ
    simp [Prod.snd_sum, coordinateDirection, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm]

theorem vectorOfLinear_inner (κ : ℝ) (m v : Vector3) (L : LiftTangent →L[ℝ] ℝ) :
    ⟪vectorOfLinear κ m L, v⟫_ℝ = L (transportDirection κ m v) := by
  rw [← coordinateDirections_sum κ m v, map_sum]
  simp [vectorOfLinear, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    map_smul, smul_eq_mul]

omit [Fact (0 < period)] in
theorem liftedGradient_eq_vectorOfLinear (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (x : LiftDomain period) :
    liftedGradient period κ m φ x =
      vectorOfLinear κ m (fderiv ℝ (localLift period φ x) 0) := by
  apply PiLp.ext
  intro i
  have hd : coordinateDirection κ m i =
      κ • (EuclideanSpace.single i 1, (0 : ℝ)) + m i • ((0 : Vector3), (1 : ℝ)) := by
    ext <;> simp [coordinateDirection]
  change κ * (fderiv ℝ (localLift period φ x) 0) (EuclideanSpace.single i 1, 0) +
      m i * (fderiv ℝ (localLift period φ x) 0) (0, 1) =
    (fderiv ℝ (localLift period φ x) 0) (coordinateDirection κ m i)
  rw [hd, map_add, map_smul, map_smul]
  rfl

/-- The pointwise quadratic metric energy of a vector field. -/
def metricEnergy (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) : ℝ :=
  (1 / 2 : ℝ) * ⟪K x (e x), e x⟫_ℝ

omit [Fact (0 < period)] in
theorem metricEnergy_compact (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (he : HasCompactSupport e) :
    HasCompactSupport (metricEnergy period K e) := by
  apply he.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  simp [Function.mem_support, metricEnergy, hx]

omit [Fact (0 < period)] in
theorem metricEnergy_smooth (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localLift period (metricEnergy period K e) x) := by
  exact contDiff_const.mul (((hK x).clm_apply (he x)).inner ℝ (he x))

omit [Fact (0 < period)] in
theorem metricEnergy_fderiv (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (x : LiftDomain period) (v : LiftTangent) :
    fderiv ℝ (localLift period (metricEnergy period K e) x) 0 v =
      ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0 v⟫_ℝ +
        (1 / 2 : ℝ) *
          ⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ := by
  have hdK := ((hK x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hde := ((he x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hd := (((hdK.clm_apply hde).inner ℝ hde).const_mul (1 / 2 : ℝ)).fderiv
  have heq := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L v) hd
  dsimp [localFieldLift] at heq
  change fderiv ℝ (localLift period (metricEnergy period K e) x) 0 v = _ at heq
  rw [heq]
  simp only [smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.flip_apply, add_zero, inner_add_left]
  have hs : ⟪K x (fderiv ℝ (localFieldLift period e x) 0 v), e x⟫_ℝ =
      ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0 v⟫_ℝ := by
    rw [hsym]
    exact real_inner_comm _ _
  rw [hs]
  ring

omit [Fact (0 < period)] in
theorem metricEnergy_gradient_transport (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (x : LiftDomain period) (z : Vector3) :
    ⟪liftedGradient period κ m (metricEnergy period K e) x, z⟫_ℝ =
      ⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m z)⟫_ℝ +
      (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m z)) (e x), e x⟫_ℝ := by
  rw [liftedGradient_eq_vectorOfLinear, vectorOfLinear_inner]
  exact metricEnergy_fderiv period K e hK he hsym x _

theorem metric_transport_zero (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m) :
    ∫ x, (⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ +
      (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ∂liftMeasure period = 0 := by
  have htest := weak_divergence_test_integral period κ m hz (metricEnergy period K e)
    ⟨metricEnergy_compact period K e hec, metricEnergy_smooth period K e hK he⟩
  convert htest using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    (metricEnergy_gradient_transport period κ m K e hK he hsym x (z x)).symm

/-- The compact vector coefficient whose pairing with velocity is the metric transport term. -/
def transportFlux (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) : Vector3 :=
  vectorOfLinear κ m ((innerSL ℝ (K x (e x))).comp
    (fderiv ℝ (localFieldLift period e x) 0))

omit [Fact (0 < period)] in
theorem transportFlux_inner (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) (z : Vector3) :
    ⟪transportFlux period κ m K e x, z⟫_ℝ =
      ⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m z)⟫_ℝ := by
  rw [transportFlux, vectorOfLinear_inner]
  rfl

omit [Fact (0 < period)] in
theorem transportFlux_continuous (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) :
    Continuous (transportFlux period κ m K e) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact ((smoothField_continuous period K hK).clm_apply
    (smoothField_continuous period e he)).inner
      ((localFDeriv_continuous period e he).clm_apply continuous_const)

omit [Fact (0 < period)] in
theorem transportFlux_compact (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (he : HasCompactSupport e) :
    HasCompactSupport (transportFlux period κ m K e) := by
  apply he.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  apply PiLp.ext
  intro i
  simp [transportFlux, vectorOfLinear, hx]

theorem compact_pairing_integrable (f : LiftDomain period → Vector3)
    (hf : Continuous f) (hfc : HasCompactSupport f) (z : LiftL2 period) :
    Integrable (fun x => ⟪f x, z x⟫_ℝ) (liftMeasure period) := by
  have hlp : MemLp f 2 (liftMeasure period) := hf.memLp_of_hasCompactSupport hfc
  apply (L2.integrable_inner (hlp.toLp f) z).congr
  filter_upwards [hlp.coeFn_toLp] with x hx
  rw [hx]

theorem metric_transport_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) (z : LiftL2 period) :
    Integrable (fun x => ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ)
      (liftMeasure period) := by
  simpa only [transportFlux_inner] using
    compact_pairing_integrable period (transportFlux period κ m K e)
      (transportFlux_continuous period κ m K e hK he)
      (transportFlux_compact period κ m K e hec) z

theorem metric_transport_by_parts (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m) :
    (∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ
      ∂liftMeasure period) =
    -(∫ x, (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ ∂liftMeasure period) := by
  have ht := metric_transport_integrable period κ m K e hec hK he z
  have hg := compact_pairing_integrable period
    (liftedGradient period κ m (metricEnergy period K e))
    (liftedGradient_continuous period κ m (metricEnergy period K e)
      (metricEnergy_smooth period K e hK he))
    (liftedGradient_hasCompactSupport period κ m (metricEnergy period K e)
      (metricEnergy_compact period K e hec)) z
  simp only [metricEnergy_gradient_transport period κ m K e hK he hsym] at hg
  have hq : Integrable (fun x => (1 / 2 : ℝ) *
      ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period) := by
    convert hg.sub ht using 1
    funext x
    simp
  have hzint := metric_transport_zero period κ m K e hec hK he hsym hz
  rw [integral_add ht hq] at hzint
  exact eq_neg_of_add_eq_zero_left hzint

theorem transportDirection_norm_le (κ : ℝ) (m v : Vector3) :
    ‖transportDirection κ m v‖ ≤ (|κ| + ‖m‖) * ‖v‖ := by
  rw [transportDirection, Prod.norm_mk, norm_smul, Real.norm_eq_abs]
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg m))
      (norm_nonneg v)
  · exact (norm_inner_le_norm m v).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg κ)) (norm_nonneg v))

theorem metric_transport_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C B : ℝ≥0)
    (hDK : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ C)
    (hb : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    |∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ
      ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * C * B * ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
  rw [metric_transport_by_parts period κ m K e hec hK he hsym hz, abs_neg]
  have heLp : MemLp e 2 (liftMeasure period) :=
    (smoothField_continuous period e he).memLp_of_hasCompactSupport hec
  have heint := heLp.norm.integrable_sq
  have hbound := norm_integral_le_of_norm_le
    (heint.const_mul ((1 / 2 : ℝ) * C * B)) (f := fun x => (1 / 2 : ℝ) *
      ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ?_
  · simpa only [Real.norm_eq_abs, integral_const_mul] using hbound
  filter_upwards [hb] with x hx
  have hL : ‖fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))‖ ≤ (C : ℝ) * B :=
    ((fderiv ℝ (localFieldLift period K x) 0).le_opNorm _).trans
      (mul_le_mul (hDK x) hx (norm_nonneg _) C.coe_nonneg)
  have hLe : ‖(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x)‖ ≤ (C : ℝ) * B * ‖e x‖ :=
    ((fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ‖ := by
          rw [norm_mul]
          norm_num
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((C : ℝ) * B * ‖e x‖) * ‖e x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hLe (norm_nonneg _)) (by norm_num)
    _ = _ := by ring


end EulerMetricTransport

end

section

/-!
Actual directional differentiation of transport and coefficient multiplication.
The commutator is derived by the chain rule and symmetry of second derivatives,
rather than postulated as a recurrence on a norm sequence.
-/


namespace EulerTransportDerivatives

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal NNReal Topology

section Euclidean

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual Fréchet directional derivative along a constant vector. -/
def directionalDerivative (a : V) (f : V → W) (x : V) : W := fderiv ℝ f x a

/-- Differentiation of a field in the direction of a variable transport field. -/
def transport (b : V → V) (f : V → W) (x : V) : W := fderiv ℝ f x (b x)

theorem directionalDerivative_smooth (a : V) (f : V → W) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalDerivative a f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const


theorem directional_transport_commutator (a : V) (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (x : V) :
    directionalDerivative a (transport b f) x =
      transport b (directionalDerivative a f) x +
        fderiv ℝ f x (directionalDerivative a b x) := by
  have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp)) x).hasFDerivAt
  have hdb := (hb.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hdT := congrArg (fun L : V →L[ℝ] W => L a) (hdf.clm_apply hdb).fderiv
  have hdA := congrArg (fun L : V →L[ℝ] W => L (b x))
    (hdf.clm_apply (hasFDerivAt_const a x)).fderiv
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) a (b x)
  change fderiv ℝ (transport b f) x a = _ at hdT
  change fderiv ℝ (directionalDerivative a f) x (b x) = _ at hdA
  change fderiv ℝ (transport b f) x a =
    fderiv ℝ (directionalDerivative a f) x (b x) + fderiv ℝ f x (fderiv ℝ b x a)
  rw [hdT, hdA]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add]
  rw [hs]
  exact add_comm _ _


end Euclidean

variable (period : ℝ)

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Directional differentiation in the cylinder covering coordinates. -/
def fieldDerivative (a : LiftTangent) (f : LiftDomain period → W)
    (x : LiftDomain period) : W := fderiv ℝ (localFieldLift period f x) 0 a


omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_shift (f : LiftDomain period → W) (x : LiftDomain period)
    (h : LiftTangent) :
    localFieldLift period f (x.1 + h.1, x.2 + (h.2 : AddCircle period)) =
      fun u => localFieldLift period f x (h + u) := by
  funext u
  simp [localFieldLift, add_assoc]

theorem fderiv_localFieldLift_shift (f : LiftDomain period → W) (x : LiftDomain period)
    (h : LiftTangent) :
    fderiv ℝ (localFieldLift period f
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) 0 =
      fderiv ℝ (localFieldLift period f x) h := by
  rw [localFieldLift_shift, fderiv_comp_add_left, add_zero]

theorem localFieldLift_fieldDerivative (a : LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldDerivative period a f) x =
      directionalDerivative a (localFieldLift period f x) := by
  funext h
  exact congrArg (fun L : LiftTangent →L[ℝ] W => L a)
    (fderiv_localFieldLift_shift period f x h)


theorem fieldDerivative_smooth (a : LiftTangent) (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldDerivative period a f) x) := by
  rw [localFieldLift_fieldDerivative]
  exact directionalDerivative_smooth a _ (hf x)




end Fields

end EulerTransportDerivatives

end

section

/-!
Spatial pressure regularity in the genuine lifted L² space.  Coefficient
translations are actual pointwise translations, and pressure translation
covariance follows from the uniquely constructed projected equation.
-/


namespace EulerPressureSpatialRegularity

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerCoerciveProjection EulerInverseRegularity EulerMetricTransport EulerTransportDerivatives
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

section CoefficientDifferentiation

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coefficientOperator_remainder_norm
    (A B D : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hD : AEStronglyMeasurable D μ) (CA CB CD R : ℝ≥0)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hBb : ∀ x, ‖B x‖ ≤ CB) (hDb : ∀ x, ‖D x‖ ≤ CD)
    (t : ℝ) (hR : ∀ x, ‖A x - B x - t • D x‖ ≤ R) :
    ‖coefficientOperator A hA CA hAb - coefficientOperator B hB CB hBb -
      t • coefficientOperator D hD CD hDb‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ R.coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  let a := coefficientOperator A hA CA hAb f
  let b := coefficientOperator B hB CB hBb f
  let d := coefficientOperator D hD CD hDb f
  filter_upwards [coefficientOperator_ae A hA CA hAb f,
    coefficientOperator_ae B hB CB hBb f, coefficientOperator_ae D hD CD hDb f,
    Lp.coeFn_sub a b, Lp.coeFn_smul t d, Lp.coeFn_sub (a - b) (t • d)]
    with x ha hb hd hab htd hsub
  change ‖((a - b) - t • d) x‖ ≤ (R : ℝ) * ‖f x‖
  simp only [Pi.sub_apply, Pi.smul_apply] at hab htd hsub
  rw [hsub, hab, htd]
  change ‖a x - b x - t • d x‖ ≤ _
  rw [ha, hb, hd]
  change ‖(A x - B x - t • D x) (f x)‖ ≤ _
  exact ((A x - B x - t • D x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (hR x) (norm_nonneg _))

theorem uniform_derivative_remainder {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f f' : ℝ → W) (hf : ∀ s, HasDerivAt f (f' s) s) (L : ℝ≥0)
    (hL : ∀ s, ‖f' s - f' 0‖ ≤ L * |s|) (t : ℝ) :
    ‖f t - f 0 - t • f' 0‖ ≤ L * |t| ^ 2 := by
  have hd : ∀ s, HasDerivAt (fun u => f u - u • f' 0) (f' s - f' 0) s := by
    intro s
    convert (hf s).sub ((hasDerivAt_id s).smul_const (f' 0)) using 1
    · rfl
    · simp
  have hb : ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖f' s - f' 0‖ ≤ (L : ℝ) * |t| := by
    intro s hs
    exact (hL s).trans (mul_le_mul_of_nonneg_left
      (by simpa using Set.abs_sub_left_of_mem_uIcc hs) L.coe_nonneg)
  have hm := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, sub_zero, Real.norm_eq_abs] at hm
  calc
    ‖f t - f 0 - t • f' 0‖ = ‖f t - t • f' 0 - f 0‖ := by congr 1; abel
    _ ≤ (L : ℝ) * |t| * |t| := hm
    _ = _ := by ring

theorem coefficientOperator_hasDerivAt
    (A A' : ℝ → α → V →L[ℝ] V)
    (hA : ∀ t, AEStronglyMeasurable (A t) μ)
    (hA' : AEStronglyMeasurable (A' 0) μ)
    (C D L : ℝ≥0) (hAb : ∀ t x, ‖A t x‖ ≤ C) (hDb : ∀ x, ‖A' 0 x‖ ≤ D)
    (hder : ∀ t x, HasDerivAt (fun s => A s x) (A' t x) t)
    (hLip : ∀ t x, ‖A' t x - A' 0 x‖ ≤ L * |t|) :
    HasDerivAt (fun t => coefficientOperator (A t) (hA t) C (hAb t))
      (coefficientOperator (A' 0) hA' D hDb) 0 := by
  apply (hasDerivAt_iff_tendsto
    (f := fun t => coefficientOperator (A t) (hA t) C (hAb t))
    (f' := coefficientOperator (A' 0) hA' D hDb) (x := (0 : ℝ))).mpr
  apply squeeze_zero
  · intro t
    positivity
  · intro t
    let R : ℝ≥0 := ⟨(L : ℝ) * |t| ^ 2, mul_nonneg L.coe_nonneg (sq_nonneg _)⟩
    have hr := coefficientOperator_remainder_norm (A t) (A 0) (A' 0)
      (hA t) (hA 0) hA' C C D R
      (hAb t) (hAb 0) hDb t
      (fun x => uniform_derivative_remainder (fun s => A s x) (fun s => A' s x)
        (fun s => hder s x) L (fun s => hLip s x) t)
    change ‖coefficientOperator (A t) (hA t) C (hAb t) -
      coefficientOperator (A 0) (hA 0) C (hAb 0) -
      t • coefficientOperator (A' 0) hA' D hDb‖ ≤ (L : ℝ) * |t| ^ 2 at hr
    simp only [sub_zero]
    calc
      _ ≤ ‖t‖⁻¹ * ((L : ℝ) * |t| ^ 2) :=
        mul_le_mul_of_nonneg_left hr (inv_nonneg.2 (norm_nonneg _))
      _ ≤ (L : ℝ) * |t| := by
        by_cases ht : t = 0
        · simp [ht]
        · rw [Real.norm_eq_abs]
          have ha : |t| ≠ 0 := abs_ne_zero.mpr ht
          field_simp
          exact le_rfl
  · simpa only [Pi.mul_def, abs_zero, mul_zero] using
      (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

end CoefficientDifferentiation

theorem directionalDerivative_line_lipschitz
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (hf : ContDiff ℝ ∞ f) (M : ℝ≥0)
    (hDD : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (a : V) (t : ℝ) :
    ‖fderiv ℝ f (t • a) a - fderiv ℝ f 0 a‖ ≤
      (M : ℝ) * ‖a‖ ^ 2 * |t| := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => fderiv ℝ f (u • a) a)
      ((fderiv ℝ (fderiv ℝ f) (s • a) a) a) s := by
    intro s
    have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp)) (s • a)).hasFDerivAt
    have hline := hdf.comp_hasDerivAt s ((hasDerivAt_id s).smul_const a)
    simpa using hline.clm_apply (hasDerivAt_const s a)
  have hb : ∀ s ∈ (Set.univ : Set ℝ),
      ‖(fderiv ℝ (fderiv ℝ f) (s • a) a) a‖ ≤ (M : ℝ) * ‖a‖ ^ 2 := by
    intro s _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (s • a) a‖ * ‖a‖ :=
        (fderiv ℝ (fderiv ℝ f) (s • a) a).le_opNorm a
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) (s • a)‖ * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          ((fderiv ℝ (fderiv ℝ f) (s • a)).le_opNorm a) (norm_nonneg _)
      _ ≤ ((M : ℝ) * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hDD _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hm := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [zero_smul, sub_zero, Real.norm_eq_abs] using hm

section LiftedTranslation

variable (period : ℝ) [Fact (0 < period)]

/-- Pointwise coefficient translation on the actual cylinder. -/
def translatedCoefficient (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (x : LiftDomain period) := A (x + a)

theorem translatedCoefficient_measurable (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period)) :
    AEStronglyMeasurable (translatedCoefficient period a A) (liftMeasure period) :=
  hA.comp_measurePreserving (measurePreserving_translation period a)

/-- The one-parameter spatial/angular translation determined by a covering-space direction. -/
def translationPath (a : LiftTangent) (t : ℝ) : LiftDomain period :=
  coveringMap period (t • a)

omit [Fact (0 < period)] in
@[simp]
theorem translationPath_zero (a : LiftTangent) : translationPath period a 0 = 0 := by
  simp [translationPath, coveringMap]

/-- The actual directional derivative of the translated coefficient field. -/
def translatedCoefficientDerivative (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (t : ℝ) (x : LiftDomain period) :=
  fderiv ℝ (localFieldLift period A x) (t • a) a

omit [Fact (0 < period)] in
theorem translatedCoefficient_path (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (t : ℝ) (x : LiftDomain period) :
    translatedCoefficient period (translationPath period a t) A x =
      localFieldLift period A x (t • a) := rfl

omit [Fact (0 < period)] in
theorem translatedCoefficient_hasDerivAt (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) (t : ℝ) (x : LiftDomain period) :
    HasDerivAt (fun s => translatedCoefficient period (translationPath period a s) A x)
      (translatedCoefficientDerivative period a A t x) t := by
  have hd := (((hA x).differentiable (by simp)) (t • a)).hasFDerivAt
  simpa only [translatedCoefficient_path, translatedCoefficientDerivative, one_smul,
    Function.comp_def, id_eq] using
    hd.comp_hasDerivAt t ((hasDerivAt_id t).smul_const a)

theorem translatedCoefficientDerivative_measurable (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) :
    AEStronglyMeasurable (translatedCoefficientDerivative period a A 0) (liftMeasure period) := by
  have hc := (localFDeriv_continuous period A hA).clm_apply (g := fun _ => a) continuous_const
  change AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period A x) (0 • a) a)
    (liftMeasure period)
  simpa only [zero_smul] using hc.aestronglyMeasurable (μ := liftMeasure period)

omit [Fact (0 < period)] in
theorem translatedCoefficientDerivative_bound (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (D : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D) (x : LiftDomain period) :
    ‖translatedCoefficientDerivative period a A 0 x‖ ≤ (D : ℝ) * ‖a‖ := by
  simp only [translatedCoefficientDerivative, zero_smul]
  exact ((fderiv ℝ (localFieldLift period A x) 0).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))

omit [Fact (0 < period)] in
theorem translatedCoefficientDerivative_lipschitz (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) (M : ℝ≥0)
    (hDD : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (t : ℝ) (x : LiftDomain period) :
    ‖translatedCoefficientDerivative period a A t x -
      translatedCoefficientDerivative period a A 0 x‖ ≤ (M : ℝ) * ‖a‖ ^ 2 * |t| := by
  simpa only [translatedCoefficientDerivative, zero_smul] using
    directionalDerivative_line_lipschitz (localFieldLift period A x) (hA x) M (hDD x) a t

theorem coefficientOperator_translation (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (f : LiftL2 period) :
    translation period a (coefficientOperator A hA C hAb f) =
      coefficientOperator (translatedCoefficient period a A)
        (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a))
        (translation period a f) := by
  apply Lp.ext
  filter_upwards [translation_ae period a (coefficientOperator A hA C hAb f),
    (measurePreserving_translation period a).quasiMeasurePreserving.ae
      (coefficientOperator_ae A hA C hAb f),
    coefficientOperator_ae (translatedCoefficient period a A)
      (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a))
      (translation period a f), translation_ae period a f] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₂, hx₃, hx₄]
  rfl

/-- The concrete coercive pressure solution, viewed in ambient L². -/
def liftedPressure (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) : LiftL2 period :=
  pressureSolver (gradientSpace period κ m) (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f

theorem liftedPressure_mem (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    liftedPressure period κ m A hA C hAb c hc hpos f ∈ gradientSpace period κ m :=
  (pressureSolver (gradientSpace period κ m) (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f).property

theorem liftedPressure_equation (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    gradientProjection period κ m
      (coefficientOperator A hA C hAb (liftedPressure period κ m A hA C hAb c hc hpos f)) =
      gradientProjection period κ m f := by
  exact congrArg Subtype.val (pressureSolver_equation (gradientSpace period κ m)
    (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f)

theorem liftedPressure_unique (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f p : LiftL2 period)
    (hp : p ∈ gradientSpace period κ m)
    (heq : gradientProjection period κ m (coefficientOperator A hA C hAb p) =
      gradientProjection period κ m f) :
    p = liftedPressure period κ m A hA C hAb c hc hpos f := by
  let S := gradientSpace period κ m
  let G := coefficientOperator A hA C hAb
  let hG := coefficientOperator_coercive A hA C hAb c hpos
  have hsub : (⟨p, hp⟩ : S) = pressureSolver S G c hc hG f := by
    apply (coerciveEquiv (projectedOperator S G) c hc
      (projectedOperator_coercive S G c hG)).injective
    simp only [coerciveEquiv_apply]
    change S.orthogonalProjectionOnto (G p) =
      S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : LiftL2 period))
    rw [pressureSolver_equation]
    exact Subtype.ext heq
  exact congrArg Subtype.val hsub

theorem liftedPressure_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    translation period a (liftedPressure period κ m A hA C hAb c hc hpos f) =
      liftedPressure period κ m (translatedCoefficient period a A)
        (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a)) c hc
        (fun x v => hpos (x + a) v) (translation period a f) := by
  apply liftedPressure_unique period κ m (translatedCoefficient period a A)
    (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a)) c hc
    (fun x v => hpos (x + a) v)
  · exact gradientSpace_translation_mem period κ m a
      (liftedPressure_mem period κ m A hA C hAb c hc hpos f)
  · rw [← coefficientOperator_translation period a A hA C hAb,
      ← gradientProjection_translation,
      liftedPressure_equation, gradientProjection_translation]

theorem liftedPressure_hasDerivAt (κ : ℝ) (m : Vector3)
    (A A' : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ t, AEStronglyMeasurable (A t) (liftMeasure period))
    (hA' : AEStronglyMeasurable (A' 0) (liftMeasure period))
    (C D L : ℝ≥0) (hAb : ∀ t x, ‖A t x‖ ≤ C) (hDb : ∀ x, ‖A' 0 x‖ ≤ D)
    (hder : ∀ t x, HasDerivAt (fun s => A s x) (A' t x) t)
    (hLip : ∀ t x, ‖A' t x - A' 0 x‖ ≤ L * |t|)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪A t x v, v⟫_ℝ)
    (f : ℝ → LiftL2 period) (f' : LiftL2 period) (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => liftedPressure period κ m (A t) (hA t) C (hAb t) c hc
      (hpos t) (f t))
      (liftedPressure period κ m (A 0) (hA 0) C (hAb 0) c hc (hpos 0)
        (f' - coefficientOperator (A' 0) hA' D hDb
          (liftedPressure period κ m (A 0) (hA 0) C (hAb 0) c hc (hpos 0) (f 0)))) 0 := by
  let S := gradientSpace period κ m
  let G := fun t => coefficientOperator (A t) (hA t) C (hAb t)
  let G' := coefficientOperator (A' 0) hA' D hDb
  have hG : ∀ t u, c * ‖u‖ ^ 2 ≤ ⟪G t u, u⟫_ℝ :=
    fun t => coefficientOperator_coercive (A t) (hA t) C (hAb t) c (hpos t)
  have hGder : HasDerivAt G G' 0 :=
    coefficientOperator_hasDerivAt A A' hA hA' C D L hAb hDb hder hLip
  have hsol := hasDerivAt_coerciveSolution (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t))
    (fun t => S.orthogonalProjectionOnto (f t)) 0 (projectedOperator S G')
    (S.orthogonalProjectionOnto f')
    (hasDerivAt_projectedOperator S G 0 G' hGder)
    (S.orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt 0 hf)
  have hval := S.subtypeL.hasFDerivAt.comp_hasDerivAt 0 hsol
  convert hval using 1
  · rfl
  · rfl
  · rfl
  · simp [liftedPressure, pressureSolver, projectedInverse, projectedOperator,
      S, G, G', ContinuousLinearMap.comp_apply, map_sub]

theorem pressure_translation_hasDerivAt (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (liftedPressure period κ m A hA C hAb c hc hpos f))
      (liftedPressure period κ m A hA C hAb c hc hpos
        (f' - coefficientOperator (translatedCoefficientDerivative period a A 0)
          (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
          (fun x => translatedCoefficientDerivative_bound period a A D hDA x)
          (liftedPressure period κ m A hA C hAb c hc hpos f))) 0 := by
  let At := fun t => translatedCoefficient period (translationPath period a t) A
  let Ad := translatedCoefficientDerivative period a A
  have hAt : ∀ t, AEStronglyMeasurable (At t) (liftMeasure period) :=
    fun t => translatedCoefficient_measurable period (translationPath period a t) A hA
  have hAtb : ∀ t x, ‖At t x‖ ≤ C := fun t x => hAb (x + translationPath period a t)
  have hAtpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪At t x v, v⟫_ℝ :=
    fun t x v => hpos (x + translationPath period a t) v
  have hAdb : ∀ x, ‖Ad 0 x‖ ≤ (D * ‖a‖₊ : ℝ≥0) :=
    fun x => translatedCoefficientDerivative_bound period a A D hDA x
  have hAdL : ∀ t x, ‖Ad t x - Ad 0 x‖ ≤ (M * ‖a‖₊ ^ 2 : ℝ≥0) * |t| := by
    intro t x
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      translatedCoefficientDerivative_lipschitz period a A hAs M hDDA t x
  have hsol := liftedPressure_hasDerivAt period κ m At Ad hAt
    (translatedCoefficientDerivative_measurable period a A hAs)
    C (D * ‖a‖₊) (M * ‖a‖₊ ^ 2) hAtb hAdb
    (translatedCoefficient_hasDerivAt period a A hAs) hAdL c hc hAtpos
    (fun t => translation period (translationPath period a t) f) f' hf
  have hcov : (fun t => liftedPressure period κ m (At t) (hAt t) C (hAtb t)
      c hc (hAtpos t) (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t)
        (liftedPressure period κ m A hA C hAb c hc hpos f) := by
    funext t
    exact (liftedPressure_translation period κ m (translationPath period a t)
      A hA C hAb c hc hpos f).symm
  rw [hcov] at hsol
  have hzero : At 0 = A := by
    funext x
    simp [At, translatedCoefficient]
  simpa only [hzero, translationPath_zero, translation_zero] using hsol


end LiftedTranslation

end EulerPressureSpatialRegularity

end

section

/-!
Translation derivatives and actual weak derivatives on the lifted cylinder.
Smooth compact test fields are realized in L², and their translation orbits
are differentiated in the strong L² topology.
-/


namespace EulerLiftedWeakDerivative

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerPressureSpatialRegularity
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace


variable (period : ℝ) [Fact (0 < period)]

section FieldCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The full derivative of a field in covering coordinates, evaluated at the center. -/
def fieldFDeriv (f : LiftDomain period → W) (x : LiftDomain period) : LiftTangent →L[ℝ] W :=
  fderiv ℝ (localFieldLift period f x) 0

omit [Fact (0 < period)] in
theorem localFieldLift_fieldFDeriv (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldFDeriv period f) x = fderiv ℝ (localFieldLift period f x) := by
  funext h
  exact fderiv_localFieldLift_shift period f x h

omit [Fact (0 < period)] in
theorem fieldFDeriv_smooth (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldFDeriv period f) x) := by
  rw [localFieldLift_fieldFDeriv]
  exact (hf x).fderiv_right (by simp)

omit [Fact (0 < period)] in
theorem fieldFDeriv_zero_outside (f : LiftDomain period → W) (x : LiftDomain period)
    (hx : x ∉ tsupport f) : fieldFDeriv period f x = 0 := by
  have hc : Continuous (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) :=
    (continuous_const.add continuous_fst).prodMk
      (continuous_const.add ((AddCircle.continuous_mk' period).comp continuous_snd))
  have ht : Filter.Tendsto (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : LiftTangent)
  have hz : localFieldLift period f x =ᶠ[𝓝 0] (fun _ : LiftTangent => (0 : W)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto ht
  change fderiv ℝ (localFieldLift period f x) 0 = 0
  rw [hz.fderiv_eq]
  simp

omit [Fact (0 < period)] in
theorem fieldFDeriv_compact (f : LiftDomain period → W) (hf : HasCompactSupport f) :
    HasCompactSupport (fieldFDeriv period f) :=
  HasCompactSupport.intro hf (fieldFDeriv_zero_outside period f)

omit [Fact (0 < period)] in
theorem fieldDerivative_compact (a : LiftTangent) (f : LiftDomain period → W)
    (hf : HasCompactSupport f) : HasCompactSupport (fieldDerivative period a f) := by
  apply (fieldFDeriv_compact period f hf).mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  change fieldFDeriv period f x a = 0
  rw [hx]
  rfl

theorem fieldDerivative_memLp (a : LiftTangent) (f : LiftDomain period → W)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    MemLp (fieldDerivative period a f) 2 (liftMeasure period) :=
  (smoothField_continuous period _ (fieldDerivative_smooth period a f hf)).memLp_of_hasCompactSupport
    (fieldDerivative_compact period a f hfc)

omit [Fact (0 < period)] in
theorem compact_smooth_second_derivative_bound (f : LiftDomain period → W)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∃ M : ℝ≥0, ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period f x)) y‖ ≤ M := by
  let F := fieldFDeriv period (fieldFDeriv period f)
  have hFc : HasCompactSupport F := fieldFDeriv_compact period _ (fieldFDeriv_compact period f hfc)
  have hFs : ∀ x, ContDiff ℝ ∞ (localFieldLift period F x) :=
    fieldFDeriv_smooth period _ (fieldFDeriv_smooth period f hf)
  have hFb := (hFc.isCompact_range (smoothField_continuous period F hFs)).isBounded
  obtain ⟨M, hM, hbound⟩ := hFb.exists_pos_norm_le
  refine ⟨⟨M, hM.le⟩, fun x y => ?_⟩
  have hBy := hbound (F (x.1 + y.1, x.2 + (y.2 : AddCircle period))) (Set.mem_range_self _)
  change ‖fderiv ℝ (localFieldLift period (fieldFDeriv period f)
    (x.1 + y.1, x.2 + (y.2 : AddCircle period))) 0‖ ≤ M at hBy
  rw [fderiv_localFieldLift_shift, localFieldLift_fieldFDeriv] at hBy
  exact hBy

end FieldCalculus

omit [Fact (0 < period)] in
theorem translationPath_continuous (a : LiftTangent) : Continuous (translationPath period a) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp
    (continuous_id.smul continuous_const)

omit [Fact (0 < period)] in
theorem translationPath_add (a : LiftTangent) (s t : ℝ) :
    translationPath period a (s + t) = translationPath period a s + translationPath period a t := by
  simp [translationPath, coveringMap, add_smul]

omit [Fact (0 < period)] in
theorem translationPath_neg (a : LiftTangent) (t : ℝ) :
    translationPath period a (-t) = -translationPath period a t := by
  simp [translationPath, coveringMap]

theorem translation_pairing (a : LiftDomain period) (f g : LiftL2 period) :
    ⟪translation period a f, g⟫_ℝ = ⟪f, translation period (-a) g⟫_ℝ := by
  have hi := (translation period a).inner_map_map f (translation period (-a) g)
  simpa only [translation_add, add_neg_cancel, translation_zero] using hi

omit [Fact (0 < period)] in
theorem compact_translation_support (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f) :
    ∃ K : Set (LiftDomain period), IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x ∉ K, f (x + translationPath period a t) = 0 := by
  let K := (fun p : LiftDomain period × ℝ => p.1 - translationPath period a p.2) ''
    (tsupport f ×ˢ Set.Icc (-1 : ℝ) 1)
  have hK : IsCompact K := (hfc.isCompact.prod isCompact_Icc).image
    (continuous_fst.sub ((translationPath_continuous period a).comp continuous_snd))
  refine ⟨K, hK, ?_, ?_⟩
  · intro x hx
    refine ⟨(x, 0), ⟨hx, by constructor <;> norm_num⟩, ?_⟩
    simp
  · intro t ht x hx
    by_contra hn
    apply hx
    refine ⟨(x + translationPath period a t, t),
      ⟨subset_tsupport f (Function.mem_support.mpr hn), abs_le.mp ht⟩, ?_⟩
    simp

/-- The actual L² element represented by a smooth compact vector field. -/
def smoothFieldLp (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) : LiftL2 period :=
  ((smoothField_continuous period f hf).memLp_of_hasCompactSupport hfc).toLp f

theorem smoothFieldLp_ae (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    smoothFieldLp period f hfc hf =ᵐ[liftMeasure period] f :=
  ((smoothField_continuous period f hf).memLp_of_hasCompactSupport hfc).coeFn_toLp

/-- The L² element represented by the actual directional derivative of a compact test field. -/
def derivativeFieldLp (a : LiftTangent) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    LiftL2 period := (fieldDerivative_memLp period a f hfc hf).toLp (fieldDerivative period a f)

theorem derivativeFieldLp_ae (a : LiftTangent) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    derivativeFieldLp period a f hfc hf =ᵐ[liftMeasure period] fieldDerivative period a f :=
  (fieldDerivative_memLp period a f hfc hf).coeFn_toLp

omit [Fact (0 < period)] in
theorem field_translation_remainder (a : LiftTangent)
    (f : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (M : ℝ≥0)
    (hDD : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period f x)) y‖ ≤ M)
    (t : ℝ) (x : LiftDomain period) :
    ‖f (x + translationPath period a t) - f x - t • fieldDerivative period a f x‖ ≤
      (M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2 := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => localFieldLift period f x (u • a))
      (fderiv ℝ (localFieldLift period f x) (s • a) a) s := by
    intro s
    have hF := (((hf x).differentiable (by simp)) (s • a)).hasFDerivAt
    convert hF.comp_hasDerivAt s ((hasDerivAt_id s).smul_const a) using 1 <;>
      first | rfl | simp
  have hr := uniform_derivative_remainder
    (fun s => localFieldLift period f x (s • a))
    (fun s => fderiv ℝ (localFieldLift period f x) (s • a) a) hd (M * ‖a‖₊ ^ 2)
    (fun s => by simpa only [zero_smul, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      directionalDerivative_line_lipschitz (localFieldLift period f x) (hf x) M (hDD x) a s) t
  change ‖f (x.1 + (t • a).1, x.2 + ((t • a).2 : AddCircle period)) - f x -
    t • fieldDerivative period a f x‖ ≤ _
  simpa only [localFieldLift, zero_smul, Prod.fst_zero, Prod.snd_zero,
    AddCircle.coe_zero, add_zero, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
    fieldDerivative] using hr

theorem smoothFieldLp_translation_hasDerivAt (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (smoothFieldLp period f hfc hf)) (derivativeFieldLp period a f hfc hf) 0 := by
  obtain ⟨M, hM⟩ := compact_smooth_second_derivative_bound period f hfc hf
  obtain ⟨K, hK, hKf, hKshift⟩ := compact_translation_support period a f hfc
  let f₀ := smoothFieldLp period f hfc hf
  let df := derivativeFieldLp period a f hfc hf
  let χ : Lp ℝ 2 (liftMeasure period) :=
    indicatorConstLp 2 hK.isClosed.measurableSet hK.measure_ne_top (1 : ℝ)
  have hR : ∀ t : ℝ, |t| ≤ 1 →
      ‖translation period (translationPath period a t) f₀ - f₀ - t • df‖ ≤
        ((M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2) * ‖χ‖ := by
    intro t ht
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [translation_ae period (translationPath period a t) f₀,
      (measurePreserving_translation period (translationPath period a t)).quasiMeasurePreserving.ae
        (smoothFieldLp_ae period f hfc hf), smoothFieldLp_ae period f hfc hf,
      derivativeFieldLp_ae period a f hfc hf,
      Lp.coeFn_sub (translation period (translationPath period a t) f₀) f₀,
      Lp.coeFn_smul t df,
      Lp.coeFn_sub (translation period (translationPath period a t) f₀ - f₀) (t • df),
      (indicatorConstLp_coeFn (p := 2) (hs := hK.isClosed.measurableSet)
        (hμs := hK.measure_ne_top) (c := (1 : ℝ)))]
      with x hτ hfx hf₀ hdf hsub hsmul hrem hχ
    simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hrem
    rw [hrem, hsub, hsmul, hτ, hfx, hf₀, hdf]
    change ‖f (x + translationPath period a t) - f x -
      t • fieldDerivative period a f x‖ ≤ (M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2 * ‖χ x‖
    change χ x = _ at hχ
    rw [hχ]
    by_cases hx : x ∈ K
    · simpa only [Set.indicator_of_mem hx, norm_one, mul_one] using
        field_translation_remainder period a f hf M hM t x
    · have hxf : x ∉ tsupport f := fun h => hx (hKf h)
      have hdz : fieldDerivative period a f x = 0 := by
        change fieldFDeriv period f x a = 0
        rw [fieldFDeriv_zero_outside period f x hxf]
        rfl
      rw [hKshift t ht x hx, image_eq_zero_of_notMem_tsupport hxf, hdz,
        Set.indicator_of_notMem hx]
      simp
  apply (hasDerivAt_iff_tendsto
    (f := fun t => translation period (translationPath period a t) f₀)
    (f' := df) (x := (0 : ℝ))).mpr
  simp only [translationPath_zero, translation_zero, sub_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => by positivity
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
    have ht' : |t| ≤ 1 := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht.le
    calc
      _ ≤ ‖t‖⁻¹ * (((M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2) * ‖χ‖) :=
        mul_le_mul_of_nonneg_left (hR t ht') (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ((M : ℝ) * ‖a‖ ^ 2 * ‖χ‖) * |t| := by
        by_cases ht0 : t = 0
        · simp [ht0]
        · rw [Real.norm_eq_abs]
          have hta : |t| ≠ 0 := abs_ne_zero.mpr ht0
          field_simp
          ring_nf
          exact le_rfl
  · simpa only [Pi.mul_def, abs_zero, mul_zero] using
      (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

theorem translation_derivative_pairing (a : LiftTangent) (f f' g g' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (hg : HasDerivAt (fun t => translation period (translationPath period a t) g) g' 0) :
    ⟪f', g⟫_ℝ = -⟪f, g'⟫_ℝ := by
  have hleft : HasDerivAt (fun t =>
      ⟪translation period (translationPath period a t) f, g⟫_ℝ) ⟪f', g⟫_ℝ 0 := by
    simpa only [translationPath_zero, translation_zero, inner_zero_right, zero_add] using
      hf.inner ℝ (hasDerivAt_const (0 : ℝ) g)
  have hneg : HasDerivAt (fun t => translation period (translationPath period a (-t)) g) (-g') 0 := by
    convert hg.scomp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg) (by simp) using 1 <;>
      first | rfl | simp
  have hright : HasDerivAt (fun t =>
      ⟪f, translation period (translationPath period a (-t)) g⟫_ℝ) (-⟪f, g'⟫_ℝ) 0 := by
    simpa only [inner_neg_right, inner_zero_left, add_zero] using
      (hasDerivAt_const (0 : ℝ) f).inner ℝ hneg
  have heq : (fun t => ⟪translation period (translationPath period a t) f, g⟫_ℝ) =
      fun t => ⟪f, translation period (translationPath period a (-t)) g⟫_ℝ := by
    funext t
    simpa only [translationPath_neg] using
      translation_pairing period (translationPath period a t) f g
  rw [heq] at hleft
  exact hleft.unique hright

/-- A strong L² translation derivative is the actual distributional derivative. -/
theorem strong_translation_derivative_weak (a : LiftTangent) (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (φ : LiftDomain period → Vector3) (hφc : HasCompactSupport φ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) :
    (∫ x, ⟪f' x, φ x⟫_ℝ ∂liftMeasure period) =
      -(∫ x, ⟪f x, fieldDerivative period a φ x⟫_ℝ ∂liftMeasure period) := by
  have hp := translation_derivative_pairing period a f f'
    (smoothFieldLp period φ hφc hφ) (derivativeFieldLp period a φ hφc hφ) hf
    (smoothFieldLp_translation_hasDerivAt period a φ hφc hφ)
  calc
    _ = ⟪f', smoothFieldLp period φ hφc hφ⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [smoothFieldLp_ae period φ hφc hφ] with x hx
      rw [hx]
    _ = -⟪f, derivativeFieldLp period a φ hφc hφ⟫_ℝ := hp
    _ = _ := by
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [derivativeFieldLp_ae period a φ hφc hφ] with x hx
      rw [hx]




end EulerLiftedWeakDerivative

end

section

/-!
Finite spatial Sobolev jets in the actual lifted L² space.  Jet entries are
actual strong translation derivatives and therefore genuine weak derivatives.
The pressure jet is constructed, rather than assumed, from coercivity and
pointwise smooth coefficient data.
-/


namespace EulerSpatialSobolevInverse


open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerTransportDerivatives EulerPressureSpatialRegularity
  EulerLiftedWeakDerivative EulerCoerciveProjection
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace


variable (period : ℝ) [Fact (0 < period)]

/-- A bounded smooth pointwise coefficient field with quantitative first and second derivatives. -/
structure SmoothCoefficient where
  /-- The actual pointwise coefficient matrix field. -/
  coefficient : LiftDomain period → Vector3 →L[ℝ] Vector3
  smooth : ∀ x, ContDiff ℝ ∞ (localFieldLift period coefficient x)
  /-- A uniform operator-norm bound for the coefficient field. -/
  bound : ℝ≥0
  norm_bound : ∀ x, ‖coefficient x‖ ≤ bound
  /-- A uniform norm bound for the first covering derivative. -/
  firstBound : ℝ≥0
  norm_first : ∀ x, ‖fderiv ℝ (localFieldLift period coefficient x) 0‖ ≤ firstBound
  /-- A uniform norm bound for the second covering derivative. -/
  secondBound : ℝ≥0
  norm_second : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period coefficient x)) y‖ ≤ secondBound

namespace SmoothCoefficient

variable {period}

theorem measurable (A : SmoothCoefficient period) :
    AEStronglyMeasurable A.coefficient (liftMeasure period) :=
  (smoothField_continuous period A.coefficient A.smooth).aestronglyMeasurable

/-- Actual multiplication by the coefficient field in L². -/
def operator (A : SmoothCoefficient period) : LiftL2 period →L[ℝ] LiftL2 period :=
  coefficientOperator A.coefficient A.measurable A.bound A.norm_bound

theorem operator_ae (A : SmoothCoefficient period) (f : LiftL2 period) :
    A.operator f =ᵐ[liftMeasure period] fun x => A.coefficient x (f x) :=
  coefficientOperator_ae A.coefficient A.measurable A.bound A.norm_bound f

theorem operator_norm (A : SmoothCoefficient period) (f : LiftL2 period) :
    ‖A.operator f‖ ≤ A.bound * ‖f‖ :=
  coefficientApply_norm_le A.coefficient A.measurable A.bound A.norm_bound f

/-- The Lax–Milgram pressure associated with this actual coefficient. -/
def pressure (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (f : LiftL2 period) : LiftL2 period :=
  liftedPressure period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f

theorem pressure_norm (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (f : LiftL2 period) :
    ‖A.pressure κ m c hc hpos f‖ ≤ c⁻¹ * ‖f‖ :=
  pressureSolver_apply_norm_le (gradientSpace period κ m) A.operator c hc
    (coefficientOperator_coercive A.coefficient A.measurable A.bound A.norm_bound c hpos) f

theorem derivative_operator_eq (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x) :
    coefficientOperator (translatedCoefficientDerivative period a A.coefficient 0)
      (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
      (A.firstBound * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
        A.norm_first x) = B.operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coefficientOperator_ae (translatedCoefficientDerivative period a A.coefficient 0)
      (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
      (A.firstBound * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
        A.norm_first x) f, B.operator_ae f] with x hx hy
  rw [hx, hy, hB]
  simp [translatedCoefficientDerivative, fieldDerivative]

theorem operator_translation_hasDerivAt (A : SmoothCoefficient period) (a : LiftTangent) :
    HasDerivAt (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a t)))
      (coefficientOperator (translatedCoefficientDerivative period a A.coefficient 0)
        (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
        (A.firstBound * ‖a‖₊)
        (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
          A.norm_first x)) 0 := by
  apply coefficientOperator_hasDerivAt
    (A' := translatedCoefficientDerivative period a A.coefficient)
    (L := A.secondBound * ‖a‖₊ ^ 2)
  · exact translatedCoefficient_hasDerivAt period a A.coefficient A.smooth
  · intro t x
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      translatedCoefficientDerivative_lipschitz period a A.coefficient A.smooth
        A.secondBound A.norm_second t x

theorem product_hasDerivAt (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t) (A.operator f))
      (A.operator f' + B.operator f) 0 := by
  have hprod := (A.operator_translation_hasDerivAt a).clm_apply hf
  rw [A.derivative_operator_eq B a hB] at hprod
  have hcov : (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a t))
      (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t) (A.operator f) := by
    funext t
    exact (coefficientOperator_translation period (translationPath period a t) A.coefficient
      A.measurable A.bound A.norm_bound f).symm
  rw [hcov] at hprod
  have hop0 : coefficientOperator
      (translatedCoefficient period (translationPath period a 0) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a 0)) = A.operator := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [coefficientOperator_ae
      (translatedCoefficient period (translationPath period a 0) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a 0)) u,
      A.operator_ae u] with x hx hy
    rw [hx, hy]
    simp [translatedCoefficient]
  rw [hop0] at hprod
  simp only [translationPath_zero, translation_zero] at hprod
  convert hprod using 1 <;> first | rfl | exact add_comm _ _

theorem pressure_hasDerivAt (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (A.pressure κ m c hc hpos f))
      (A.pressure κ m c hc hpos (f' - B.operator (A.pressure κ m c hc hpos f))) 0 := by
  have hp := pressure_translation_hasDerivAt period κ m a A.coefficient A.measurable A.smooth
    A.bound A.firstBound A.secondBound A.norm_bound A.norm_first A.norm_second c hc hpos f f' hf
  rwa [A.derivative_operator_eq B a hB] at hp

end SmoothCoefficient

/-- A finite tree of actual strong translation derivatives of an L² field. -/
inductive SpatialJet (directions : Fin 4 → LiftTangent) : ℕ → LiftL2 period → Type
  | zero (f : LiftL2 period) : SpatialJet directions 0 f
  | succ {n : ℕ} {f : LiftL2 period} (derivatives : Fin 4 → LiftL2 period)
      (lower : ∀ i, SpatialJet directions n (derivatives i))
      (hasDeriv : ∀ i, HasDerivAt (fun t => translation period
        (translationPath period (directions i) t) f) (derivatives i) 0) :
      SpatialJet directions (n + 1) f

/-- A finite tree of actual coefficient derivatives, with bounded smooth data at every node. -/
inductive CoefficientJet (directions : Fin 4 → LiftTangent) : ℕ → SmoothCoefficient period → Type
  | zero (A : SmoothCoefficient period) : CoefficientJet directions 0 A
  | succ {n : ℕ} {A : SmoothCoefficient period} (derivatives : Fin 4 → SmoothCoefficient period)
      (lower : ∀ i, CoefficientJet directions n (derivatives i))
      (derivative_eq : ∀ i x, (derivatives i).coefficient x =
        fieldDerivative period (directions i) A.coefficient x) :
      CoefficientJet directions (n + 1) A

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Forget the highest derivative order of a genuine spatial jet. -/
def truncate {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions (n + 1) f) :
    SpatialJet period directions n f :=
  match n, J with
  | 0, _ => .zero f
  | _n + 1, .succ df lower hd => .succ df (fun i => (lower i).truncate) hd

/-- The sum of all derivative-word L² norms represented by the jet. -/
def sobolevNorm {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) : ℝ :=
  match J with
  | .zero f => ‖f‖
  | .succ _ lower _ => ‖f‖ + ∑ i, (lower i).sobolevNorm

theorem nonneg {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) :
    0 ≤ J.sobolevNorm := by
  induction J with
  | zero f => exact norm_nonneg f
  | succ df lower hd ih =>
    exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => ih i)

theorem value_norm_le {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) :
    ‖f‖ ≤ J.sobolevNorm := by
  cases J with
  | zero => exact le_rfl
  | succ df lower hd =>
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (lower i).nonneg)

theorem truncate_norm_le {n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions (n + 1) f) :
    J.truncate.sobolevNorm ≤ J.sobolevNorm := by
  induction n generalizing f with
  | zero => exact J.value_norm_le
  | succ n ih =>
    cases J with
    | succ df lower hd =>
      exact add_le_add_right (Finset.sum_le_sum fun i _ => ih (lower i)) ‖f‖

theorem lower_norm_le {n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions n (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) (i : Fin 4) :
    (lower i).sobolevNorm ≤ (SpatialJet.succ df lower hd).sobolevNorm := by
  exact (Finset.single_le_sum (fun j _ => (lower j).nonneg) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (norm_nonneg f))

/-- Addition preserves the actual strong derivatives recorded in a spatial jet. -/
def add {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    SpatialJet period directions n (f + g) :=
  match J, K with
  | .zero _, .zero _ => .zero (f + g)
  | .succ df Jd hJ, .succ dg Kd hK =>
    .succ (fun i => df i + dg i) (fun i => (Jd i).add (Kd i)) (fun i => by
      convert (hJ i).add (hK i) using 1 <;> first | rfl | (funext t; simp))

/-- Subtraction preserves the actual strong derivatives recorded in a spatial jet. -/
def sub {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    SpatialJet period directions n (f - g) :=
  match J, K with
  | .zero _, .zero _ => .zero (f - g)
  | .succ df Jd hJ, .succ dg Kd hK =>
    .succ (fun i => df i - dg i) (fun i => (Jd i).sub (Kd i)) (fun i => by
      convert (hJ i).sub (hK i) using 1 <;> first | rfl | (funext t; simp))

theorem add_norm_le {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    (J.add K).sobolevNorm ≤ J.sobolevNorm + K.sobolevNorm := by
  induction n generalizing f g with
  | zero => cases J; cases K; exact norm_add_le _ _
  | succ n ih =>
    cases J with
    | succ df Jd hJ =>
      cases K with
      | succ dg Kd hK =>
        change ‖f + g‖ + ∑ i, ((Jd i).add (Kd i)).sobolevNorm ≤ _
        calc
          _ ≤ (‖f‖ + ‖g‖) + ∑ i, ((Jd i).sobolevNorm + (Kd i).sobolevNorm) :=
            add_le_add (norm_add_le _ _) (Finset.sum_le_sum fun i _ => ih (Jd i) (Kd i))
          _ = _ := by simp only [Finset.sum_add_distrib, sobolevNorm]; ring

theorem sub_norm_le {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    (J.sub K).sobolevNorm ≤ J.sobolevNorm + K.sobolevNorm := by
  induction n generalizing f g with
  | zero => cases J; cases K; exact norm_sub_le _ _
  | succ n ih =>
    cases J with
    | succ df Jd hJ =>
      cases K with
      | succ dg Kd hK =>
        change ‖f - g‖ + ∑ i, ((Jd i).sub (Kd i)).sobolevNorm ≤ _
        calc
          _ ≤ (‖f‖ + ‖g‖) + ∑ i, ((Jd i).sobolevNorm + (Kd i).sobolevNorm) :=
            add_le_add (norm_sub_le _ _) (Finset.sum_le_sum fun i _ => ih (Jd i) (Kd i))
          _ = _ := by simp only [Finset.sum_add_distrib, sobolevNorm]; ring

end SpatialJet

namespace CoefficientJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Forget the highest derivative level while retaining the original coefficient. -/
def truncate {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions (n + 1) A) : CoefficientJet period directions n A :=
  match n, J with
  | 0, _ => .zero A
  | _n + 1, .succ dA lower hd => .succ dA (fun i => (lower i).truncate) hd

/-- A finite polynomial bound for multiplication in the jet Sobolev norm. -/
def productConstant {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) : ℝ :=
  match J with
  | .zero A => A.bound
  | .succ dA lower hd => A.bound + ∑ i : Fin 4,
      ((CoefficientJet.succ dA lower hd).truncate.productConstant + (lower i).productConstant)
termination_by n

omit [Fact (0 < period)] in
theorem productConstant_nonneg {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) : 0 ≤ J.productConstant := by
  induction n generalizing A with
  | zero => cases J; rw [productConstant]; exact NNReal.coe_nonneg _
  | succ n ih =>
    cases J with
    | succ dA lower hd =>
      rw [productConstant]
      exact add_nonneg A.bound.coe_nonneg (Finset.sum_nonneg fun i _ =>
        add_nonneg (ih (CoefficientJet.succ dA lower hd).truncate) (ih (lower i)))

end CoefficientJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Construct every finite-order derivative of actual coefficient multiplication. -/
def multiply {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (J : SpatialJet period directions n f) :
    SpatialJet period directions n (A.operator f) :=
  match n, K, J with
  | 0, .zero _, .zero _ => .zero (A.operator f)
  | _n + 1, .succ dA KA hA, .succ df Jf hf =>
    .succ (fun i => A.operator (df i) + (dA i).operator f)
      (fun i => (multiply (CoefficientJet.succ dA KA hA).truncate (Jf i)).add
        (multiply (KA i) (SpatialJet.succ df Jf hf).truncate))
      (fun i => A.product_hasDerivAt (dA i) (directions i) (hA i) f (df i) (hf i))
termination_by n

theorem multiply_norm_le {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (J : SpatialJet period directions n f) :
    (multiply K J).sobolevNorm ≤ K.productConstant * J.sobolevNorm := by
  induction n generalizing A f with
  | zero =>
    cases K; cases J
    simpa only [multiply, sobolevNorm, CoefficientJet.productConstant] using A.operator_norm f
  | succ n ih =>
    cases K with
    | succ dA KA hA =>
      cases J with
      | succ df Jf hf =>
        let K₀ := (CoefficientJet.succ dA KA hA).truncate
        let J₀ := (SpatialJet.succ df Jf hf).truncate
        let N := (SpatialJet.succ df Jf hf).sobolevNorm
        have hlow : J₀.sobolevNorm ≤ N := (SpatialJet.succ df Jf hf).truncate_norm_le
        have hkid : ∀ i, (Jf i).sobolevNorm ≤ N := lower_norm_le df Jf hf
        have hterms : ∀ i,
            ((multiply K₀ (Jf i)).add (multiply (KA i) J₀)).sobolevNorm ≤
              (K₀.productConstant + (KA i).productConstant) * N := by
          intro i
          calc
            _ ≤ (multiply K₀ (Jf i)).sobolevNorm + (multiply (KA i) J₀).sobolevNorm :=
              add_norm_le _ _
            _ ≤ K₀.productConstant * (Jf i).sobolevNorm +
                (KA i).productConstant * J₀.sobolevNorm := add_le_add (ih K₀ (Jf i)) (ih (KA i) J₀)
            _ ≤ K₀.productConstant * N + (KA i).productConstant * N :=
              add_le_add (mul_le_mul_of_nonneg_left (hkid i) K₀.productConstant_nonneg)
                (mul_le_mul_of_nonneg_left hlow (KA i).productConstant_nonneg)
            _ = _ := by ring
        rw [multiply, sobolevNorm]
        change ‖A.operator f‖ + ∑ i,
          ((multiply K₀ (Jf i)).add (multiply (KA i) J₀)).sobolevNorm ≤ _
        calc
          _ ≤ A.bound * N + ∑ i, (K₀.productConstant + (KA i).productConstant) * N :=
            add_le_add ((A.operator_norm f).trans
              (mul_le_mul_of_nonneg_left (SpatialJet.succ df Jf hf).value_norm_le A.bound.coe_nonneg))
              (Finset.sum_le_sum fun i _ => hterms i)
          _ = _ := by
            rw [← Finset.sum_mul, ← add_mul, CoefficientJet.productConstant]

end SpatialJet

namespace CoefficientJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- The explicit finite-order inverse constant obtained from coercivity and coefficient products. -/
def pressureConstant {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) (c : ℝ) : ℝ :=
  match J with
  | .zero _ => c⁻¹
  | .succ dA lower hd => c⁻¹ + ∑ i : Fin 4,
      ((CoefficientJet.succ dA lower hd).truncate.pressureConstant c *
        (1 + (lower i).productConstant *
          (CoefficientJet.succ dA lower hd).truncate.pressureConstant c))
termination_by n

omit [Fact (0 < period)] in
theorem pressureConstant_nonneg {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) (c : ℝ) (hc : 0 < c) :
    0 ≤ J.pressureConstant c := by
  induction n generalizing A with
  | zero => cases J; rw [pressureConstant]; exact inv_nonneg.mpr hc.le
  | succ n ih =>
    cases J with
    | succ dA lower hd =>
      rw [pressureConstant]
      exact add_nonneg (inv_nonneg.mpr hc.le) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (ih (CoefficientJet.succ dA lower hd).truncate)
          (add_nonneg zero_le_one (mul_nonneg (lower i).productConstant_nonneg
            (ih (CoefficientJet.succ dA lower hd).truncate))))

end CoefficientJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Construct a genuine pressure Sobolev jet at every finite order. -/
def solvePressure {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (J : SpatialJet period directions n f) :
    SpatialJet period directions n (A.pressure κ m c hc hpos f) :=
  match n, K, J with
  | 0, .zero _, .zero _ => .zero (A.pressure κ m c hc hpos f)
  | _n + 1, .succ dA KA hA, .succ df Jf hf =>
    let K₀ := (CoefficientJet.succ dA KA hA).truncate
    let J₀ := (SpatialJet.succ df Jf hf).truncate
    let P₀ := solvePressure K₀ κ m c hc hpos J₀
    .succ (fun i => A.pressure κ m c hc hpos
        (df i - (dA i).operator (A.pressure κ m c hc hpos f)))
      (fun i => solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀)))
      (fun i => A.pressure_hasDerivAt (dA i) (directions i) (hA i)
        κ m c hc hpos f (df i) (hf i))
termination_by n

theorem solvePressure_norm_le {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (J : SpatialJet period directions n f) :
    (solvePressure K κ m c hc hpos J).sobolevNorm ≤ K.pressureConstant c * J.sobolevNorm := by
  induction n generalizing A f with
  | zero =>
    cases K; cases J
    simpa only [solvePressure, sobolevNorm, CoefficientJet.pressureConstant] using
      A.pressure_norm κ m c hc hpos f
  | succ n ih =>
    cases K with
    | succ dA KA hA =>
      cases J with
      | succ df Jf hf =>
        let K₀ := (CoefficientJet.succ dA KA hA).truncate
        let J₀ := (SpatialJet.succ df Jf hf).truncate
        let P₀ := solvePressure K₀ κ m c hc hpos J₀
        let N := (SpatialJet.succ df Jf hf).sobolevNorm
        have hlow : J₀.sobolevNorm ≤ N := (SpatialJet.succ df Jf hf).truncate_norm_le
        have hkid : ∀ i, (Jf i).sobolevNorm ≤ N := lower_norm_le df Jf hf
        have hp : P₀.sobolevNorm ≤ K₀.pressureConstant c * N :=
          (ih K₀ hpos J₀).trans
            (mul_le_mul_of_nonneg_left hlow (K₀.pressureConstant_nonneg c hc))
        have hterms : ∀ i,
            (solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀))).sobolevNorm ≤
              (K₀.pressureConstant c * (1 + (KA i).productConstant * K₀.pressureConstant c)) * N := by
          intro i
          calc
            _ ≤ K₀.pressureConstant c * ((Jf i).sub (multiply (KA i) P₀)).sobolevNorm :=
              ih K₀ hpos _
            _ ≤ K₀.pressureConstant c * ((Jf i).sobolevNorm + (multiply (KA i) P₀).sobolevNorm) :=
              mul_le_mul_of_nonneg_left (sub_norm_le _ _) (K₀.pressureConstant_nonneg c hc)
            _ ≤ K₀.pressureConstant c * (N + (KA i).productConstant * P₀.sobolevNorm) :=
              mul_le_mul_of_nonneg_left (add_le_add (hkid i) (multiply_norm_le (KA i) P₀))
                (K₀.pressureConstant_nonneg c hc)
            _ ≤ K₀.pressureConstant c * (N + (KA i).productConstant * (K₀.pressureConstant c * N)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add_right (mul_le_mul_of_nonneg_left hp (KA i).productConstant_nonneg) N)
                (K₀.pressureConstant_nonneg c hc)
            _ = _ := by ring
        rw [solvePressure, sobolevNorm]
        change ‖A.pressure κ m c hc hpos f‖ + ∑ i,
          (solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀))).sobolevNorm ≤ _
        calc
          _ ≤ c⁻¹ * N + ∑ i,
              (K₀.pressureConstant c * (1 + (KA i).productConstant * K₀.pressureConstant c)) * N :=
            add_le_add ((A.pressure_norm κ m c hc hpos f).trans
              (mul_le_mul_of_nonneg_left (SpatialJet.succ df Jf hf).value_norm_le (inv_nonneg.mpr hc.le)))
              (Finset.sum_le_sum fun i _ => hterms i)
          _ = _ := by
            rw [← Finset.sum_mul, ← add_mul, CoefficientJet.pressureConstant]

end SpatialJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- A derivative word, ordered with its head differentiated last; invalid orders return zero. -/
def word {s : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f)
    {n : ℕ} (w : Fin n → Fin 4) : LiftL2 period :=
  match n, J with
  | 0, _ => f
  | _n + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => (lower (w (Fin.last n))).word (Fin.init w)
termination_by s

@[simp]
theorem word_zero {s : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f)
    (w : Fin 0 → Fin 4) : J.word w = f := by rw [word]

@[simp]
theorem word_succ {s n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions s (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) (w : Fin (n + 1) → Fin 4) :
    (SpatialJet.succ df lower hd).word w = (lower (w (Fin.last n))).word (Fin.init w) := by
  rw [word]

theorem word_hasDerivAt {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (hn : n < s) (w : Fin n → Fin 4) (i : Fin 4) :
    HasDerivAt (fun t => translation period (translationPath period (directions i) t) (J.word w))
      (J.word (Fin.cons i w)) 0 := by
  induction n generalizing s f with
  | zero =>
    cases J with
    | zero => omega
    | succ df lower hd => simpa using hd i
  | succ n ih =>
    cases J with
    | zero => omega
    | succ df lower hd =>
      have h := ih (lower (w (Fin.last n))) (by omega) (Fin.init w)
      have hi : Fin.init (n := n + 1) (α := fun _ : Fin (n + 2) => Fin 4)
          (Fin.cons (α := fun _ : Fin (n + 2) => Fin 4) i w) =
          Fin.cons (α := fun _ : Fin (n + 1) => Fin 4) i (Fin.init w) := by
        funext j
        cases j using Fin.cases <;> rfl
      simp only [word_succ, hi]
      convert h using 1
      rfl

/-- Split a coordinate word into its last direction and its initial word. -/
def wordSnocEquiv (n : ℕ) : (Fin (n + 1) → Fin 4) ≃ Fin 4 × (Fin n → Fin 4) where
  toFun w := (w (Fin.last n), Fin.init w)
  invFun v := Fin.snoc v.2 v.1
  left_inv w := Fin.snoc_init_self w
  right_inv v := by simp

/-- The sum over words of positive length is the sum over final directions and initial words. -/
theorem sum_word_succ {s n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions s (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) :
    (∑ w : Fin (n + 1) → Fin 4, ‖(SpatialJet.succ df lower hd).word w‖) =
      ∑ i, ∑ w : Fin n → Fin 4, ‖(lower i).word w‖ := by
  calc
    _ = ∑ v : Fin 4 × (Fin n → Fin 4), ‖(lower v.1).word v.2‖ :=
      Fintype.sum_equiv (wordSnocEquiv n)
        (fun w => ‖(SpatialJet.succ df lower hd).word w‖)
        (fun v => ‖(lower v.1).word v.2‖) (fun _ => by rw [word_succ]; rfl)
    _ = _ := Fintype.sum_prod_type _

/-- The recursive jet norm equals the explicit sum of the norms of all coordinate words. -/
theorem sobolevNorm_eq_sum_words {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) :
    J.sobolevNorm = ∑ n ∈ Finset.range (s + 1), ∑ w : Fin n → Fin 4, ‖J.word w‖ := by
  induction s generalizing f with
  | zero => cases J; simp [sobolevNorm]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      rw [sobolevNorm, Finset.sum_range_succ']
      simp only [word_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, pow_zero, one_smul]
      simp_rw [sum_word_succ]
      rw [Finset.sum_comm]
      simp_rw [← ih]
      exact add_comm _ _

end SpatialJet

end EulerSpatialSobolevInverse

end

section

/-!
The closed lifted gradient space consists of distributionally curl-free
fields.  The proof uses actual compact scalar tests and mixed derivative
symmetry, then passes to the L² closure through continuous inner products.
-/


namespace EulerLiftedCurl

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerPressureSpatialRegularity EulerLiftedWeakDerivative
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Isometric inclusion of a scalar into the first Euclidean component. -/
def scalarEmbedding : ℝ →L[ℝ] Vector3 :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 3) 1)

omit [Fact (0 < period)] in
theorem scalarEmbedding_inner (r s : ℝ) :
    ⟪scalarEmbedding r, scalarEmbedding s⟫_ℝ = r * s := by
  simp [scalarEmbedding, inner_smul_left, inner_smul_right, mul_comm]

omit [Fact (0 < period)] in
theorem fieldDerivative_linear {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    (f : LiftDomain period → V) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (a : LiftTangent) (x : LiftDomain period) :
    fieldDerivative period a (fun y => L (f y)) x = L (fieldDerivative period a f x) := by
  have hd := L.hasFDerivAt.comp (0 : LiftTangent)
    (((hf x).differentiable (by simp)) 0).hasFDerivAt
  have he := congrArg (fun D : LiftTangent →L[ℝ] W => D a) hd.fderiv
  exact he

omit [Fact (0 < period)] in
theorem scalar_embedding_smooth (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fun y => scalarEmbedding (φ y)) x) :=
  scalarEmbedding.contDiff.comp (hφ x)

omit [Fact (0 < period)] in
theorem scalar_embedding_compact (φ : LiftDomain period → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun x => scalarEmbedding (φ x)) := by
  apply hφ.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [hx, map_zero]

/-- Genuine scalar integration by parts on the cylinder in any constant covering direction. -/
theorem scalar_integration_by_parts (a : LiftTangent) (φ ψ : LiftDomain period → ℝ)
    (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    (∫ x, fieldDerivative period a φ x * ψ x ∂liftMeasure period) =
      -(∫ x, φ x * fieldDerivative period a ψ x ∂liftMeasure period) := by
  let F := fun x => scalarEmbedding (φ x)
  let G := fun x => scalarEmbedding (ψ x)
  let hFc := scalar_embedding_compact period φ hφc
  let hGc := scalar_embedding_compact period ψ hψc
  let hFs := scalar_embedding_smooth period φ hφ
  let hGs := scalar_embedding_smooth period ψ hψ
  have hi := strong_translation_derivative_weak period a
    (smoothFieldLp period F hFc hFs) (derivativeFieldLp period a F hFc hFs)
    (smoothFieldLp_translation_hasDerivAt period a F hFc hFs) G hGc hGs
  have hleft : (∫ x, ⟪(derivativeFieldLp period a F hFc hFs) x, G x⟫_ℝ
      ∂liftMeasure period) = ∫ x, fieldDerivative period a φ x * ψ x ∂liftMeasure period := by
    apply integral_congr_ae
    filter_upwards [derivativeFieldLp_ae period a F hFc hFs] with x hx
    rw [hx]
    change ⟪fieldDerivative period a (fun y => scalarEmbedding (φ y)) x,
      scalarEmbedding (ψ x)⟫_ℝ = _
    rw [fieldDerivative_linear period scalarEmbedding φ hφ, scalarEmbedding_inner]
  have hright : (∫ x, ⟪(smoothFieldLp period F hFc hFs) x, fieldDerivative period a G x⟫_ℝ
      ∂liftMeasure period) = ∫ x, φ x * fieldDerivative period a ψ x ∂liftMeasure period := by
    apply integral_congr_ae
    filter_upwards [smoothFieldLp_ae period F hFc hFs] with x hx
    rw [hx]
    change ⟪scalarEmbedding (φ x),
      fieldDerivative period a (fun y => scalarEmbedding (ψ y)) x⟫_ℝ = _
    rw [fieldDerivative_linear period scalarEmbedding ψ hψ, scalarEmbedding_inner]
  rw [hleft, hright] at hi
  exact hi

omit [Fact (0 < period)] in
theorem fieldDerivatives_commute {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (a b : LiftTangent) (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    fieldDerivative period a (fieldDerivative period b f) x =
      fieldDerivative period b (fieldDerivative period a f) x := by
  have h := directional_transport_commutator a (fun _ : LiftTangent => b)
    (localFieldLift period f x) contDiff_const (hf x) 0
  change fderiv ℝ (localFieldLift period (fieldDerivative period b f) x) 0 a =
    fderiv ℝ (localFieldLift period (fieldDerivative period a f) x) 0 b
  rw [localFieldLift_fieldDerivative, localFieldLift_fieldDerivative]
  change fderiv ℝ (directionalDerivative b (localFieldLift period f x)) 0 a =
    fderiv ℝ (directionalDerivative a (localFieldLift period f x)) 0 b +
      fderiv ℝ (localFieldLift period f x) 0 (fderiv ℝ (fun _ : LiftTangent => b) 0 a) at h
  have hc : fderiv ℝ (fun _ : LiftTangent => b) 0 = 0 := by simp
  rw [hc, zero_apply, map_zero, add_zero] at h
  exact h

/-- A compact antisymmetric derivative test field for one lifted curl component. -/
def curlTest (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (x : LiftDomain period) : Vector3 :=
  fieldDerivative period (coordinateDirection κ m j) ψ x • EuclideanSpace.single i 1 -
    fieldDerivative period (coordinateDirection κ m i) ψ x • EuclideanSpace.single j 1

omit [Fact (0 < period)] in
theorem curlTest_smooth (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (curlTest period κ m i j ψ) x) := by
  exact ((fieldDerivative_smooth period _ ψ hψ x).smul contDiff_const).sub
    ((fieldDerivative_smooth period _ ψ hψ x).smul contDiff_const)

omit [Fact (0 < period)] in
theorem curlTest_compact (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (curlTest period κ m i j ψ) := by
  apply HasCompactSupport.intro hψ
  intro x hx
  have hd : ∀ a, fieldDerivative period a ψ x = 0 := by
    intro a
    change fieldFDeriv period ψ x a = 0
    rw [fieldFDeriv_zero_outside period ψ x hx]
    rfl
  simp [curlTest, hd]

omit [Fact (0 < period)] in
theorem vector_curlTest_inner (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (x : LiftDomain period) (v : Vector3) :
    ⟪v, curlTest period κ m i j ψ x⟫_ℝ =
      v i * fieldDerivative period (coordinateDirection κ m j) ψ x -
        v j * fieldDerivative period (coordinateDirection κ m i) ψ x := by
  simp [curlTest, inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]

omit [Fact (0 < period)] in
theorem liftedGradient_component (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (x : LiftDomain period) (i : Fin 3) :
    liftedGradient period κ m φ x i = fieldDerivative period (coordinateDirection κ m i) φ x := by
  rw [liftedGradient_eq_vectorOfLinear]
  rfl

theorem scalar_derivative_product_integrable (a b : LiftTangent)
    (φ ψ : LiftDomain period → ℝ) (hφc : HasCompactSupport φ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    Integrable (fun x => fieldDerivative period a φ x * fieldDerivative period b ψ x)
      (liftMeasure period) := by
  have hc := (smoothField_continuous period _ (fieldDerivative_smooth period a φ hφ)).mul
    (smoothField_continuous period _ (fieldDerivative_smooth period b ψ hψ))
  exact hc.integrable_of_hasCompactSupport (fieldDerivative_compact period a φ hφc).mul_right

theorem test_gradient_curl_integral (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (φ ψ : LiftDomain period → ℝ) (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    ∫ x, ⟪liftedGradient period κ m φ x, curlTest period κ m i j ψ x⟫_ℝ
      ∂liftMeasure period = 0 := by
  simp only [vector_curlTest_inner, liftedGradient_component]
  rw [integral_sub (scalar_derivative_product_integrable period _ _ φ ψ hφc hφ hψ)
    (scalar_derivative_product_integrable period _ _ φ ψ hφc hφ hψ)]
  have hi := scalar_integration_by_parts period (coordinateDirection κ m i) φ
    (fieldDerivative period (coordinateDirection κ m j) ψ) hφc
    (fieldDerivative_compact period _ ψ hψc) hφ (fieldDerivative_smooth period _ ψ hψ)
  have hj := scalar_integration_by_parts period (coordinateDirection κ m j) φ
    (fieldDerivative period (coordinateDirection κ m i) ψ) hφc
    (fieldDerivative_compact period _ ψ hψc) hφ (fieldDerivative_smooth period _ ψ hψ)
  rw [hi, hj]
  have heq : (fun x => φ x * fieldDerivative period (coordinateDirection κ m i)
      (fieldDerivative period (coordinateDirection κ m j) ψ) x) =
      fun x => φ x * fieldDerivative period (coordinateDirection κ m j)
        (fieldDerivative period (coordinateDirection κ m i) ψ) x := by
    funext x
    rw [fieldDerivatives_commute period _ _ ψ hψ]
  rw [heq, sub_self]

/-- The L² realization of an actual compact lifted curl test. -/
def curlTestLp (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψc : HasCompactSupport ψ) (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    LiftL2 period := smoothFieldLp period (curlTest period κ m i j ψ)
      (curlTest_compact period κ m i j ψ hψc) (curlTest_smooth period κ m i j ψ hψ)

theorem curlTestLp_ae (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψc : HasCompactSupport ψ) (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    curlTestLp period κ m i j ψ hψc hψ =ᵐ[liftMeasure period] curlTest period κ m i j ψ :=
  smoothFieldLp_ae period (curlTest period κ m i j ψ)
    (curlTest_compact period κ m i j ψ hψc) (curlTest_smooth period κ m i j ψ hψ)

theorem generator_curl_pairing (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    {g : LiftL2 period} (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) :
    ⟪g, curlTestLp period κ m i j ψ hψc hψ⟫_ℝ = 0 := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  rw [L2.inner_def]
  rw [← test_gradient_curl_integral period κ m i j φ ψ hφ.1 hψc hφ.2 hψ]
  apply integral_congr_ae
  filter_upwards [hgφ, curlTestLp_ae period κ m i j ψ hψc hψ] with x hx hy
  rw [hx, hy]

theorem gradient_curl_pairing (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    {p : LiftL2 period} (hp : p ∈ gradientSpace period κ m) :
    ⟪p, curlTestLp period κ m i j ψ hψc hψ⟫_ℝ = 0 := by
  let L := innerSL ℝ (curlTestLp period κ m i j ψ hψc hψ)
  have hspan : Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro g hg
    change ⟪curlTestLp period κ m i j ψ hψc hψ, g⟫_ℝ = 0
    rw [real_inner_comm]
    exact generator_curl_pairing period κ m i j ψ hψc hψ hg
  have hclosed : IsClosed (L.ker : Set (LiftL2 period)) := L.isClosed_ker
  have hclosure : gradientSpace period κ m ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan hclosed
  have h := hclosure hp
  change ⟪curlTestLp period κ m i j ψ hψc hψ, p⟫_ℝ = 0 at h
  rwa [real_inner_comm] at h

/-- Every field in the closed lifted gradient space has zero distributional lifted curl. -/
theorem gradientSpace_weak_curl_zero (κ : ℝ) (m : Vector3)
    {p : LiftL2 period} (hp : p ∈ gradientSpace period κ m)
    (i j : Fin 3) (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    ∫ x, ((p x) i * fieldDerivative period (coordinateDirection κ m j) ψ x -
      (p x) j * fieldDerivative period (coordinateDirection κ m i) ψ x)
      ∂liftMeasure period = 0 := by
  have h := gradient_curl_pairing period κ m i j ψ hψc hψ hp
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [curlTestLp_ae period κ m i j ψ hψc hψ] with x hx
  rw [hx, vector_curlTest_inner]

end EulerLiftedCurl

end

section

/-! Expanding spatial cutoffs and transport cancellation for noncompact fields on the cylinder. -/


namespace EulerNoncompactTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A fixed smooth spatial cutoff equal to one on the unit ball. -/
def spatialBump : ContDiffBump (0 : Vector3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The reciprocal spatial scale in the expanding cutoff sequence. -/
def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

/-- Smooth expanding cutoffs on the cylinder; the angular variable is unchanged. -/
def spatialCutoff (n : ℕ) (x : LiftDomain period) : ℝ :=
  spatialBump (cutoffScale n • x.1)

omit [Fact (0 < period)] in
theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  exact inv_pos.mpr (by positivity)

omit [Fact (0 < period)] in
theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (by have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

omit [Fact (0 < period)] in
theorem cutoffScale_tendsto : Filter.Tendsto cutoffScale Filter.atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

omit [Fact (0 < period)] in
theorem spatialCutoff_bounds (n : ℕ) (x : LiftDomain period) :
    0 ≤ spatialCutoff period n x ∧ spatialCutoff period n x ≤ 1 :=
  ⟨spatialBump.nonneg, spatialBump.le_one⟩

omit [Fact (0 < period)] in
theorem spatialCutoff_smooth (n : ℕ) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localLift period (spatialCutoff period n) x) := by
  exact spatialBump.contDiff.comp ((contDiff_const.add contDiff_fst).const_smul _)

omit [Fact (0 < period)] in
theorem spatialCutoff_tendsto (x : LiftDomain period) :
    Filter.Tendsto (fun n => spatialCutoff period n x) Filter.atTop (𝓝 1) := by
  have h := spatialBump.continuous.continuousAt.tendsto.comp
    (cutoffScale_tendsto.smul_const x.1)
  have hb : spatialBump 0 = 1 := spatialBump.one_of_mem_closedBall (by simp [spatialBump])
  convert h using 1 <;> simp [spatialCutoff, hb, Function.comp_def]

theorem spatialCutoff_compact (n : ℕ) : HasCompactSupport (spatialCutoff period n) := by
  apply HasCompactSupport.intro
    ((isCompact_closedBall (0 : Vector3) (2 * ((n : ℝ) + 1))).prod
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle period))))
  intro x hx
  have hnorm : 2 * ((n : ℝ) + 1) < ‖x.1‖ := by
    simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, Set.mem_univ,
      and_true, not_le] using hx
  apply spatialBump.zero_of_le_dist
  change 2 ≤ dist (cutoffScale n • x.1) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
  change 2 ≤ ((n : ℝ) + 1)⁻¹ * ‖x.1‖
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hnorm.le

omit [Fact (0 < period)] in
theorem spatialCutoff_fderiv (n : ℕ) (x : LiftDomain period) (v : LiftTangent) :
    fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v =
      fderiv ℝ spatialBump (cutoffScale n • x.1) (cutoffScale n • v.1) := by
  have hi : HasFDerivAt (fun h : LiftTangent => cutoffScale n • (x.1 + h.1))
      (cutoffScale n • ContinuousLinearMap.fst ℝ Vector3 ℝ) 0 := by
    convert ((ContinuousLinearMap.fst ℝ Vector3 ℝ).hasFDerivAt.const_add x.1).const_smul
      (cutoffScale n) using 1 <;> rfl
  have ho := ((spatialBump.contDiff : ContDiff ℝ ∞ spatialBump).differentiable
    (by simp)).differentiableAt.hasFDerivAt (x := cutoffScale n • (x.1 + (0 : LiftTangent).1))
  have h := ho.comp 0 hi
  have heq := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L v) h.fderiv
  simpa +unfoldPartialApp [spatialCutoff, localLift, Function.comp_def] using heq

omit [Fact (0 < period)] in
/-- The cutoff derivatives have a uniform constant times their reciprocal spatial scale. -/
theorem spatialCutoff_derivative_bound : ∃ M : ℝ, 0 < M ∧ ∀ n x v,
    ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v‖ ≤
      M * cutoffScale n * ‖v‖ := by
  obtain ⟨M, hM, hbound⟩ :=
    ((spatialBump.hasCompactSupport.fderiv ℝ).isCompact_range
      ((spatialBump.contDiff : ContDiff ℝ ∞ spatialBump).continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨M, hM, fun n x v => ?_⟩
  rw [spatialCutoff_fderiv]
  calc
    _ ≤ ‖fderiv ℝ spatialBump (cutoffScale n • x.1)‖ * ‖cutoffScale n • v.1‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * (cutoffScale n * ‖v‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
      exact mul_le_mul (hbound _ (Set.mem_range_self _))
        (mul_le_mul_of_nonneg_left (norm_fst_le v) (cutoffScale_pos n).le)
        (mul_nonneg (cutoffScale_pos n).le (norm_nonneg _)) hM.le
    _ = _ := by ring

omit [Fact (0 < period)] in
theorem spatialCutoff_derivative_tendsto (x : LiftDomain period) (v : LiftTangent) :
    Filter.Tendsto (fun n => fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v)
      Filter.atTop (𝓝 0) := by
  obtain ⟨M, _, hM⟩ := spatialCutoff_derivative_bound period
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hM n x v)
  simpa using (tendsto_const_nhds.mul cutoffScale_tendsto).mul_const (‖v‖ : ℝ)

omit [Fact (0 < period)] in
theorem cutoff_product_transport (κ : ℝ) (m : Vector3) (n : ℕ)
    (φ : LiftDomain period → ℝ) (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x))
    (x : LiftDomain period) (v : Vector3) :
    ⟪liftedGradient period κ m (fun y => spatialCutoff period n y * φ y) x, v⟫_ℝ =
      spatialCutoff period n x * fderiv ℝ (localLift period φ x) 0 (transportDirection κ m v) +
      φ x * fderiv ℝ (localLift period (spatialCutoff period n) x) 0 (transportDirection κ m v) := by
  rw [liftedGradient_eq_vectorOfLinear, vectorOfLinear_inner]
  have hc := ((spatialCutoff_smooth period n x).differentiable (by simp)).differentiableAt.hasFDerivAt
    (x := 0)
  have hf := ((hφ x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have h := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L (transportDirection κ m v))
    (hc.mul hf).fderiv
  simpa +unfoldPartialApp [localLift, Pi.mul_def] using h

/-- Smooth scalar weak-divergence tests extend to integrable noncompact energies. -/
theorem weak_divergence_integral_noncompact (κ : ℝ) (m : Vector3)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (B : ℝ) (_hB : 0 ≤ B) (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (φ : LiftDomain period → ℝ) (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x))
    (hφI : Integrable φ (liftMeasure period))
    (hflux : Integrable (fun x => fderiv ℝ (localLift period φ x) 0
      (transportDirection κ m (z x))) (liftMeasure period)) :
    ∫ x, fderiv ℝ (localLift period φ x) 0 (transportDirection κ m (z x))
      ∂liftMeasure period = 0 := by
  obtain ⟨M, hM, hMb⟩ := spatialCutoff_derivative_bound period
  let C := M * (|κ| + ‖m‖) * B
  let flux := fun x => fderiv ℝ (localLift period φ x) 0 (transportDirection κ m (z x))
  let F := fun n x => ⟪liftedGradient period κ m (fun y => spatialCutoff period n y * φ y) x, z x⟫_ℝ
  have hs : ∀ n x, ContDiff ℝ ∞ (localLift period (fun y => spatialCutoff period n y * φ y) x) :=
    fun n x => (spatialCutoff_smooth period n x).mul (hφ x)
  have hc : ∀ n, HasCompactSupport (fun y => spatialCutoff period n y * φ y) :=
    fun n => (spatialCutoff_compact period n).mul_right
  have hF0 : ∀ n, ∫ x, F n x ∂liftMeasure period = 0 :=
    fun n => weak_divergence_test_integral period κ m hz _ ⟨hc n, hs n⟩
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (liftMeasure period) := by
    intro n
    exact (liftedGradient_continuous period κ m _ (hs n)).aestronglyMeasurable.inner
      (Lp.aestronglyMeasurable z)
  have hbound : ∀ n, ∀ᵐ x ∂liftMeasure period, ‖F n x‖ ≤ ‖flux x‖ + C * ‖φ x‖ := by
    intro n
    filter_upwards [hzB] with x hx
    have hcut := spatialCutoff_bounds period n x
    have hv : ‖transportDirection κ m (z x)‖ ≤ (|κ| + ‖m‖) * B :=
      (transportDirection_norm_le κ m (z x)).trans
        (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
    have hd : ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0
        (transportDirection κ m (z x))‖ ≤ C := by
      calc
        _ ≤ M * cutoffScale n * ‖transportDirection κ m (z x)‖ := hMb n x _
        _ ≤ M * 1 * ((|κ| + ‖m‖) * B) := by
          gcongr
          exact cutoffScale_le_one n
        _ = C := by dsimp [C]; ring
    dsimp [F]
    rw [cutoff_product_transport period κ m n φ hφ]
    calc
      _ ≤ ‖spatialCutoff period n x * flux x‖ +
          ‖φ x * fderiv ℝ (localLift period (spatialCutoff period n) x) 0
            (transportDirection κ m (z x))‖ := norm_add_le _ _
      _ = ‖spatialCutoff period n x‖ * ‖flux x‖ + ‖φ x‖ *
          ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0
            (transportDirection κ m (z x))‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖flux x‖ + ‖φ x‖ * C := by
        gcongr
        simpa only [Real.norm_eq_abs, abs_of_nonneg hcut.1] using hcut.2
      _ = _ := by simp only [Real.norm_eq_abs]; ring
  have hlim : ∀ᵐ x ∂liftMeasure period, Filter.Tendsto (fun n => F n x)
      Filter.atTop (𝓝 (flux x)) := by
    apply Filter.Eventually.of_forall
    intro x
    simp_rw [F, cutoff_product_transport period κ m _ φ hφ]
    convert ((spatialCutoff_tendsto period x).mul_const (flux x)).add
      ((spatialCutoff_derivative_tendsto period x (transportDirection κ m (z x))).const_mul
        (φ x)) using 1
    simp
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖flux x‖ + C * ‖φ x‖)
    hmeas (hflux.norm.add (hφI.norm.const_mul C)) hbound hlim
  have heq : (fun n => ∫ x, F n x ∂liftMeasure period) = fun _ : ℕ => 0 := by
    funext n
    exact hF0 n
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Integration by parts for a noncompact smooth metric energy with integrable terms. -/
theorem metric_transport_noncompact_by_parts (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (B : ℝ) (hB : 0 ≤ B) (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (hE : Integrable (metricEnergy period K e) (liftMeasure period))
    (hT : Integrable (fun x => ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ) (liftMeasure period))
    (hQ : Integrable (fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period)) :
    (∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period) =
    -(∫ x, (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ ∂liftMeasure period) := by
  have hf : Integrable (fun x => fderiv ℝ (localLift period (metricEnergy period K e) x) 0
      (transportDirection κ m (z x))) (liftMeasure period) := by
    simp only [metricEnergy_fderiv period K e hK he hsym]
    exact hT.add hQ
  have hz0 := weak_divergence_integral_noncompact period κ m hz B hB hzB
    (metricEnergy period K e) (metricEnergy_smooth period K e hK he) hE hf
  simp only [metricEnergy_fderiv period K e hK he hsym] at hz0
  rw [integral_add hT hQ] at hz0
  exact eq_neg_of_add_eq_zero_left hz0

theorem aestronglyMeasurable_apply {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : LiftDomain period → V →L[ℝ] W} {u : LiftDomain period → V}
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hu : AEStronglyMeasurable u (liftMeasure period)) :
    AEStronglyMeasurable (fun x => A x (u x)) (liftMeasure period) :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hu)

/-- Bounded metrics have integrable quadratic energy on every actual L² field. -/
theorem metricEnergy_integrable (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period)) (he : MemLp e 2 (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C) :
    Integrable (metricEnergy period K e) (liftMeasure period) := by
  apply (he.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * C)).mono'
  · exact aestronglyMeasurable_const.mul ((aestronglyMeasurable_apply period hK he.aestronglyMeasurable).inner
      he.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hKe : ‖K x (e x)‖ ≤ (C : ℝ) * ‖e x‖ :=
    ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪K x (e x), e x⟫_ℝ‖ := by dsimp [metricEnergy]; rw [abs_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖K x (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((C : ℝ) * ‖e x‖) * ‖e x‖) := by gcongr
    _ = _ := by ring

/-- The actual lifted transport velocity of an L² field is measurable. -/
theorem transportDirection_aestronglyMeasurable (κ : ℝ) (m : Vector3) (z : LiftL2 period) :
    AEStronglyMeasurable (fun x => transportDirection κ m (z x)) (liftMeasure period) := by
  exact ((Lp.aestronglyMeasurable z).const_smul κ).prodMk
    (aestronglyMeasurable_const.inner (Lp.aestronglyMeasurable z))

/-- The principal transport pairing is integrable for smooth H¹ fields and bounded velocity. -/
theorem metricTransport_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period))
    (he : MemLp e 2 (liftMeasure period))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period e x) 0) 2 (liftMeasure period))
    (C B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C) (z : LiftL2 period)
    (hz : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    Integrable (fun x => ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ) (liftMeasure period) := by
  apply ((he.norm.integrable_mul hDe.norm).const_mul ((C : ℝ) * B)).mono'
  · exact (aestronglyMeasurable_apply period hK he.aestronglyMeasurable).inner
      (aestronglyMeasurable_apply period hDe.aestronglyMeasurable
        (transportDirection_aestronglyMeasurable period κ m z))
  filter_upwards [hz] with x hx
  have hKe : ‖K x (e x)‖ ≤ (C : ℝ) * ‖e x‖ :=
    ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hDv : ‖fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))‖ ≤
      ‖fderiv ℝ (localFieldLift period e x) 0‖ * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  calc
    _ ≤ ‖K x (e x)‖ * ‖fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ((C : ℝ) * ‖e x‖) * (‖fderiv ℝ (localFieldLift period e x) 0‖ * B) :=
      mul_le_mul hKe hDv (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Pi.mul_apply]; ring

omit [Fact (0 < period)] in
theorem metricCorrection_pointwise_bound
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (D B : ℝ≥0) (x : LiftDomain period) (v : LiftTangent)
    (hD : ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D) (hv : ‖v‖ ≤ B) :
    ‖(1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ‖ ≤
      (1 / 2 : ℝ) * D * B * ‖e x‖ ^ 2 := by
  have hL : ‖fderiv ℝ (localFieldLift period K x) 0 v‖ ≤ (D : ℝ) * B :=
    ((fderiv ℝ (localFieldLift period K x) 0).le_opNorm _).trans
      (mul_le_mul hD hv (norm_nonneg _) D.coe_nonneg)
  have hLe : ‖(fderiv ℝ (localFieldLift period K x) 0 v) (e x)‖ ≤ (D : ℝ) * B * ‖e x‖ :=
    ((fderiv ℝ (localFieldLift period K x) 0 v).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ‖ := by
      rw [norm_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ (localFieldLift period K x) 0 v) (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((D : ℝ) * B * ‖e x‖) * ‖e x‖) := by gcongr
    _ = _ := by ring

/-- The metric correction is integrable for L² fields and bounded metric derivative and velocity. -/
theorem metricCorrection_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hDK : AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period K x) 0)
      (liftMeasure period)) (he : MemLp e 2 (liftMeasure period))
    (D B : ℝ≥0) (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (z : LiftL2 period) (hz : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    Integrable (fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period) := by
  apply (he.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * D * B)).mono'
  · exact aestronglyMeasurable_const.mul
      ((aestronglyMeasurable_apply period
        (aestronglyMeasurable_apply period hDK (transportDirection_aestronglyMeasurable period κ m z))
          he.aestronglyMeasurable).inner he.aestronglyMeasurable)
  filter_upwards [hz] with x hx
  exact metricCorrection_pointwise_bound period K e D B x _ (hD x) hx

/-- The genuine noncompact H¹ metric transport estimate; no cancellation is assumed. -/
theorem metric_transport_H1_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (heLp : MemLp e 2 (liftMeasure period))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period e x) 0) 2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
  let β : ℝ≥0 := ⟨(|κ| + ‖m‖) * B,
    mul_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _)) B.coe_nonneg⟩
  have hv : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ β := by
    filter_upwards [hzB] with x hx
    exact (transportDirection_norm_le κ m (z x)).trans
      (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  have hKm : AEStronglyMeasurable K (liftMeasure period) :=
    (smoothField_continuous period K hK).aestronglyMeasurable
  have hDKm : AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period K x) 0)
      (liftMeasure period) :=
    (localFDeriv_continuous period K hK).aestronglyMeasurable
  have hT := metricTransport_integrable period κ m K e hKm heLp hDe C β hC z hv
  have hQ := metricCorrection_integrable period κ m K e hDKm heLp D β hD z hv
  rw [metric_transport_noncompact_by_parts period κ m K e hK he hsym hz B B.coe_nonneg hzB
    (metricEnergy_integrable period K e hKm heLp C hC) hT hQ, abs_neg]
  have hbound := norm_integral_le_of_norm_le
    (heLp.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * D * β))
    (f := fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ?_
  · have hβ : (β : ℝ) = (|κ| + ‖m‖) * B := rfl
    rw [hβ] at hbound
    simpa only [Real.norm_eq_abs, integral_const_mul] using hbound
  filter_upwards [hv] with x hx
  exact metricCorrection_pointwise_bound period K e D β x _ (hD x) hx

end EulerNoncompactTransport

end

section

namespace EulerMetricEnergyEvolution

open InnerProductSpace Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact time derivative of a quadratic energy with a moving metric. -/
theorem metric_energy_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t : ℝ) (K' : H →L[ℝ] H) (e' : H)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ) :
    HasDerivAt (fun s => ⟪K s (e s), e s⟫_ℝ)
      (⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), e'⟫_ℝ) t := by
  refine ((hK.clm_apply he).inner ℝ he).congr_deriv ?_
  rw [inner_add_left, hsym e' (e t), real_inner_comm e' (K t (e t))]
  ring

/-- Cancellation of pressure and integration by parts for transport leave only
metric variation and the forcing in the time derivative. -/
theorem metric_energy_evolution (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing : H)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : e' + transport + pressure = forcing)
    (hp : ⟪K t (e t), pressure⟫_ℝ = 0) :
    HasDerivAt (fun s => ⟪K s (e s), e s⟫_ℝ)
      (⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), forcing⟫_ℝ -
        2 * ⟪K t (e t), transport⟫_ℝ) t := by
  refine (metric_energy_hasDerivAt K e t K' e' hK he hsym).congr_deriv ?_
  have h := congrArg (fun v => ⟪K t (e t), v⟫_ℝ) heq
  simp only [inner_add_right, hp, add_zero] at h
  linarith

theorem energy_derivative_bound (K K' : H →L[ℝ] H) (e transport forcing : H)
    (B : ℝ) (_hB : 0 ≤ B) (ht : |⟪K e, transport⟫_ℝ| ≤ B * ‖e‖ ^ 2) :
    ⟪K' e, e⟫_ℝ + 2 * ⟪K e, forcing⟫_ℝ - 2 * ⟪K e, transport⟫_ℝ ≤
      (‖K'‖ + 2 * B) * ‖e‖ ^ 2 + 2 * ‖K‖ * ‖e‖ * ‖forcing‖ := by
  have hk : ⟪K' e, e⟫_ℝ ≤ ‖K'‖ * ‖e‖ ^ 2 := by
    calc
      _ ≤ ‖K' e‖ * ‖e‖ := real_inner_le_norm _ _
      _ ≤ (‖K'‖ * ‖e‖) * ‖e‖ := by gcongr; exact K'.le_opNorm e
      _ = _ := by ring
  have hf : ⟪K e, forcing⟫_ℝ ≤ ‖K‖ * ‖e‖ * ‖forcing‖ := by
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (K.le_opNorm e) (norm_nonneg _))
  have ht' := (abs_le.mp ht).1
  nlinarith

end EulerMetricEnergyEvolution

end

section

/-! Metric-energy evolution using a separate actual smooth representative of each L² class. -/


namespace EulerRepresentativeMetricEvolution

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerNoncompactTransport EulerMetricEnergyEvolution
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual directional transport derivative is square integrable under H¹ and bounded velocity. -/
theorem liftedTransport_memLp (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0
      (transportDirection κ m (z x))) 2 (liftMeasure period) := by
  apply hDe.of_le_mul (c := (|κ| + ‖m‖) * B)
  · exact aestronglyMeasurable_apply period hDe.aestronglyMeasurable
      (transportDirection_aestronglyMeasurable period κ m z)
  filter_upwards [hzB] with x hx
  have hv := (transportDirection_norm_le κ m (z x)).trans
    (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ ‖fderiv ℝ (localFieldLift period g x) 0‖ *
        ‖transportDirection κ m (z x)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (localFieldLift period g x) 0‖ * ((|κ| + ‖m‖) * B) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = _ := by ring

/-- The genuine L² element represented by the lifted directional transport derivative. -/
def liftedTransport (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) : LiftL2 period :=
  (liftedTransport_memLp period κ m g z hDe B hzB).toLp _

theorem liftedTransport_ae (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    liftedTransport period κ m g z hDe B hzB =ᵐ[liftMeasure period]
      fun x => fderiv ℝ (localFieldLift period g x) 0
        (transportDirection κ m (z x)) :=
  (liftedTransport_memLp period κ m g z hDe B hzB).coeFn_toLp

/-- The Hilbert metric pairing equals the actual spatial transport integral. -/
theorem metric_transport_inner_eq (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period)) (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (e : LiftL2 period) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hrep : (e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    ⟪coefficientOperator K hKm C hC e, liftedTransport period κ m g z hDe B hzB⟫_ℝ =
      ∫ x, ⟪K x (g x), fderiv ℝ (localFieldLift period g x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae K hKm C hC e, liftedTransport_ae period κ m g z hDe B hzB, hrep]
    with x hx hy hr
  rw [hx, hy, hr]

/-- The transport bound required by the Hilbert energy theorem, with genuine spatial fields. -/
theorem metric_transport_inner_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period))
    (e : LiftL2 period) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hrep : (e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |⟪coefficientOperator K hKm C hC e, liftedTransport period κ m g z hDe B hzB⟫_ℝ| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  rw [metric_transport_inner_eq period κ m K hKm C hC e g z hrep hDe B hzB]
  have hn : (∫ x, ‖g x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    calc
      _ = ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
      _ = _ := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_H1_bound period κ m K g
    hK he ((memLp_congr_ae hrep).mp (Lp.memLp e)) hDe hsym hz C D B hC hD hzB

end EulerRepresentativeMetricEvolution

end

section

/-! Exact differentiated projected-pressure equations for actual translation Sobolev jets. -/


namespace EulerPressureJetIdentities

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerPressureSpatialRegularity EulerLiftedWeakDerivative EulerSpatialSobolevInverse
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Strong derivatives preserve the actual closed lifted gradient subspace. -/
theorem gradientSpace_translation_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    {f f' : LiftL2 period} (hf : f ∈ gradientSpace period κ m)
    (hder : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    f' ∈ gradientSpace period κ m := by
  have hlim := hder.tendsto_slope_zero
  simp only [zero_add, translationPath_zero, translation_zero] at hlim
  apply (gradientSpace_closed period κ m).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun t => (gradientSpace period κ m).smul_mem _
    ((gradientSpace period κ m).sub_mem
      (gradientSpace_translation_mem period κ m (translationPath period a t) hf) hf)

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Actual strong derivative words are independent of the chosen derivative witness tree. -/
theorem word_unique {s t n : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions t g)
    (hfg : f = g) (hn : n ≤ s) (hm : n ≤ t) (w : Fin n → Fin 4) : J.word w = K.word w := by
  subst g
  induction n with
  | zero => simp
  | succ n ih =>
    have hbase := ih (by omega) (by omega) (Fin.tail w)
    have hJ := J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0)
    have hK := K.word_hasDerivAt (by omega : n < t) (Fin.tail w) (w 0)
    rw [hbase] at hJ
    simpa only [Fin.cons_self_tail] using hJ.unique hK

/-- Every valid word of a gradient-valued Sobolev jet remains in the gradient subspace. -/
theorem word_mem_gradientSpace {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (hf : f ∈ gradientSpace period κ m) (hn : n ≤ s)
    (w : Fin n → Fin 4) : J.word w ∈ gradientSpace period κ m := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := gradientSpace_translation_derivative period κ m (directions (w 0))
      (ih (by omega) (Fin.tail w))
      (J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0))
    simpa only [Fin.cons_self_tail] using h


/-- A bounded operator commuting with actual translations maps genuine spatial jets. -/
def map (L : LiftL2 period →L[ℝ] LiftL2 period)
    (hL : ∀ a f, translation period a (L f) = L (translation period a f))
    {s : ℕ} {f : LiftL2 period} (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) :
    EulerSpatialSobolevInverse.SpatialJet period directions s (L f) :=
  match J with
  | .zero f => .zero (L f)
  | .succ df lower hd => .succ (fun i => L (df i)) (fun i => map L hL (lower i))
      (fun i => by
        have h := L.hasFDerivAt.comp_hasDerivAt 0 (hd i)
        convert h using 1 <;> first | rfl | (funext t; exact hL _ _))

theorem map_word {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (L : LiftL2 period →L[ℝ] LiftL2 period)
    (hL : ∀ a f, translation period a (L f) = L (translation period a f))
    (w : Fin n → Fin 4) : (map L hL J).word w = L (J.word w) := by
  induction J generalizing n with
  | zero f => cases n <;> simp [map, EulerSpatialSobolevInverse.SpatialJet.word]
  | succ df lower hd ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [map, EulerSpatialSobolevInverse.SpatialJet.word_succ] using
        (ih (w (Fin.last n)) (Fin.init w))

/-- At every derivative word, the actual projected equation differentiates exactly. -/
theorem pressure_word_projected_equation {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    gradientProjection period κ m
      ((EulerSpatialSobolevInverse.SpatialJet.multiply K (J.solvePressure K κ m c hc hpos)).word w) =
      gradientProjection period κ m (J.word w) := by
  let P := J.solvePressure K κ m c hc hpos
  let M := EulerSpatialSobolevInverse.SpatialJet.multiply K P
  have heq : gradientProjection period κ m (A.operator (A.pressure κ m c hc hpos f)) =
      gradientProjection period κ m f :=
    liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f
  have h := word_unique (map (gradientProjection period κ m)
      (gradientProjection_translation period κ m) M)
    (map (gradientProjection period κ m) (gradientProjection_translation period κ m) J) heq hn hn w
  simpa only [map_word] using h

/-- The actual derivative word is the coercive inverse applied to its differentiated source
minus the genuine product commutator. -/
theorem pressure_word_inverse {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    (J.solvePressure K κ m c hc hpos).word w = A.pressure κ m c hc hpos
      (J.word w - ((EulerSpatialSobolevInverse.SpatialJet.multiply K
        (J.solvePressure K κ m c hc hpos)).word w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w))) := by
  let P := J.solvePressure K κ m c hc hpos
  let M := EulerSpatialSobolevInverse.SpatialJet.multiply K P
  apply liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos
  · exact word_mem_gradientSpace P κ m
      (liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f) hn w
  · have hp := pressure_word_projected_equation K J κ m c hc hpos hn w
    change gradientProjection period κ m (A.operator (P.word w)) =
      gradientProjection period κ m (J.word w - (M.word w - A.operator (P.word w)))
    rw [map_sub, map_sub, hp]
    abel


end SpatialJet

end EulerPressureJetIdentities

end

section

/-! Sharp order-by-order Leibniz bounds for actual cylinder Sobolev jets. -/


namespace EulerJetProductBounds

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerPressureSpatialRegularity EulerSpatialSobolevInverse
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The sum of the L² norms of all actual derivative words of one order. -/
def levelNorm {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) : ℝ :=
  match n, J with
  | 0, _ => ‖f‖
  | _ + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => ∑ i, levelNorm (lower i) n
termination_by s

/-- The sum of the uniform bounds of all coefficient derivatives of one order. -/
def boundLevel {directions : Fin 4 → LiftTangent} {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) (n : ℕ) : ℝ :=
  match n, K with
  | 0, _ => A.bound
  | _ + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => ∑ i, boundLevel (lower i) n
termination_by s

variable {period} {directions : Fin 4 → LiftTangent}

theorem levelNorm_nonneg {s n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f) :
    0 ≤ levelNorm period J n := by
  induction J generalizing n with
  | zero => cases n <;> simp [levelNorm]
  | succ df lower hd ih =>
    cases n with
    | zero => rw [levelNorm]; exact norm_nonneg _
    | succ n =>
      rw [levelNorm]
      exact Finset.sum_nonneg fun i _ => ih i

omit [Fact (0 < period)] in
theorem boundLevel_nonneg {s n : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) : 0 ≤ boundLevel period K n := by
  induction K generalizing n with
  | zero => cases n <;> simp [boundLevel]
  | succ dA lower hd ih =>
    cases n with
    | zero => rw [boundLevel]; exact NNReal.coe_nonneg _
    | succ n =>
      rw [boundLevel]
      exact Finset.sum_nonneg fun i _ => ih i

/-- The recursive level norm is exactly the finite sum over coordinate words. -/
theorem levelNorm_eq_words {s n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f) :
    levelNorm period J n = ∑ w : Fin n → Fin 4, ‖J.word w‖ := by
  induction J generalizing n with
  | zero f => cases n <;> simp [levelNorm, SpatialJet.word]
  | succ df lower hd ih =>
    cases n with
    | zero => simp [levelNorm]
    | succ n =>
      rw [levelNorm, SpatialJet.sum_word_succ]
      exact Finset.sum_congr rfl fun i _ => ih i

theorem levelNorm_truncate {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions (s + 1) f) (hn : n ≤ s) :
    levelNorm period J.truncate n = levelNorm period J n := by
  induction s generalizing f n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp only [levelNorm]
  | succ s ih =>
    cases n with
    | zero => simp only [levelNorm]
    | succ n =>
      cases J with
      | succ df lower hd =>
        simp only [SpatialJet.truncate, levelNorm]
        exact Finset.sum_congr rfl fun i _ => ih (lower i) (by omega)

omit [Fact (0 < period)] in
theorem boundLevel_truncate {s n : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions (s + 1) A) (hn : n ≤ s) :
    boundLevel period K.truncate n = boundLevel period K n := by
  induction s generalizing A n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp only [boundLevel]
  | succ s ih =>
    cases n with
    | zero => simp only [boundLevel]
    | succ n =>
      cases K with
      | succ dA lower hd =>
        simp only [CoefficientJet.truncate, boundLevel]
        exact Finset.sum_congr rfl fun i _ => ih (lower i) (by omega)

theorem levelNorm_add_le {s n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g) :
    levelNorm period (J.add K) n ≤ levelNorm period J n + levelNorm period K n := by
  induction s generalizing f g n with
  | zero => cases J; cases K; cases n <;> simp [SpatialJet.add, levelNorm, norm_add_le]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases n with
        | zero => simp only [levelNorm]; exact norm_add_le _ _
        | succ n =>
          rw [SpatialJet.add, levelNorm, levelNorm, levelNorm, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => ih (lower i) (lowerG i)

/-- Binomial convolution of nonnegative derivative-order bounds. -/
def leibnizConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun l => (n.choose l : ℝ) * A l * B (n - l))

theorem leibnizConvolution_succ (A B : ℕ → ℝ) (n : ℕ) :
    leibnizConvolution A B (n + 1) =
      leibnizConvolution A (fun k => B (k + 1)) n +
      leibnizConvolution (fun k => A (k + 1)) B n := by
  simp only [leibnizConvolution, mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun l r => A l * B r) n]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hln : l ≤ n := by simpa using Finset.mem_range.mp hl
  rw [show n + 1 - l = n - l + 1 by omega]

theorem leibnizConvolution_congr (A B C D : ℕ → ℝ) (n : ℕ)
    (hA : ∀ l ≤ n, A l = C l) (hB : ∀ l ≤ n, B l = D l) :
    leibnizConvolution A B n = leibnizConvolution C D n := by
  apply Finset.sum_congr rfl
  intro l hl
  have hl : l ≤ n := by simpa using Finset.mem_range.mp hl
  rw [hA l hl, hB (n - l) (by omega)]

theorem sum_leibnizConvolution_right (A : ℕ → ℝ) (B : Fin 4 → ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution A (B i) n) = leibnizConvolution A (fun l => ∑ i, B i l) n := by
  simp only [leibnizConvolution]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum ..).symm

theorem sum_leibnizConvolution_left (A : Fin 4 → ℕ → ℝ) (B : ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution (A i) B n) = leibnizConvolution (fun l => ∑ i, A i l) B n := by
  simp only [leibnizConvolution]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Sharp binomial Leibniz estimate for the actual product jet, at every finite derivative order. -/
theorem multiply_levelNorm_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (hn : n ≤ s) :
    levelNorm period (SpatialJet.multiply K J) n ≤
      leibnizConvolution (boundLevel period K) (levelNorm period J) n := by
  induction n generalizing s A f with
  | zero =>
    simpa [levelNorm, leibnizConvolution, boundLevel] using A.operator_norm f
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := CoefficientJet.succ dA lowerA hA
          let J := SpatialJet.succ df lowerF hF
          have hterm : ∀ i,
              levelNorm period ((SpatialJet.multiply K.truncate (lowerF i)).add
                (SpatialJet.multiply (lowerA i) J.truncate)) n ≤
              leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
              leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n ≤ s)
            have hright := ih (lowerA i) J.truncate (by omega : n ≤ s)
            have heqL : leibnizConvolution (boundLevel period K.truncate)
                (levelNorm period (lowerF i)) n =
                leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n :=
              leibnizConvolution_congr _ _ _ _ n
                (fun l hl => boundLevel_truncate K (by omega)) (fun _ _ => rfl)
            have heqR : leibnizConvolution (boundLevel period (lowerA i))
                (levelNorm period J.truncate) n =
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n :=
              leibnizConvolution_congr _ _ _ _ n
                (fun _ _ => rfl) (fun l hl => levelNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact (levelNorm_add_le _ _).trans (add_le_add hleft hright)
          rw [SpatialJet.multiply, levelNorm]
          calc
            _ ≤ ∑ i, (leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n) :=
              Finset.sum_le_sum fun i _ => hterm i
            _ = leibnizConvolution (boundLevel period K)
                  (fun l => ∑ i, levelNorm period (lowerF i) l) n +
                leibnizConvolution (fun l => ∑ i, boundLevel period (lowerA i) l)
                  (levelNorm period J) n := by
              rw [Finset.sum_add_distrib, sum_leibnizConvolution_right, sum_leibnizConvolution_left]
            _ = leibnizConvolution (boundLevel period K) (levelNorm period J) (n + 1) := by
              rw [leibnizConvolution_succ]
              congr 2 <;> funext l <;> simp only [K, J, levelNorm, boundLevel]

theorem word_add {s n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g)
    (w : Fin n → Fin 4) : (J.add K).word w = J.word w + K.word w := by
  induction s generalizing f g n with
  | zero => cases J; cases K; cases n <;> simp [SpatialJet.add, SpatialJet.word]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases n with
        | zero => simp
        | succ n =>
          simp only [SpatialJet.add, SpatialJet.word_succ]
          exact ih (lower _) (lowerG _) _

/-- Binomial derivative convolution with its undifferentiated-coefficient term removed. -/
def commutatorConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  leibnizConvolution A B n - A 0 * B n

theorem commutatorConvolution_eq_sum (A B : ℕ → ℝ) (n : ℕ) :
    commutatorConvolution A B n =
      ∑ l ∈ Finset.range n, (n.choose (l + 1) : ℝ) * A (l + 1) * B (n - (l + 1)) := by
  rw [commutatorConvolution, leibnizConvolution, Finset.sum_range_succ']
  simp

theorem commutatorConvolution_congr (A B C D : ℕ → ℝ) (n : ℕ)
    (hA : ∀ l ≤ n, A l = C l) (hB : ∀ l ≤ n, B l = D l) :
    commutatorConvolution A B n = commutatorConvolution C D n := by
  rw [commutatorConvolution, commutatorConvolution, leibnizConvolution_congr A B C D n hA hB,
    hA 0 (Nat.zero_le n), hB n le_rfl]

theorem commutatorConvolution_succ (A B : ℕ → ℝ) (n : ℕ) :
    commutatorConvolution A B (n + 1) =
      commutatorConvolution A (fun k => B (k + 1)) n +
      leibnizConvolution (fun k => A (k + 1)) B n := by
  rw [commutatorConvolution, leibnizConvolution_succ, commutatorConvolution]
  ring

theorem sum_commutatorConvolution_right (A : ℕ → ℝ) (B : Fin 4 → ℕ → ℝ) (n : ℕ) :
    (∑ i, commutatorConvolution A (B i) n) =
      commutatorConvolution A (fun l => ∑ i, B i l) n := by
  simp only [commutatorConvolution]
  rw [Finset.sum_sub_distrib, sum_leibnizConvolution_right, Finset.mul_sum]


theorem sum_word_snoc (n : ℕ) (F : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ w, F w) = ∑ i, ∑ w : Fin n → Fin 4, F (Fin.snoc w i) := by
  calc
    _ = ∑ v : Fin 4 × (Fin n → Fin 4), F ((SpatialJet.wordSnocEquiv n).symm v) :=
      ((SpatialJet.wordSnocEquiv n).symm.sum_comp F).symm
    _ = _ := Fintype.sum_prod_type _

theorem multiply_word_snoc {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lowerA : ∀ i, CoefficientJet period directions s (dA i))
    (hA : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
      (directions i) A.coefficient x)
    (df : Fin 4 → LiftL2 period) (lowerF : ∀ i, SpatialJet period directions s (df i))
    (hF : ∀ i, HasDerivAt (fun t => translation period (translationPath period (directions i) t) f)
      (df i) 0) (i : Fin 4) (w : Fin n → Fin 4) :
    (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA) (SpatialJet.succ df lowerF hF)).word
        (Fin.snoc w i) =
      (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w +
      (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w := by
  rw [SpatialJet.multiply, SpatialJet.word_succ]
  simp only [Fin.init_snoc, word_add, Fin.snoc, Fin.val_last, cast_eq]
  generalize hval : (if h : n < n then w ((Fin.last n).castLT h) else i) = j
  have hj : j = i := hval.symm.trans (dite_eq_right (Nat.lt_irrefl n))
  clear hval
  subst j
  rfl




end EulerJetProductBounds

end

end
