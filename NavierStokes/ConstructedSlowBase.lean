import NavierStokes.AssembledSlowBase
import NavierStokes.GlobalStressSupport
import NavierStokes.BasePrefixIdentity
import NavierStokes.PreparedOutgoing
import NavierStokes.BaseExterior
import NavierStokes.TerminalHistoryBridge
import NavierStokes.ModulatedProfileAssembly
import NavierStokes.FirstOrderBaseEdge

/-!
# The actual constructed slow base

The finite residual identities, regular axis descriptors, and stress support
used here are derived from the same repaired coefficient sequence.  No
residual estimate or infinite-dimensional output certificate is an input.
-/

noncomputable section

open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace NavierStokes.ConstructedSlowBase

open GlobalSlowProfiles AssembledSlowBase SlowBorelBase

private theorem parameter_abs_le {eta : ℝ} (h : eta ∈ Ioo (-1 : ℝ) 1) :
    |eta| ≤ 1 := (abs_lt.mpr h).le

/-- Restricting the compact set preserves the very same cutoff schedule. -/
theorem admissibleScales_mono {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℕ → ℕ} {h : ℝ} {f : ℕ → Inner → V} {K K' : Set Inner}
    (ha : AdmissibleScales h f K a) (hK : K' ⊆ K) : AdmissibleScales h f K' a where
  positive := ha.positive
  doubling := ha.doubling
  strictMono := ha.strictMono
  ordinary := fun j hj m hm q hq hq1 w hw => ha.ordinary j hj m hm q hq hq1 w (hK hw)
  blown := fun j hj m hm q hq hq1 w hw => ha.blown j hj m hm q hq hq1 w (hK hw)

/-- The genuine smooth vector potential of the summed base. -/
noncomputable def potential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    ProblemStatement.VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d) (swirlPotential a h C d)


theorem potential_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (potential a h C d) BaseResidual.past :=
  AxisymmetricFields.contDiffOn_potential
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _)

section RepairedFamily

variable {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
  {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
  {A : SlowRecursion.LocalHierarchy rho U h C base}
  (L : Localization s A inner) (B0 : BaseAgreement s A inner)
  (Z0 : ZeroOrderSolved s inner) (hI : Icc (-1 : ℝ) 1 ⊆ S)

/-- The only base flux premise is the actual mass reconstruction.  Every
positive-order flux is reconstructed by the global recursion itself. -/
theorem repaired_coefficientMatches
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) :
    BasePrefixIdentity.CoefficientMatches h C (coefficients L B0 Z0 hI) (asSlowProfiles s) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).1
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2.1
  · intro n w hw
    have hb : w.1 * extendedCoefficient s hI n 2 w =
        SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n)
          ((coefficients L B0 Z0 hI).axial n) w := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have he := extended_flux_zero s hI hbase hw.1.le (parameter_abs_le hw.2)
        simp only [SlowExpansionResidual.slowOrder, Nat.cast_zero, mul_zero, zero_mul] at he ⊢
        exact he
      · exact extended_flux s hI hn hw.1.le (parameter_abs_le hw.2)
    rw [← hb]
    change w.1 * extendedCoefficient s hI n 2 w = w.1 * xProfile (profiles s n).beta w
    rw [extendedCoefficient_eq s hI n 2 hw.1.le (parameter_abs_le hw.2)]
    rfl
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2.2
  · intro n w hw
    exact (coefficients_stress_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).1
  · intro n w hw
    exact (coefficients_stress_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2

/-- The finite Cartesian PDE identity is derived from scalar equations and
the actual stream primitives, using the proved finite-prefix bridge. -/
theorem repaired_finiteIdentities (hh : 0 < h) (hh1 : h < 1 / 2)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (hp : ∀ n, ∀ w ∈ BasePrefixIdentity.profileWindow,
      SlowExpansionResidual.pressureCoefficient h C (asSlowProfiles s) n w = 0) :
    BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s) := by
  apply BasePrefixIdentity.finiteIdentities_of_coefficients hh hh1
    (coefficients_smooth L B0 Z0 hI) (repaired_coefficientMatches L B0 Z0 hI hbase)
  · intro n
    exact (thetaDensity_smooth L B0 Z0 n).mono
      (fun _ hw => ⟨hw.1, hI ⟨hw.2.1.le, hw.2.2.le⟩⟩)
  · intro n
    exact (zDensity_smooth L B0 Z0 n).mono
      (fun _ hw => ⟨hw.1, hI ⟨hw.2.1.le, hw.2.2.le⟩⟩)
  · exact hp

theorem repaired_stressZeroCore :
    BaseResidual.StressZeroCore (coefficients L B0 Z0 hI) (inner / 8) := by
  intro n X hX eta _
  exact coefficients_stress_zero_left L B0 Z0 hI n hX.2.le

/-- One open coefficient neighborhood contains the whole physical parameter
band and avoids the coordinate denominator's zeros. -/
noncomputable def regularDomain (s : Scheme S h C) (hI : Icc (-1 : ℝ) 1 ⊆ S) : Set Inner :=
  {w | |w.2| < (commonWindow s hI).inner ∧ CoordinateAlgebra.L h w.2 ≠ 0}

theorem regularDomain_open : IsOpen (regularDomain s hI) := by
  have hL : Continuous (fun w : Inner => CoordinateAlgebra.L h w.2) :=
    continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))
  exact (isOpen_lt continuous_snd.abs continuous_const).inter
    (isOpen_ne_fun hL continuous_const)

theorem innerBox_subset_regularDomain (hh : 0 < h) (hh1 : h < 1 / 2) (lo hi : ℝ) :
    innerBox lo hi ⊆ regularDomain s hI := by
  intro w hw
  have he : |w.2| ≤ 1 := abs_le.mpr hw.2
  exact ⟨he.trans_lt (commonWindow s hI).one_lt_inner,
    (CoordinateAlgebra.L_pos hh.le hh1 ((sq_le_one_iff_abs_le_one w.2).mpr he)).ne'⟩

theorem regular_fields_eq (n : ℕ) {w : Inner} (hw : w ∈ regularDomain s hI) (hX : 0 ≤ w.1) :
    (asSlowProfiles s).phi n w = extendedCoefficient s hI n 0 w ∧
    (asSlowProfiles s).axial n w = extendedCoefficient s hI n 1 w ∧
    (asSlowProfiles s).flux n w = w.1 * extendedCoefficient s hI n 2 w := by
  refine ⟨?_, ?_, ?_⟩
  · exact (extendEven_eq (commonWindow s hI) (profiles s n).phi hX hw.1.le).symm
  · exact (extendEven_eq (commonWindow s hI) (profiles s n).axial hX hw.1.le).symm
  · exact congrArg (w.1 * ·)
      (extendEven_eq (commonWindow s hI) (profiles s n).beta hX hw.1.le).symm

/-- Every fixed physical derivative has every requested power of decay,
including on approaches that meet the symmetry axis. -/
theorem repaired_jetRate {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (P : BaseResidual.PhysicalApproach l h 0 hi)
    (ha : AdmissibleScales h (coefficientBundle C (coefficients L B0 Z0 hI)) (innerBox 0 hi) a)
    (hf : BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s))
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart h z).1)
      (BaseResidual.baseResidual a h C (coefficients L B0 Z0 hI)) m n := by
  exact BaseResidual.baseResidual_jetRate_axis hh hh1 P
    (div_pos L.inner_pos (by norm_num)) (coefficients_smooth L B0 Z0 hI)
    (repaired_stressZeroCore L B0 Z0 hI) ha (asSlowProfiles s) hf
    (regularDomain_open hI) (innerBox_subset_regularDomain hI hh hh1 0 hi)
    (fun j => extendedCoefficient s hI j 0) (fun j => extendedCoefficient s hI j 1)
    (fun j => extendedCoefficient s hI j 2)
    (fun j => (extendedCoefficient_contDiff s hI j 0).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 1).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 2).contDiffOn)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.2)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.1)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).1)
    (fun _ hw => hw.2) m n hn

theorem repaired_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (P : BaseResidual.PhysicalApproach l h 0 hi)
    (ha : AdmissibleScales h (coefficientBundle C (coefficients L B0 Z0 hI)) (innerBox 0 hi) a)
    (hf : BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s)) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart h z).1)
      (BaseResidual.baseResidual a h C (coefficients L B0 Z0 hI)) := by
  exact BaseResidual.baseResidual_allJetsFlat_axis hh hh1 P
    (div_pos L.inner_pos (by norm_num)) (coefficients_smooth L B0 Z0 hI)
    (repaired_stressZeroCore L B0 Z0 hI) ha (asSlowProfiles s) hf
    (regularDomain_open hI) (innerBox_subset_regularDomain hI hh hh1 0 hi)
    (fun j => extendedCoefficient s hI j 0) (fun j => extendedCoefficient s hI j 1)
    (fun j => extendedCoefficient s hI j 2)
    (fun j => (extendedCoefficient_contDiff s hI j 0).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 1).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 2).contDiffOn)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.2)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.1)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).1)
    (fun _ hw => hw.2)

/-- Exterior confinement is a consequence of the five repaired rows, not
an extra hypothesis on higher-order stress coefficients. -/
theorem repaired_higherInteriorSupport
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    {left right : ℝ} (hl : Real.exp left < inner / 8) (hr : s.B ^ 2 / 2 < Real.exp right) :
    BaseResidual.HigherInteriorSupport (coefficients L B0 Z0 hI) left right := by
  intro n hn
  have he := GlobalStressSupport.raw_stresses_exterior s hbase hn
  have hs := coefficients_stress_support L B0 Z0 hI n s.B_pos.le he.1 he.2
  have hz {w : Inner} (hw : w.1 ∉ Icc (inner / 8) (s.B ^ 2 / 2)) :
      ((coefficients L B0 Z0 hI).stressTheta n w,
        (coefficients L B0 Z0 hI).stressAxial n w) = 0 := by
    by_contra hh
    exact hw (hs (subset_closure hh)).1
  refine ⟨inner / 8, s.B ^ 2 / 2, fun _ hw => ⟨hl.trans_le hw.1, hw.2.trans_lt hr⟩, ?_, ?_⟩
  · intro eta _ X hX
    exact congrArg Prod.fst (hz hX)
  · intro eta _ X hX
    exact congrArg Prod.snd (hz hX)

end RepairedFamily

section Nominal

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

include W

theorem height_pos : 0 < F.data.h := W.axis.small.h_pos

theorem height_lt_half : F.data.h < 1 / 2 := by linarith [W.axis.small.h_le]






theorem nominal_higherInteriorSupport {left right : ℝ}
    (hl : Real.exp left < nominalInner W / 8) (hr : nominalOuterX W < Real.exp right) :
    BaseResidual.HigherInteriorSupport (nominalCoefficients W) left right := by
  apply repaired_higherInteriorSupport (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) rfl hl
  change nominalOuterRadius W ^ 2 / 2 < Real.exp right
  rwa [nominalOuterRadius_square]

/-- The leading coefficient retains the actual natural axis datum. -/
theorem nominal_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (nominalCoefficients W).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  have h0 : (0 : ℝ) ≤ 4 / W.axis.scale := (div_pos (by norm_num) W.axis.scale_pos).le
  calc
    _ = W.U (0, eta) := (nominalCoefficients_zero_fields W (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1
    _ = W.controls.seedU (0, eta) :=
      (W.seed_agreement (p := (0, eta)) le_rfl NominalProfile.Xi_pos.le).2.1
    _ = W.axis.natural.profile.family.U (0, eta) := (W.controls.seed_initial h0).2
    _ = _ := W.axis.natural.profile.family.natural.U_axis eta
      (NaturalAxisCoefficients.original_interval_interior heta)

theorem nominal_leading_origin : (nominalCoefficients W).axial 0 (0, 0) = W.axis.j := by
  simpa using nominal_leading_axis W (eta := 0) (by constructor <;> norm_num)









end Nominal

section Modified

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

include M


theorem modified_finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (asSlowProfiles (modifiedScheme W Q M)) := by
  apply repaired_finiteIdentities (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) rfl
  intro n w hw
  exact modified_pressureCoefficient W Q M n hw.1 (M.contains ⟨hw.2.1.le, hw.2.2.le⟩)



theorem modified_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {upper : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 upper)
    (ha : AdmissibleScales F.data.h
      (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M)) (innerBox 0 upper) a) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (BaseResidual.baseResidual a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) :=
  repaired_allJetsFlat (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) P ha
    (modified_finiteIdentities W Q M)

theorem modified_higherInteriorSupport {left right : ℝ}
    (hl : Real.exp left < nominalInner W / 8) (hr : nominalOuterX W < Real.exp right) :
    BaseResidual.HigherInteriorSupport (modifiedCoefficients W Q M) left right := by
  apply repaired_higherInteriorSupport (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains rfl hl
  change nominalOuterRadius W ^ 2 / 2 < Real.exp right
  rwa [nominalOuterRadius_square]

theorem modified_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (modifiedCoefficients W Q M).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  calc
    _ = Q.U (0, eta) := (modifiedCoefficients_zero_fields W Q M (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1
    _ = W.U (0, eta) := (M.fields (0, eta) le_rfl (M.contains heta)
      (Or.inl ((nominalInner_pos W).le.trans M.inner))).2
    _ = (nominalCoefficients W).axial 0 (0, eta) :=
      (nominalCoefficients_zero_fields W (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1.symm
    _ = _ := nominal_leading_axis W heta

theorem modified_leading_origin : (modifiedCoefficients W Q M).axial 0 (0, 0) = W.axis.j := by
  simpa using modified_leading_axis W Q M (eta := 0) (by constructor <;> norm_num)

theorem modified_origin {a : ℕ → ℕ} (ha : StrictMono a) {t : ℝ} (ht : t < 1) :
    baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 := by
  rw [BaseResidual.baseVelocity_at_origin ha (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization
    (fun _ hn => (modifiedCoefficients_axis W Q M hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1) ht,
    modified_leading_origin]

theorem modified_axis_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto (fun t : ℝ =>
      ‖baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M) (t, 0)‖)
      (𝓝[<] 1) atTop := by
  apply BaseResidual.baseVelocity_axis_tendsto_atTop ha (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization
    (fun _ hn => (modifiedCoefficients_axis W Q M hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1)
  rw [modified_leading_origin]
  exact W.axis.small.j_pos

theorem modified_speedUnbounded {a : ℕ → ℕ} (ha : StrictMono a) :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) :=
  NaturalCore.speedUnbounded_of_axis_tendsto (modified_axis_tendsto W Q M ha)

end Modified

section CommonWeightedSchedule

open BaseResidual ActiveAnnulusWeight

/-- The actual two-slot, all-order weighted estimate, used only as an output
of the coefficient construction and common schedule selection. -/
def WeightedStressBound (a : ℕ → ℕ) (h : ℝ) (d : Coefficients) (c left right : ℝ) : Prop :=
  ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 →
    ∀ w ∈ activeWindow left right,
      ‖blownJet m (fun v => normalizedTensor a h d v - stressPair d 0 v.2) (q, w)‖ ≤
        D * q ^ h * activeZeta c left right w * (activeDelta left right w)⁻¹ ^ N

/-- This form uses actual derivative bounds on the closed parameter band.
It requires no ambient germ equality to an auxiliary extension at eta=±1. -/
theorem weighted_on_actual_scales {a : ℕ → ℕ} {h C : ℝ} (hh : 0 < h)
    {d : Coefficients} (hd : SmoothCoefficients d) {c left right inner cut : ℝ}
    (hc : 0 < c) (hl : Real.exp left < inner) (hi : inner ≤ cut) (hr : cut < Real.exp right)
    (hs : HigherInteriorSupport d left right)
    (hz : ∀ w : Inner, w.1 < inner → stressPair d 1 w = 0)
    (ho : PolynomialEdgeJets (outerWindow cut right) (activeZeta c left right)
      (activeDelta left right) (stressPair d 1))
    {K : Set Inner} (hK : IsCompact K) (hWK : activeWindow left right ⊆ K)
    (ha : AdmissibleScales h (weightedBundle C d (activeZeta c left right)) K a) :
    WeightedStressBound a h d c left right := by
  let O : Set Inner := Ioo (Real.exp left) (Real.exp right) ×ˢ univ
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_univ
  have hWO : activeWindow left right ⊆ O := fun _ hw => ⟨hw.1, mem_univ _⟩
  exact normalizedTensor_weighted_bound hh hd hK hWK hO hWO
    (activeZeta_smooth hc left right) (fun _ hw => radialWeight_pos hw.1)
    (fun _ hw => activeDelta_bounds hw)
    (edgeJets_of_outer_collar (stressPair_smooth hd 1) hc hl hi hr hz ho)
    (activeZeta_edgeJets (Real.exp_lt_exp.mp ((hl.trans_le hi).trans hr)) hc)
    (higherStressQuotient_smooth_of_support hd hc hs) ha



end CommonWeightedSchedule

section FixedGeometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def activeLeft : ℝ := Real.log (nominalInner W / 16)

noncomputable def terminalShift : ℝ := TerminalHistoryBridge.shift F W.controls.radius

noncomputable def activeRight : ℝ := terminalShift W + 3

noncomputable def activeUpper : ℝ := Real.exp (activeRight W)

noncomputable def scaleUpper (upper : ℝ) : ℝ := max upper (activeUpper W)

theorem exp_activeLeft : Real.exp (activeLeft W) = nominalInner W / 16 :=
  Real.exp_log (div_pos (nominalInner_pos W) (by norm_num))

theorem activeLeft_margin : Real.exp (activeLeft W) < nominalInner W / 8 := by
  rw [exp_activeLeft]
  linarith [nominalInner_pos W]

theorem core_before_outer : nominalInner W / 8 < nominalOuterX W := by
  have hi := (nominalInner_lt_stop W).trans (nominalStop_lt_initial W)
  have ho := (W.controls.Xi_lt_heatJoin W.separated).trans
    (W.controls.heatJoin_lt_radius.trans (nominalOuterX_gt_radius W))
  have hxi := nominalInitial_le_Xi W
  linarith [nominalInner_pos W]

theorem switch_before_collar : BaseExterior.nominalHeatSwitch W < Real.exp (terminalShift W + 2) := by
  change BaseExterior.nominalHeatSwitch W <
    Real.exp (Real.log (BaseExterior.nominalHeatSwitch W) - 1 / 5 + 2)
  calc
    _ = Real.exp (Real.log (BaseExterior.nominalHeatSwitch W)) :=
      (Real.exp_log (BaseExterior.nominalHeatSwitch_pos W)).symm
    _ < _ := Real.exp_lt_exp.mpr (by linarith)

theorem outer_before_collar : nominalOuterX W < Real.exp (terminalShift W + 2) :=
  (nominalOuterX_lt_switch W).trans (switch_before_collar W)

theorem collar_before_upper : Real.exp (terminalShift W + 2) < activeUpper W :=
  Real.exp_lt_exp.mpr (by dsimp [activeUpper, activeRight]; linarith)

theorem outer_before_upper : nominalOuterX W < activeUpper W :=
  (outer_before_collar W).trans (collar_before_upper W)

theorem core_before_collar : nominalInner W / 8 ≤ Real.exp (terminalShift W + 3 - 1) := by
  have hh := (core_before_outer W).trans (outer_before_collar W)
  simpa only [show terminalShift W + 3 - 1 = terminalShift W + 2 by ring] using hh.le

theorem activeLeft_before_collar : activeLeft W < terminalShift W + 2 :=
  Real.exp_lt_exp.mp ((activeLeft_margin W).trans
    ((core_before_outer W).trans (outer_before_collar W)))



theorem activeWindow_subset_box (upper : ℝ) :
    BaseResidual.activeWindow (activeLeft W) (activeRight W) ⊆ innerBox 0 (scaleUpper W upper) := by
  intro w hw
  exact ⟨⟨(Real.exp_pos _).le.trans hw.1.1.le,
    hw.1.2.le.trans (le_max_right upper (activeUpper W))⟩, hw.2⟩

theorem nominal_higher_support :
    BaseResidual.HigherInteriorSupport (nominalCoefficients W) (activeLeft W) (activeRight W) :=
  nominal_higherInteriorSupport W (activeLeft_margin W) (outer_before_upper W)

theorem nominal_quotients_smooth {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ContDiff ℝ ∞ (BaseResidual.higherStressQuotient (nominalCoefficients W)
      (BaseResidual.activeZeta c (activeLeft W) (activeRight W)) j) :=
  BaseResidual.higherStressQuotient_smooth_of_support (nominalCoefficients_smooth W) hc
    (nominal_higher_support W) j

theorem modified_higher_support {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi) :
    BaseResidual.HigherInteriorSupport (modifiedCoefficients W Q M) (activeLeft W) (activeRight W) :=
  modified_higherInteriorSupport W Q M (activeLeft_margin W) (outer_before_upper W)

theorem modified_quotients_smooth {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ContDiff ℝ ∞ (BaseResidual.higherStressQuotient (modifiedCoefficients W Q M)
      (BaseResidual.activeZeta c (activeLeft W) (activeRight W)) j) :=
  BaseResidual.higherStressQuotient_smooth_of_support (modifiedCoefficients_smooth W Q M) hc
    (modified_higher_support W Q M) j

end FixedGeometry

section SelectedSchedules

open BaseResidual

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)

/-- This is one actual choice for the enlarged bundle.  The ordinary base
schedule and the weighted stress estimate use this very same function. -/
noncomputable def nominalScales : ℕ → ℕ :=
  Classical.choose (exists_admissibleScales
    (weightedBundle_smooth (nominalCoefficients_smooth W) (nominal_quotients_smooth W hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem nominalScales_spec : B ≤ nominalScales W c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (weightedBundle W.axis.normalization (nominalCoefficients W)
        (activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (nominalScales W c hc upper B) :=
  Classical.choose_spec (exists_admissibleScales
    (weightedBundle_smooth (nominalCoefficients_smooth W) (nominal_quotients_smooth W hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)












variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- The modified family gets one schedule, derived from its actual repaired
coefficients. No stress estimate enters this definition. -/
noncomputable def modifiedScales : ℕ → ℕ :=
  Classical.choose (exists_admissibleScales
    (weightedBundle_smooth (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem modifiedScales_spec : B ≤ modifiedScales W c hc upper B Q M 0 ∧
    AdmissibleScales F.data.h
      (weightedBundle W.axis.normalization (modifiedCoefficients W Q M)
        (activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (modifiedScales W c hc upper B Q M) :=
  Classical.choose_spec (exists_admissibleScales
    (weightedBundle_smooth (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem modifiedScales_admissible :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M))
      (innerBox 0 (scaleUpper W upper)) (modifiedScales W c hc upper B Q M) :=
  weightedBundle_base_scales (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
    (modifiedScales_spec W c hc upper B Q M).2

theorem modifiedScales_strictMono : StrictMono (modifiedScales W c hc upper B Q M) :=
  (modifiedScales_spec W c hc upper B Q M).2.strictMono

theorem modifiedScales_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (baseResidual (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) :=
  modified_allJetsFlat W Q M P (admissibleScales_mono (modifiedScales_admissible W c hc upper B Q M)
    (fun _ hw => ⟨⟨hw.1.1, hw.1.2.trans hr⟩, hw.2⟩))

theorem modifiedScales_origin {t : ℝ} (ht : t < 1) :
    baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 :=
  modified_origin W Q M (modifiedScales_strictMono W c hc upper B Q M) ht

theorem modifiedScales_speedUnbounded :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) :=
  modified_speedUnbounded W Q M (modifiedScales_strictMono W c hc upper B Q M)


theorem modifiedScales_potential_smooth :
    ContDiffOn ℝ ∞
      (potential (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) past :=
  potential_smooth (modifiedScales_strictMono W c hc upper B Q M) (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization

end SelectedSchedules

section ActualWeightedStress

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)


variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- A finite modification additionally retains its literal angular history.
This fixes the first-order integration constant; the actual modulation
witness proves this equality from its five restored rows. -/
theorem modifiedScales_weighted_bound
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta)) :
    WeightedStressBound (modifiedScales W c hc upper B Q M) F.data.h (modifiedCoefficients W Q M)
      c (activeLeft W) (activeRight W) := by
  refine weighted_on_actual_scales (height_pos W) (modifiedCoefficients_smooth W Q M) hc
    (activeLeft_margin W) (core_before_collar W) ?_ (modified_higher_support W Q M) ?_
    (FirstOrderBaseEdge.modified_first_edgeJets W Q M hI hc (activeLeft_before_collar W))
    (innerBox_isCompact 0 (scaleUpper W upper)) (activeWindow_subset_box W upper)
    (modifiedScales_spec W c hc upper B Q M).2
  · apply Real.exp_lt_exp.mpr
    change terminalShift W + 3 - 1 < terminalShift W + 3
    linarith
  · intro w hw
    have hz := coefficients_stress_zero_left (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
      (modifiedZeroOrder W Q M) M.contains 1 hw.le
    exact Prod.ext hz.1 hz.2

end ActualWeightedStress

namespace Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- The coefficients are rebuilt from this particular solved finite
modulation, using its preserved histories and its original nominal witness. -/
noncomputable def coefficients : Coefficients :=
  modifiedCoefficients W v.profiles v.finiteModification

theorem coefficients_smooth : SmoothCoefficients (coefficients v) :=
  modifiedCoefficients_smooth W v.profiles v.finiteModification

noncomputable def scales (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) : ℕ → ℕ :=
  modifiedScales W c hc upper B v.profiles v.finiteModification

theorem scales_spec (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    B ≤ scales v c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (BaseResidual.weightedBundle W.axis.normalization (coefficients v)
        (BaseResidual.activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_spec W c hc upper B v.profiles v.finiteModification

theorem scales_admissible (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (coefficients v))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_admissible W c hc upper B v.profiles v.finiteModification

theorem scales_strictMono (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    StrictMono (scales v c hc upper B) := (scales_spec v c hc upper B).2.strictMono

noncomputable def velocity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  baseVelocity (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def pressure (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.PressureField :=
  basePressure (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def stressForce (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseStressForce (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def error (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseResidual (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

noncomputable def vectorPotential (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  potential (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

theorem velocity_eq_curl (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    velocity v c hc upper B = SpatialCurl.spatialCurl (vectorPotential v c hc upper B) := rfl

theorem vectorPotential_smooth (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (vectorPotential v c hc upper B) BaseResidual.past :=
  modifiedScales_potential_smooth W c hc upper B v.profiles v.finiteModification


theorem origin (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    velocity v c hc upper B (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • ProblemStatement.coordinateVector 2 :=
  modifiedScales_origin W c hc upper B v.profiles v.finiteModification ht

theorem speedUnbounded (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpeedUnboundedAtOne (velocity v c hc upper B) :=
  modifiedScales_speedUnbounded W c hc upper B v.profiles v.finiteModification

theorem finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization (coefficients v)
      (asSlowProfiles (modifiedScheme W v.profiles v.finiteModification)) :=
  modified_finiteIdentities W v.profiles v.finiteModification

theorem residual_identity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) (z : ProblemStatement.SpaceTime) :
    ProblemStatement.navierStokesResidual (velocity v c hc upper B) (pressure v c hc upper B) z.1 z.2 =
      stressForce v c hc upper B z + error v c hc upper B z :=
  BaseResidual.baseResidual_identity _ _ _ _ z

theorem error_allJetsFlat (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1) (error v c hc upper B) :=
  modifiedScales_allJetsFlat W c hc upper B v.profiles v.finiteModification P hr

/-- Every finite identity and support input of this weighted estimate is
proved for the same actual modulation witness. -/
theorem weighted_bound (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    WeightedStressBound (scales v c hc upper B) F.data.h (coefficients v)
      c (activeLeft W) (activeRight W) :=
  modifiedScales_weighted_bound W c hc upper B v.profiles v.finiteModification
    (fun _ heta => v.slow_outer_angular heta)

end Modulated


end NavierStokes.ConstructedSlowBase
