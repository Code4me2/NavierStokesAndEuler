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










end Nominal

section Modified

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

include M






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








end SelectedSchedules

section ActualWeightedStress

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)


variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)


end ActualWeightedStress

namespace Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- The coefficients are rebuilt from this particular solved finite
modulation, using its preserved histories and its original nominal witness. -/
noncomputable def coefficients : Coefficients :=
  modifiedCoefficients W v.profiles v.finiteModification


noncomputable def scales (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) : ℕ → ℕ :=
  modifiedScales W c hc upper B v.profiles v.finiteModification

theorem scales_spec (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    B ≤ scales v c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (BaseResidual.weightedBundle W.axis.normalization (coefficients v)
        (BaseResidual.activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_spec W c hc upper B v.profiles v.finiteModification



noncomputable def velocity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  baseVelocity (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)




noncomputable def vectorPotential (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  potential (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

theorem velocity_eq_curl (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    velocity v c hc upper B = SpatialCurl.spatialCurl (vectorPotential v c hc upper B) := rfl









end Modulated


end NavierStokes.ConstructedSlowBase
