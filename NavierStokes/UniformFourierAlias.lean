import NavierStokes.FourierAlias
import NavierStokes.WeightedRadialPrimitive
import NavierStokes.RadialPullback
import NavierStokes.SmoothFamilyTorusInverse
import NavierStokes.WithTopLemmas

/-!
# Uniform seminorm bounds for families of exact Fourier aliases

All constants are chosen before the source and the band. The estimates use
actual derivatives and actual translated integrals.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Interval Topology BigOperators

namespace NavierStokes.UniformFourierAlias

open TorusInverse JetBounds

section JetOperations

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finiteJetBound_fixedPartial {f : D → E} (hf : ContDiff ℝ ∞ f)
    {s : Set D} {C : ℝ} {m : ℕ} (hb : FiniteJetBound (m + 1) f s C)
    (v : D) (hv : ‖v‖ ≤ 1) :
    FiniteJetBound m (fun x => fderiv ℝ f x v) s C := by
  intro j hj z hz
  have h := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (c := v)
    (hf.fderiv_right (by simp)).contDiffAt (natCast_le_infty j) (x := z)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans ((mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb (j + 1) (Nat.add_le_add_right hj 1) z hz))

end JetOperations

section IterationBounds

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sourceJet_mem (G : (ℝ × E → F) → Prop) (J : (ℝ × E → F) → ℝ × E → F)
    (hclosed : ∀ f, G f → G (RadialAlias.slowDeriv (J f))) (p : ℕ)
    {f : ℝ × E → F} (hf : G f) : G (RadialAlias.sourceJet J f p) := by
  induction p with
  | zero => exact hf
  | succ p ih =>
    rw [RadialAlias.sourceJet_succ]
    exact hclosed _ ih


end IterationBounds

section Integrals

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The exact defect in the compact transport primitive, with all auxiliary
slow variables retained in `E`. -/
noncomputable def exactAlias (χ : ℝ → ℝ) (M : ℝ) (v : E)
    (f : ℝ × E → F) (z : ℝ × E) : F :=
  deriv χ z.1 • TransportPrimitive.totalIntegral M v f z








end Integrals

section RealTransfer

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def complexify (f : D → ℝ) (z : D) : ℂ := f z

theorem complexify_smooth {f : D → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexify f) := Complex.ofRealCLM.contDiff.comp hf

theorem norm_iteratedFDeriv_complexify {f : D → ℝ} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (z : D) :
    ‖iteratedFDeriv ℝ m (complexify f) z‖ = ‖iteratedFDeriv ℝ m f z‖ :=
  Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (natCast_le_infty m)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem complexify_supported {a b : ℝ} {f : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (complexify f) := by
  intro z hz
  apply hs
  intro h
  exact hz (by simp only [complexify, h, Complex.ofReal_zero])

theorem totalIntegral_complexify (M : ℝ) (v : E) (f : ℝ × E → ℝ) :
    TransportPrimitive.totalIntegral M v (complexify f) =
      complexify (TransportPrimitive.totalIntegral M v f) := by
  funext z
  exact Complex.ofRealLI.integral_comp_comm (fun u => f (TransportPrimitive.shift M v z u))

theorem norm_iteratedFDeriv_totalIntegral_complexify {a b M : ℝ} {v : E}
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (m : ℕ) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ m (TransportPrimitive.totalIntegral M v (complexify f)) z‖ =
      ‖iteratedFDeriv ℝ m (TransportPrimitive.totalIntegral M v f) z‖ := by
  rw [totalIntegral_complexify]
  exact norm_iteratedFDeriv_complexify (TransportPrimitive.totalIntegral_contDiff hf hs) m z



end RealTransfer

section ParameterGeometry

variable {S F : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reassociate radial, slow, and torus variables without changing the norm. -/
noncomputable def toProduct (f : ℝ × (S × Plane) → F) (z : (ℝ × S) × Plane) : F :=
  f (z.1.1, (z.1.2, z.2))

noncomputable def fromProduct (f : (ℝ × S) × Plane → F) (z : ℝ × (S × Plane)) : F :=
  f ((z.1, z.2.1), z.2.2)



theorem toProduct_smooth {f : ℝ × (S × Plane) → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (toProduct f) :=
  hf.comp (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).toContinuousLinearEquiv.contDiff

theorem fromProduct_smooth {f : (ℝ × S) × Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fromProduct f) :=
  hf.comp (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv.contDiff

theorem norm_iteratedFDeriv_toProduct (f : ℝ × (S × Plane) → F)
    (m : ℕ) (z : (ℝ × S) × Plane) :
    ‖iteratedFDeriv ℝ m (toProduct f) z‖ =
      ‖iteratedFDeriv ℝ m f (z.1.1, (z.1.2, z.2))‖ :=
  (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).norm_iteratedFDeriv_comp_right f z m

theorem norm_iteratedFDeriv_fromProduct (f : (ℝ × S) × Plane → F)
    (m : ℕ) (z : ℝ × (S × Plane)) :
    ‖iteratedFDeriv ℝ m (fromProduct f) z‖ =
      ‖iteratedFDeriv ℝ m f ((z.1, z.2.1), z.2.2)‖ :=
  (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.norm_iteratedFDeriv_comp_right f z m

noncomputable def sourceMean (f : ℝ × (S × Plane) → F) (p : ℝ × S) : F :=
  FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y)))

noncomputable def SourcePeriodic (f : ℝ × (S × Plane) → F) : Prop :=
  ∀ U s, FourierAlias.TorusPeriodic (fun Y => f (U, (s, Y)))







omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceMean_complexify (f : ℝ × (S × Plane) → ℝ) (p : ℝ × S) :
    sourceMean (complexify f) p = ((sourceMean f p : ℝ) : ℂ) := by
  simp only [sourceMean, FourierAlias.torusMean, complexify, intervalIntegral.integral_ofReal]

end ParameterGeometry

section RealInverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def ParameterPeriodic {F : Type} (f : P × Plane → F) : Prop :=
  ∀ p, FourierAlias.TorusPeriodic (fun Y => f (p, Y))

noncomputable def parameterMean {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P × Plane → F) (p : P) : F := FourierAlias.torusMean (fun Y => f (p, Y))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexify_parameterPeriodic {f : P × Plane → ℝ} (hp : ParameterPeriodic f) :
    SmoothFamilyTorusInverse.Periodic (complexify f) := by
  intro p Y k
  exact congrArg Complex.ofReal (hp p Y k)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem parameterMean_complexify (f : P × Plane → ℝ) (p : P) :
    parameterMean (complexify f) p = ((parameterMean f p : ℝ) : ℂ) := by
  simp only [parameterMean, FourierAlias.torusMean, complexify, intervalIntegral.integral_ofReal]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem familyMean_eq_parameterMean (f : P × Plane → ℂ) (p : P) :
    SmoothFamilyTorusInverse.mean f p = parameterMean f p :=
  SmoothFamilyTorusInverse.mean_eq_integral f p


/-- A genuine real directional inverse, obtained from the actual complex
Fourier inverse by real part. -/
noncomputable def realInverse (d : Direction) (f : P × Plane → ℝ) (z : P × Plane) : ℝ :=
  Complex.re (SmoothFamilyTorusInverse.inverse d (complexify f) z)

noncomputable def realCentered (f : P × Plane → ℝ) (z : P × Plane) : ℝ :=
  f z - parameterMean f z.1

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexify_realCentered (f : P × Plane → ℝ) :
    complexify (realCentered f) = SmoothFamilyTorusInverse.nonbarPart (complexify f) := by
  funext z
  change ((f z - parameterMean f z.1 : ℝ) : ℂ) =
    (f z : ℂ) - SmoothFamilyTorusInverse.mean (complexify f) z.1
  rw [Complex.ofReal_sub, familyMean_eq_parameterMean, parameterMean_complexify]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realCentered_eq_re_nonbar (f : P × Plane → ℝ) :
    realCentered f = fun z => Complex.re (SmoothFamilyTorusInverse.nonbarPart (complexify f) z) := by
  funext z
  have h := congrArg Complex.re (congrFun (complexify_realCentered f) z)
  exact h

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realCentered_periodic {f : P × Plane → ℝ} (hp : ParameterPeriodic f) :
    ParameterPeriodic (realCentered f) := by
  intro p Y k
  exact congrArg (fun c => c - parameterMean f p) (hp p Y k)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realCentered_preserves_parameter_support (f : P × Plane → ℝ)
    (S : Set P) (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) :
    ∀ p, p ∉ S → ∀ Y, realCentered f (p, Y) = 0 := by
  have hc := SmoothFamilyTorusInverse.nonbarPart_preserves_parameter_support (complexify f) S
    (fun p hp Y => by simp only [complexify, hs p hp Y, Complex.ofReal_zero])
  intro p hp Y
  rw [realCentered_eq_re_nonbar]
  change Complex.re (SmoothFamilyTorusInverse.nonbarPart (complexify f) (p, Y)) = 0
  rw [hc p hp Y, Complex.zero_re]



variable [FiniteDimensional ℝ P]

theorem realCentered_smooth {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ParameterPeriodic f) : ContDiff ℝ ∞ (realCentered f) := by
  rw [realCentered_eq_re_nonbar]
  exact Complex.reCLM.contDiff.comp
    (SmoothFamilyTorusInverse.nonbarPart_smooth (complexify_smooth hf) (complexify_parameterPeriodic hp))

omit [FiniteDimensional ℝ P] in
theorem realCentered_zeroMean {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ParameterPeriodic f) : ∀ p, parameterMean (realCentered f) p = 0 := by
  intro p
  have hc := SmoothFamilyTorusInverse.nonbarPart_zeroMean (complexify_smooth hf)
    (complexify_parameterPeriodic hp) p
  rw [familyMean_eq_parameterMean, ← complexify_realCentered, parameterMean_complexify] at hc
  exact Complex.ofReal_eq_zero.mp hc




theorem norm_iteratedFDeriv_realInverse_le (d : Direction) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ParameterPeriodic f) (m : ℕ) (z : P × Plane) :
    ‖iteratedFDeriv ℝ m (realInverse d f) z‖ ≤
      ‖iteratedFDeriv ℝ m (SmoothFamilyTorusInverse.inverse d (complexify f)) z‖ := by
  have hi := SmoothFamilyTorusInverse.inverse_smooth d (complexify_smooth hf)
    (complexify_parameterPeriodic hp)
  have hnorm : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro c
    simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm c
  exact (SmoothFamilyTorusInverse.norm_jet_linear Complex.reCLM hi m z).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _))

theorem realInverse_finiteJets (d : Direction) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : P × Plane → ℝ) (A : Set P) (C : ℝ),
      ContDiff ℝ ∞ f → ParameterPeriodic f → 0 ≤ C →
      (∀ j ≤ m + 5, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C) →
      ∀ j ≤ m, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j (realInverse d f) (p, Y)‖ ≤ K * C := by
  obtain ⟨K, hK, hb⟩ := SmoothFamilyTorusInverse.inverse_finiteJets (P := P) d m
  refine ⟨K, hK, ?_⟩
  intro f A C hf hp hC hsource j hj p hpA Y
  apply (norm_iteratedFDeriv_realInverse_le d hf hp j (p, Y)).trans
  apply hb (complexify f) A C (complexify_smooth hf) (complexify_parameterPeriodic hp) hC
    _ j hj p hpA Y
  intro i hi q hq Z
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi q hq Z

theorem realCentered_finiteJets (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : P × Plane → ℝ) (A : Set P) (C : ℝ),
      ContDiff ℝ ∞ f → ParameterPeriodic f → 0 ≤ C →
      (∀ j ≤ m + 4, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C) →
      ∀ j ≤ m, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j (realCentered f) (p, Y)‖ ≤ K * C := by
  obtain ⟨K, hK, hb⟩ := SmoothFamilyTorusInverse.nonbarPart_finiteJets (P := P) m
  refine ⟨K, hK, ?_⟩
  intro f A C hf hp hC hsource j hj p hpA Y
  rw [← norm_iteratedFDeriv_complexify (realCentered_smooth hf hp), complexify_realCentered]
  apply hb (complexify f) A C (complexify_smooth hf) (complexify_parameterPeriodic hp) hC
    _ j hj p hpA Y
  intro i hi q hq Z
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi q hq Z

end RealInverse

section TransportInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def familyInverse (d : Direction) (f : ℝ × (S × Plane) → ℂ) :
    ℝ × (S × Plane) → ℂ := fromProduct (SmoothFamilyTorusInverse.inverse d (toProduct f))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem mean_toProduct (f : ℝ × (S × Plane) → ℂ) (p : ℝ × S) :
    SmoothFamilyTorusInverse.mean (toProduct f) p = sourceMean f p :=
  SmoothFamilyTorusInverse.mean_eq_integral _ _

noncomputable def realCenterSource (f : ℝ × (S × Plane) → ℝ) : ℝ × (S × Plane) → ℝ :=
  fromProduct (realCentered (toProduct f))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem realCenterSource_apply (f : ℝ × (S × Plane) → ℝ) (z : ℝ × (S × Plane)) :
    realCenterSource f z = f z - sourceMean f (z.1, z.2.1) := rfl

theorem realCenterSource_smooth {f : ℝ × (S × Plane) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) : ContDiff ℝ ∞ (realCenterSource f) :=
  fromProduct_smooth (realCentered_smooth (toProduct_smooth hf) (fun p => hp p.1 p.2))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem realCenterSource_periodic {f : ℝ × (S × Plane) → ℝ} (hp : SourcePeriodic f) :
    SourcePeriodic (realCenterSource f) := by
  intro U s Y k
  exact realCentered_periodic (fun p => hp p.1 p.2) (U, s) Y k

omit [FiniteDimensional ℝ S] in
theorem realCenterSource_zeroMean {f : ℝ × (S × Plane) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) : ∀ p, sourceMean (realCenterSource f) p = 0 :=
  realCentered_zeroMean (toProduct_smooth hf) (fun p => hp p.1 p.2)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
/-- Radial support only constrains the regrouped parameter, so an operator
preserving the parameter support of `toProduct f` preserves it. -/
theorem radiallySupported_of_preserves {V W : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {a b : ℝ} {f : ℝ × (S × Plane) → V} {g : ℝ × (S × Plane) → W}
    (hs : RadialAlias.RadiallySupported a b f)
    (hpres : ∀ A : Set (ℝ × S), (∀ p, p ∉ A → ∀ Y : Plane, toProduct f (p, Y) = 0) →
      ∀ p, p ∉ A → ∀ Y : Plane, toProduct g (p, Y) = 0) :
    RadialAlias.RadiallySupported a b g := by
  have hi := hpres (Prod.fst ⁻¹' Icc a b)
    (fun p hp Y => by by_contra hn; exact hp (@hs (p.1, (p.2, Y)) hn))
  intro z hz
  by_contra hn
  exact hz (hi (z.1, z.2.1) hn z.2.2)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem realCenterSource_supported {a b : ℝ} {f : ℝ × (S × Plane) → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (realCenterSource f) :=
  radiallySupported_of_preserves hs
    (fun A hA => realCentered_preserves_parameter_support (toProduct f) A hA)

theorem totalIntegral_realCenterSource {a b M : ℝ} {v : Plane}
    {f : ℝ × (S × Plane) → ℝ} (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hm : ∀ s, (∫ U in a..b, sourceMean f (U, s)) = 0) (z : ℝ × (S × Plane)) :
    TransportPrimitive.totalIntegral M ((0 : S), v) (realCenterSource f) z =
      TransportPrimitive.totalIntegral M ((0 : S), v) f z := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval (realCenterSource_smooth hf hp).continuous
      (realCenterSource_supported hs),
    TransportPrimitive.totalIntegral_eq_radialInterval hf.continuous hs]
  have hshift (U : ℝ) : z.2 + (M * (U - z.1)) • ((0 : S), v) =
      (z.2.1, z.2.2 + (M * (U - z.1)) • v) := by
    apply Prod.ext <;> simp
  simp_rw [hshift, realCenterSource_apply]
  have hc : Continuous (fun U => f (U, (z.2.1, z.2.2 + (M * (U - z.1)) • v))) :=
    hf.continuous.comp (continuous_id.prodMk (continuous_const.prodMk
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).smul
        continuous_const))))
  have ht : Continuous (fun U => Complex.re
      (SmoothFamilyTorusInverse.mean (toProduct (complexify f)) (U, z.2.1))) :=
    Complex.continuous_re.comp
      ((SmoothFamilyTorusInverse.coefficient_smooth (toProduct_smooth (complexify_smooth hf)) 0).continuous.comp
        (continuous_id.prodMk continuous_const))
  have hmc : Continuous (fun U => sourceMean f (U, z.2.1)) := by
    simpa only [mean_toProduct, sourceMean_complexify, Complex.ofReal_re] using ht
  rw [intervalIntegral.integral_sub
    (f := fun U => f (U, (z.2.1, z.2.2 + (M * (U - z.1)) • v)))
    (g := fun U => sourceMean f (U, z.2.1)) (hc.intervalIntegrable _ _) (hmc.intervalIntegrable _ _),
    hm z.2.1, sub_zero]



theorem familyInverse_smooth (d : Direction) {f : ℝ × (S × Plane) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFamilyTorusInverse.Periodic (toProduct f)) :
    ContDiff ℝ ∞ (familyInverse d f) :=
  fromProduct_smooth (SmoothFamilyTorusInverse.inverse_smooth d (toProduct_smooth hf) hp)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem familyInverse_periodic (d : Direction) (f : ℝ × (S × Plane) → ℂ) :
    SmoothFamilyTorusInverse.Periodic (toProduct (familyInverse d f)) :=
  SmoothFamilyTorusInverse.inverse_periodic d _

omit [FiniteDimensional ℝ S] in
theorem familyInverse_zeroMean (d : Direction) {f : ℝ × (S × Plane) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFamilyTorusInverse.Periodic (toProduct f)) :
    SmoothFamilyTorusInverse.ZeroMean (toProduct (familyInverse d f)) :=
  SmoothFamilyTorusInverse.inverse_zeroMean d (toProduct_smooth hf) hp

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem familyInverse_supported (d : Direction) {a b : ℝ} {f : ℝ × (S × Plane) → ℂ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (familyInverse d f) :=
  radiallySupported_of_preserves hs
    (fun A hA => SmoothFamilyTorusInverse.inverse_preserves_parameter_support d (toProduct f) A hA)

omit [FiniteDimensional ℝ S] in
theorem toProduct_slowDeriv {f : ℝ × (S × Plane) → ℂ} (hf : ContDiff ℝ ∞ f) :
    toProduct (RadialAlias.slowDeriv f) =
      SmoothFamilyTorusInverse.parameterPartial ((1 : ℝ), (0 : S)) (toProduct f) := by
  funext z
  let e := (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).toContinuousLinearEquiv
  have he := (((hf.differentiable (by simp)) (e z)).hasFDerivAt.comp z e.hasFDerivAt).fderiv
  change fderiv ℝ f (e z) (1, 0) = fderiv ℝ (f ∘ e) z ((1, 0), 0)
  rw [he]
  rfl

theorem familyInverse_solves (d : Direction) {f : ℝ × (S × Plane) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFamilyTorusInverse.Periodic (toProduct f))
    (hm : SmoothFamilyTorusInverse.ZeroMean (toProduct f)) :
    RadialAlias.directionalDeriv ((0 : S), vector d) (familyInverse d f) = f := by
  funext z
  let g := SmoothFamilyTorusInverse.inverse d (toProduct f)
  have hg : ContDiff ℝ ∞ g := SmoothFamilyTorusInverse.inverse_smooth d (toProduct_smooth hf) hp
  let e := (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv
  have he := (((hg.differentiable (by simp)) (e z)).hasFDerivAt.comp z e.hasFDerivAt).fderiv
  change fderiv ℝ (g ∘ e) z (0, (0, vector d)) = f z
  rw [he]
  have hi := congrFun (SmoothFamilyTorusInverse.inverse_solves d (toProduct_smooth hf) hp hm) (e z)
  exact hi

noncomputable def Admissible (a b : ℝ) (f : ℝ × (S × Plane) → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ SmoothFamilyTorusInverse.Periodic (toProduct f) ∧
    SmoothFamilyTorusInverse.ZeroMean (toProduct f) ∧ RadialAlias.RadiallySupported a b f

theorem admissible_step (d : Direction) {a b : ℝ} {f : ℝ × (S × Plane) → ℂ}
    (hf : Admissible a b f) : Admissible a b (RadialAlias.slowDeriv (familyInverse d f)) := by
  have hi := familyInverse_smooth d hf.1 hf.2.1
  refine ⟨TransportPrimitive.fixedDeriv_contDiff hi (1, 0), ?_, ?_,
    RadialAlias.radialSupport_slowDeriv (familyInverse_supported d hf.2.2.2)⟩
  · rw [toProduct_slowDeriv hi]
    exact SmoothFamilyTorusInverse.parameterPartial_periodic (familyInverse_periodic d f) (1, 0)
  · rw [toProduct_slowDeriv hi]
    exact SmoothFamilyTorusInverse.parameterPartial_zeroMean (toProduct_smooth hi)
      (familyInverse_zeroMean d hf.1 hf.2.1) (1, 0)





end TransportInverse

section MeanClassBounds

open WeightedRadialPrimitive WeightedClasses

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



end MeanClassBounds

section FiberClass

open WeightedClasses WeightedRadialPrimitive

variable {S F H : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A proved finite loss on each parameter fiber preserves the actual
all-order mean class, including its radial weight. -/
theorem fiberOperator_preserves_meanClass
    (T : (((ℝ × S) × Plane) → F) → ((ℝ × S) × Plane) → H) (loss : ℕ)
    (hTsmooth : ∀ f, ContDiff ℝ ∞ f → ParameterPeriodic f → ContDiff ℝ ∞ (T f))
    (hTbound : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ((ℝ × S) × Plane) → F)
      (A : Set (ℝ × S)) (C : ℝ), ContDiff ℝ ∞ f → ParameterPeriodic f → 0 ≤ C →
      (∀ j ≤ m + loss, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C) →
      ∀ j ≤ m, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j (T f) (p, Y)‖ ≤ K * C)
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → ℝ × (S × Plane) → F}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => fromProduct (T (toProduct (f n)))) := by
  let st := logStripData (E := S × Plane) a b cL cR ha hcL hcR ε R hε hεone hR
  have hprod (n : ℕ) : ParameterPeriodic (toProduct (f n)) := fun p => hp n p.1 p.2
  refine ⟨fun n z hz => st.zeta_nonneg z hz, ?_, ?_⟩
  · intro n
    exact (fromProduct_smooth (hTsmooth _ (toProduct_smooth (hfc n)) (hprod n))).contDiffOn
  · intro m
    obtain ⟨K, hK, hbound⟩ := hTbound m
    obtain ⟨C, hC, q, hb⟩ := hf.bounds (m + loss)
    refine ⟨K * C, mul_nonneg hK hC, q, ?_⟩
    intro n z hz j hj
    let B := (C * ε n ^ α * R n ^ q) * logWeight cL cR a b q z.1
    have hεα : 0 < ε n ^ α := Real.rpow_pos_of_pos (hε n) α
    have hRn : 0 ≤ R n := zero_le_one.trans (hR n)
    have hw : 0 < logWeight cL cR a b q z.1 := weight_pos cL cR q (logPosition_mem ha hz)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hin : ∀ i ≤ m + loss, ∀ p ∈ ({(z.1, z.2.1)} : Set (ℝ × S)), ∀ Y,
        ‖iteratedFDeriv ℝ i (toProduct (f n)) (p, Y)‖ ≤ B := by
      intro i hi p hpA Y
      have heq : p = (z.1, z.2.1) := Set.mem_singleton_iff.mp hpA
      subst p
      rw [norm_iteratedFDeriv_toProduct]
      have h := hb n (z.1, (z.2.1, Y)) hz i hi
      rw [logStrip_majorant_eq ha hcL hcR ε R hε hεone hR α C q n (z.1, (z.2.1, Y)) hz] at h
      exact h
    rw [norm_iteratedFDeriv_fromProduct,
      logStrip_majorant_eq ha hcL hcR ε R hε hεone hR α (K * C) q n z hz]
    calc
      _ ≤ K * B := hbound (toProduct (f n)) {(z.1, z.2.1)} B (toProduct_smooth (hfc n))
        (hprod n) hB hin j hj (z.1, z.2.1) (Set.mem_singleton _) z.2.2
      _ = ((K * C) * ε n ^ α * R n ^ q) * logWeight cL cR a b q z.1 := by dsimp [B]; ring

variable [FiniteDimensional ℝ S]


theorem meanClass_realCenterSource {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => realCenterSource (f n)) :=
  fiberOperator_preserves_meanClass realCentered 4
    (fun _ hf hp => realCentered_smooth hf hp) realCentered_finiteJets
    ha hcL hcR ε R hε hεone hR hf hfc hp

end FiberClass

section BandScales





end BandScales

section UniformFamilies

open WeightedClasses WeightedRadialPrimitive

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]


omit [FiniteDimensional ℝ S] in
theorem admissible_complexify {a b : ℝ} {f : ℝ × (S × Plane) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) (hm : ∀ p, sourceMean f p = 0)
    (hs : RadialAlias.RadiallySupported a b f) : Admissible a b (complexify f) := by
  refine ⟨complexify_smooth hf, ?_, ?_, complexify_supported hs⟩
  · intro p Y k
    exact congrArg Complex.ofReal (hp p.1 p.2 Y k)
  · intro p
    rw [mean_toProduct, sourceMean_complexify, hm p, Complex.ofReal_zero]








end UniformFamilies

end NavierStokes.UniformFourierAlias
