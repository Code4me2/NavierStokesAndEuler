import NavierStokes.SolenoidalDiagonal
import NavierStokes.AxisymmetricResidual
import NavierStokes.PhysicalWaveSum
import NavierStokes.VariableGaugeMean
import NavierStokes.ResidualCalculus
import NavierStokes.SpatialLocalization
import NavierStokes.OffplaneCorrectionExtensions
import NavierStokes.LocalRankDefect

/-!
# Direct angular means in the physical diagonal

The angular velocity is retained as a direct field. It is not replaced by
an axial primitive. Axisymmetry proves its divergence equation, and an
annular zero germ removes the coordinate singularity on the axis.
-/

noncomputable section

namespace NavierStokes.DirectAngularDiagonal

open Set Function Filter ProblemStatement
open scoped Topology ContDiff BigOperators

abbrev Slow := ℝ × ℝ
abbrev CylPoint := ℝ × (ℝ × ℝ)
abbrev Coefficient := CylPoint → ℝ

noncomputable def radius (w : SpaceTime) : ℝ :=
  PolarCharts.radius (PhysicalGraphBounds.radialProjection w)

noncomputable def slowPoint (w : SpaceTime) : Slow := (w.1, w.2 2)

noncomputable def cylPoint (w : SpaceTime) : CylPoint := (w.1, (radius w, w.2 2))

noncomputable def slowOfCyl (p : CylPoint) : Slow := (p.1, p.2.2)

noncomputable def physicalDomain (U : Set Slow) : Set SpaceTime := slowPoint ⁻¹' U

noncomputable def positiveDomain (U : Set Slow) : Set CylPoint :=
  {p | slowOfCyl p ∈ U ∧ 0 < p.2.1}

theorem slowPoint_smooth : ContDiff ℝ ∞ slowPoint :=
  contDiff_fst.prodMk ((AxisymmetricFields.projection 2).contDiff.comp contDiff_snd)

theorem physicalDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (physicalDomain U) :=
  hU.preimage slowPoint_smooth.continuous

theorem positiveDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (positiveDomain U) :=
  (hU.preimage (continuous_fst.prodMk continuous_snd.snd)).inter
    (isOpen_lt continuous_const continuous_snd.fst)

theorem radius_nonneg (w : SpaceTime) : 0 ≤ radius w := PolarCharts.radius_nonneg _

theorem radius_continuous : Continuous radius :=
  PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous

noncomputable def profileToCyl (p : AxisymmetricFields.ProfilePoint) : CylPoint :=
  (p.1, (Real.sqrt (2 * p.2.1), p.2.2))

noncomputable def rate (b : Coefficient) (p : AxisymmetricFields.ProfilePoint) : ℝ :=
  b (profileToCyl p) / Real.sqrt (2 * p.2.1)

/-- Literal angular velocity with physical tangential magnitude `b`. -/
noncomputable def angularField (b : Coefficient) (w : SpaceTime) : Space :=
  (-w.2 1 / radius w * b (cylPoint w)) • coordinateVector 0 +
    (w.2 0 / radius w * b (cylPoint w)) • coordinateVector 1

noncomputable def rotationField (F : AxisymmetricFields.Profile) (w : SpaceTime) : Space :=
  AxisymmetricResidual.pack (-w.2 1 * F (AxisymmetricFields.profilePoint w.1 w.2))
    (w.2 0 * F (AxisymmetricFields.profilePoint w.1 w.2)) 0

theorem profileToCyl_profilePoint (w : SpaceTime) :
    profileToCyl (AxisymmetricFields.profilePoint w.1 w.2) = cylPoint w := by
  have he : 2 * AxisymmetricFields.radialEnergy w.2 = w.2 0 ^ 2 + w.2 1 ^ 2 := by
    unfold AxisymmetricFields.radialEnergy
    ring
  simp only [profileToCyl, AxisymmetricFields.profilePoint, he, cylPoint, radius,
    PolarCharts.radius, PhysicalGraphBounds.radialProjection_apply]

theorem angularField_eq_rotationField (b : Coefficient) : angularField b = rotationField (rate b) := by
  funext w
  have hr : Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) = radius w :=
    congrArg (fun p : CylPoint => p.2.1) (profileToCyl_profilePoint w)
  simp only [angularField, rotationField, rate]
  rw [profileToCyl_profilePoint]
  simp only [AxisymmetricFields.profilePoint, hr, AxisymmetricResidual.pack, zero_smul, add_zero]
  congr 1 <;> congr 1 <;> ring

/-- The cancellation is computed from actual Cartesian derivatives. -/
theorem divergence_rotationField {F : AxisymmetricFields.Profile} {w : SpaceTime}
    (hF : DifferentiableAt ℝ F (AxisymmetricFields.profilePoint w.1 w.2)) :
    spatialDivergence (rotationField F) w.1 w.2 = 0 := by
  have hf := AxisymmetricFields.hasFDerivAt_profile_composition F w.1 w.2 hF
  have hd := AxisymmetricResidual.hasFDerivAt_pack
    ((AxisymmetricFields.projection 1).hasFDerivAt.neg.mul hf)
    ((AxisymmetricFields.projection 0).hasFDerivAt.mul hf)
    (hasFDerivAt_const (0 : ℝ) w.2)
  unfold spatialDivergence spatialDerivative
  change (∑ i : Fin 3, fderiv ℝ (fun x => rotationField F (w.1, x)) w.2
    (coordinateVector i) i) = 0
  rw [show fderiv ℝ (fun x => rotationField F (w.1, x)) w.2 = _ from hd.fderiv,
    Fin.sum_univ_three]
  simp [AxisymmetricResidual.packDerivative_apply, AxisymmetricFields.profileDerivative_apply,
    AxisymmetricFields.projection, coordinateVector]
  ring

theorem rotationField_smoothAt {F : AxisymmetricFields.Profile} {w : SpaceTime}
    (hF : ContDiffAt ℝ ∞ F (AxisymmetricFields.profilePoint w.1 w.2)) :
    ContDiffAt ℝ ∞ (rotationField F) w := by
  have hf := hF.comp w AxisymmetricFields.contDiff_profilePoint.contDiffAt
  exact (((((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).contDiffAt.neg.mul hf).smul
    contDiffAt_const).add
    ((((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd).contDiffAt.mul hf).smul
      contDiffAt_const)).add (show ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : ℝ) • coordinateVector 2) w from contDiffAt_const)

theorem rate_smoothAt {U : Set Slow} (hU : IsOpen U) {b : Coefficient}
    (hb : ContDiffOn ℝ ∞ b (positiveDomain U)) {w : SpaceTime}
    (hw : w ∈ physicalDomain U) (hr : 0 < radius w) :
    ContDiffAt ℝ ∞ (rate b) (AxisymmetricFields.profilePoint w.1 w.2) := by
  have he : 2 * AxisymmetricFields.radialEnergy w.2 = w.2 0 ^ 2 + w.2 1 ^ 2 := by
    unfold AxisymmetricFields.radialEnergy
    ring
  have hpos : 0 < 2 * AxisymmetricFields.radialEnergy w.2 := by
    rw [he]
    exact Real.sqrt_pos.mp hr
  have hs : ContDiffAt ℝ ∞ (fun p : AxisymmetricFields.ProfilePoint => Real.sqrt (2 * p.2.1))
      (AxisymmetricFields.profilePoint w.1 w.2) :=
    (contDiffAt_const.mul contDiffAt_snd.fst).sqrt hpos.ne'
  have hp : profileToCyl (AxisymmetricFields.profilePoint w.1 w.2) ∈ positiveDomain U := by
    rw [profileToCyl_profilePoint]
    exact ⟨hw, hr⟩
  have hb' := hb.contDiffAt ((positiveDomain_open hU).mem_nhds hp)
  exact (hb'.comp _ (contDiffAt_fst.prodMk (hs.prodMk contDiffAt_snd.snd))).div hs
    (Real.sqrt_pos.mpr hpos).ne'

/-- A moving positive inner support radius is a primitive support datum.
It may shrink as the physical terminal point is approached. -/
structure AngularData (U : Set Slow) where
  scalar : Coefficient
  smooth : ContDiffOn ℝ ∞ scalar (positiveDomain U)
  inner : Slow → ℝ
  inner_continuous : ContinuousOn inner U
  inner_pos : ∀ s ∈ U, 0 < inner s
  vanishes : ∀ p, slowOfCyl p ∈ U → 0 ≤ p.2.1 → p.2.1 < inner (slowOfCyl p) → scalar p = 0

namespace AngularData

variable {U : Set Slow} (D : AngularData U)

theorem field_zero_germ (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U)
    (hr : radius w < D.inner (slowPoint w)) :
    angularField D.scalar =ᶠ[𝓝 w] fun _ => 0 := by
  have hi : ContinuousAt (fun y => D.inner (slowPoint y)) w :=
    (D.inner_continuous.continuousAt (hU.mem_nhds hw)).comp slowPoint_smooth.continuous.continuousAt
  have hp := (hi.sub radius_continuous.continuousAt)
    (lt_mem_nhds (sub_pos.mpr hr))
  filter_upwards [(physicalDomain_open hU).mem_nhds hw, hp] with y hy hpy
  have hz := D.vanishes (cylPoint y) hy (radius_nonneg y) (sub_pos.mp hpy)
  simp only [angularField, hz, mul_zero, zero_smul, add_zero]

theorem field_smoothAt (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    ContDiffAt ℝ ∞ (angularField D.scalar) w := by
  by_cases hr : 0 < radius w
  · rw [angularField_eq_rotationField]
    exact rotationField_smoothAt (rate_smoothAt hU D.smooth hw hr)
  · have hz : radius w = 0 := le_antisymm (le_of_not_gt hr) (radius_nonneg w)
    exact contDiffAt_const.congr_of_eventuallyEq
      (D.field_zero_germ hU hw (hz ▸ D.inner_pos _ hw))

theorem field_smooth (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (angularField D.scalar) (physicalDomain U) :=
  fun _ hw => (D.field_smoothAt hU hw).contDiffWithinAt

theorem field_divergence (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    spatialDivergence (angularField D.scalar) w.1 w.2 = 0 := by
  by_cases hr : 0 < radius w
  · rw [angularField_eq_rotationField]
    exact divergence_rotationField ((rate_smoothAt hU D.smooth hw hr).differentiableAt (by simp))
  · have hz : radius w = 0 := le_antisymm (le_of_not_gt hr) (radius_nonneg w)
    have he := (D.field_zero_germ hU hw (hz ▸ D.inner_pos _ hw)).comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
    have he' : (fun y : Space => angularField D.scalar (w.1, y)) =ᶠ[𝓝 w.2] fun _ => 0 := he
    unfold spatialDivergence spatialDerivative
    rw [he'.fderiv_eq]
    simp

noncomputable def multiply (f : Coefficient) (hf : ContDiffOn ℝ ∞ f (positiveDomain U)) : AngularData U where
  scalar p := f p * D.scalar p
  smooth := hf.mul D.smooth
  inner := D.inner
  inner_continuous := D.inner_continuous
  inner_pos := D.inner_pos
  vanishes p hp hr hi := by rw [D.vanishes p hp hr hi, mul_zero]

end AngularData

theorem angularField_axis (b : Coefficient) (t : ℝ) (x : Space) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    angularField b (t, x) = 0 := by
  simp [angularField, h0, h1]

theorem angularField_mul (f b : Coefficient) :
    angularField (fun p => f p * b p) = fun w => f (cylPoint w) • angularField b w := by
  funext w
  simp only [angularField, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

noncomputable def cutCoefficient (a : ℝ) (q b : Coefficient) : Coefficient :=
  fun p => SmoothCutoffs.scaledCutoff a (q p) * b p

theorem cut_angularField (a : ℝ) (q b : Coefficient) :
    angularField (cutCoefficient a q b) =
      fun w => SmoothCutoffs.scaledCutoff a (q (cylPoint w)) • angularField b w :=
  angularField_mul _ _

noncomputable def AngularData.cut {U : Set Slow} (D : AngularData U) (a : ℝ)
    (q : Coefficient) (hq : ContDiffOn ℝ ∞ q (positiveDomain U)) : AngularData U :=
  D.multiply (fun p => SmoothCutoffs.scaledCutoff a (q p))
    ((SmoothCutoffs.scaledCutoff_contDiff a).comp_contDiffOn hq)

theorem divergence_cut_angular {U : Set Slow} (hU : IsOpen U) (D : AngularData U)
    (a : ℝ) (q : Coefficient) (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    spatialDivergence (fun y => SmoothCutoffs.scaledCutoff a (q (cylPoint y)) • angularField D.scalar y)
      w.1 w.2 = 0 := by
  rw [← cut_angularField]
  exact (D.cut a q hq).field_divergence hU hw

/-! ## Locally finite direct angular sums -/

noncomputable def angularSum (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (b : ℕ → Coefficient) : VelocityField :=
  SolenoidalDiagonal.potentialSum a q (fun j => angularField (b j))

noncomputable def angularPartial (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (b : ℕ → Coefficient) (N : ℕ) : VelocityField :=
  SolenoidalDiagonal.partialPotential a q (fun j => angularField (b j)) N

theorem divergence_congr {v w : VelocityField} {x : SpaceTime} (h : v =ᶠ[𝓝 x] w) :
    spatialDivergence v x.1 x.2 = spatialDivergence w x.1 x.2 := by
  have he : (fun y : Space => v (x.1, y)) =ᶠ[𝓝 x.2] fun y => w (x.1, y) :=
    h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  unfold spatialDivergence spatialDerivative
  rw [he.fderiv_eq]

theorem divergence_finset_sum {I : Type} (J : Finset I) (v : I → VelocityField)
    (x : SpaceTime) (hv : ∀ j ∈ J, DifferentiableAt ℝ (fun y : Space => v j (x.1, y)) x.2) :
    spatialDivergence (fun y => ∑ j ∈ J, v j y) x.1 x.2 =
      ∑ j ∈ J, spatialDivergence (v j) x.1 x.2 := by
  unfold spatialDivergence spatialDerivative
  rw [fderiv_fun_sum hv]
  simp only [_root_.sum_apply]
  calc
    _ = ∑ i : Fin 3, ∑ j ∈ J, (fderiv ℝ (fun y => v j (x.1, y)) x.2 (coordinateVector i)) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact map_sum (EuclideanSpace.proj i) _ _
    _ = _ := Finset.sum_comm

theorem angularSum_eventuallyEq_partial {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {x : SpaceTime} (hq : ContinuousAt q x) (hx : 0 < q x)
    (b : ℕ → Coefficient) :
    ∃ N : ℕ, angularSum a q b =ᶠ[𝓝 x] angularPartial a q b N :=
  SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha hq hx _

theorem angularSum_smooth {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q (physicalDomain U)) (hpos : ∀ x ∈ physicalDomain U, 0 < q x) :
    ContDiffOn ℝ ∞ (angularSum a q (fun j => (D j).scalar)) (physicalDomain U) :=
  SolenoidalDiagonal.potentialSum_contDiffOn ha (physicalDomain_open hU) hpos hq
    (fun j => (D j).field_smooth hU)



theorem angularSum_divergence {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (q : Coefficient)
    (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    (hqp : ContDiffOn ℝ ∞ (fun x => q (cylPoint x)) (physicalDomain U))
    (hpos : ∀ x ∈ physicalDomain U, 0 < q (cylPoint x))
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    spatialDivergence (angularSum a (fun x => q (cylPoint x)) (fun j => (D j).scalar)) x.1 x.2 = 0 := by
  have hqAt := hqp.contDiffAt ((physicalDomain_open hU).mem_nhds hx)
  obtain ⟨N, hN⟩ := angularSum_eventuallyEq_partial ha hqAt.continuousAt (hpos x hx)
    (fun j => (D j).scalar)
  rw [divergence_congr hN]
  have hs (j : ℕ) : DifferentiableAt ℝ
      (fun y : Space => SolenoidalDiagonal.cutStage a (fun x => q (cylPoint x))
        (fun j => angularField (D j).scalar) j (x.1, y)) x.2 :=
    ((SolenoidalDiagonal.cutStage_contDiffAt hqAt
      (fun j => (D j).field_smoothAt hU hx) j).comp x.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change spatialDivergence (fun y => ∑ j ∈ Finset.range N,
    SolenoidalDiagonal.cutStage a (fun x => q (cylPoint x)) (fun j => angularField (D j).scalar) j y) x.1 x.2 = 0
  rw [divergence_finset_sum _ _ x (fun j _ => hs j)]
  apply Finset.sum_eq_zero
  intro j _
  exact divergence_cut_angular hU (D j) (a j) q hq hx

theorem angularSum_axis (a : ℕ → ℝ) (q : SpaceTime → ℝ) (b : ℕ → Coefficient)
    (t : ℝ) (x : Space) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    angularSum a q b (t, x) = 0 := by
  simp only [angularSum, SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage,
    angularField_axis _ _ _ h0 h1, smul_zero, tsum_zero]


/-! ## Curl potentials plus direct angular velocity -/

noncomputable def mixedVelocity (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (A : ℕ → VelocityField) (b : ℕ → Coefficient) : VelocityField :=
  fun x => SolenoidalDiagonal.velocitySum a q A x + angularSum a q b x




/-! ## The actual similarity cutoff -/

noncomputable def preterminalSlow : Set Slow := {s | s.1 < 1}

theorem preterminalSlow_open : IsOpen preterminalSlow := isOpen_lt continuous_fst continuous_const

noncomputable def qCoefficient (h : ℝ) : Coefficient := SimilarityProfile.q h



theorem qCoefficient_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (qCoefficient h) (positiveDomain preterminalSlow) :=
  fun _ hp => (SimilarityProfile.q_smoothAt hh hh1 hp.1).contDiffWithinAt

theorem physicalQ_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) (physicalDomain preterminalSlow) :=
  fun _ hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt




/-! ## The existing Cartesian spatial cutoff is axisymmetric -/

noncomputable def spatialProfile (p : CylPoint) : ℝ :=
  SpatialLocalization.cutoffProfile (p.2.1 ^ 2, p.2.2)

theorem spatialProfile_smooth : ContDiff ℝ ∞ spatialProfile :=
  SpatialLocalization.cutoffProfile_contDiff.comp ((contDiff_snd.fst.pow 2).prodMk contDiff_snd.snd)

theorem spatialProfile_physical (w : SpaceTime) :
    spatialProfile (cylPoint w) = SpatialLocalization.spatialCutoff w.2 := by
  have hr : radius w ^ 2 = w.2 0 ^ 2 + w.2 1 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  simp only [spatialProfile, cylPoint, hr, SpatialLocalization.spatialCutoff,
    SpatialLocalization.radialSquare]


theorem angularSum_multiply (a : ℕ → ℝ) (q : SpaceTime → ℝ) (f : Coefficient)
    (b : ℕ → Coefficient) :
    angularSum a q (fun j p => f p * b j p) = fun w => f (cylPoint w) • angularSum a q b w := by
  funext w
  simp only [angularSum, SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage, angularField_mul]
  simp_rw [smul_comm (SmoothCutoffs.scaledCutoff _ _) (f (cylPoint w))]
  exact tsum_const_smul'' _

theorem spatialCut_angularSum (a : ℕ → ℝ) (q : SpaceTime → ℝ) (b : ℕ → Coefficient) :
    SpatialLocalization.cutPotential (angularSum a q b) =
      angularSum a q (fun j p => spatialProfile p * b j p) := by
  rw [angularSum_multiply]
  funext w
  rw [spatialProfile_physical]
  rfl

theorem spatialCut_angularSum_divergence {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (q : Coefficient)
    (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    (hqp : ContDiffOn ℝ ∞ (fun x => q (cylPoint x)) (physicalDomain U))
    (hpos : ∀ x ∈ physicalDomain U, 0 < q (cylPoint x))
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    spatialDivergence (SpatialLocalization.cutPotential
      (angularSum a (fun x => q (cylPoint x)) (fun j => (D j).scalar))) x.1 x.2 = 0 := by
  rw [spatialCut_angularSum]
  exact angularSum_divergence hU
    (fun j => (D j).multiply spatialProfile spatialProfile_smooth.contDiffOn) ha q hq hqp hpos hx


/-! ## Actual full-fiber means restricted to a physical graph -/

abbrev Lift := PressureStream.Lift Slow

/-- The time/axial variables in the actual mean-field convention `(T,Z)`. -/
noncomputable def graphSlow (G : PhysicalResidualBridge.ScaledGraph) (s : Slow) : Slow :=
  (G.velocityScale * G.radialScale * G.epsilon * (1 - s.1),
    G.radialScale * G.epsilon * s.2)

noncomputable def graphPoint (G : PhysicalResidualBridge.ScaledGraph) (p : CylPoint) : Lift :=
  (G.radialScale * p.2.1, (graphSlow G (slowOfCyl p),
    (G.frequency * (G.radialScale * p.2.1) ^ G.exponent) • G.radialVector +
      (G.velocityScale * G.radialScale * G.fastCoefficient * p.1) • G.temporalVector))

/-- The physical velocity normalization is included here. -/
noncomputable def graphCoefficient (G : PhysicalResidualBridge.ScaledGraph) (f : Lift → ℝ) : Coefficient :=
  fun p => G.velocityScale * f (graphPoint G p)










/-! ## Agreement with the actual offplane continuation fields -/






/-! ## Mixed finite prefixes and preservation of every axis jet -/



theorem potentialSum_zero_germ {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {x : SpaceTime} (hq : ContinuousAt q x) (hpos : 0 < q x)
    (A : ℕ → VelocityField) (hA : ∀ j, A j =ᶠ[𝓝 x] fun _ => 0) :
    SolenoidalDiagonal.potentialSum a q A =ᶠ[𝓝 x] fun _ => 0 := by
  obtain ⟨N, hN⟩ := SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha hq hpos A
  have hz (j : ℕ) : SolenoidalDiagonal.cutStage a q A j =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hA j] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, smul_zero]
  apply hN.trans
  filter_upwards [(Filter.eventually_all_finset (Finset.range N)).2 (fun j _ => hz j)] with y hy
  exact Finset.sum_eq_zero hy



end NavierStokes.DirectAngularDiagonal
