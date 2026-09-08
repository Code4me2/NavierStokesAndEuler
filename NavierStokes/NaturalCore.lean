import NavierStokes.NaturalProfile
import NavierStokes.SimilarityCoordinates
import NavierStokes.AxisymmetricFields
import NavierStokes.SmoothParameterIntegral
import NavierStokes.BlowupImplication

/-!
# The physical natural core

The core is the actual Cartesian curl of meridional and swirl potentials
obtained from the natural profiles. All regularity assertions are on the
explicit open physical domain where those profiles have been constructed.
No assertion about the regularity of the final Navier--Stokes force is made.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace NavierStokes.NaturalCore

open ProblemStatement AxisymmetricFields

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

noncomputable def physicalQ (h : ℝ) (p : ProfilePoint) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * h) (1 - p.1, p.2.2)

noncomputable def physicalEta (h : ℝ) (p : ProfilePoint) : ℝ :=
  SimilarityCoordinates.coordinateEta (2 * h) (1 - p.1, p.2.2)

noncomputable def similarityPoint (h : ℝ) (p : ProfilePoint) : ℝ × ℝ :=
  (p.2.1 / physicalQ h p, physicalEta h p)

noncomputable def profileDomain (h Λ : ℝ) : Set ProfilePoint :=
  {p | p.1 < 1 ∧ similarityPoint h p ∈ NaturalProfile.domain Λ}

noncomputable def coreDomain (h Λ : ℝ) : Set SpaceTime :=
  {z | profilePoint z.1 z.2 ∈ profileDomain h Λ}

/-- The actual integral from zero to the radial profile coordinate. -/
noncomputable def radialPrimitive (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..p.1, f (v, p.2)

noncomputable def meridionalPotential (h : ℝ) (V : ℝ × ℝ → ℝ) : Profile := fun p =>
  physicalQ h p ^ (-NaturalAxisData.A h) * V (similarityPoint h p)

noncomputable def swirlPotential (h : ℝ) (f : ℝ × ℝ → ℝ) : Profile := fun p =>
  -(physicalQ h p ^ (-h)) * radialPrimitive f (similarityPoint h p)


noncomputable def coreVelocity (h : ℝ) (f V : ℝ × ℝ → ℝ) : VelocityField :=
  velocity (meridionalPotential h V) (swirlPotential h f)

theorem physicalQ_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : ProfilePoint} (hp : p.1 < 1) : 0 < physicalQ h p :=
  (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith)
    (sub_pos.mpr hp)).1

theorem physicalQ_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : ProfilePoint} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalQ h) p := by
  exact (SimilarityCoordinates.coordinateQ_smooth (by linarith) (by linarith)
    (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)).comp p
    ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd.snd)

theorem physicalEta_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : ProfilePoint} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (physicalEta h) p := by
  exact (SimilarityCoordinates.coordinateEta_smooth (by linarith) (by linarith)
    (p := (1 - p.1, p.2.2)) (sub_pos.mpr hp)).comp p
    ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd.snd)

theorem similarityPoint_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : ProfilePoint} (hp : p.1 < 1) : ContDiffAt ℝ ∞ (similarityPoint h) p :=
  (contDiffAt_snd.fst.div (physicalQ_contDiffAt hh hh1 hp)
    (physicalQ_pos hh hh1 hp).ne').prodMk (physicalEta_contDiffAt hh hh1 hp)



theorem physicalQ_at_zero_z {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} (ht : t < 1) (s : ℝ) : physicalQ h (t, (s, 0)) = 1 - t := by
  apply (SimilarityCoordinates.eq_coordinateQ (by linarith) (by linarith)
    (p := (1 - t, 0)) (sub_pos.mpr ht) (sub_pos.mpr ht) ?_).symm
  simp [SimilarityCoordinates.forwardScalar]

theorem physicalEta_at_zero_z (h t s : ℝ) : physicalEta h (t, (s, 0)) = 0 := by
  simp [physicalEta, SimilarityCoordinates.coordinateEta]

theorem profile_axis_mem (h Λ : ℝ)
    {t : ℝ} (ht : t < 1) : (t, ((0 : ℝ), 0)) ∈ profileDomain h Λ := by
  refine ⟨ht, ?_⟩
  have hs : similarityPoint h (t, ((0 : ℝ), 0)) = (0, 0) := by
    simp [similarityPoint, physicalEta, SimilarityCoordinates.coordinateEta]
  rw [hs]
  norm_num [NaturalProfile.domain, NaturalProfile.rescalePoint,
    AxisEvaluation.strip, NaturalAxisCoefficients.window]

theorem core_axis_mem (h Λ : ℝ)
    {t : ℝ} (ht : t < 1) : (t, (0 : Space)) ∈ coreDomain h Λ := by
  simpa only [coreDomain, Set.mem_ofPred_eq, profilePoint, radialEnergy, PiLp.zero_apply,
    zero_pow (by decide : 2 ≠ 0), zero_add, zero_div] using profile_axis_mem h Λ ht

theorem radial_segment_mem_domain {Λ : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ NaturalProfile.domain Λ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (p.1 * r, p.2) ∈ NaturalProfile.domain Λ := by
  change (Λ * p.1 ∈ Ioo (-20 : ℝ) 20) ∧
    p.2 ∈ Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right at hp
  change (Λ * (p.1 * r) ∈ Ioo (-20 : ℝ) 20) ∧
    p.2 ∈ Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right
  refine ⟨?_, hp.2⟩
  have hrad : |Λ * p.1| < 20 := abs_lt.mpr hp.1
  have hbound : |Λ * (p.1 * r)| ≤ |Λ * p.1| := by
    rw [← mul_assoc, abs_mul, abs_of_nonneg hr.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hr.2
  exact abs_lt.mp (hbound.trans_lt hrad)

/-- Local joint smoothness implies local joint smoothness of all actual
parameter derivatives, even when the integration variable lies at an endpoint. -/
theorem parameterJet_contDiffAt {F : (ℝ × ℝ) × ℝ → ℝ} {z : (ℝ × ℝ) × ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (k : ℕ) :
    ContDiffAt ℝ ∞
      (fun w : (ℝ × ℝ) × ℝ => iteratedFDeriv ℝ k (fun p => F (p, w.2)) w.1) z := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ (ℝ × ℝ) ℝ).symm :
        ℝ →L[ℝ] (ℝ × ℝ)[×0]→L[ℝ] ℝ)
  | succ k ih =>
    have hG : ContDiffAt ℝ ∞
        (fun w : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ) =>
          iteratedFDeriv ℝ k (fun p => F (p, w.1.2)) w.2) (z, z.1) :=
      ih.comp (z, z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hD : ContDiffAt ℝ ∞
        (fun w : (ℝ × ℝ) × ℝ => fderiv ℝ
          (fun p : ℝ × ℝ => iteratedFDeriv ℝ k (fun q => F (q, w.2)) p) w.1) z :=
      hG.fderiv contDiffAt_fst infty_add_one_le
    exact hD.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ × ℝ) ℝ).symm :
        ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)[×k]→L[ℝ] ℝ) →L[ℝ] (ℝ × ℝ)[×(k + 1)]→L[ℝ] ℝ)

theorem radialPrimitive_unit_interval (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    radialPrimitive f p = p.1 * ∫ r in (0 : ℝ)..1, f (p.1 * r, p.2) := by
  simpa only [radialPrimitive, smul_eq_mul, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (fun v => f (v, p.2)) p.1
      (a := 0) (b := 1)).symm

theorem radialPrimitive_contDiffOn {Λ : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (NaturalProfile.domain Λ)) :
    ContDiffOn ℝ ∞ (radialPrimitive f) (NaturalProfile.domain Λ) := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun z => f (z.1.1 * z.2, z.1.2)
  have hF : ∀ z ∈ NaturalProfile.domain Λ ×ˢ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ F z := by
    intro z hz
    exact (hf.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds
      (radial_segment_mem_domain hz.1 hz.2))).comp z
      ((contDiffAt_fst.fst.mul contDiffAt_snd).prodMk contDiffAt_fst.snd)
  have hi : ContDiffOn ℝ ∞ (fun p => ∫ r in (0 : ℝ)..1, F (p, r))
      (NaturalProfile.domain Λ) := by
    apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet
      (NaturalProfile.domain_isOpen Λ) zero_le_one
    · intro r hr p hp
      exact ((hF (p, r) ⟨hp, hr⟩).comp p
        (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
    · intro k z hz
      exact (parameterJet_contDiffAt (hF z hz) k).continuousAt.continuousWithinAt
  have hmul := contDiffOn_fst.mul hi
  exact hmul.congr (fun p _ => radialPrimitive_unit_interval f p)

theorem radial_interval_mem_domain {Λ : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ NaturalProfile.domain Λ) {r : ℝ} (hr : r ∈ uIcc (0 : ℝ) p.1) :
    (r, p.2) ∈ NaturalProfile.domain Λ := by
  change (Λ * p.1 ∈ Ioo (-20 : ℝ) 20) ∧
    p.2 ∈ Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right at hp
  change (Λ * r ∈ Ioo (-20 : ℝ) 20) ∧
    p.2 ∈ Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right
  refine ⟨?_, hp.2⟩
  have hr' : |r| ≤ |p.1| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hr
  have hbound : |Λ * r| ≤ |Λ * p.1| := by
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left hr' (abs_nonneg Λ)
  exact abs_lt.mp (hbound.trans_lt (abs_lt.mpr hp.1))



theorem meridionalPotential_contDiffAt {h Λ : ℝ} {V : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hV : ContDiffOn ℝ ∞ V (NaturalProfile.domain Λ))
    {p : ProfilePoint} (hp : p ∈ profileDomain h Λ) :
    ContDiffAt ℝ ∞ (meridionalPotential h V) p :=
  ((physicalQ_contDiffAt hh hh1 hp.1).rpow_const_of_ne
    (physicalQ_pos hh hh1 hp.1).ne').mul
      ((hV.contDiffAt ((NaturalProfile.domain_isOpen Λ).mem_nhds hp.2)).comp p
        (similarityPoint_contDiffAt hh hh1 hp.1))

theorem swirlPotential_contDiffAt {h Λ : ℝ} {f : ℝ × ℝ → ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hf : ContDiffOn ℝ ∞ f (NaturalProfile.domain Λ))
    {p : ProfilePoint} (hp : p ∈ profileDomain h Λ) :
    ContDiffAt ℝ ∞ (swirlPotential h f) p :=
  ((physicalQ_contDiffAt hh hh1 hp.1).rpow_const_of_ne
    (physicalQ_pos hh hh1 hp.1).ne').neg.mul
      (((radialPrimitive_contDiffOn hf).contDiffAt
        ((NaturalProfile.domain_isOpen Λ).mem_nhds hp.2)).comp p
          (similarityPoint_contDiffAt hh hh1 hp.1))










/-- The axial velocity is exactly the prescribed nonzero axis datum,
multiplied by the singular similarity scale. -/
theorem coreVelocity_at_origin {h j Λ : ℝ} {P0 a0 : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr)
    {t : ℝ} (ht : t < 1) :
    coreVelocity h f V (t, 0) = ((1 - t) ^ (-NaturalAxisData.A h) * j) • coordinateVector 2 := by
  have hp : profilePoint t (0 : Space) ∈ profileDomain h Λ := core_axis_mem h Λ ht
  have hH := (meridionalPotential_contDiffAt hh hh1 hs.average_smooth hp).differentiableAt (by simp)
  have hK := (swirlPotential_contDiffAt hh hh1 hs.f_smooth hp).differentiableAt (by simp)
  change velocity (meridionalPotential h V) (swirlPotential h f) (t, 0) = _
  rw [velocity_on_axis _ _ t 0 hH hK (by simp) (by simp)]
  have haxis : V (0, 0) = j := by
    simpa only [NaturalAxisData.U, mul_zero, zero_add] using
      hs.average_axis 0 (by norm_num [NaturalAxisCoefficients.window])
  change (physicalQ h (t, (0, 0)) ^ (-NaturalAxisData.A h) *
    V (0 / physicalQ h (t, (0, 0)), physicalEta h (t, (0, 0)))) • coordinateVector 2 = _
  rw [physicalQ_at_zero_z hh hh1 ht, physicalEta_at_zero_z, zero_div, haxis]



theorem speedUnbounded_of_axis_tendsto {u : VelocityField}
    (hu : Tendsto (fun t : ℝ => ‖u (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne u := by
  intro M hM δ hδ
  have hlow : Ioi (max 0 (1 - δ)) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (max_lt (by norm_num) (by linarith)))
  have hlarge : ∀ᶠ t in 𝓝[<] (1 : ℝ), M < ‖u (t, 0)‖ :=
    hu.eventually (eventually_gt_atTop M)
  have hbefore : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t, ht, hMt, hlo⟩ := (hbefore.and (hlarge.and hlow)).exists
  exact ⟨t, 0, ⟨(le_max_left _ _).trans_lt hlo, ht⟩,
    (le_max_right _ _).trans_lt hlo, hMt⟩





end NavierStokes.NaturalCore
