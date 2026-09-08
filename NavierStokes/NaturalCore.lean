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




theorem physicalQ_at_zero_z {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} (ht : t < 1) (s : ℝ) : physicalQ h (t, (s, 0)) = 1 - t := by
  apply (SimilarityCoordinates.eq_coordinateQ (by linarith) (by linarith)
    (p := (1 - t, 0)) (sub_pos.mpr ht) (sub_pos.mpr ht) ?_).symm
  simp [SimilarityCoordinates.forwardScalar]

theorem physicalEta_at_zero_z (h t s : ℝ) : physicalEta h (t, (s, 0)) = 0 := by
  simp [physicalEta, SimilarityCoordinates.coordinateEta]
























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
