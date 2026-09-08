import NavierStokes.ScheduledProfileChoice
import NavierStokes.MatchingDebtBounds
import NavierStokes.OutgoingCone

/-!
# One prepared outgoing profile and arbitrarily late nominal matching

The reset bound precedes the outgoing exponent, the height bounds precede
the actual height, and the natural-axis choices use this same profile.
The clean cone below belongs to the unedited outgoing profile. Identification
with the complete edited nominal stress is a separate construction.
-/

noncomputable section

namespace NavierStokes.PreparedOutgoing

open Set Filter OutgoingProfile

/-- Data obtained from the actual schedule construction, with a clean cone
available at all sufficiently late matching radii. -/
structure PreparedProfile where
  profile : Profile
  bound : ℝ
  bound_pos : 0 < bound
  specification : Specification profile bound
  schedule : ExtendedHeatedOutgoing.ScheduleBounds profile
  terminal : TerminalCone.SmallTail profile.data
  amplitude_lower : 2 ≤ profile.data.core.P
  height_upper : profile.data.h ≤ 1 / 1000
  clean : ∀ left : ℝ, left ≤ 0 →
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 < R → OutgoingCone.ProfileCleanCone profile R left

/-- Select the reset bound and exponent together, respecting the clean-cone
cap before constructing the profile. No existing exponent is changed later. -/
theorem exists_prepared : Nonempty PreparedProfile := by
  classical
  obtain ⟨M, hM, hcone⟩ := OutgoingCone.exists_ordered_profile_cone
  let P : ℝ := max 2 (OutgoingEntranceCone.amplitudeThreshold M)
  have hP2 : 2 ≤ P := le_max_left _ _
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP2
  have hPamp : OutgoingEntranceCone.amplitudeThreshold M ≤ P := le_max_right _ _
  let caps := hcone M le_rfl P hPamp
  let cap : ℝ → ℝ := fun K =>
    if hK : 0 < K then Classical.choose (caps K hK) else 1
  have hcap : ∀ K : ℝ, 0 < K → 0 < cap K := by
    intro K hK
    dsimp only [cap]
    rw [dite_eq_left hK]
    exact (Classical.choose_spec (caps K hK)).1
  obtain ⟨K, B, H, core, hK, hB, hH, hcP, hcm, hwait, hlam, _hsmall,
      _h2H, hheight, hHsmall, hfamily⟩ :=
    ScheduledProfileChoice.exists_scheduled_family_below P M hPpos hM cap hcap
      (fun core => OutgoingCone.heightThreshold M core.lam)
      (fun core => OutgoingCone.heightThreshold_pos M core.lam_pos)
  obtain ⟨F, hcore, hh, hFK, hschedule, hspec, hterminal⟩ := hfamily H hH le_rfl
  have hFP : F.data.core.P = P := by rw [hcore, hcP]
  have hFm : F.data.core.m = M := by rw [hcore, hcm]
  have hFwait : F.data.core.wait = 60 * Real.log (1 / F.data.core.lam) := by
    rw [hcore]
    exact hwait
  have hFlam : F.data.core.lam < Classical.choose (caps K hK) := by
    rw [hcore]
    simpa only [cap, dite_eq_left hK] using hlam
  have hFheight : F.data.h ≤ OutgoingCone.heightThreshold M F.data.core.lam := by
    rw [hh, hcore]
    exact hheight
  have hclean := (Classical.choose_spec (caps K hK)).2 F hFP hFm hFK hFwait hFlam hFheight
  exact ⟨{
    profile := F
    bound := B
    bound_pos := hB
    specification := hspec
    schedule := hschedule
    terminal := hterminal
    amplitude_lower := by rw [hFP]; exact hP2
    height_upper := by rw [hh]; exact hHsmall
    clean := hclean }⟩


/-- An actual fixed prepared profile, obtained from the proved existence. -/
noncomputable def prepared : PreparedProfile := Classical.choice exists_prepared


end NavierStokes.PreparedOutgoing
