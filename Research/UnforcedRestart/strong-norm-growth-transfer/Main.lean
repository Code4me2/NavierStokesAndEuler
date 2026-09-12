import NavierStokes.PeriodicUniqueness

/-! Conditional norm infrastructure, not a Navier–Stokes stability theorem. -/
namespace UnforcedRestart.StrongNormGrowthTransfer
open Set NavierStokes.ProblemStatement

/-- Evaluation plus a numerical budget transfers a lower bound. `N` is an
explicit scalar bound, not a newly defined solution class or Sobolev norm. -/
theorem evaluation_budget {E : Type*} [NormedAddCommGroup E]
    (a b : E) {C N ρ B : ℝ}
    (heval : ‖a - b‖ ≤ C * N) (hbudget : C * N ≤ ρ * ‖a‖ + B) :
    (1 - ρ) * ‖a‖ - B ≤ ‖b‖ := by
  have htriangle : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - b) b
  nlinarith

/-- Relative pointwise error strictly below one, up to a fixed additive
constant, transfers the repository's actual speed-unbounded predicate.
The estimate is required only after an interior restart time. -/
theorem speed_transfer {u v : VelocityField} {t₀ ρ B : ℝ}
    (ht₀ : t₀ < 1) (hρ : ρ < 1) (hB : 0 ≤ B)
    (hu : SpeedUnboundedAtOne u)
    (herr : ∀ t ∈ Ioo (0 : ℝ) 1, t₀ < t → ∀ x : Space,
      ‖u (t, x) - v (t, x)‖ ≤ ρ * ‖u (t, x)‖ + B) :
    SpeedUnboundedAtOne v := by
  intro M hM δ hδ
  have hd : 0 < 1 - ρ := sub_pos.mpr hρ
  have hthreshold : 0 < (M + B) / (1 - ρ) := div_pos (by linarith) hd
  obtain ⟨t, x, ht, hnear, hgrowth⟩ := hu _ hthreshold
    (min δ (1 - t₀)) (lt_min hδ (sub_pos.mpr ht₀))
  have hlate : t₀ < t := by
    have := min_le_right δ (1 - t₀)
    linarith
  have hnear' : 1 - δ < t := by
    have := min_le_left δ (1 - t₀)
    linarith
  have hlow := evaluation_budget (u (t, x)) (v (t, x))
    (C := 1) (N := ‖u (t, x) - v (t, x)‖) (by simp)
    (by simpa using herr t ht hlate x)
  have hg : M + B < ‖u (t, x)‖ * (1 - ρ) := (div_lt_iff₀ hd).mp hgrowth
  exact ⟨t, x, ht, hnear', by nlinarith⟩

/-- Periodic endpoint continuity rules out the transferred growth. No PDE,
existence, uniqueness, or quantitative norm estimate is asserted here. -/
theorem no_periodic_continuous_comparator {u v : VelocityField} {t₀ ρ B : ℝ}
    (ht₀ : t₀ < 1) (hρ : ρ < 1) (hB : 0 ≤ B)
    (hu : SpeedUnboundedAtOne u)
    (herr : ∀ t ∈ Ioo (0 : ℝ) 1, t₀ < t → ∀ x : Space,
      ‖u (t, x) - v (t, x)‖ ≤ ρ * ‖u (t, x)‖ + B)
    (hv : ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    (hp : UnitSpatialPeriodsOn (Icc (0 : ℝ) 1) v) : False := by
  obtain ⟨C, _, hC⟩ := NavierStokes.PeriodicUniqueness.periodic_bound_on_slab hv hp
  exact unbounded_speed_excludes_uniform_bound (speed_transfer ht₀ hρ hB hu herr)
    ⟨C, fun t ht x => hC t ⟨ht.1, ht.2.le⟩ x⟩

/-- The actual axis mechanism needs comparison only at the origin, not a
whole-space bound on the competitor. Growth is an explicit reference premise. -/
theorem no_continuous_axis_comparator {u v : VelocityField} {t₀ ρ B : ℝ}
    (hρ : ρ < 1) (hB : 0 ≤ B)
    (hgrowth : ∀ M : ℝ, 0 < M → ∃ t ∈ Ioo t₀ 1, M < ‖u (t, 0)‖)
    (herr : ∀ t ∈ Ioo t₀ 1,
      ‖u (t, 0) - v (t, 0)‖ ≤ ρ * ‖u (t, 0)‖ + B)
    (hv : ContinuousOn v (Icc t₀ 1 ×ˢ ({0} : Set Space))) : False := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_singleton (x := (0 : Space)))).exists_bound_of_continuousOn hv
  have hd : 0 < 1 - ρ := sub_pos.mpr hρ
  have hpos : 0 < (max C 0 + B + 1) / (1 - ρ) := by
    apply div_pos _ hd
    have := le_max_right C 0
    linarith
  obtain ⟨t, ht, hg⟩ := hgrowth _ hpos
  have hb := hC (t, 0) ⟨⟨ht.1.le, ht.2.le⟩, mem_singleton 0⟩
  have hl := evaluation_budget (u (t, 0)) (v (t, 0))
    (C := 1) (N := ‖u (t, 0) - v (t, 0)‖) (by simp)
    (by simpa using herr t ht)
  have hh := (div_lt_iff₀ hd).mp hg
  have := le_max_left C 0
  nlinarith

end UnforcedRestart.StrongNormGrowthTransfer

#print axioms UnforcedRestart.StrongNormGrowthTransfer.no_continuous_axis_comparator
#print axioms UnforcedRestart.StrongNormGrowthTransfer.evaluation_budget
#print axioms UnforcedRestart.StrongNormGrowthTransfer.speed_transfer
#print axioms UnforcedRestart.StrongNormGrowthTransfer.no_periodic_continuous_comparator
