import Research.UnforcedRestart.Round2.PeriodicSlab.Main

/-! Actual candidate-contract L² force interface. This supplies spatially
integrated/time-integrable forcing, not an H³ stability threshold. -/
noncomputable section
open Set
open scoped ContDiff
namespace UnforcedRestart.Round2.ActualForce
open NavierStokes.ProblemStatement NavierStokes.SolutionDifference
open NavierStokes.PeriodicIntegration NavierStokes.PeriodicUniqueness

/-- The real unit cube has volume one in the coordinates used by energy. -/
theorem cubeIntegral_constant (c : ℝ) : cubeIntegral (fun _ : Space => c) = c := by
  simp [cubeIntegral, cubeMeasure, cube, MeasureTheory.Measure.real,
    Real.volume_Icc_pi]

/-- A spatial uniform bound gives a bound of the actual squared cell norm. -/
theorem cell_energy_le {f : Space → Space} {C : ℝ}
    (hf : Continuous f) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    cubeIntegral (fun x => ‖f x‖ ^ 2) ≤ C ^ 2 := by
  rw [← cubeIntegral_constant (C ^ 2)]
  exact cubeIntegral_mono_on_cube (hf.norm.pow 2) continuous_const
    (fun y _ => (sq_le_sq₀ (norm_nonneg _) hC).2 (hb (toSpace y)))

/-- Future force smoothness includes the old terminal time. No velocity
smoothness at time one is used to establish this force-only continuity. -/
theorem candidate_shift_force_continuous {u f : VelocityField} {p : PressureField}
    (h : CandidateProperties u p f) {t0 S : ℝ} (ht0 : 0 ≤ t0) :
    ContinuousOn (fun z : SpaceTime => f (t0 + z.1, z.2)) (slab 0 S) := by
  apply h.force_smooth.continuousOn.comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
  intro z hz
  exact ⟨add_nonneg ht0 hz.1.1, mem_univ _⟩

/-- One candidate and one restart give a cell-energy majorant uniform in all
S ≤ H, and a genuine time integral of the spatial integral. Constants are
existential, not a quantitative growth-transfer certificate. -/
theorem candidate_cell_budget {u f : VelocityField} {p : PressureField}
    (h : CandidateProperties u p f) {t0 H : ℝ} (ht0 : 0 ≤ t0) (hH : 0 < H) :
    ∃ C : ℝ, 0 < C ∧
      (∀ s ∈ Icc 0 H, cubeIntegral (fun x => ‖f (t0 + s, x)‖ ^ 2) ≤ C ^ 2) ∧
      (∀ S ∈ Icc 0 H,
        IntervalIntegrable (fun s => cubeIntegral (fun x => ‖f (t0 + s, x)‖ ^ 2))
          MeasureTheory.volume 0 S) ∧
      ∀ S ∈ Icc 0 H,
        (∫ s in 0..S, cubeIntegral (fun x => ‖f (t0 + s, x)‖ ^ 2)) ≤ C ^ 2 * S := by
  have hc := candidate_shift_force_continuous (S := H) h ht0
  obtain ⟨C, hC, hb⟩ := periodic_bound_on_slab hc
    (fun s hs x i => h.force_periodic (t0 + s) (add_nonneg ht0 hs.1) x i)
  have hcell (s : ℝ) (hs : s ∈ Icc 0 H) :
      cubeIntegral (fun x => ‖f (t0 + s, x)‖ ^ 2) ≤ C ^ 2 := by
    apply cell_energy_le _ hC.le (hb s hs)
    rw [← continuousOn_univ]
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨hs, mem_univ x⟩)
  have hg := UnforcedRestart.Round2.PeriodicSlab.force_energy_continuousOn hc
  have hi := (UnforcedRestart.Round2.PeriodicSlab.primitive_on_slab hH hg).2.2
  refine ⟨C, hC, hcell, hi, ?_⟩
  intro S hS
  have hm := intervalIntegral.integral_mono_on hS.1 (hi S hS)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C ^ 2)
      MeasureTheory.volume 0 S)
    (fun s hs => hcell s ⟨hs.1, hs.2.trans hS.2⟩)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hm

end UnforcedRestart.Round2.ActualForce
#print axioms UnforcedRestart.Round2.ActualForce.cubeIntegral_constant
#print axioms UnforcedRestart.Round2.ActualForce.cell_energy_le
#print axioms UnforcedRestart.Round2.ActualForce.candidate_shift_force_continuous
#print axioms UnforcedRestart.Round2.ActualForce.candidate_cell_budget
