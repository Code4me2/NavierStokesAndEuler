import NavierStokes.MaximalLifespan
import NavierStokes.PeriodicSobolev
import NavierStokes.PeriodicForceDecay
import NavierStokes.CompactForceDecay
import NavierStokes.CandidateFromLimits
import NavierStokes.MixedPeriodicAssembly
import NavierStokes.WithTopLemmas

/-!
# The manuscript's corollaries of the candidate contract

Everything here follows from `CandidateProperties` alone and none of it is on
the delivered path: the two Comparator theorems use only `speed_unbounded`,
through `MaximalLifespan.candidate_excludes_global_solution` and
`ComparatorBridge.compact_candidate_excludes_global_solution`. The
manuscript-facing statements — maximality of the classical lifespan, the set
of admissible lifespans, a nonzero force before time one, the `H³` blow-up,
and the full force-jet decay — are collected here so that a reader of the
spine need not decide whether they are load-bearing (they are not).
`Consequences` bundles them for the witness hub; `mixed_exists_force_with_consequences`
post-composes the mixed assembly with that bundle.
-/

noncomputable section

namespace NavierStokes.CandidateConsequences

open Set Filter Function ProblemStatement MaximalLifespan PeriodicForceDecay
open scoped ContDiff Topology BigOperators Pointwise

/-! ### Maximality of the classical lifespan -/

/-- An extension has a strictly larger time interval and preserves the
velocity on the entire original interval. Its pressure may have a different
time-dependent spatially constant normalization. -/
noncomputable def HasClassicalExtension (f : VelocityField) (T : ℝ) (u : VelocityField) : Prop :=
  ∃ S : ℝ, ∃ v : VelocityField, ∃ q : PressureField,
    T < S ∧ ClassicalSolution f S v q ∧ VelocityAgreesOn T u v

noncomputable def IsMaximalClassicalSolution (f : VelocityField) (T : ℝ) (u : VelocityField)
    (p : PressureField) : Prop :=
  ClassicalSolution f T u p ∧ ¬HasClassicalExtension f T u

/-- The actual set of finite positive times supported by classical solutions
for the fixed force and zero datum. No existence is built into the definition. -/
noncomputable def admissibleLifespans (f : VelocityField) : Set ℝ :=
  {T | ∃ u : VelocityField, ∃ p : PressureField, ClassicalSolution f T u p}

/-- The given lifespan-one solution is maximal under extension of its
velocity. No literal equality between pressure representatives is required. -/
theorem candidate_is_maximal {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    IsMaximalClassicalSolution f 1 u p := by
  refine ⟨candidate_is_classical_solution h, ?_⟩
  rintro ⟨T, v, q, hT, hv, _⟩
  exact candidate_no_solution_after_one h hT hv

/-- The entire set of finite admissible classical lifespans is `(0,1]`. -/
theorem candidate_admissible_lifespans {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    admissibleLifespans f = Ioc (0 : ℝ) 1 := by
  ext T
  constructor
  · rintro ⟨v, q, hv⟩
    exact ⟨hv.lifespan_pos, candidate_all_lifespans_le_one h hv⟩
  · intro ht
    exact ⟨u, p, (candidate_is_classical_solution h).restrict ht.1 ht.2⟩

theorem zero_classical_solution_of_zero_force {f : VelocityField} {T : ℝ}
    (hT : 0 < T) (hf : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, f (t, x) = 0) :
    ClassicalSolution f T (fun _ => 0) (fun _ => 0) where
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  zero_initial_velocity := fun _ => rfl
  divergence_free := fun _ _ x => by simp [spatialDivergence, spatialDerivative]
  navier_stokes := fun t ht ht0 x => (zero_residual t x).trans (hf t ⟨ht0, ht.2⟩ x).symm
  lifespan_pos := hT
  velocity_periodic := fun _ _ _ _ => rfl
  pressure_periodic := fun _ _ _ _ => rfl

/-- The specified force must be nonzero somewhere before the breakdown
time. Otherwise uniqueness identifies the candidate with the zero solution. -/
theorem candidate_force_nonzero_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0 := by
  by_contra hnot
  have hf : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space, f (t, x) = 0 := by
    intro t ht x
    by_contra hnonzero
    exact hnot ⟨t, ht, x, hnonzero⟩
  have hz := zero_classical_solution_of_zero_force zero_lt_one hf
  have hagree : VelocityAgreesOn 1 (fun _ => 0) u := by
    simpa only [min_self] using candidate_agree_on_overlap h hz
  apply unbounded_speed_excludes_uniform_bound h.speed_unbounded
  refine ⟨0, ?_⟩
  intro t ht x
  rw [← hagree t ht x]
  exact norm_zero.le

/-! ### Full force-jet decay and the bundle -/

/-- The ordinary tensor bound for the same force.  Global smoothness is
provided by the actual force constructor; negative-time periodicity is not needed. -/
theorem full_forceJet_decay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (hf : ContDiff ℝ ∞ f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hb⟩ := futureJet_decay h.force_smooth h.force_periodic h.force_time_support m K hK
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← futureJet_eq_full ht x m hf.contDiffAt]
  exact hb t ht x

theorem full_forceMixed_decay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (hf : ContDiff ℝ ∞ f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
        |(iteratedFDeriv ℝ m f (t, x)
          (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
            C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hb⟩ := full_forceJet_decay h hf m K hK
  exact ⟨C, hC, fun t ht x directions j =>
    (CompactForceDecay.mixed_component_le_full f m (t, x) directions j).trans (hb t ht x)⟩

/-- All conclusions here follow from the exact candidate properties alone. -/
structure Consequences (u : VelocityField) (p : PressureField) (f : VelocityField) : Prop where
  maximal : IsMaximalClassicalSolution f 1 u p
  lifespans : admissibleLifespans f = Ioc (0 : ℝ) 1
  h3_unbounded : PeriodicSobolev.DerivativeH3UnboundedAtOne u
  force_nonzero : ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0
  force_jet_decay : ∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K)

theorem consequences_of_candidate {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) : Consequences u p f :=
  ⟨candidate_is_maximal h, candidate_admissible_lifespans h,
    PeriodicSobolev.candidate_derivativeH3_unbounded h,
    candidate_force_nonzero_before_one h,
    futureJet_decay h.force_smooth h.force_periodic h.force_time_support⟩

/-- Retaining one growing physical trajectory strengthens unboundedness to
a genuine limit.  No monotonicity of the velocity or its norm is assumed. -/
theorem h3_tendsto_of_speed_tendsto {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (x : ℝ → Space)
    (hx : Tendsto (fun t => ‖u (t, x t)‖) (𝓝[<] (1 : ℝ)) atTop) :
    Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun y => u (t, y)))
      (𝓝[<] (1 : ℝ)) atTop := by
  rw [tendsto_atTop]
  intro M
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hpre : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  filter_upwards [hx.eventually (eventually_ge_atTop (3 * M)), hpos, hpre] with t hlarge ht ht1
  have hslice := TimeLocalization.spatial_smooth_including_initial u h.velocity_smooth t ⟨ht.le, ht1⟩
  have hb := PeriodicSobolev.norm_le_three_derivativeH3Norm hslice
    (h.velocity_periodic t ⟨ht.le, ht1⟩) (x t)
  linarith

theorem mixed_activated_speed_tendsto {A v : VelocityField}
    (haxis : Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖)
      (𝓝[<] (1 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => ‖TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.periodicVelocity A v) (t, 0)‖) (𝓝[<] (1 : ℝ)) atTop := by
  have he : (fun t : ℝ => ‖TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.periodicVelocity A v) (t, 0)‖) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖) := by
    filter_upwards [show Ioi (3 / 4 : ℝ) ∈ 𝓝[<] (1 : ℝ) from
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))] with t ht
    rw [TimeLocalization.activatedVelocity_eq_late _ ht.le, MixedPeriodicAssembly.periodicVelocity_origin]
  exact haxis.congr' he.symm

/-- The exact mixed assembly inputs produce one force carrying all the
lifespan, Sobolev, and full force-jet conclusions.  Nothing is assumed about
the output force, the infinite-time PDE, or the Sobolev embedding. -/
theorem mixed_exists_force_with_consequences {A v : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hd : ∀ t < 1, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    (hz : JointResidualLimits.VanishingJointJets (MixedPeriodicAssembly.originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖)
      (𝓝[<] (1 : ℝ)) atTop) :
    ∃ F : VelocityField,
      CandidateProperties (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      Consequences (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
        TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v) (t, x)))
        (𝓝[<] (1 : ℝ)) atTop ∧
      (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
          |(iteratedFDeriv ℝ m F (t, x)
            (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
              C * (1 + t) ^ (-K)) ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (1, x) =
        MixedPeriodicAssembly.boundaryLimits A v p eA ev ep x n) := by
  obtain ⟨F, hc, hF, hjet⟩ := MixedPeriodicAssembly.exists_candidate_force hA hv hp hd hz eA ev ep haxis
  exact ⟨F, hc, hF, consequences_of_candidate hc,
    h3_tendsto_of_speed_tendsto hc (fun _ => 0) (mixed_activated_speed_tendsto haxis),
    full_forceMixed_decay hc hF, hjet⟩

end NavierStokes.CandidateConsequences
