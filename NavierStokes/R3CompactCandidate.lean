import NavierStokes.CompactSpatialForceDecay
import NavierStokes.CandidateFromLimits

/-!
# The compact whole-space candidate

`Properties` is the whole-space counterpart of `CandidateProperties`: a
`Solution` on `[0,1)` with compactly supported velocity and force, force
support in future time, and unbounded speed at time one. It is what the (C)
exclusion `ComparatorBridge.compact_candidate_excludes_global_solution`
consumes.

`of_limits` builds such a candidate from spatially compactly supported fields
and the locally uniform limits of their residual jets: the force is the
Taylor--Borel extension `CandidateFromLimits.force`, which inherits the
spatial support of the fields (`CandidateFromLimits.force_zero_outside`).
The project's fields are the cut mixed sums of `MixedPeriodicAssembly`, which
periodizes this compact candidate to obtain the periodic one; the compact
candidate is therefore built first, and nothing here refers to the lattice.
-/

noncomputable section

namespace NavierStokes.R3CompactCandidate

open Set Filter ProblemStatement TimeLocalization
open scoped ContDiff Topology

/-- The whole-space candidate conditions needed for option (C): a
`Solution` on `[0,1)` with compactly supported velocity and force, force
support in future time, and unbounded speed at time one. This is the
whole-space counterpart of `CandidateProperties`. -/
structure Properties (u : VelocityField) (p : PressureField) (f : VelocityField) : Prop
    extends Solution (Ico 0 1) f u p where
  force_smooth : ContDiffOn ℝ ∞ f futureDomain
  velocity_support : ∃ K : Set Space, IsCompact K ∧
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → u (t, x) = 0
  force_support : ∃ K : Set Space, IsCompact K ∧ CompactSpatialForceDecay.SupportedIn K f
  force_time_support : CompactFutureTimeSupport f
  speed_unbounded : SpeedUnboundedAtOne u

/-- The compact candidate from fields vanishing outside a compact set `K` at
every time, their residual-jet limits at time one, and the two properties of
the activated velocity that the force construction does not supply:
divergence-freeness and unbounded speed. The force is
`CandidateFromLimits.force`, which vanishes outside `K` at every time. -/
theorem of_limits {u : VelocityField} {p : PressureField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    {K : Set Space} (hK : IsCompact K)
    (hus : ∀ t : ℝ, ∀ x : Space, x ∉ K → u (t, x) = 0)
    (hps : ∀ t : ℝ, ∀ x : Space, x ∉ K → p (t, x) = 0)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
    (hlim : CandidateFromLimits.ResidualLimits u p L)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence (activatedVelocity u) t x = 0)
    (hunbounded : SpeedUnboundedAtOne (activatedVelocity u)) :
    Properties (activatedVelocity u) (activatedPressure p)
      (CandidateFromLimits.force u p hu hp L hlim) := by
  have hsol : Solution (Ico 0 1) (CandidateFromLimits.force u p hu hp L hlim)
      (activatedVelocity u) (activatedPressure p) :=
    ⟨activatedVelocity_smooth u hu, activatedPressure_smooth p hp,
      activatedVelocity_zero_initial u, hdiv, fun t ht _ x =>
        (CandidateFromLimits.force_eq_activated_residual u p hu hp L hlim ht.1 ht.2 x).symm⟩
  have hvs : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, x ∉ K → activatedVelocity u (t, x) = 0 := by
    intro t _ x hx
    simp [activatedVelocity, hus t x hx]
  have hfs : CompactSpatialForceDecay.SupportedIn K (CandidateFromLimits.force u p hu hp L hlim) :=
    fun t _ x hx => CandidateFromLimits.force_zero_outside u p hu hp L hlim hK.isClosed hus hps hx t
  exact ⟨hsol, (CandidateFromLimits.force_smooth u p hu hp L hlim).contDiffOn, ⟨K, hK, hvs⟩,
    ⟨K, hK, hfs⟩, CandidateFromLimits.force_time_support u p hu hp L hlim, hunbounded⟩

/-- Step three of the whole-space argument: once agreement with the compact
candidate below time one is known, a competitor smooth across time one is
bounded on `[0,1] × K` for the candidate's support `K`, and the candidate
vanishes off `K`, so `SpeedUnboundedAtOne` fails. This is the (C) instance of
`SpeedUnboundedAtOne.false_of_agree`; the (D) instance is
`MaximalLifespan.candidate_no_solution_after_one`. -/
theorem Properties.not_global_agreement {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : Properties u p f) {v : VelocityField} (hv : ContDiffOn ℝ ∞ v futureDomain) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  intro heq
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  refine h.speed_unbounded.false_of_agree hK
    (hv.continuousOn.mono (fun _ hz => ⟨hz.1.1, mem_univ _⟩)) (fun t ht x _ => heq t ht x) ?_
  intro t ht x
  by_cases hx : x ∈ K
  · exact Or.inr ⟨x, hx, rfl⟩
  · exact Or.inl (hs t ht x hx)

end NavierStokes.R3CompactCandidate
