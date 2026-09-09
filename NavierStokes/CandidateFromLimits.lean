import NavierStokes.PastExtension
import NavierStokes.SpacetimeGluing
import NavierStokes.CompactForceDecay

/-!
# Conditional candidate construction from actual residual derivative limits

The inputs are physical velocity and pressure fields and locally uniform limits
of every full derivative of their actual Navier--Stokes residual. No future force
or boundary compatibility is assumed. The force is the explicit Taylor--Borel
extension of the traced residual of the activated, zero-extended fields.

The residual limits and the existence of singular incoming fields remain
analytic hypotheses. This module does not prove the unconditional candidate.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.CandidateFromLimits

open ProblemStatement TimeLocalization

/-- Fill in the endpoint trace after extending the activated residual to
negative times by the construction in `PastExtension`. -/
def tracedResidual (u : VelocityField) (p : PressureField)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space) : VelocityField :=
  SpacetimeEndpoint.extendTrace 1 (PastExtension.pastResidual u p)
    (fun x => (L x 0).curry0)

section Construction

variable (u : VelocityField) (p : PressureField)
variable (hu : ContDiffOn ℝ ∞ u preSingularDomain)
variable (hp : ContDiffOn ℝ ∞ p preSingularDomain)
variable (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
variable (hlim : ∀ n : ℕ, TendstoLocallyUniformly
  (fun t x => iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
  (fun x => L x n) (𝓝[<] (1 : ℝ)))

include hu hp hlim

/-- Closed-side joint smoothness is derived from the actual derivative
recurrence and the supplied locally uniform limits. -/
theorem tracedResidual_smooth :
    ContDiffOn ℝ ∞ (tracedResidual u p L) (SpacetimeEndpoint.closedPast 1) := by
  apply SpacetimeEndpoint.contDiffOn_joint_extension
    (J := ftaylorSeries ℝ (PastExtension.pastResidual u p))
  · intro z _
    rfl
  · exact PastExtension.pastResidual_derivative_recurrence u p hu hp
  · intro n
    exact PastExtension.pastResidual_locallyUniform_limit u p n (fun x => L x n) (hlim n)

theorem tracedResidual_boundary_jets (n : ℕ) (x : Space) :
    iteratedFDerivWithin ℝ n (tracedResidual u p L)
      (SpacetimeEndpoint.closedPast 1) (1, x) = L x n := by
  apply SpacetimeEndpoint.boundary_jets_eq_limits
    (J := ftaylorSeries ℝ (PastExtension.pastResidual u p))
  · intro z _
    rfl
  · exact PastExtension.pastResidual_derivative_recurrence u p hu hp
  · intro k
    exact PastExtension.pastResidual_locallyUniform_limit u p k (fun y => L y k) (hlim k)

omit hu hp in
theorem tracedResidual_periodic
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn univ (tracedResidual u p L) := by
  apply SpacetimeEndpoint.unit_periods_joint_extension
    (J := ftaylorSeries ℝ (PastExtension.pastResidual u p))
  · intro z _
    rfl
  · exact PastExtension.pastResidual_locallyUniform_limit u p 0 (fun x => L x 0) (hlim 0)
  · exact PastExtension.pastResidual_periodic u p huper hpper

/-- The specified force: glue the traced past residual to the Taylor--Borel
series of its actual normal jets. No force is an input to this definition. -/
def force : VelocityField :=
  SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)
    (tracedResidual_smooth u p hu hp L hlim)

theorem force_smooth : ContDiff ℝ ∞ (force u p hu hp L hlim) :=
  SpacetimeGluing.smoothExtension_contDiff (tracedResidual_smooth u p hu hp L hlim)

theorem force_periodic
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p) :
    UnitSpatialPeriodsOn univ (force u p hu hp L hlim) := by
  apply SpacetimeGluing.smoothExtension_unit_periods (tracedResidual_smooth u p hu hp L hlim)
  intro t _ x i
  exact tracedResidual_periodic u p L hlim huper hpper t (mem_univ t) x i

/-- The force agrees with the actual activated residual throughout the
whole past, not just on an arbitrarily short terminal overlap. -/
theorem force_eq_pastResidual {t : ℝ} (ht : t < 1) (x : Space) :
    force u p hu hp L hlim (t, x) = PastExtension.pastResidual u p (t, x) := by
  calc
    _ = tracedResidual u p L (t, x) :=
      SpacetimeGluing.smoothExtension_eqOn_past
        (tracedResidual_smooth u p hu hp L hlim)
        (show (t, x) ∈ SpacetimeGluing.past 1 from ⟨ht.le, mem_univ x⟩)
    _ = _ := SpacetimeEndpoint.extendTrace_of_lt (z := (t, x)) ht

theorem force_eq_activated_residual {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (x : Space) :
    force u p hu hp L hlim (t, x) =
      navierStokesResidual (activatedVelocity u) (activatedPressure p) t x := by
  rw [force_eq_pastResidual u p hu hp L hlim ht1 x]
  exact PastExtension.pastResidual_eq_activated u p ht0 x

theorem force_zero_from {t : ℝ} (ht : 2 ≤ t) (x : Space) :
    force u p hu hp L hlim (t, x) = 0 :=
  SpacetimeGluing.smoothExtension_zero_from
    (tracedResidual_smooth u p hu hp L hlim) (by linarith) x


theorem force_time_support : CompactFutureTimeSupport (force u p hu hp L hlim) :=
  ⟨2, by norm_num, fun t ht x => force_zero_from u p hu hp L hlim ht x⟩

/-- Every full spacetime boundary derivative is exactly its supplied limit. -/
theorem force_boundary_jets (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (force u p hu hp L hlim) (1, x) = L x n := by
  calc
    _ = iteratedFDerivWithin ℝ n (tracedResidual u p L)
        (SpacetimeEndpoint.closedPast 1) (1, x) :=
      SpacetimeGluing.smoothExtension_iteratedFDeriv
        (tracedResidual_smooth u p hu hp L hlim) n
        ⟨mem_Iic.mpr (le_refl (1 : ℝ)), mem_univ x⟩
    _ = L x n := tracedResidual_boundary_jets u p hu hp L hlim n x



/-- The constructed force and activated fields satisfy the original explicit
candidate specification. No force or closed-side regularity is assumed. -/
theorem candidate_properties
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u) :
    CandidateProperties (activatedVelocity u) (activatedPressure p) (force u p hu hp L hlim) := by
  refine ⟨activatedVelocity_smooth u hu, activatedPressure_smooth p hp,
    (force_smooth u p hu hp L hlim).contDiffOn,
    activatedVelocity_periodic u _ huper, activatedPressure_periodic p _ hpper,
    ?_, activatedVelocity_zero_initial u, force_time_support u p hu hp L hlim,
    activatedVelocity_divergence_free u hu hdiv, ?_,
    activatedVelocity_speed_unbounded u hunbounded⟩
  · intro t _ x i
    exact force_periodic u p hu hp L hlim huper hpper t (mem_univ t) x i
  · intro t ht x
    exact (force_eq_activated_residual u p hu hp L hlim ht.1.le ht.2 x).symm



end Construction

end NavierStokes.CandidateFromLimits
