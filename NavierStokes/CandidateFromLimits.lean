import NavierStokes.PastExtension
import NavierStokes.SpacetimeGluing
import NavierStokes.CompactForceDecay

/-!
# The force from actual residual derivative limits

The inputs are velocity and pressure fields, smooth before time one, together
with locally uniform limits of every full derivative of their Navier--Stokes
residual as `t → 1⁻`. No future force or boundary compatibility is assumed. The
force is the explicit Taylor--Borel extension of the traced residual of the
activated, zero-extended fields: it is the residual before time one
(`force_eq_activated_residual`), has the supplied jets at time one
(`force_boundary_jets`), and vanishes from time two on (`force_zero_from`).

The construction is local in space: where the fields vanish, so does the force
at every time (`force_zero_outside`). This is what gives the compact
whole-space candidate its compactly supported force
(`R3CompactCandidate.of_limits`); the periodic candidate is then the lattice
periodization of the compact one (`MixedPeriodicAssembly`).
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

/-- The analytic input of the construction: locally uniform limits, as
`t → 1⁻`, of every full spacetime derivative of the residual of `u`, `p`.
The family `L` becomes the jets of the force at time one. -/
def ResidualLimits (u : VelocityField) (p : PressureField)
    (L : Space → FormalMultilinearSeries ℝ SpaceTime Space) : Prop :=
  ∀ n : ℕ, TendstoLocallyUniformly
    (fun t x => iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
    (fun x => L x n) (𝓝[<] (1 : ℝ))

section Construction

variable (u : VelocityField) (p : PressureField)
variable (hu : ContDiffOn ℝ ∞ u preSingularDomain)
variable (hp : ContDiffOn ℝ ∞ p preSingularDomain)
variable (L : Space → FormalMultilinearSeries ℝ SpaceTime Space)
variable (hlim : ResidualLimits u p L)

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

/-- The specified force: glue the traced past residual to the Taylor--Borel
series of its actual normal jets. No force is an input to this definition. -/
def force : VelocityField :=
  SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)
    (tracedResidual_smooth u p hu hp L hlim)

theorem force_smooth : ContDiff ℝ ∞ (force u p hu hp L hlim) :=
  SpacetimeGluing.smoothExtension_contDiff (tracedResidual_smooth u p hu hp L hlim)

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


/-! ## Spatial locality

Where both fields vanish at every time, the residual, its jets, the traced
residual and the Borel extension all vanish, so the force does. -/

section Locality

variable {K : Set Space} (hK : IsClosed K)
variable (hus : ∀ t : ℝ, ∀ x : Space, x ∉ K → u (t, x) = 0)
variable (hps : ∀ t : ℝ, ∀ x : Space, x ∉ K → p (t, x) = 0)
include hK hus hps

omit hu hp hlim in
theorem residual_zero_outside {z : SpaceTime} (hz : z.2 ∉ K) :
    navierStokesResidual u p z.1 z.2 = 0 := by
  have hn : {w : SpaceTime | w.2 ∉ K} ∈ 𝓝 z :=
    (hK.isOpen_compl.preimage continuous_snd).mem_nhds hz
  apply ResidualRegularity.residual_eq_zero_of_eventually_zero
  · filter_upwards [hn] with w hw
    exact hus w.1 w.2 hw
  · filter_upwards [hn] with w hw
    exact hps w.1 w.2 hw

omit hu hp hlim in
theorem pastResidual_zero_outside {t : ℝ} {x : Space} (hx : x ∉ K) :
    PastExtension.pastResidual u p (t, x) = 0 := by
  have hn : {w : SpaceTime | w.2 ∉ K} ∈ 𝓝 (t, x) :=
    (hK.isOpen_compl.preimage continuous_snd).mem_nhds hx
  apply ResidualRegularity.residual_eq_zero_of_eventually_zero
  · filter_upwards [hn] with w hw
    have hw' : u w = 0 := hus w.1 w.2 hw
    simp [PastExtension.pastVelocity, PastExtension.zeroBefore,
      TimeLocalization.activatedVelocity, hw']
  · filter_upwards [hn] with w hw
    have hw' : p w = 0 := hps w.1 w.2 hw
    simp [PastExtension.pastPressure, PastExtension.zeroBefore,
      TimeLocalization.activatedPressure, hw']

omit hu hp in
/-- The supplied limits are forced to vanish where the residual does: every
residual jet is identically zero along the time line through such a point. -/
theorem limits_zero_outside {x : Space} (hx : x ∉ K) (n : ℕ) : L x n = 0 := by
  have hjet : ∀ t : ℝ,
      iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x) = 0 := by
    intro t
    have hn : {w : SpaceTime | w.2 ∉ K} ∈ 𝓝 (t, x) :=
      (hK.isOpen_compl.preimage continuous_snd).mem_nhds hx
    have he : (fun z : SpaceTime => navierStokesResidual u p z.1 z.2) =ᶠ[𝓝 (t, x)]
        (fun _ => 0) := by
      filter_upwards [hn] with w hw
      exact residual_zero_outside u p hK hus hps hw
    have he' : (fun z : SpaceTime => navierStokesResidual u p z.1 z.2) =ᶠ[𝓝[univ] (t, x)]
        (fun _ => 0) := he.filter_mono nhdsWithin_le_nhds
    simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using
      he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.eq_of_nhds n
  have hL : Tendsto (fun t : ℝ =>
      iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
      (𝓝[<] (1 : ℝ)) (𝓝 (L x n)) :=
    (hlim n).tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)
  have hzero : Tendsto (fun t : ℝ =>
      iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simp only [hjet]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hL hzero

omit hu hp in
theorem tracedResidual_zero_outside {x : Space} (hx : x ∉ K) (t : ℝ) :
    tracedResidual u p L (t, x) = 0 := by
  rcases lt_or_ge t 1 with ht | ht
  · rw [tracedResidual, SpacetimeEndpoint.extendTrace_of_lt (z := (t, x)) ht]
    exact pastResidual_zero_outside u p hK hus hps hx
  · simp [tracedResidual, SpacetimeEndpoint.extendTrace, not_lt.mpr ht,
      limits_zero_outside u p L hlim hK hus hps hx 0]

theorem normalTrace_zero_outside {x : Space} (hx : x ∉ K) (n : ℕ) :
    SpacetimeGluing.normalTrace 1 (tracedResidual u p L) n x = 0 := by
  rw [SpacetimeGluing.normalTrace_eq_time_jet (tracedResidual_smooth u p hu hp L hlim) n x]
  have hzero : (fun t : ℝ => tracedResidual u p L (t, x)) = fun _ => (0 : Space) :=
    funext fun t => tracedResidual_zero_outside u p L hlim hK hus hps hx t
  rw [hzero, iteratedDerivWithin_const, ite_self]

/-- The force vanishes at every time wherever both fields vanish at every time. -/
theorem force_zero_outside {x : Space} (hx : x ∉ K) (t : ℝ) :
    force u p hu hp L hlim (t, x) = 0 := by
  rcases le_or_gt t 1 with ht | ht
  · rw [force, SpacetimeGluing.smoothExtension_eqOn_past (tracedResidual_smooth u p hu hp L hlim)
      (show (t, x) ∈ SpacetimeGluing.past 1 from ⟨ht, mem_univ x⟩)]
    exact tracedResidual_zero_outside u p L hlim hK hus hps hx t
  · simp only [force, SpacetimeGluing.smoothExtension, SpacetimeGluing.glue, not_le.mpr ht,
      ite_false, SpatialBorelExtension.rightExtension, SpatialBorelExtension.extension,
      SpatialBorelExtension.term, normalTrace_zero_outside u p hu hp L hlim hK hus hps hx,
      BorelExtension.term, BorelExtension.monomial, smul_zero, tsum_zero]

end Locality

end Construction

end NavierStokes.CandidateFromLimits
