import NavierStokes.SpacetimeEndpoint
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Endpoint limits from actual joint jets and local one-sided extensions

The input is an actual function, smooth on `t < 1`. Its full Frechet jets
vanish jointly at `(1,0)`, and it has an actual smooth local extension near
each other point of the terminal slice. The boundary tensor family and its
local uniform convergence are constructed below.
-/

noncomputable section

namespace NavierStokes.JointResidualLimits

open Set Filter
open scoped Topology ContDiff

abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

section JointTopology

variable {ι X V : Type*} [TopologicalSpace X] [PseudoMetricSpace V]
  {p : Filter ι} [p.NeBot] {F : ι × X → V} {L : X → V}

/-- Joint convergence to boundary values forces continuity of those values.
No continuity or local-uniform convergence of the boundary map is assumed. -/
theorem continuous_of_joint_limits
    (hlim : ∀ x, Tendsto F (p ×ˢ 𝓝 x) (𝓝 (L x))) : Continuous L := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh : {q : ι × X | dist (F q) (L x) < ε / 2} ∈ p ×ˢ 𝓝 x :=
    (hlim x).eventually (Metric.ball_mem_nhds (L x) (half_pos hε))
  obtain ⟨U, hU, W, hW, hUW⟩ := Filter.mem_prod_iff.mp hh
  filter_upwards [hW] with y hy
  have hpoint : Tendsto (fun i => F (i, y)) p (𝓝 (L y)) :=
    (hlim y).comp (tendsto_id.prodMk tendsto_const_nhds)
  have hnear : ∀ᶠ i in p, dist (F (i, y)) (L y) < ε / 2 :=
    hpoint.eventually (Metric.ball_mem_nhds (L y) (half_pos hε))
  have hU' : ∀ᶠ i in p, i ∈ U := hU
  obtain ⟨i, hiU, hi⟩ := (hU'.and hnear).exists
  have hix : dist (F (i, y)) (L x) < ε / 2 := hUW ⟨hiU, hy⟩
  calc
    dist (L y) (L x) ≤ dist (L y) (F (i, y)) + dist (F (i, y)) (L x) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hi) hix
    _ = ε := by ring

/-- Reverse joint-to-local-uniform implication, using the uniform-space
characterization of local uniform convergence. -/
theorem locallyUniform_of_joint_limits
    (hlim : ∀ x, Tendsto F (p ×ˢ 𝓝 x) (𝓝 (L x))) :
    TendstoLocallyUniformly (fun i x => F (i, x)) L p := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro x
  have hL : Tendsto (fun q : ι × X => L q.2) (p ×ˢ 𝓝 x) (𝓝 (L x)) :=
    ((continuous_of_joint_limits hlim).tendsto x).comp tendsto_snd
  exact (tendsto_right_nhds_uniformity.comp hL).uniformity_trans
    (tendsto_left_nhds_uniformity.comp (hlim x))

end JointTopology

section ActualJets

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A genuine smooth extension on a neighborhood, agreeing with the original
function on the portion of that neighborhood with `t < 1`. -/
structure OneSidedExtension (f : SpaceTime → V) (x : Space) where
  value : SpaceTime → V
  domain : Set SpaceTime
  isOpen : IsOpen domain
  mem : (1, x) ∈ domain
  smooth : ContDiffOn ℝ ∞ value domain
  agrees : EqOn value f (domain ∩ SpacetimeEndpoint.openPast 1)

def AwayExtensions (f : SpaceTime → V) : Prop :=
  ∀ x : Space, x ≠ 0 → Nonempty (OneSidedExtension f x)

def VanishingJointJets (f : SpaceTime → V) : Prop :=
  ∀ n : ℕ, Tendsto (iteratedFDeriv ℝ n f)
    (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))) (𝓝 0)

theorem past_filter (x : Space) :
    𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), x) = (𝓝[<] (1 : ℝ)) ×ˢ 𝓝 x := by
  simp only [SpacetimeEndpoint.openPast, nhdsWithin_prod_eq, nhdsWithin_univ]

theorem OneSidedExtension.eventuallyEq {f : SpaceTime → V} {x : Space}
    (e : OneSidedExtension f x) :
    f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)] e.value := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (e.isOpen.mem_nhds e.mem)] with z hz he
  exact (e.agrees ⟨he, hz⟩).symm

/-- Local agreement on the open past gives agreement of every actual jet. -/
theorem OneSidedExtension.jets_eventuallyEq {f : SpaceTime → V} {x : Space}
    (e : OneSidedExtension f x) (n : ℕ) :
    iteratedFDeriv ℝ n f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)]
      iteratedFDeriv ℝ n e.value := by
  have he := e.eventuallyEq.iteratedFDerivWithin (𝕜 := ℝ) n
  filter_upwards [he, self_mem_nhdsWithin] with z hz hp
  simpa only [iteratedFDerivWithin_of_isOpen n (SpacetimeEndpoint.openPast_isOpen 1) hp] using hz

theorem OneSidedExtension.jet_tendsto {f : SpaceTime → V} {x : Space}
    (e : OneSidedExtension f x) (n : ℕ) :
    Tendsto (iteratedFDeriv ℝ n f) (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (iteratedFDeriv ℝ n e.value (1, x))) := by
  have hg : ContDiffAt ℝ ∞ e.value (1, x) := e.smooth.contDiffAt (e.isOpen.mem_nhds e.mem)
  have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ n e.value) (1, x) :=
    hg.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (n : ℕ∞) ≤ ⊤))
  exact (hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (e.jets_eventuallyEq n).symm

/-- One family of tensors, selected from actual extensions away from zero.
At the origin each tensor is explicitly zero. -/
noncomputable def boundaryLimits (f : SpaceTime → V) (hext : AwayExtensions f)
    (x : Space) : FormalMultilinearSeries ℝ SpaceTime V := by
  classical
  exact if hx : x = 0 then 0 else
    ftaylorSeries ℝ (Classical.choice (hext x hx)).value (1, x)

@[simp] theorem boundaryLimits_zero (f : SpaceTime → V) (hext : AwayExtensions f) (n : ℕ) :
    boundaryLimits f hext 0 n = 0 := by
  simp [boundaryLimits]

theorem boundaryLimits_joint {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) (n : ℕ) (x : Space) :
    Tendsto (iteratedFDeriv ℝ n f) (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (boundaryLimits f hext x n)) := by
  classical
  by_cases hx : x = 0
  · subst x
    simpa only [boundaryLimits_zero] using hzero n
  · simp only [boundaryLimits, dite_eq_right hx]
    exact (Classical.choice (hext x hx)).jet_tendsto n


theorem boundaryLimits_locallyUniform {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) (n : ℕ) :
    TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n f (t, x))
      (fun x => boundaryLimits f hext x n) (𝓝[<] (1 : ℝ)) := by
  apply locallyUniform_of_joint_limits (F := iteratedFDeriv ℝ n f)
  intro x
  simpa only [past_filter] using boundaryLimits_joint hzero hext n x


theorem past_filter_neBot (x : Space) :
    (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), x)).NeBot := by
  rw [past_filter]
  infer_instance


theorem boundaryLimits_independent {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (h₁ h₂ : AwayExtensions f) : boundaryLimits f h₁ = boundaryLimits f h₂ := by
  funext x n
  let := past_filter_neBot x
  exact tendsto_nhds_unique (boundaryLimits_joint hzero h₁ n x) (boundaryLimits_joint hzero h₂ n x)















end ActualJets

end NavierStokes.JointResidualLimits
