import NavierStokes.SmoothCutoffs
import NavierStokes.DiagonalScale
import NavierStokes.SpatialCurl
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.LocallyFinite

/-!
# Smooth solenoidal diagonal sums

The sum in this file is an actual `tsum` of cut potentials. At each point
where the continuous scale `q` is positive, an entire tail is identically zero
on a common neighborhood. Thus the sum equals a finite prefix locally.
Smoothness requires smooth `q` and smooth potentials; mere continuity of `q`
is sufficient for local finiteness only. The resulting spatial curl is smooth
and divergence-free. No residual estimate or singular endpoint regularity is
assumed or proved here.
-/

noncomputable section

namespace NavierStokes.SolenoidalDiagonal

open Set Filter Function
open scoped Topology BigOperators ContDiff

section Topological

variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cut the potential before applying any velocity derivative. -/
def cutStage (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V) (j : ℕ) (x : X) : V :=
  SmoothCutoffs.scaledCutoff (a j) (q x) • A j x

/-- The actual infinite sum; local finiteness below proves it is well behaved
on the positive-scale domain. -/
def potentialSum (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V) (x : X) : V :=
  ∑' j : ℕ, cutStage a q A j x

def partialPotential (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V)
    (N : ℕ) (x : X) : V :=
  ∑ j ∈ Finset.range N, cutStage a q A j x

/-- A common neighborhood, not merely a pointwise support bound, kills all
sufficiently late stages. No regularity of the potentials is needed. -/
theorem eventually_zero_tail {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {x : X} (hq : ContinuousAt q x) (hqx : 0 < q x)
    (A : ℕ → X → V) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ j : ℕ, N ≤ j → cutStage a q A j y = 0 := by
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood a ha hqx
  refine ⟨N, ?_⟩
  filter_upwards [hq (lt_mem_nhds (half_lt_self hqx))] with y hy
  intro j hj
  simp only [cutStage, hN j hj (q y) hy, zero_smul]

/-- Local equality to a finite prefix establishes the meaning of the `tsum`.
The prefix length works for all derivative orders. -/
theorem potentialSum_eventuallyEq_partial {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {x : X} (hq : ContinuousAt q x) (hqx : 0 < q x)
    (A : ℕ → X → V) :
    ∃ N : ℕ, potentialSum a q A =ᶠ[𝓝 x] partialPotential a q A N := by
  obtain ⟨N, hN⟩ := eventually_zero_tail ha hq hqx A
  refine ⟨N, hN.mono ?_⟩
  intro y hy
  apply tsum_eq_sum
  intro j hj
  exact hy j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))

theorem summable_cutStage {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : X → ℝ} {x : X} (hq : ContinuousAt q x) (hqx : 0 < q x)
    (A : ℕ → X → V) : Summable (fun j => cutStage a q A j x) := by
  obtain ⟨N, hN⟩ := eventually_zero_tail ha hq hqx A
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro j hj
  exact hN.self_of_nhds j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj))



end Topological

section Smooth

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cutStage_contDiffAt {a : ℕ → ℝ} {q : E → ℝ} {A : ℕ → E → V}
    {x : E} (hq : ContDiffAt ℝ ∞ q x) (hA : ∀ j, ContDiffAt ℝ ∞ (A j) x)
    (j : ℕ) : ContDiffAt ℝ ∞ (cutStage a q A j) x :=
  ((SmoothCutoffs.scaledCutoff_contDiff (a j)).comp_contDiffAt x hq).smul (hA j)

/-- Smoothness is proved for the constructed sum, not postulated. -/
theorem potentialSum_contDiffAt {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {x : E} (hqx : 0 < q x)
    (hq : ContDiffAt ℝ ∞ q x) (hA : ∀ j, ContDiffAt ℝ ∞ (A j) x) :
    ContDiffAt ℝ ∞ (potentialSum a q A) x := by
  obtain ⟨N, hN⟩ := potentialSum_eventuallyEq_partial ha hq.continuousAt hqx A
  have hpartial : ContDiffAt ℝ ∞ (partialPotential a q A N) x :=
    ContDiffAt.sum (fun j _ => cutStage_contDiffAt hq hA j)
  exact hpartial.congr_of_eventuallyEq hN

theorem potentialSum_contDiffOn {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : E → ℝ} {A : ℕ → E → V} {U : Set E} (hU : IsOpen U)
    (hqpos : ∀ x ∈ U, 0 < q x) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    ContDiffOn ℝ ∞ (potentialSum a q A) U := by
  intro x hx
  exact (potentialSum_contDiffAt ha (hqpos x hx) (hq.contDiffAt (hU.mem_nhds hx))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

/-- Equality on a neighborhood preserves every iterated actual Fréchet
derivative, including the totalized derivative at nonsmooth points. -/
theorem iteratedFDeriv_eventuallyEq {f g : E → V} {x : E}
    (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedFDeriv ℝ k f =ᶠ[𝓝 x] iteratedFDeriv ℝ k g := by
  have h' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [nhdsWithin_univ, iteratedFDerivWithin_univ] using
    h'.iteratedFDerivWithin (𝕜 := ℝ) k




end Smooth

section Spatial

open ProblemStatement

/-- The constructed velocity is the actual spatial curl of the summed
potential, with time held fixed by `SpatialCurl.spatialCurl`. -/
def velocitySum (a : ℕ → ℝ) (q : SpaceTime → ℝ) (A : ℕ → VelocityField) :
    VelocityField :=
  SpatialCurl.spatialCurl (potentialSum a q A)

theorem velocitySum_contDiffAt {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {z : SpaceTime}
    (hqz : 0 < q z) (hq : ContDiffAt ℝ ∞ q z)
    (hA : ∀ j, ContDiffAt ℝ ∞ (A j) z) :
    ContDiffAt ℝ ∞ (velocitySum a q A) z :=
  SpatialCurl.contDiffAt_spatialCurl (potentialSum_contDiffAt ha hqz hq hA) (by simp)

theorem velocitySum_contDiffOn {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) :
    ContDiffOn ℝ ∞ (velocitySum a q A) U := by
  intro z hz
  exact (velocitySum_contDiffAt ha (hqpos z hz) (hq.contDiffAt (hU.mem_nhds hz))
    (fun j => (hA j).contDiffAt (hU.mem_nhds hz))).contDiffWithinAt



theorem spatialCurl_eq_of_eventuallyEq {A B : VelocityField} {z : SpaceTime}
    (h : A =ᶠ[𝓝 z] B) : SpatialCurl.spatialCurl A z = SpatialCurl.spatialCurl B z := by
  apply SpatialCurl.curl_eq_of_eventuallyEq
  exact h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt

theorem spatialCurl_eventuallyEq {A B : VelocityField} {z : SpaceTime}
    (h : A =ᶠ[𝓝 z] B) : SpatialCurl.spatialCurl A =ᶠ[𝓝 z] SpatialCurl.spatialCurl B :=
  h.eventuallyEq_nhds.mono fun _ hz => spatialCurl_eq_of_eventuallyEq hz




/-- Integer schedules from `DiagonalScale` supply the required real divergence
of the cutoff scales. -/
theorem realScales_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto (fun j => (a j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp ha.tendsto_atTop



end Spatial

end NavierStokes.SolenoidalDiagonal
