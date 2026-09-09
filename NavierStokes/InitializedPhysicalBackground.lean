import NavierStokes.PhysicalStageBounds
import NavierStokes.ActualBaseVelocityBounds
import NavierStokes.MixedFiniteBackground

/-!
# Initial physical velocity bounds from the actual base and native data

The base potential is the anchored `TailGaugePotential.finalPotential`.
Its curl is the constructed `FinalSlowBase.velocity`.  Only the finite
initialization potential pays the derivative used by the curl estimate;
no growth estimate on the base potential or its gauge is required.
-/

noncomputable section

namespace NavierStokes.InitializedPhysicalBackground

open Set Filter ProblemStatement DiagonalResidual PhysicalStageBounds
open scoped Topology ContDiff BigOperators

/-- The loss for the actual finite initialization potential, before curl.
The offsets absorb its own native homogeneity, without a positivity
assumption on the initialization gain. -/
noncomputable def seedPotentialLoss (h waveAlpha waveShift meanAlpha : ℝ) (m : ℕ) : ℝ :=
  potentialLoss h (-(h * waveAlpha + waveShift)) (-(h * meanAlpha)) m

noncomputable def seedDirectLoss (h meanAlpha : ℝ) (m : ℕ) : ℝ :=
  directLoss h (-(h * meanAlpha)) m

/-- This loss depends only on fixed initialization data and derivative
order. It has no later correction-stage parameter. -/
noncomputable def initialLoss (h waveAlpha waveShift potentialAlpha directAlpha : ℝ)
    (m : ℕ) : ℝ :=
  max (ActualBaseVelocityBounds.heatLoss m)
    (max (seedPotentialLoss h waveAlpha waveShift potentialAlpha (m + 1))
      (seedDirectLoss h directAlpha m))


theorem endpoint_sublevel {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) :
    ∀ᶠ w in ActualBaseVelocityBounds.endpoint,
      w ∈ CutStageEstimates.physicalSublevel h qbig := by
  have ht := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  filter_upwards [ActualBaseVelocityBounds.endpoint_past,
    ht.eventually (gt_mem_nhds hqbig)] with w hw hqw
  exact ⟨hw, hqw⟩

theorem spatialCurl_add_on {U : Set SpaceTime} (hU : IsOpen U)
    {A B : VelocityField} (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    EqOn (SpatialCurl.spatialCurl (fun w => A w + B w))
      (fun w => SpatialCurl.spatialCurl A w + SpatialCurl.spatialCurl B w) U := by
  intro w hw
  have ha := ResidualStability.spatialSlice_differentiable hU hA hw
  have hb := ResidualStability.spatialSlice_differentiable hU hB hw
  change SpatialCurl.curlLinear
    (fderiv ℝ (fun y => A (w.1, y) + B (w.1, y)) w.2) = _
  rw [fderiv_fun_add ha hb, map_add]
  rfl

theorem spatialCurl_smoothOn {U : Set SpaceTime} (hU : IsOpen U)
    {A : VelocityField} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl A) U := by
  intro w hw
  exact (SpatialCurl.contDiffAt_spatialCurl (hA.contDiffAt (hU.mem_nhds hw))
    (by simp)).contDiffWithinAt

section NativeInitialization

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}



end NativeInitialization

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}












end ActualBase

end NavierStokes.InitializedPhysicalBackground
