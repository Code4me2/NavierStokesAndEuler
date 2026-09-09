import Euler.PacketFiniteLifespan
import Euler.StageDisplacementBound
import Euler.StageDisplacementConfinement
import Euler.StageInitialSupport
import Euler.PacketCurlTransport
import Euler.H3CurlConvergence
import Euler.OrdinaryEulerMaximal

/-!
# Uniformly compact vorticity of the canonical maximal solution

The compact set that step 3 of the top of the Euler argument needs. Every
packet horizon contains the maximal lifespan (`lifespan_le_packet_horizon`),
so H³ stability passes the common vorticity support of the packet stages to
every shorter ordinary Euler evolution, and hence to the canonical maximal
field itself: `canonical_vorticity_confined`.
-/

/-! Every selected finite packet has vorticity supported in one fixed ball
throughout its horizon. Initial support, the actual vorticity transport law,
and the summable particle-map displacement bound supply the three ingredients. -/

noncomputable section

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerMeanCutoffCurl Euler.ComparatorBridge

theorem packets_vorticity_support (n : ℕ)
    (t : Icc (0 : ℝ) (packets n).parent.T) :
    tsupport (vectorCurl (fun x => (packets n).state.evolution.velocity (t,x))) ⊆
      Metric.closedBall 0 (2 + particleDisplacementCap constructionScales le_rfl le_rfl) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  exact support_subset_of_transport ((packets n).parent.position t)
    ((packets n).state.evolution.inverse.field t)
    (vectorCurl (fun x => (packets n).state.evolution.velocity (0,x)))
    (vectorCurl (fun x => (packets n).state.evolution.velocity (t,x)))
    ((packets n).state.evolution.inverse.right_inverse t)
    (packets_position_mapsTo_closedBall 2 n t)
    ((subset_tsupport _).trans (packets_initial_curl_support n))
    (fun a ha => (packets n).state.evolution.curl_eq_zero_along_position a ha t)

end EulerPacketInduction
end

noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerMeanCutoffCurl EulerSmoothL2Series
open scoped Topology

def canonicalVorticityBall : Set Space :=
  Metric.closedBall 0 (2 + particleDisplacementCap constructionScales le_rfl le_rfl)

theorem canonicalVorticityBall_compact : IsCompact canonicalVorticityBall :=
  isCompact_closedBall _ _

theorem evolution_vorticity_support (S : ℝ) (hS : 0 < S) (hSL : S < lifespan.duration)
    (t : Icc (0 : ℝ) S) :
    tsupport (vectorCurl ((lifespan.evolution S hS hSL).velocity t).field) ⊆
      canonicalVorticityBall := by
  let U := lifespan.evolution S hS hSL
  let hST : ∀ n, S ≤ (packets n).parent.T :=
    fun n => hSL.le.trans (lifespan_le_packet_horizon n)
  let V : ℕ → Evolution S hS.le := fun n =>
    (packets n).state.regularity.ordinaryEvolution.restrictTime S hS.le (hST n)
  have hfield (n : ℕ) (s : Icc (0 : ℝ) S) : ((V n).velocity s).field =
      fun x => (packets n).state.evolution.velocity (s,x) := by
    funext x
    exact ((packets n).state.regularity.velocity_match
      ⟨s,s.property.1,s.property.2.trans (hST n)⟩ x).symm
  have hnorm (n : ℕ) : tensorNorm 3 (U.difference (V n) ⟨0,le_rfl,hS.le⟩) =
      derivativeSum 3 ((fun x => (packets n).state.evolution.velocity (0,x)) -
        initialDatum.field) := by
    rw [tensorNorm_eq_derivativeSum]
    congr 1
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((V n).velocity ⟨0,le_rfl,hS.le⟩).field x -
      ((lifespan.evolution S hS hSL).velocity ⟨0,le_rfl,hS.le⟩).field x = _
    rw [hfield,lifespan.evolution_initial S hS hSL]
    rfl
  have hinit : Tendsto (fun n => tensorNorm 3
      (U.difference (V n) ⟨0,le_rfl,hS.le⟩)) atTop (𝓝 0) := by
    simpa only [hnorm] using initialDatum_Hm 3
  have hsupport (n : ℕ) : tsupport (vectorCurl ((V n).velocity t).field) ⊆
      canonicalVorticityBall := by
    rw [hfield]
    exact packets_vorticity_support n ⟨t,t.property.1,t.property.2.trans (hST n)⟩
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hout
  have hz (n : ℕ) : vectorCurl ((V n).velocity t).field x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hout (hsupport n hm))
  have hzero : Tendsto (fun n => vectorCurl ((V n).velocity t).field x) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Space)) atTop (𝓝 0))
  exact hx (tendsto_nhds_unique (U.curl_tendsto_of_initial_h3 V hinit t x) hzero)

/-- Step 3, the confinement: the vorticity of the canonical maximal solution
stays in one fixed ball throughout the lifespan. -/
theorem canonical_vorticity_confined (t : lifespan.Time) :
    tsupport (vectorCurl (lifespan.maximalVelocity t)) ⊆ canonicalVorticityBall :=
  evolution_vorticity_support (lifespan.intermediateHorizon t)
    (lifespan.intermediateHorizon_pos t) (lifespan.intermediateHorizon_lt t)
    (lifespan.intermediateTime t)

end EulerPacketInduction
