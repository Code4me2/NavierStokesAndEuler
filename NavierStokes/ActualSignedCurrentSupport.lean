import NavierStokes.ActualCyclePreservation
import NavierStokes.CurrentSignedCurl

/-!
# Omitted labels in the actual current signed fields

The current potential and pressure are constructed from the same signed
copy sum as the correction cycle.  Their support implies membership in the
actual active-label set, before any physical pullback or finite sum.
-/

noncomputable section

namespace NavierStokes.ActualSignedCurrentSupport

open Set Function Filter CorrectionState CorrectionStep HarmonicCalculus
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

abbrev Point := ActualSignedCoherence.Point
abbrev FullPoint := ActualSignedCoherence.FullPoint
abbrev Index := ActualInitialization.Index

variable {B N0 : ℕ}

theorem outside_core (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    x ∉ ActualCoreSupport.refinedCarrier l n :=
  fun hc => hn (ActualCyclePreservation.core_active l n hx hc)

/-- Zero values of the literal common coefficient, with arbitrary current
state and no smoothness or residual bound hypothesis. -/
theorem common_zero (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    (ActualSignedCoherence.copies l u).common.amplitude n x = 0 ∧
      (ActualSignedCoherence.copies l u).common.pressure n x = 0 :=
  ActualCycleAssembly.refined_signed_common_zero l ActualInitialization.geometry.strip
    (ActualSignedCoherence.request B u) n hx (outside_core l n hx hn)

theorem potentialCoefficient_zero (l : Index B N0) (u : State Point) (n : ℕ)
    {x : FullPoint} (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.potentialCoefficient l u n x = 0 := by
  simp only [ActualSignedPotentialCoherence.potentialCoefficient, (common_zero l u n hx hn).1,
    CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross, map_zero, smul_zero]

theorem potential_zero (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.potential l u n x = 0 := by
  rw [ActualSignedPotentialCoherence.potential_eq_mode]
  funext i
  simp only [vectorMode, mode, potentialCoefficient_zero l u n hx hn, Pi.zero_apply, zero_mul]

theorem pressureMode_zero (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.pressureMode l u n x = 0 := by
  simp only [ActualSignedPotentialCoherence.pressureMode, mode,
    (common_zero l u n hx hn).2, zero_mul]

theorem native_zero_germs (l : Index B N0) (u : State Point) (n : ℕ) {x : FullPoint}
    (hx : x.1 ∈ ActualInitialization.geometry.domain)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    (ActualSignedPotentialCoherence.potential l u n =ᶠ[𝓝 x] fun _ => 0) ∧
      (ActualSignedPotentialCoherence.pressureMode l u n =ᶠ[𝓝 x] fun _ => 0) := by
  have hU : {y : FullPoint | y.1 ∈ ActualInitialization.geometry.domain} ∈ 𝓝 x :=
    (ActualInitialization.geometry.domain_open.preimage continuous_fst).mem_nhds hx
  constructor
  · filter_upwards [hU] with y hy
    exact potential_zero l u n hy hn
  · filter_upwards [hU] with y hy
    exact pressureMode_zero l u n hy hn

theorem cylindrical_zero (l : Index B N0) (u : State Point) (n : ℕ)
    {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualSignedPotentialCoherence.physicalDomain n)
    (hn : l ∉ activeLabels standardRegion B N0 n) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 := by
  constructor
  · simp only [ActualSignedPotentialCoherence.cylindricalPotential,
      ActualSignedPotentialCoherence.rescaledPotential, potential_zero l u n hz.2 hn, smul_zero]
  · simp only [ActualSignedPotentialCoherence.cylindricalPressureMode,
      ActualSignedPotentialCoherence.rescaledPressureMode, pressureMode_zero l u n hz.2 hn, smul_zero]

theorem physicalDomain_of_source (n : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.source n) :
    z ∈ ActualSignedPotentialCoherence.physicalDomain n :=
  ⟨hz.1, (CurrentSignedCurl.nativePoint_mem n hz).1.1⟩





/-! ## The canonical sum is the finite current active-label sum -/










end NavierStokes.ActualSignedCurrentSupport
