import NavierStokes.CorrectionStep
import NavierStokes.PhysicalResidualTZ
import NavierStokes.PhysicalCurlCovariance
import NavierStokes.MixedDiagonalResidual

/-!
# Physical finite prefixes of the actual correction cycle

The state and its coefficient data evolve by `CorrectionStep.CycleState.iterate`.
At one fixed band and graph, the physical field differences below are derived
from its literal four updates.  Stage zero contains the base and initialization.

`velocityTZ` gives cylindrical components.  The Cartesian realization uses the
existing genuine local polar charts; its physical interpretation is asserted
only on their valid domains.  A final adapter accepts individual potential-curl
realizations, not an assumed equality of finite prefixes.
-/

noncomputable section

namespace NavierStokes.CyclePhysicalPrefixes

open Set Filter Function ProblemStatement CorrectionState CorrectionStep
open MeanIncrementBounds
open scoped ContDiff Topology BigOperators

abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev Components := Cylinder → Fin 3 → ℝ
abbrev ScaledGraph := PhysicalResidualBridge.ScaledGraph

/-- The actual cylindrical realization is linear in the three components. -/
noncomputable def velocityMap (G : ScaledGraph) : Components →ₗ[ℝ] VelocityField where
  toFun := PhysicalResidualTZ.velocityTZ G
  map_add' a b := by
    funext z
    ext i
    simp [PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply,
      mul_add]
  map_smul' r a := by
    funext z
    ext i
    simp [PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply,
      mul_left_comm]

/-- Pressure includes the square of the same fixed velocity scale. -/
noncomputable def pressureMap (G : ScaledGraph) : (Cylinder → ℝ) →ₗ[ℝ] PressureField where
  toFun := PhysicalResidualTZ.pressureTZ G
  map_add' a b := by
    funext z
    simp [PhysicalResidualTZ.pressureTZ, PhysicalResidualBridge.ScaledGraph.pressure, mul_add]
  map_smul' r a := by
    funext z
    simp [PhysicalResidualTZ.pressureTZ, PhysicalResidualBridge.ScaledGraph.pressure,
      mul_left_comm]

noncomputable def meanComponents (m : Triple CyclePoint) (n : ℕ) : Components :=
  fun x => ![m.radial n x.1, m.angular n x.1, m.axial n x.1]

theorem meanComponents_updated (m h : Triple CyclePoint) (n : ℕ) :
    meanComponents (updated m h) n = meanComponents m n + meanComponents h n := by
  funext x i
  fin_cases i <;> rfl

theorem incrementComponents_eq (u : State CyclePoint) (n : ℕ) :
    PhysicalResidualBridge.incrementComponents u n = meanComponents u.mean n + u.oscillation n := by
  funext x i
  fin_cases i <;> rfl

/-- Base plus the actual mean and oscillatory velocity, at one fixed band. -/
noncomputable def cylindricalVelocity (G : ScaledGraph) (n : ℕ)
    (c : Context CyclePoint) (u : State CyclePoint) : VelocityField :=
  velocityMap G (PhysicalResidualBridge.baseComponents c n +
    PhysicalResidualBridge.incrementComponents u n)

/-- The fixed base pressure is retained once, in addition to both state pressures. -/
noncomputable def cylindricalPressure (G : ScaledGraph) (n : ℕ)
    (p₀ : Cylinder → ℝ) (u : State CyclePoint) : PressureField :=
  pressureMap G (p₀ + u.totalPressureIncrement n)

section OneStep

variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)

/-- All four actual velocity increments, in their order of construction. -/
noncomputable def stepComponents (n : ℕ) : Components :=
  p.particularVelocity v c u n + p.signedVelocity v c u n +
    meanComponents (p.temporalIncrement v c u) n + meanComponents (p.rankIncrement v c u) n

/-- The four actual mean-pressure changes, and the two oscillatory pressures. -/
noncomputable def stepPressureComponents (n : ℕ) : Cylinder → ℝ :=
  fun x =>
    ((p.afterParticular v c u).pressure n x.1 - u.pressure n x.1) +
    ((p.afterSigned v c u).pressure n x.1 - (p.afterParticular v c u).pressure n x.1) +
    ((p.afterTemporal v c u).pressure n x.1 - (p.afterSigned v c u).pressure n x.1) +
    ((p.afterRank v c u).pressure n x.1 - (p.afterTemporal v c u).pressure n x.1) +
    p.particularPressure v c u n x + p.signedPressure v c u n x

theorem next_incrementComponents (n : ℕ) :
    PhysicalResidualBridge.incrementComponents (p.next v c u) n =
      PhysicalResidualBridge.incrementComponents u n + stepComponents p v c u n := by
  rw [incrementComponents_eq, p.next_mean, p.next_oscillation,
    meanComponents_updated, meanComponents_updated, incrementComponents_eq]
  simp only [stepComponents, Pi.add_apply]
  abel

theorem next_pressure : (p.next v c u).pressure = (p.afterRank v c u).pressure := rfl

theorem next_pressureComponents (n : ℕ) :
    (p.next v c u).totalPressureIncrement n =
      u.totalPressureIncrement n + stepPressureComponents p v c u n := by
  funext x
  simp only [State.totalPressureIncrement, p.next_oscillatoryPressure,
    next_pressure, stepPressureComponents, Pi.add_apply]
  ring

noncomputable def cylindricalStepVelocity (G : ScaledGraph) (n : ℕ) : VelocityField :=
  velocityMap G (stepComponents p v c u n)

noncomputable def cylindricalStepPressure (G : ScaledGraph) (n : ℕ) : PressureField :=
  pressureMap G (stepPressureComponents p v c u n)

theorem cylindricalVelocity_next (G : ScaledGraph) (n : ℕ) :
    cylindricalVelocity G n c (p.next v c u) =
      cylindricalVelocity G n c u + cylindricalStepVelocity p v c u G n := by
  unfold cylindricalVelocity cylindricalStepVelocity
  rw [next_incrementComponents, ← add_assoc, map_add]

theorem cylindricalPressure_next (G : ScaledGraph) (n : ℕ) (p₀ : Cylinder → ℝ) :
    cylindricalPressure G n p₀ (p.next v c u) =
      cylindricalPressure G n p₀ u + cylindricalStepPressure p v c u G n := by
  unfold cylindricalPressure cylindricalStepPressure
  rw [next_pressureComponents, ← add_assoc, map_add]



end OneStep

/-- A genuine local Cartesian realization using the frozen inverse polar chart. -/
noncomputable def polarVelocityMap (a : ℝ) (j : PolarCharts.Index) :
    VelocityField →ₗ[ℝ] VelocityField where
  toFun v z := CylindricalResidual.frame (PhysicalCurlCovariance.polarInput a j z).2
    (v (PhysicalCurlCovariance.polarCoordinates a j z))
  map_add' v w := by
    funext z
    exact map_add _ _ _
  map_smul' r v := by
    funext z
    exact (CylindricalResidual.frame (PhysicalCurlCovariance.polarInput a j z).2).map_smul
      r (v (PhysicalCurlCovariance.polarCoordinates a j z))

noncomputable def polarPressureMap (a : ℝ) (j : PolarCharts.Index) :
    PressureField →ₗ[ℝ] PressureField where
  toFun p z := p (PhysicalCurlCovariance.polarCoordinates a j z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual state velocity in this local Cartesian chart. -/
noncomputable def velocity (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)
    (c : Context CyclePoint) (u : State CyclePoint) : VelocityField :=
  polarVelocityMap a j (cylindricalVelocity G n c u)

noncomputable def pressure (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)
    (p₀ : Cylinder → ℝ) (u : State CyclePoint) : PressureField :=
  polarPressureMap a j (cylindricalPressure G n p₀ u)





section CartesianStep

variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)
    (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)

noncomputable def stepVelocity : VelocityField :=
  polarVelocityMap a j (cylindricalStepVelocity p v c u G n)

noncomputable def stepPressure : PressureField :=
  polarPressureMap a j (cylindricalStepPressure p v c u G n)

theorem velocity_next :
    velocity a j G n c (p.next v c u) = velocity a j G n c u + stepVelocity p v c u a j G n := by
  simp only [velocity, stepVelocity, cylindricalVelocity_next, map_add]

theorem pressure_next (p₀ : Cylinder → ℝ) :
    pressure a j G n p₀ (p.next v c u) = pressure a j G n p₀ u + stepPressure p v c u a j G n := by
  simp only [pressure, stepPressure, cylindricalPressure_next, map_add]



end CartesianStep

/-! ## The literal finite prefixes, including initialization at index zero -/

section Prefixes

variable {ι : Type} (p : ℕ → CycleParameters ι) (c : Context CyclePoint)
    (seed : CycleState ι) (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)

noncomputable def velocityStages (k : ℕ) : VelocityField :=
  Nat.casesOn k (velocity a j G n c seed.state)
    (fun k => stepVelocity (p k) (CycleState.iterate p c seed k).coefficients c
      (CycleState.iterate p c seed k).state a j G n)

noncomputable def pressureStages (p₀ : Cylinder → ℝ) (k : ℕ) : PressureField :=
  Nat.casesOn k (pressure a j G n p₀ seed.state)
    (fun k => stepPressure (p k) (CycleState.iterate p c seed k).coefficients c
      (CycleState.iterate p c seed k).state a j G n)


@[simp] theorem pressureStages_zero (p₀ : Cylinder → ℝ) :
    pressureStages p c seed a j G n p₀ 0 = pressure a j G n p₀ seed.state := rfl

theorem velocity_prefix (J : ℕ) :
    DiagonalJetBounds.uncutPrefix (velocityStages p c seed a j G n) (J + 1) =
      velocity a j G n c (CycleState.iterate p c seed J).state := by
  induction J with
  | zero =>
      funext z
      simp [DiagonalJetBounds.uncutPrefix, velocityStages, CycleState.iterate]
  | succ J ih =>
      funext z
      calc
        _ = DiagonalJetBounds.uncutPrefix (velocityStages p c seed a j G n) (J + 1) z +
            stepVelocity (p J) (CycleState.iterate p c seed J).coefficients c
              (CycleState.iterate p c seed J).state a j G n z :=
          Finset.sum_range_succ (fun k => velocityStages p c seed a j G n k z) (J + 1)
        _ = velocity a j G n c (CycleState.iterate p c seed J).state z +
            stepVelocity (p J) (CycleState.iterate p c seed J).coefficients c
              (CycleState.iterate p c seed J).state a j G n z := by rw [ih]
        _ = _ := (congrFun (velocity_next (p J) (CycleState.iterate p c seed J).coefficients c
          (CycleState.iterate p c seed J).state a j G n) z).symm

theorem pressure_prefix (p₀ : Cylinder → ℝ) (J : ℕ) :
    DiagonalJetBounds.uncutPrefix (pressureStages p c seed a j G n p₀) (J + 1) =
      pressure a j G n p₀ (CycleState.iterate p c seed J).state := by
  induction J with
  | zero =>
      funext z
      simp [DiagonalJetBounds.uncutPrefix, pressureStages, CycleState.iterate]
  | succ J ih =>
      funext z
      calc
        _ = DiagonalJetBounds.uncutPrefix (pressureStages p c seed a j G n p₀) (J + 1) z +
            stepPressure (p J) (CycleState.iterate p c seed J).coefficients c
              (CycleState.iterate p c seed J).state a j G n z :=
          Finset.sum_range_succ (fun k => pressureStages p c seed a j G n p₀ k z) (J + 1)
        _ = pressure a j G n p₀ (CycleState.iterate p c seed J).state z +
            stepPressure (p J) (CycleState.iterate p c seed J).coefficients c
              (CycleState.iterate p c seed J).state a j G n z := by rw [ih]
        _ = _ := (congrFun (pressure_next (p J) (CycleState.iterate p c seed J).coefficients c
          (CycleState.iterate p c seed J).state a j G n p₀) z).symm

end Prefixes

/-! ## The actual split into potential and direct angular contributions -/

noncomputable def meridionalComponents (m : Triple CyclePoint) (n : ℕ) : Components :=
  fun x => ![m.radial n x.1, 0, m.axial n x.1]

noncomputable def angularComponents (m : Triple CyclePoint) (n : ℕ) : Components :=
  fun x => ![0, m.angular n x.1, 0]

theorem meanComponents_split (m : Triple CyclePoint) (n : ℕ) :
    meanComponents m n = meridionalComponents m n + angularComponents m n := by
  funext x i
  fin_cases i <;> simp [meanComponents, meridionalComponents, angularComponents]

/-- This velocity contribution still needs a potential realization. It includes
the full base, the initialized wave, and the meridional mean. -/
noncomputable def initialPotentialPart (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph)
    (n : ℕ) (c : Context CyclePoint) (u : State CyclePoint) : VelocityField :=
  polarVelocityMap a j (velocityMap G (PhysicalResidualBridge.baseComponents c n +
    meridionalComponents u.mean n + u.oscillation n))

noncomputable def initialDirectPart (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph)
    (n : ℕ) (u : State CyclePoint) : VelocityField :=
  polarVelocityMap a j (velocityMap G (angularComponents u.mean n))

theorem velocity_initial_split (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph)
    (n : ℕ) (c : Context CyclePoint) (u : State CyclePoint) :
    velocity a j G n c u = initialPotentialPart a j G n c u + initialDirectPart a j G n u := by
  simp only [velocity, cylindricalVelocity, initialPotentialPart, initialDirectPart,
    incrementComponents_eq, meanComponents_split, map_add]
  abel

section SplitStep

variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context CyclePoint) (u : State CyclePoint)
    (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)

/-- The wave increments and the two meridional mean increments, literally. -/
noncomputable def stepPotentialPart : VelocityField :=
  polarVelocityMap a j (velocityMap G (p.particularVelocity v c u n + p.signedVelocity v c u n +
    meridionalComponents (p.temporalIncrement v c u) n +
    meridionalComponents (p.rankIncrement v c u) n))

/-- The angular means remain direct velocities, not unspecified curls. -/
noncomputable def stepDirectPart : VelocityField :=
  polarVelocityMap a j (velocityMap G (angularComponents (p.temporalIncrement v c u) n +
    angularComponents (p.rankIncrement v c u) n))

theorem stepVelocity_split :
    stepVelocity p v c u a j G n = stepPotentialPart p v c u a j G n +
      stepDirectPart p v c u a j G n := by
  simp only [stepVelocity, cylindricalStepVelocity, stepComponents, stepPotentialPart,
    stepDirectPart, meanComponents_split, map_add]
  abel

end SplitStep

section MixedPrefixes

variable {ι : Type} (p : ℕ → CycleParameters ι) (c : Context CyclePoint)
    (seed : CycleState ι) (a : ℝ) (j : PolarCharts.Index) (G : ScaledGraph) (n : ℕ)

/-- The exact velocity each still-to-be-constructed potential must realize. -/
noncomputable def potentialParts (k : ℕ) : VelocityField :=
  Nat.casesOn k (initialPotentialPart a j G n c seed.state)
    (fun k => stepPotentialPart (p k) (CycleState.iterate p c seed k).coefficients c
      (CycleState.iterate p c seed k).state a j G n)

/-- The direct angular sequence is constructed from the actual states. -/
noncomputable def directStages (k : ℕ) : VelocityField :=
  Nat.casesOn k (initialDirectPart a j G n seed.state)
    (fun k => stepDirectPart (p k) (CycleState.iterate p c seed k).coefficients c
      (CycleState.iterate p c seed k).state a j G n)

theorem velocityStages_split (k : ℕ) :
    velocityStages p c seed a j G n k = potentialParts p c seed a j G n k +
      directStages p c seed a j G n k := by
  cases k with
  | zero => exact velocity_initial_split a j G n c seed.state
  | succ k =>
      exact stepVelocity_split (p k) (CycleState.iterate p c seed k).coefficients c
        (CycleState.iterate p c seed k).state a j G n

/-- The linearity of the genuine spatial derivative in the finite potential sum.
Only local first differentiability is needed for this identity. -/
theorem curl_uncutPrefix {U : Set SpaceTime} (hU : IsOpen U)
    (A : ℕ → VelocityField) (hA : ∀ k, DifferentiableOn ℝ (A k) U)
    (N : ℕ) {z : SpaceTime} (hz : z ∈ U) :
    SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A N) z =
      ∑ k ∈ Finset.range N, SpatialCurl.spatialCurl (A k) z := by
  exact PhysicalParticularWave.spatialCurl_finset_sum (Finset.range N) A
    (fun k _ => (hA k).differentiableAt (hU.mem_nhds hz))

/-- No prefix matching is assumed: individual curl realizations give the
actual finite state, with its initialized index zero and literal direct means. -/
theorem mixedVelocity_prefix {U : Set SpaceTime} (hU : IsOpen U)
    (A : ℕ → VelocityField) (hA : ∀ k, DifferentiableOn ℝ (A k) U)
    (hcurl : ∀ k, EqOn (SpatialCurl.spatialCurl (A k))
      (potentialParts p c seed a j G n k) U) (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A (directStages p c seed a j G n) J)
      (velocity a j G n c (CycleState.iterate p c seed J).state) U := by
  intro z hz
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)) z +
    (∑ k ∈ Finset.range (J + 1), directStages p c seed a j G n k z) = _
  rw [curl_uncutPrefix hU A hA (J + 1) hz, ← Finset.sum_add_distrib]
  calc
    _ = DiagonalJetBounds.uncutPrefix (velocityStages p c seed a j G n) (J + 1) z := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcurl k hz]
      exact (congrFun (velocityStages_split p c seed a j G n k) z).symm
    _ = _ := congrFun (velocity_prefix p c seed a j G n J) z



end MixedPrefixes

end NavierStokes.CyclePhysicalPrefixes
