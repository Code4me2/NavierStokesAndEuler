import Euler.ComparatorEvolutionIdentification
import Euler.ComparatorLocalCompactVorticity
import Euler.OrdinaryEulerMaximal
import Euler.ComparatorTruncationFamily
import Euler.ComparatorUniformSpatialJets
import Euler.DivCurlTensorRecovery
import Euler.CompactVorticityTimeUpgrade
import Euler.CompactProjectedEulerLaw

/-!
# Step 2: a Comparator solution agrees with the canonical maximal solution

The local Comparator-to-development conversion: compact initial vorticity
remains in one compact set for a positive time; elliptic recovery gives all
spatial L² derivatives on that interval, and the genuine Euler pairings
against dense compact solenoidal tests provide the time regularity of an
ordinary Euler evolution (`compactCurlLocalUpgrade`). Restarting the
conversion at every time of agreement, ordinary uniqueness identifies a
global Comparator solution with the canonical maximal solution on the whole
lifespan, provided the canonical vorticity stays compact
(`comparator_agrees_with_canonical`).
-/

noncomputable section


namespace Euler.ComparatorBridge

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanHarmonic EulerMeanCutoffCurl EulerComparatorRecovery
open scoped ContDiff Topology

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

/-- Actual ordinary smooth-L² velocity slices recovered from a common compact
vorticity support. The fields are definitionally the Comparator velocity. -/
def recoveredVelocity (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    Icc (0 : ℝ) T → SmoothL2Field Space := fun t =>
  smoothL2Field_of_curl_compact (v · (t : ℝ))
    (h.velocity_contDiff t t.property.1)
    (h.velocity_memLp t t.property.1)
    (fun x => h.div_free x t t.property.1)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t t.property))

@[simp] theorem recoveredVelocity_field (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (t : Icc (0 : ℝ) T) :
    (recoveredVelocity h T K hK hsupport t).field = (v · (t : ℝ)) := rfl

/-- All genuine spatial L² tensor norms are uniformly bounded on the common
compact-vorticity interval. No time regularity of these norms is assumed. -/
theorem recoveredVelocity_jetLp_uniform (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    ∀ n : ℕ, ∃ M : ℝ, ∀ t,
      ‖(recoveredVelocity h T K hK hsupport t).jetLp n‖ ≤ M := by
  intro n
  refine jetLp_norm_uniform_of_coordinate_energy
    (recoveredVelocity h T K hK hsupport) ?_ n
  intro j word
  obtain ⟨B, hB⟩ := h.component_word_energy_uniform_of_commonCompactCurl
    T K hK hsupport j word
  exact ⟨B, fun t => hB t t.property⟩

/-- A Comparator Euler solution with a common compact vorticity support is
represented by an actual ordinary evolution throughout that interval. -/
theorem exists_evolution_of_commonCompactCurl
    (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (T : ℝ) (hT : 0 < T) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    ∃ U : Evolution T hT.le,
      ∀ t : Icc (0 : ℝ) T, (U.velocity t).field = (v · (t : ℝ)) := by
  let A := recoveredVelocity h T K hK hsupport
  have hA (t : Icc (0 : ℝ) T) : (A t).field = (v · (t : ℝ)) := rfl
  have hscalar : IsSmoothScalarEuler (hT := hT.le) A := by
    apply isSmoothScalarEuler_of_weak_projectedEquation hT A
      (comparator_velocity_mem_solenoidal h A hA)
      (tensorNorm_uniform_of_jetLp_uniform A
        (recoveredVelocity_jetLp_uniform h T K hK hsupport))
      compactSolenoidalTests compactSolenoidalTests_dense
    · intro φ _
      exact comparator_weak_pairings_continuous h A hA φ
    · intro φ hφ t ht
      exact comparator_projected_pairing_hasDerivAt h hT A hA φ hφ t ht
  obtain ⟨U, hU⟩ := (exists_evolution_iff_scalar (hT := hT.le) hT A).mpr hscalar
  refine ⟨U, ?_⟩
  intro t
  rw [hU]
  exact hA t

/-- Compact initial vorticity alone supplies the complete local conversion:
the truncations, support propagation, spatial recovery, and time regularity
are all obtained from the actual Comparator solution assumptions. -/
theorem compactCurlLocalUpgrade (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (hc : HasCompactSupport (vectorCurl u₀)) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ U : Evolution δ hδ.le,
      ∀ t : Icc (0 : ℝ) δ, (U.velocity t).field = (v · (t : ℝ)) := by
  obtain ⟨δ, B, hδ, hsupport⟩ :=
    h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc
  obtain ⟨U, hU⟩ := exists_evolution_of_commonCompactCurl h δ hδ
    (Metric.closedBall (0 : Space) B) (isCompact_closedBall _ _) hsupport
  exact ⟨δ, hδ, U, hU⟩

/-- The local conversion restarted at any later time of compact vorticity,
through the time-shifted Comparator solution. -/
theorem local_evolution_at_compact_curl (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (a : ℝ) (ha : 0 ≤ a) (hc : HasCompactSupport (vectorCurl (v · a))) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ U : Evolution δ hδ.le,
      ∀ t : Icc (0 : ℝ) δ, (U.velocity t).field = (v · (a + (t : ℝ))) :=
  compactCurlLocalUpgrade (h.shiftTime a ha) hc

/-- Step 2 of the top of the Euler argument: a global Comparator solution from
the datum of a finite lifespan whose canonical vorticity stays compact is the
canonical maximal solution below the lifespan. -/
theorem comparator_agrees_with_canonical {A : SmoothL2Field Space} (L : FiniteLifespan A)
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (hcompact : ∀ t : L.Time, HasCompactSupport (vectorCurl (L.maximalVelocity t))) :
    ∀ t : L.Time, L.maximalVelocity t = (v · (t : ℝ)) := by
  intro t
  let S := L.intermediateHorizon t
  have hS : 0 < S := L.intermediateHorizon_pos t
  have hSL : S < L.duration := L.intermediateHorizon_lt t
  have hc : ∀ s, HasCompactSupport
      (vectorCurl ((L.evolution S hS hSL).velocity s).field) := by
    intro s
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcompact _
  have he := evolution_field_eq_of_local_evolution (L.evolution S hS hSL) h
    (L.evolution_initial S hS hSL) hc (local_evolution_at_compact_curl h) (L.intermediateTime t)
  rwa [← L.maximalVelocity_eq_evolution S hS hSL (L.intermediateTime t)] at he

end Euler.ComparatorBridge
