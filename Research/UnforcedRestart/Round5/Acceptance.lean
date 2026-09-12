import Research.UnforcedRestart.Round5.SelectedExterior

/-! PARTIAL ACCEPTANCE ONLY. There is intentionally no declaration claiming W,
N, or Z. The force in the first check is the literal closed selected record.
The other checks concern the actual model input and same-record sums, not curl
nonvanishing. No cancellation, nonzero-curl, or growth-preservation assumption
is introduced. -/
noncomputable section
namespace UnforcedRestart.Round5.Acceptance
open NavierStokes NavierStokes.ProblemStatement
open scoped Topology

/-- Literal selected force continuity; inherited, not a new discriminator. -/
theorem literal_selected_curl_continuous :
    Continuous (SpatialCurl.spatialCurl
      UnforcedRestart.Round3.WitnessFeasibility.selected.forcing) :=
  UnforcedRestart.Round3.CurlGeometry.selected_curl_continuous

/-- Exact closed transition interval and actual nominal normalization. -/
theorem literal_transition_primitive_positive :
    ∀ s : ℝ, 1 / 64 ≤ s → s ≤ 1 / 32 →
      0 < TailGaugePotential.heatPrimitive
        (BaseExterior.nominalHeatNormalization CorrectionInitialization.ActualPrimary.nominal)
        CorrectionInitialization.ActualPrimary.h (1, (s, 0)) := by
  intro s hlo hhi
  exact RadialPrimitive.transition_primitive_pos ⟨hlo, hhi⟩

/-- Actual selected direct sum, with the precise exterior restriction, not an
all-space assertion or an all-region terminal zero slab. -/
theorem literal_selected_direct_exterior_zero :
    ∀ w : SpaceTime,
      w ∈ ActualExteriorPrefix.exteriorDomain
        (ActualCandidateConstruction.residualBand
          ActualCandidateConstruction.selectedBudget ActualCandidateConstruction.selectedThreshold) →
      UnforcedRestart.Round3.WitnessFeasibility.directSum
        UnforcedRestart.Round3.WitnessFeasibility.selected.schedule w = 0 := by
  intro w hw
  exact SelectedExterior.selected_direct_eqOn hw

#print axioms literal_selected_curl_continuous
#print axioms literal_transition_primitive_positive
#print axioms literal_selected_direct_exterior_zero
end UnforcedRestart.Round5.Acceptance
