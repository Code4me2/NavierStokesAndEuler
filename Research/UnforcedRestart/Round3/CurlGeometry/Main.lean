import Research.UnforcedRestart.Round3.WitnessFeasibility.Main

/-! Actual selected-force curl, read from the full terminal jet, not pointwise velocity data. -/
noncomputable section
namespace UnforcedRestart.Round3.CurlGeometry
open NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff Topology
open UnforcedRestart.Round3.WitnessFeasibility

/-- Spatial entries of the selected boundary tensor, including the localization annulus. -/
def terminalEntry (x : Space) (i j : Fin 3) : ℝ :=
  (MixedPeriodicAssembly.boundaryLimits (potentialSum selected.schedule)
    (directSum selected.schedule) (pressureSum selected.schedule)
    selected.ea selected.eb selected.ep x 1
      (fun _ => (0, coordinateVector i))) j

/-- Chain rule for a spatial slice; a joint differentiability hypothesis is essential. -/
theorem spatial_slice_derivative {f : VelocityField} {t : ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f (t, x)) (v : Space) :
    fderiv ℝ (fun y => f (t, y)) x v = fderiv ℝ f (t, x) (0, v) := by
  have hp := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  have hh := (hf.hasFDerivAt.comp x hp).fderiv
  exact congrArg (fun L => L v) hh

/-- Checked actual-candidate specialization of the first full terminal jet. -/
theorem terminalEntry_eq (x : Space) (i j : Fin 3) :
    (spatialDerivative selected.forcing 1 x (coordinateVector i)) j =
      terminalEntry x i j := by
  unfold spatialDerivative
  rw [spatial_slice_derivative (selected.smooth.differentiable (by simp) (1, x))]
  have he := congrArg (fun J => (J (fun _ => (0, coordinateVector i))) j)
    (selected.jets 1 x)
  simpa only [iteratedFDeriv_one_apply, terminalEntry] using he

/-- The repository curl convention, with cyclic indices in Fin 3. -/
theorem terminal_curl_component (x : Space) (i : Fin 3) :
    SpatialCurl.spatialCurl selected.forcing (1, x) i =
      terminalEntry x (i + 1) (i + 2) - terminalEntry x (i + 2) (i + 1) := by
  fin_cases i <;>
    simp [SpatialCurl.spatialCurl, SpatialCurl.curl,
      ← terminalEntry_eq, spatialDerivative]

/-- Origin flatness really implies spatial curl flatness, but only at this point. -/
theorem terminal_curl_origin : SpatialCurl.spatialCurl selected.forcing (1, 0) = 0 := by
  ext i
  rw [terminal_curl_component]
  simp [terminalEntry, MixedPeriodicAssembly.boundaryLimits_zero]

/-- A certificate needs unequal actual tensor entries, not a nonzero velocity sample. -/
theorem terminal_curl_ne_zero (x : Space) (i : Fin 3)
    (h : terminalEntry x (i + 1) (i + 2) ≠ terminalEntry x (i + 2) (i + 1)) :
    SpatialCurl.spatialCurl selected.forcing (1, x) ≠ 0 := by
  intro he
  have hc := congrArg (fun v : Space => v i) he
  rw [terminal_curl_component] at hc
  exact h (sub_eq_zero.mp hc)

/-- Continuity concerns the smooth force, never a terminal velocity extension. -/
theorem selected_curl_continuous : Continuous (SpatialCurl.spatialCurl selected.forcing) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (SpatialCurl.contDiffAt_spatialCurl selected.smooth.contDiffAt
    (m := 0) (by simp)).continuousAt

/-- Actual finite-time residual curl on one separated copy. The strict time bounds
keep all derivatives inside the presingular domain and inside the activation plateau. -/
theorem late_inner_curl {t : ℝ} (ht : 3 / 4 < t) (ht1 : t < 1) (x : Space)
    (hx : x ∈ PeriodicLocalization.innerCube (1 / 4)) :
    SpatialCurl.spatialCurl selected.forcing (t, x) =
      SpatialCurl.spatialCurl
        (MixedPeriodicAssembly.cutResidual (potentialSum selected.schedule)
          (directSum selected.schedule) (pressureSum selected.schedule)) (t, x) := by
  have hu := (TimeLocalization.activatedVelocity_eventuallyEq_late
    (MixedPeriodicAssembly.periodicVelocity (potentialSum selected.schedule)
      (directSum selected.schedule)) ht x).trans
        (MixedPeriodicAssembly.periodicVelocity_eventuallyEq_cut _ _ hx)
  have hp := (TimeLocalization.activatedPressure_eventuallyEq_late
    (SpatialLocalization.periodicPressure (pressureSum selected.schedule)) ht x).trans
        (SpatialLocalization.periodicPressure_eventuallyEq_cut _ hx)
  have hr := ResidualRegularity.residual_eventuallyEq hu hp
  have hs := hr.comp_tendsto
    (continuous_const.prodMk continuous_id : Continuous (fun y : Space => (t, y))).continuousAt
  have hf : (fun y => selected.forcing (t, y)) =
      (fun y => navierStokesResidual (velocity selected.schedule)
        (pressure selected.schedule) t y) := by
    funext y
    exact (selected.candidate.navier_stokes t ⟨by linarith, ht1⟩ y).symm
  change SpatialCurl.curl (fun y => selected.forcing (t, y)) x = _
  rw [hf]
  exact SpatialCurl.curl_eq_of_eventuallyEq hs

#print axioms late_inner_curl
#print axioms terminalEntry
#print axioms spatial_slice_derivative
#print axioms terminalEntry_eq
#print axioms terminal_curl_component
#print axioms terminal_curl_origin
#print axioms terminal_curl_ne_zero
#print axioms selected_curl_continuous
end UnforcedRestart.Round3.CurlGeometry
