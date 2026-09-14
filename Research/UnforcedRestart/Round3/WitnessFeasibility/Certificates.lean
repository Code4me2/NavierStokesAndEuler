import Research.UnforcedRestart.Round3.WitnessFeasibility.Main

/-! Source-connected selection invariance. No numerical evaluator is asserted. -/
noncomputable section
namespace UnforcedRestart.Round3.WitnessFeasibility
open NavierStokes NavierStokes.ProblemStatement Filter
open scoped Topology ContDiff

/-- Checked actual-candidate specialization; the equation is only asserted on (0,1). -/
theorem selected_force_eq_residual {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Space) :
    selected.forcing (t, x) =
      navierStokesResidual (velocity selected.schedule) (pressure selected.schedule) t x :=
  (selected.candidate.navier_stokes t ht x).symm

/-- Uniform over the actual witness record, not arbitrary choices of input fields. -/
theorem same_schedule_force_eq (d e : Data) (ha : d.schedule = e.schedule)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Space) :
    d.forcing (t, x) = e.forcing (t, x) := by
  rw [← d.candidate.navier_stokes t ht x, ← e.candidate.navier_stokes t ht x, ha]

/-- Conditional calculus tool: the incoming germ fixes all extension jets.
No vanishing at the endpoint or regularity of the original field there is assumed. -/
theorem extension_jet_unique {f : VelocityField} {x : Space}
    (e g : JointResidualLimits.OneSidedExtension f x) (n : ℕ) :
    iteratedFDeriv ℝ n e.value (1, x) = iteratedFDeriv ℝ n g.value (1, x) := by
  let _ := JointResidualLimits.past_filter_neBot x
  exact tendsto_nhds_unique (e.jet_tendsto n) (g.jet_tendsto n)

/-- Conditional calculus tool tied to the actual boundary-tensor constructor:
changing the away-extension certificates cannot change the returned tensors. -/
theorem boundaryLimits_choice_independent (f : VelocityField)
    (e g : JointResidualLimits.AwayExtensions f) (x : Space) (n : ℕ) :
    JointResidualLimits.boundaryLimits f e x n =
      JointResidualLimits.boundaryLimits f g x n := rfl

/-- Checked actual-candidate specialization, conditional on a supplied genuine
local residual extension at a nonzero representative. Its value need not be
the classically chosen extension used by the boundary-tensor definition. -/
theorem selected_terminal_jet_eq_extension (x : Space)
    (hx : MixedPeriodicAssembly.representative x ≠ 0)
    (e : JointResidualLimits.OneSidedExtension
      (MixedPeriodicAssembly.cutResidual (potentialSum selected.schedule)
        (directSum selected.schedule) (pressureSum selected.schedule))
      (MixedPeriodicAssembly.representative x)) (n : ℕ) :
    iteratedFDeriv ℝ n selected.forcing (1, x) =
      iteratedFDeriv ℝ n e.value (1, MixedPeriodicAssembly.representative x) := by
  classical
  rw [selected.jets]
  simp only [MixedPeriodicAssembly.boundaryLimits, JointResidualLimits.boundaryLimits,
    dite_eq_right hx]
  exact extension_jet_unique _ e n

#print axioms selected_force_eq_residual
#print axioms same_schedule_force_eq
#print axioms extension_jet_unique
#print axioms boundaryLimits_choice_independent
#print axioms selected_terminal_jet_eq_extension
end UnforcedRestart.Round3.WitnessFeasibility
