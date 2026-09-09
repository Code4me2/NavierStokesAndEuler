import NavierStokes.MixedCandidateAssembly
import NavierStokes.CandidateConsequences

/-!
# Retaining the actual mixed candidate and its consequences

The finite-stage inputs are exactly those of
`MixedCandidateAssembly.candidate_of_finite_stages`. The same selected
schedule supplies the actual velocity and pressure sums, their endpoint
extensions, and the force with all proved consequences.
-/

noncomputable section

namespace NavierStokes.MixedCandidateWitness

open Set Filter ProblemStatement MixedCandidateAssembly
open JointResidualLimits (OneSidedExtension)
open scoped Topology ContDiff

universe u

/-- All properties of the single scale sequence selected from the finite
stage estimates, including smooth sums and vanishing residual jets. -/
noncomputable def SelectedSchedule (h qbig : ℝ) (A B : ℕ → VelocityField)
    (P : ℕ → PressureField) (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧ (∀ j, 0 < a j) ∧ (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
    Tendsto (fun j => (a j : ℝ)) atTop atTop ∧ (∀ j, 1 / (a j : ℝ) < qbig) ∧
    MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
    JointResidualLimits.VanishingJointJets
      (MixedDiagonalResidual.residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P)

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)


end ActualBase

end NavierStokes.MixedCandidateWitness
