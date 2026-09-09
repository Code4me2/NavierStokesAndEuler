import NavierStokes.MixedCandidateAssembly
import NavierStokes.CandidateConsequences

/-!
# The selected schedule of the finite-stage hub

`SelectedSchedule` records every property of the scale sequence that
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` selects
from the finite-stage estimates; `ActualCandidateAssembly.Witness` names it
for the delivered fields.
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
end NavierStokes.MixedCandidateWitness
