import Euler.PacketPointJets
import Euler.FiniteGradeDiagonal

/-! The graded expansion and tail estimate for the actual normalized momentum expression. -/

noncomputable section

namespace EulerPacketPointJets

open Finset EulerSmoothLimit EulerFiniteGrades EulerPacketResidual

def momentumGrade (N : ℕ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain) (n : ℕ) : Space :=
  coefficient N (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z) n




end EulerPacketPointJets
