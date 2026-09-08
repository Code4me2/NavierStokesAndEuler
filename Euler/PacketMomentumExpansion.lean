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


/-- The source's finite packet has no residual grades through N once its coefficient equations hold. -/
theorem momentum_fieldSum_tail (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0)
    (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → Domain → Space) (p : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N+1, DifferentiableAt ℝ (u i) z)
    (hp : ∀ i ≤ N+1, DifferentiableAt ℝ (p i) z)
    (hu0 : jet (u 0) z=0) (hp0 : fastPressure m (jet (p 0) z)=0)
    (hcancel : ∀ n ≤ N, momentumGrade (N+1) FInv M m u p z n=0) :
    momentumResidual κ FInv M m (fieldSum (N+1) κ u) (fieldSum (N+1) κ p) z =
      ∑ n ∈ Ico (N+1) (2*N+3), κ^n • momentumGrade (N+1) FInv M m u p z n := by
  unfold momentumResidual
  rw [jet_fieldSum (N+1) κ u z hu, jet_fieldSum (N+1) κ p z hp]
  exact packet_residual_eq_tail N κ hκ (linearPart M) (slowPressure FInv) (fastPressure m)
    (slowAdvection FInv) (fastAdvection m) (fun i => jet (u i) z) (fun i => jet (p i) z)
    hu0 hp0 hcancel


end EulerPacketPointJets
