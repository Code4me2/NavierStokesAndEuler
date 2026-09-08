import Euler.PacketMomentumExpansion

/-! The low coefficients of the actual packet residual, before solving their equations. -/

noncomputable section

namespace EulerPacketResidual

open Finset EulerFiniteGrades

variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]

theorem coefficient_eq_diagonal (M n : ℕ) (hn : n+1 ≤ M)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (u : ℕ → V) (p : ℕ → Q) :
    coefficient M L G H B C u p n =
      L (u n) + G (p n) + H (p (n+1)) +
      (∑ i ∈ range (n+1), B (u i) (u (n-i))) +
      (∑ i ∈ range (n+2), C (u i) (u (n+1-i))) := by
  unfold coefficient shiftDown
  rw [truncate_of_le M n _ (by omega), truncate_of_le M n _ (by omega),
    truncate_of_le M (n+1) _ hn, truncate_of_le (2*M) (n+1) _ (by omega),
    convolution_eq_range M n (by omega), convolution_eq_range M (n+1) hn]

end EulerPacketResidual

namespace EulerPacketPointJets

open Finset EulerSmoothLimit EulerPacketResidual


end EulerPacketPointJets
