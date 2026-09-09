import Euler.PacketPointJets
import Euler.FiniteGradeDiagonal
import Euler.FiniteGradeAssembly

/-! The coefficient equations of the literal assembled packet give the force in (14).

Merged in from the former module `Euler.PacketLowGrades`: `coefficient_eq_diagonal`.
-/

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
end

noncomputable section

namespace EulerPacketResidual

open Finset EulerFiniteGrades

variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]

theorem assembled_fast_pressure (N p : ℕ) (hp : p ≤ N)
    (H : Q →ₗ[ℝ] W) (q π : ℕ → Q) (hq : ∀ i ≤ N, H (q i)=0) :
    H (assemble N q π (p+1)) = H (π p) := by
  by_cases h : p+1 ≤ N
  · rw [assemble_interior N (p+1) (by omega) h, Nat.add_sub_cancel, map_add,
      hq (p+1) h, zero_add]
  · have hpN : p=N := by omega
    rw [hpN, assemble_last]

/-- Both pressure contributions and the final corrector are retained in this identity. -/
theorem coefficient_assembled (N p : ℕ) (hp : 1 ≤ p) (hpN : p ≤ N)
    (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W) (B C : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (a b c : ℕ → V) (q π : ℕ → Q) (hq : ∀ i ≤ N, H (q i)=0) :
    coefficient (N+1) L G H B C (assemble N (fun i => a i+b i) c) (assemble N q π) p =
      (L (a p)+H (π p)) + (L (b p)+G (q p)) + (L (c (p-1))+G (π (p-1))) +
      convolution (N+1) B (assemble N (fun i => a i+b i) c)
        (assemble N (fun i => a i+b i) c) p +
      convolution (N+1) C (assemble N (fun i => a i+b i) c)
        (assemble N (fun i => a i+b i) c) (p+1) := by
  unfold coefficient shiftDown
  rw [truncate_of_le (N+1) p _ (by omega), truncate_of_le (N+1) p _ (by omega),
    truncate_of_le (N+1) (p+1) _ (by omega),
    truncate_of_le (2*(N+1)) (p+1) _ (by omega),
    assemble_interior N p hp hpN, assemble_interior N p hp hpN,
    assembled_fast_pressure N p hpN H q π hq]
  simp only [map_add]
  abel


theorem coefficient_zero_grade (N : ℕ) (L : V →ₗ[ℝ] W) (G H : Q →ₗ[ℝ] W)
    (B C : V →ₗ[ℝ] V →ₗ[ℝ] W) (u : ℕ → V) (q : ℕ → Q)
    (hu0 : u 0=0) (hq0 : G (q 0)=0) (hq1 : H (q 1)=0) :
    coefficient (N+1) L G H B C u q 0=0 := by
  rw [coefficient_eq_diagonal (N+1) 0 (by omega)]
  simp [hu0, hq0, hq1, sum_range_succ]

end EulerPacketResidual
