import Euler.PacketPointJets
import Euler.FiniteGradeAssembly

/-! The literal packet sums and their genuine first derivatives match the graded assembly. -/

noncomputable section

namespace EulerPacketPointJets

open EulerFiniteGrades Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jet_zero (z : Domain) : jet (fun _ : Domain => (0 : E)) z = 0 := by
  simp [jet]

theorem jet_add (f g : Domain → E) (z : Domain)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    jet (f+g) z = jet f z+jet g z := by
  simp only [jet, Pi.add_apply, fderiv_add hf hg, Prod.mk_add_mk]







/-- The extra degree N+1 is precisely the final divergence corrector in (13). -/
theorem fieldSum_assemble_from_one (N : ℕ) (κ : ℝ) (u c : ℕ → Domain → E)
    (hu : u 0=0) (hc : c 0=0) (z : Domain) :
    fieldSum (N+1) κ (assemble N u c) z =
      ∑ i ∈ range N, (κ^(i+1) • u (i+1) z+κ^(i+2) • c (i+1) z) := by
  have h := congrArg (fun f : Domain → E => f z)
    (evaluate_assemble_from_one N κ u c hu hc)
  simpa only [fieldSum, evaluate, Finset.sum_apply, Pi.smul_apply, Pi.add_apply] using h

end EulerPacketPointJets
