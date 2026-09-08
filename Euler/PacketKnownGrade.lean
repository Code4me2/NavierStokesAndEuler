import Euler.PacketTriangular
import Euler.PeriodicDerivativeMean

/-! The known forcing at a recursive grade uses only previously constructed coefficients. -/

noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerFiniteGrades InnerProductSpace

def history (p : ℕ) (u : ℕ → VectorJet) (previousCorrector : VectorJet) (i : ℕ) : VectorJet :=
  if i<p then u i else if i=p then previousCorrector else 0

/-- No unspecified coefficient at or above p enters the known part. -/
theorem history_congr (p : ℕ) (u v : ℕ → VectorJet) (c : VectorJet)
    (huv : ∀ i<p, u i=v i) : history p u c=history p v c := by
  funext i
  by_cases hi : i<p
  · simp only [history, hi, ite_true, huv i hi]
  · simp only [history, hi, ite_false]



end EulerPacketPointJets
