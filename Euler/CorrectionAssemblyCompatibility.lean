import Euler.CorrectionAssemblyData

/-! Compatibility of independently supplied actual finite-order corrections, proved from their equations. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionLowerData EulerAllOrderCorrectionData
  EulerCorrectionStabilityBudget EulerInviscidCorrectionCompatibility
  EulerInviscidCorrectionUniqueness EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- Adjacent supplied finite corrections coincide after restriction, by actual inviscid uniqueness. -/
theorem FiniteFamily.compatible (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (q : ℕ) (hq : 6 ≤ q) :
    (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (F.solution (q+1) (hq.trans (Nat.le_succ q))) = F.solution q hq := by
  have hs : StabilityBudget period hT.le
      (lowerData period (A.atOrder period (q+1)) (A.metric.jet q) (A.linear.jet q)
        (fun i => (A.quadratic i).jet q) (A.metric.continuous q) (A.linear.continuous q)
        (fun i => (A.quadratic i).continuous q)) := by
    rw [A.lower_atOrder period q]
    exact C.stabilityBudget period q
  apply inviscid_corrections_compatible period hq T hT.le (A.atOrder period (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    (F.solution (q+1) (hq.trans (Nat.le_succ q)))
    (F.equation (q+1) (hq.trans (Nat.le_succ q))) hs (F.solution q hq)
  · simpa only [A.lower_atOrder period q] using F.equation q hq
  · rw [F.initial, F.initial, map_zero]
  · intro t
    change value period (A.approximation.realization ((q+1)+1) t) ∈ _
    rw [A.approximation.value_eq]
    exact C.divergence t
  · exact F.divergence (q+1) (hq.trans (Nat.le_succ q))
  · exact F.divergence q hq

/-- Adjacent actual finite corrections have the same underlying L² field. -/
theorem FiniteFamily.value_succ (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.solution (q+1) (hq.trans (Nat.le_succ q)) t) =
      value period (F.solution q hq t) :=
  congrArg (fun f => value period (f t)) (F.compatible period C q hq)

/-- All supplied finite corrections have the same actual base L² field. -/
theorem FiniteFamily.value_base (F : FiniteFamily period hT A) (C : ComparisonData period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.solution q hq t) = value period (F.solution 6 le_rfl t) := by
  exact Nat.le_induction (P := fun n hn => value period (F.solution n hn t) =
      value period (F.solution 6 le_rfl t)) rfl
    (fun n hn ih => (F.value_succ period C n hn t).trans ih) q hq


end EulerCorrectionAssembly
