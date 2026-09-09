import Euler.SobolevTopBlocks
import Euler.TimeLp
import Euler.QuadraticCauchy

/-! Actual strong L²-time completion from finitely many closed derivative blocks.

Merged in from the former module `Euler.FiniteQuadraticCauchy`: `cauchy_of_finite_quadratic_bound`.

Merged in from the former module `Euler.TopBlockTimeNorm`: `pathLp_quadratic_bound`.
-/

/-! Strong time-space completion controlled by genuine finite spatial derivative blocks. -/

noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks EulerSobolevTopBlocks
open scoped Topology

/-- Integration preserves a finite quadratic norm comparison between bounded spatial observations. -/
theorem pathLp_quadratic_bound {X Y Z I : Type*} [Fintype I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖^2 ≤ ‖A x‖^2 + ∑ i, ‖B i x‖^2)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, X)) :
    ‖pathLp T hT u‖^2 ≤ ‖pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 +
      ∑ i, ‖pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 := by
  have hu := extendPath_continuous T hT u
  have hA : Continuous (fun t => ‖A (extendPath T hT u t)‖^2) := (A.continuous.comp hu).norm.pow 2
  have hB : ∀ i, Continuous (fun t => ‖B i (extendPath T hT u t)‖^2) :=
    fun i => ((B i).continuous.comp hu).norm.pow 2
  have hsum : Continuous (fun t => ∑ i, ‖B i (extendPath T hT u t)‖^2) := continuous_finsetSum _ (fun i _ => hB i)
  have h := intervalIntegral.integral_mono_on hT ((hu.norm.pow 2).intervalIntegrable (μ := volume) 0 T)
    ((hA.add hsum).intervalIntegrable (μ := volume) 0 T) (fun t _ => hb (extendPath T hT u t))
  change (∫ t in (0 : ℝ)..T, ‖extendPath T hT u t‖^2) ≤
    ∫ t in (0 : ℝ)..T, ‖A (extendPath T hT u t)‖^2 + ∑ i, ‖B i (extendPath T hT u t)‖^2 at h
  rw [intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 T)
    (hsum.intervalIntegrable (μ := volume) 0 T),
    intervalIntegral.integral_finsetSum (fun i _ => (hB i).intervalIntegrable (μ := volume) 0 T)] at h
  simp only [pathLp_norm_sq]
  exact h


end EulerTopBlockTimeNorm
end

/-! Strong Cauchy convergence controlled by finitely many genuine norm observations. -/

namespace EulerQuadraticCauchy

open scoped Topology

/-- A finite family of Cauchy observations controlling squared differences forces a sequence to be Cauchy. -/
theorem cauchy_of_finite_quadratic_bound {X Y Z I : Type*} [Fintype I]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : I → ℕ → Y) (V : ℕ → Z)
    (hu : CauchySeq U) (hf : ∀ i, CauchySeq (F i))
    (hb : ∀ n m, ‖V n-V m‖^2 ≤ ‖U n-U m‖^2 + ∑ i, ‖F i n-F i m‖^2) : CauchySeq V := by
  have hU : Filter.Tendsto (fun p : ℕ×ℕ => ‖U p.1-U p.2‖^2) Filter.atTop (𝓝 0) := by
    have h := (cauchySeq_iff_tendsto_dist_atTop_0.mp hu).pow 2
    simpa only [dist_eq_norm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hF : ∀ i, Filter.Tendsto (fun p : ℕ×ℕ => ‖F i p.1-F i p.2‖^2) Filter.atTop (𝓝 0) := by
    intro i
    have h := (cauchySeq_iff_tendsto_dist_atTop_0.mp (hf i)).pow 2
    simpa only [dist_eq_norm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hsum : Filter.Tendsto (fun p : ℕ×ℕ => ∑ i, ‖F i p.1-F i p.2‖^2) Filter.atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hF i)
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simp only [dist_eq_norm]
  apply squeeze_zero (fun p : ℕ×ℕ => norm_nonneg (V p.1-V p.2))
    (fun p : ℕ×ℕ => Real.le_sqrt_of_sq_le (hb p.1 p.2))
  simpa only [add_zero, Real.sqrt_zero] using (hU.add hsum).sqrt

end EulerQuadraticCauchy

noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {X Y Z I : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Bounded spatial observation and actual time embedding preserve subtraction together. -/
theorem mapped_pathLp_sub (T : ℝ) (hT : 0 ≤ T) (A : X →L[ℝ] Y)
    (u v : C(Icc (0 : ℝ) T, X)) :
    pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u-v)) =
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v) :=
  (congrArg (pathLp T hT) (map_sub (A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v)).trans
    (pathLp_sub T hT _ _)

/-- The integrated genuine spatial block bound also controls time-space differences. -/
theorem pathLp_quadratic_difference (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖^2 ≤ ‖A x‖^2 + ∑ i, ‖B i x‖^2)
    (T : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, X)) :
    ‖pathLp T hT u-pathLp T hT v‖^2 ≤
      ‖pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
        pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v)‖^2 +
      ∑ i, ‖pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
        pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) v)‖^2 := by
  have h := pathLp_quadratic_bound A B hb T hT (u-v)
  simp only [pathLp_sub, mapped_pathLp_sub] at h
  exact h

/-- Genuine finite block convergence and lower-order convergence construct strong convergence in the full Bochner Sobolev space. -/
theorem cauchy_pathLp_of_blocks (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖^2 ≤ ‖A x‖^2 + ∑ i, ‖B i x‖^2)
    (T : ℝ) (hT : 0 ≤ T) (u : ℕ → C(Icc (0 : ℝ) T, X))
    (hu : CauchySeq (fun n => pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))))
    (hf : ∀ i, CauchySeq (fun n => pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n)))) :
    CauchySeq (fun n => pathLp T hT (u n)) := by
  exact EulerQuadraticCauchy.cauchy_of_finite_quadratic_bound _ _ _ hu hf
    (fun n m => pathLp_quadratic_difference A B hb T hT (u n) (u m))

end EulerTopBlockTimeNorm
