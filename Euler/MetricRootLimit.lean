import Euler.CylinderViscousEnergy

/-! Removal of square-root regularization in actual finite metric-energy integral inequalities. -/

noncomputable section

namespace EulerMetricRootLimit

open MeasureTheory Set Real InnerProductSpace EulerNoncompactTransport EulerFiniteMetricEnergy
open scoped Topology

/-- A regularized square root differs from the nonnegative root by at most the regularization. -/
theorem regularized_root_le (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) :
    √(q + δ ^ 2) ≤ √q + δ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (sqrt_nonneg q) hδ, ?_⟩
  have hsq := sq_sqrt hq
  have hp := mul_nonneg (sqrt_nonneg q) hδ
  nlinarith

/-- The canonical positive regularization sequence converges at every quadratic energy value. -/
theorem regularized_root_tendsto (q : ℝ) :
    Filter.Tendsto (fun n => √(q + cutoffScale n ^ 2)) Filter.atTop (𝓝 (√q)) := by
  have hq : Filter.Tendsto (fun n => q + cutoffScale n ^ 2) Filter.atTop (𝓝 q) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      (tendsto_const_nhds.add (cutoffScale_tendsto.pow 2))
  exact (continuous_sqrt.tendsto q).comp hq

/-- At fixed finite cutoff, an integrable energy inequality survives removal of the root regularization. -/
theorem root_integral_limit (Q A F : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hQ : ContinuousOn Q (Icc s t)) (hQ0 : ∀ u ∈ Icc s t, 0 ≤ Q u)
    (hA : IntegrableOn A (Icc s t)) (hF : IntegrableOn F (Icc s t))
    (hineq : ∀ δ : ℝ, 0 < δ → √(Q t + δ ^ 2) - √(Q s + δ ^ 2) ≤
      ∫ u in s..t, (A u * √(Q u + δ ^ 2) + F u)) :
    √(Q t) - √(Q s) ≤ ∫ u in s..t, (A u * √(Q u) + F u) := by
  let μ : Measure ℝ := volume.restrict (Ioc s t)
  let fn := fun n u => A u * √(Q u + cutoffScale n ^ 2) + F u
  have hAQ : IntegrableOn (fun u => A u * √(Q u)) (Icc s t) :=
    hA.mul_continuousOn hQ.sqrt isCompact_Icc
  have hAn : Integrable A μ := hA.mono_set Ioc_subset_Icc_self
  have hFn : Integrable F μ := hF.mono_set Ioc_subset_Icc_self
  have hAQn : Integrable (fun u => A u * √(Q u)) μ := hAQ.mono_set Ioc_subset_Icc_self
  have hmeas (n : ℕ) : AEStronglyMeasurable (fn n) μ :=
    (((hA.mul_continuousOn ((hQ.add continuousOn_const).sqrt) isCompact_Icc).add hF).mono_set Ioc_subset_Icc_self).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ u ∂μ,
      ‖fn n u‖ ≤ ‖A u * √(Q u)‖ + ‖A u‖ + ‖F u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hq := hQ0 u ⟨hu.1.le, hu.2⟩
    have hr := (regularized_root_le (Q u) (cutoffScale n) hq (cutoffScale_pos n).le).trans
      (add_le_add_right (cutoffScale_le_one n) (√(Q u)))
    calc
      _ ≤ ‖A u‖ * √(Q u + cutoffScale n ^ 2) + ‖F u‖ := by
        simpa only [fn, norm_mul, Real.norm_of_nonneg (sqrt_nonneg _)] using
          norm_add_le (A u * √(Q u + cutoffScale n ^ 2)) (F u)
      _ ≤ ‖A u‖ * (√(Q u) + 1) + ‖F u‖ :=
        add_le_add_left (mul_le_mul_of_nonneg_left hr (norm_nonneg (A u))) ‖F u‖
      _ = _ := by
        rw [norm_mul, Real.norm_of_nonneg (sqrt_nonneg _)]
        ring
  have hlim : ∀ᵐ u ∂μ, Filter.Tendsto (fun n => fn n u) Filter.atTop (𝓝 (A u * √(Q u) + F u)) :=
    Filter.Eventually.of_forall (fun u =>
      ((regularized_root_tendsto (Q u)).const_mul (A u)).add_const (F u))
  have hi := tendsto_integral_of_dominated_convergence
    (fun u => ‖A u * √(Q u)‖ + ‖A u‖ + ‖F u‖) hmeas
    ((hAQn.norm.add hAn.norm).add hFn.norm) hbound hlim
  have hii : Filter.Tendsto (fun n => ∫ u in s..t, fn n u) Filter.atTop
      (𝓝 (∫ u in s..t, (A u * √(Q u) + F u))) := by
    simpa only [intervalIntegral.integral_of_le hst] using hi
  exact le_of_tendsto_of_tendsto' ((regularized_root_tendsto (Q t)).sub
    (regularized_root_tendsto (Q s))) hii (fun n => hineq (cutoffScale n) (cutoffScale_pos n))


end EulerMetricRootLimit
