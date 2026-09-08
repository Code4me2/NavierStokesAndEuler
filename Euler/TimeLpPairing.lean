import Euler.TimeLp

/-! Actual integral pairings and their strong limits for metric energy passage. -/

noncomputable section

namespace EulerTimeLpPairing

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution
open scoped Topology

/-- The actual scalar Bochner inner product is the integral of the literal product. -/
theorem inner_eq_integral (T : ℝ) (a b : TimeLp T ℝ) :
    ⟪a, b⟫_ℝ = ∫ t, a t*b t ∂timeMeasure T := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by simp [RCLike.inner_apply, mul_comm]

/-- Continuous-path Bochner pairings equal the ordinary interval integral. -/
theorem path_inner_eq_integral (T : ℝ) (hT : 0 ≤ T) (a b : C(Icc (0 : ℝ) T, ℝ)) :
    ⟪pathLp T hT a, pathLp T hT b⟫_ℝ =
      ∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT b t := by
  rw [inner_eq_integral]
  have he : (∫ t, pathLp T hT a t*pathLp T hT b t ∂timeMeasure T) =
      ∫ t in Icc 0 T, extendPath T hT a t * extendPath T hT b t := by
    apply integral_congr_ae
    filter_upwards [pathLp_ae T hT a, pathLp_ae T hT b] with t h1 h2
    rw [h1, h2]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]

/-- Signed integral coefficients pass continuously through uniform scalar energy convergence. -/
theorem integral_product_path_tendsto (T : ℝ) (hT : 0 ≤ T) (a : C(Icc (0 : ℝ) T, ℝ))
    (f : ℕ → C(Icc (0 : ℝ) T, ℝ)) (g : C(Icc (0 : ℝ) T, ℝ))
    (hf : Filter.Tendsto f Filter.atTop (𝓝 g)) :
    Filter.Tendsto (fun n => ∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT (f n) t)
      Filter.atTop (𝓝 (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT g t)) := by
  have h : Filter.Tendsto (fun n => ⟪pathLp T hT a, pathLp T hT (f n)⟫_ℝ) Filter.atTop
      (𝓝 ⟪pathLp T hT a, pathLp T hT g⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds (pathLp_tendsto T hT f g hf)
  simpa only [path_inner_eq_integral] using h

/-- Strong Bochner convergence passes signed scalar weighted integrals to their actual limit. -/
theorem integral_product_timeLp_tendsto (T : ℝ) (a : TimeLp T ℝ)
    (f : ℕ → TimeLp T ℝ) (g : TimeLp T ℝ)
    (hf : Filter.Tendsto f Filter.atTop (𝓝 g)) :
    Filter.Tendsto (fun n => ∫ t, a t*f n t ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ t, a t*g t ∂timeMeasure T)) := by
  have h : Filter.Tendsto (fun n => ⟪a, f n⟫_ℝ) Filter.atTop (𝓝 ⟪a, g⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds hf
  simpa only [inner_eq_integral] using h

/-- Three continuous weighted scalar paths have the literal additive interval integral. -/
theorem integral_three_paths (T : ℝ) (hT : 0 ≤ T)
    (a b c x y f : C(Icc (0 : ℝ) T, ℝ)) :
    (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT x t +
      extendPath T hT b t * extendPath T hT y t + extendPath T hT c t * extendPath T hT f t) =
      (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT x t) +
      (∫ t in (0 : ℝ)..T, extendPath T hT b t * extendPath T hT y t) +
      ∫ t in (0 : ℝ)..T, extendPath T hT c t * extendPath T hT f t := by
  have ha := ((extendPath_continuous T hT a).mul (extendPath_continuous T hT x)).intervalIntegrable (μ := volume) 0 T
  have hb := ((extendPath_continuous T hT b).mul (extendPath_continuous T hT y)).intervalIntegrable (μ := volume) 0 T
  have hc := ((extendPath_continuous T hT c).mul (extendPath_continuous T hT f)).intervalIntegrable (μ := volume) 0 T
  change IntervalIntegrable (fun t => extendPath T hT a t * extendPath T hT x t) volume 0 T at ha
  change IntervalIntegrable (fun t => extendPath T hT b t * extendPath T hT y t) volume 0 T at hb
  change IntervalIntegrable (fun t => extendPath T hT c t * extendPath T hT f t) volume 0 T at hc
  rw [intervalIntegral.integral_add (ha.add hb) hc, intervalIntegral.integral_add ha hb]


end EulerTimeLpPairing
