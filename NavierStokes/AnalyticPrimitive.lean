import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# An actual holomorphic primitive on a convex open set

The primitive is the radial segment integral. Its derivative is proved by
differentiating under a uniformly dominated integral on a compact local product,
then applying the real fundamental theorem of calculus along the segment.
No disk containing the entire domain and no assumed primitive are required.
-/

noncomputable section

namespace NavierStokes.AnalyticPrimitive

open Set Filter MeasureTheory Metric
open scoped Topology Interval ContDiff

/-- Integration along the straight segment from zero to `z`. -/
def primitive (g : ℂ → ℂ) (z : ℂ) : ℂ := z * ∫ t in (0 : ℝ)..1, g ((t : ℂ) * z)

@[simp] theorem primitive_zero (g : ℂ → ℂ) : primitive g 0 = 0 := by
  simp [primitive]

theorem primitive_eq_integral (g : ℂ → ℂ) (z : ℂ) :
    primitive g z = ∫ t in (0 : ℝ)..1, z * g ((t : ℂ) * z) := by
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem segment_mem {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * z ∈ U := by
  simpa only [Complex.real_smul] using hU.smul_mem_of_zero_mem h0 hz ht

theorem continuousOn_segment {U : Set ℂ} (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U)
    {g : ℂ → ℂ} (hg : ContinuousOn g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => g ((t : ℂ) * z)) (Icc (0 : ℝ) 1) := by
  exact hg.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
    (fun _ ht => segment_mem hU h0 hz ht)

/-- The complex derivative of the parameter-dependent integrand. -/
def integrandDerivative (g : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  g ((t : ℂ) * z) + ((t : ℂ) * z) * deriv g ((t : ℂ) * z)

theorem integrand_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun w : ℂ => w * g ((t : ℂ) * w)) (integrandDerivative g z t) z := by
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! (hasDerivAt_id z).mul (hgd.hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (t : ℂ))) using 1
  simp only [integrandDerivative, Function.comp_apply, id_eq, mul_one, one_mul]
  ring

theorem integrandDerivative_continuousOn_segment {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (integrandDerivative g z) (Icc (0 : ℝ) 1) := by
  exact (continuousOn_segment hU h0 hg.continuousOn hz).add
    ((Complex.continuous_ofReal.mul continuous_const).continuousOn.mul
      (continuousOn_segment hU h0 (hg.deriv ho).continuousOn hz))

/-- The same derivative integrand is the real derivative of `t*g(t*z)`. -/
theorem segment_product_hasDerivAt {U : Set ℂ} (ho : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} {t : ℝ} (htz : (t : ℂ) * z ∈ U) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
      (integrandDerivative g z t) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    exact Complex.ofRealCLM.hasDerivAt (x := t)
  have hgd := (hg _ htz).differentiableAt (ho.mem_nhds htz)
  convert! ht.mul (hgd.hasDerivAt.comp t (ht.mul_const z)) using 1
  simp only [integrandDerivative, Function.comp_apply, one_mul]
  ring

theorem integral_integrandDerivative {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    (∫ t in (0 : ℝ)..1, integrandDerivative g z t) = g z := by
  have hint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (s : ℂ) * g ((s : ℂ) * z))
    (f' := integrandDerivative g z) (a := 0) (b := 1)
    (fun t ht => segment_product_hasDerivAt ho hg
      (segment_mem hU h0 hz (by simpa only [uIcc_of_le zero_le_one] using ht))) hint
  simpa using he

/-- An actual holomorphic primitive on any convex open neighborhood of zero. -/
theorem hasDerivAt_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (primitive g) (g z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hz)
  let K : Set (ℂ × ℝ) := closedBall z r ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall z r).prod isCompact_Icc
  have hm : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst
  have hmU : MapsTo (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) K U := by
    intro p hp
    exact segment_mem hU h0 (hrU hp.1) hp.2
  have hcont : ContinuousOn (fun p : ℂ × ℝ => integrandDerivative g p.1 p.2) K := by
    exact (hg.continuousOn.comp hm.continuousOn hmU).add
      (hm.continuousOn.mul ((hg.deriv ho).continuousOn.comp hm.continuousOn hmU))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hFint : ∀ w ∈ U, IntervalIntegrable (fun t : ℝ => w * g ((t : ℂ) * w))
      volume 0 1 := by
    intro w hw
    exact (continuousOn_const.mul
      (continuousOn_segment hU h0 hg.continuousOn hw)).intervalIntegrable_of_Icc (by norm_num)
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => w * g ((t : ℂ) * w)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    simpa only [uIoc_of_le zero_le_one] using
      (hFint w (hrU (ball_subset_closedBall hw))).aestronglyMeasurable
  have hDint : IntervalIntegrable (integrandDerivative g z) volume 0 1 :=
    (integrandDerivative_continuousOn_segment ho hU h0 hg hz).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hDmeas : AEStronglyMeasurable (integrandDerivative g z)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le zero_le_one] using hDint.aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      ‖integrandDerivative g w t‖ ≤ C := by
    filter_upwards [] with t
    intro ht w hw
    apply hC (w, t)
    exact ⟨ball_subset_closedBall hw,
      by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball z r,
      HasDerivAt (fun v : ℂ => v * g ((t : ℂ) * v)) (integrandDerivative g w t) w := by
    filter_upwards [] with t
    intro ht w hw
    exact integrand_hasDerivAt ho hg (segment_mem hU h0
      (hrU (ball_subset_closedBall hw))
      (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht))
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t => w * g ((t : ℂ) * w)) (F' := integrandDerivative g)
    (bound := fun _ => C) (Metric.ball_mem_nhds _ hr) hFmeas (hFint z hz) hDmeas hbound
    intervalIntegrable_const hdiff).2
  rw [integral_integrandDerivative ho hU h0 hg hz] at hd
  simpa only [← primitive_eq_integral] using hd

theorem differentiableOn_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (primitive g) U := by
  intro z hz
  exact (hasDerivAt_primitive ho hU h0 hg hz).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_primitive {U : Set ℂ} (ho : IsOpen U)
    (hU : Convex ℝ U) (h0 : (0 : ℂ) ∈ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : AnalyticOnNhd ℂ (primitive g) U :=
  (differentiableOn_primitive ho hU h0 hg).analyticOnNhd ho


/-- If the integrand extends a real function, its segment primitive extends
the corresponding real segment integral exactly. -/
theorem primitive_ofReal (g : ℂ → ℂ) (f : ℝ → ℝ)
    (hreal : ∀ x : ℝ, g x = (f x : ℂ)) (x : ℝ) :
    primitive g x = ((x * ∫ t in (0 : ℝ)..1, f (t * x) : ℝ) : ℂ) := by
  have heq : (fun t : ℝ => g ((t : ℂ) * (x : ℂ))) =
      fun t : ℝ => (f (t * x) : ℂ) := by
    funext t
    rw [← Complex.ofReal_mul, hreal]
  rw [primitive, heq, intervalIntegral.integral_ofReal, Complex.ofReal_mul]


/-- The normalized exponential built from the actual segment primitive. -/
def amplitude (g : ℂ → ℂ) (Λ C : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (Λ * primitive g z) / C

@[simp] theorem amplitude_zero (g : ℂ → ℂ) (Λ C : ℂ) : amplitude g Λ C 0 = 1 / C := by
  simp [amplitude]

theorem amplitude_ne_zero (g : ℂ → ℂ) (Λ : ℂ) {C : ℂ} (hC : C ≠ 0) (z : ℂ) :
    amplitude g Λ C z ≠ 0 :=
  div_ne_zero (Complex.exp_ne_zero _) hC








end NavierStokes.AnalyticPrimitive

end
