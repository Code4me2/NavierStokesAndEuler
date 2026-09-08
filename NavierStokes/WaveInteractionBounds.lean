import NavierStokes.WeightedClasses
import NavierStokes.LinearWaveResidual
import NavierStokes.PartitionedCovariance
import NavierStokes.CurlClassBounds

/-!
# All-jet bounds for actual nonlinear wave interactions

Only stripped coefficients are placed in the weighted classes. The carrier is
retained in the exact differential identities and is removed before estimating.
-/

namespace NavierStokes.WaveInteractionBounds

noncomputable section

open Set Filter WeightedClasses HarmonicCalculus
open scoped ContDiff Topology BigOperators

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem class_congr {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f g : ℕ → D → E} (hf : MemClass s w α f)
    (hfg : ∀ n, EqOn (f n) (g n) s.domain) : MemClass s w α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => (hfg n hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he : f n =ᶠ[𝓝[univ] x] g n := by
    rw [nhdsWithin_univ]
    exact eventually_of_mem (s.isOpen_domain.mem_nhds hx) (hfg n)
  have hjet := he.iteratedFDerivWithin_eq (𝕜 := ℝ) (hfg n hx) j
  simp only [iteratedFDerivWithin_univ] at hjet
  rw [← hjet]
  exact hb n x hx j hj

theorem class_neg {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → E} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => -f n x) := by
  simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply] using
    hf.map (-(ContinuousLinearMap.id ℝ E))

theorem class_sub {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f g : ℕ → D → E} (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => f n x - g n x) := by
  simpa only [sub_eq_add_neg] using hf.add (class_neg hg)

theorem class_cmul {s : StripData D} {w v : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : MemClass s w α f) (hg : MemClass s v β g) :
    MemClass s (fun n x => w n x * v n x) (α + β) (fun n x => f n x * g n x) :=
  hf.bilinear hg (ContinuousLinearMap.mul ℝ ℂ)

theorem class_conj {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => star (f n x)) :=
  hf.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem class_const_cmul {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) (c : ℂ) :
    MemClass s w α (fun n x => c * f n x) :=
  hf.map (ContinuousLinearMap.mul ℝ ℂ c)

theorem unweighted_cmul {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : UnweightedClass s α f) (hg : MemClass s w β g) :
    MemClass s w (α + β) (fun n x => f n x * g n x) := by
  simpa only [one_mul] using class_cmul hf hg

theorem mean_wave_cmul {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : MeanClass s α f) (hg : WaveClass s P β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    WaveClass s P (α + β) (fun n x => f n x * g n x) :=
  hf.bilinear_wave hg hζ (ContinuousLinearMap.mul ℝ ℂ)




/-- Evaluation of the actual derivative field at an actual vector field. -/
theorem class_along {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f : ℕ → D → E} {V : ℕ → D → D}
    (hf : MemClass s w α f) (hV : UnweightedClass s β V) :
    MemClass s w (α + β) (fun n => along (V n) (f n)) := by
  have h := hV.bilinear hf.fderiv (ContinuousLinearMap.apply ℝ E)
  simp only [one_mul, add_comm β α, ContinuousLinearMap.apply_apply] at h
  exact h


/-- Actual geometric coefficient fields, rather than assumed derivative closure. -/
structure Geometry (s : StripData D) (κ : ℝ) where
  radius : ℕ → D → ℝ
  radial : ℕ → D → D
  angular : ℕ → D → D
  axial : ℕ → D → D
  radius_pos : ∀ n x, x ∈ s.domain → 0 < radius n x
  radial_class : UnweightedClass s (-κ) radial
  axial_class : UnweightedClass s 1 axial
  inverse_radius_class : UnweightedClass s 0 (fun n x => (radius n x)⁻¹)

theorem graph_vector_class {s : StripData D} {κ : ℝ} {M : ℕ → ℝ} {a : D → ℝ}
    (hκ : 0 ≤ κ) (hM : BandBound s (-κ) M)
    (ha : UnweightedClass s 0 (fun _ => a)) (e v : D) :
    UnweightedClass s (-κ) (fun n x => e + M n • (a x • v)) := by
  have he := (unweighted_const s e).mono_exponent (neg_nonpos.mpr hκ)
  have hav : UnweightedClass s 0 (fun _ x => a x • v) := by
    unfold UnweightedClass
    simpa only [one_mul, zero_add] using MemClass.smul ha (unweighted_const s v)
  have hmv : UnweightedClass s (-κ) (fun n x => M n • (a x • v)) := by
    unfold UnweightedClass
    simpa only [zero_add] using hav.band_smul hM
  exact he.add hmv

theorem axial_vector_class (s : StripData D) (v : D) :
    UnweightedClass s 1 (fun n _ => s.epsilon n • v) := by
  unfold UnweightedClass
  simpa only [zero_add, Real.rpow_one] using (unweighted_const s v).band_smul (bandBound_rpow s 1)

abbrev Family (D : Type*) := ℕ → D → ComplexVector

def WaveVector (s : StripData D) (P : ℕ → D → ℝ) (α : ℝ) (a : Family D) : Prop :=
  ∀ i, WaveClass s P α (fun n x => a n x i)

def MeanVector (s : StripData D) (μ : ℝ) (a : Family D) : Prop :=
  MeanClass s (μ + 1) (fun n x => a n x 0) ∧
    MeanClass s μ (fun n x => a n x 1) ∧ MeanClass s μ (fun n x => a n x 2)

theorem meanVector_component {s : StripData D} {μ : ℝ} {a : Family D}
    (ha : MeanVector s μ a) (i : Fin 3) : MeanClass s μ (fun n x => a n x i) := by
  fin_cases i
  · exact ha.1.mono_exponent (by linarith)
  · exact ha.2.1
  · exact ha.2.2

def AngularIndependent {s : StripData D} {κ : ℝ} (G : Geometry s κ) (a : Family D) : Prop :=
  ∀ n i x, x ∈ s.domain → along (G.angular n) (fun y => a n y i) x = 0

noncomputable def strippedTransport {s : StripData D} {κ : ℝ}
    (G : Geometry s κ) (a b : Family D) : Family D := fun n x i =>
  a n x 0 * along (G.radial n) (fun y => b n y i) x +
    (a n x 1 / (G.radius n x : ℂ)) * angularGenerator (b n x) i +
    a n x 2 * along (G.axial n) (fun y => b n y i) x


theorem generator_class {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {a : Family D}
    (ha : ∀ i, MemClass s w α (fun n x => a n x i)) (i : Fin 3) :
    MemClass s w α (fun n x => angularGenerator (a n x) i) := by
  fin_cases i
  · exact class_neg (ha 1)
  · exact ha 0
  · exact MemClass.zero (ha 0).weight_nonneg

theorem inverse_radius_complex {s : StripData D} {κ : ℝ} (G : Geometry s κ) :
    UnweightedClass s 0 (fun n x => ((G.radius n x : ℂ))⁻¹) := by
  unfold UnweightedClass
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_inv] using
    G.inverse_radius_class.map Complex.ofRealCLM

theorem class_div_radius {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
    (G : Geometry s κ) {f : ℕ → D → ℂ} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => f n x / (G.radius n x : ℂ)) := by
  simpa only [zero_add, div_eq_mul_inv, mul_comm] using
    unweighted_cmul (inverse_radius_complex G) hf

theorem strippedTransport_class {s : StripData D} {w v : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {a b : Family D}
    (ha : ∀ i, MemClass s w α (fun n x => a n x i))
    (hb : ∀ i, MemClass s v β (fun n x => b n x i)) (i : Fin 3) :
    MemClass s (fun n x => w n x * v n x) (α + β - κ)
      (fun n x => strippedTransport G a b n x i) := by
  have hr := class_cmul (ha 0) (class_along (hb i) G.radial_class)
  have hr' : MemClass s (fun n x => w n x * v n x) (α + β - κ)
      (fun n x => a n x 0 * along (G.radial n) (fun y => b n y i) x) := by
    convert! hr using 1
    ring
  have hc := class_cmul (class_div_radius G (ha 1)) (generator_class hb i)
  have hc' := hc.mono_exponent (show α + β - κ ≤ α + β by linarith)
  have hz := class_cmul (ha 2) (class_along (hb i) G.axial_class)
  have hz' := hz.mono_exponent (show α + β - κ ≤ α + (β + 1) by linarith)
  exact (hr'.add hc').add hz'

theorem strippedDivergence_class {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {a : Family D}
    (ha : ∀ i, MemClass s w α (fun n x => a n x i)) :
    MemClass s w (α - κ)
      (fun n => strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a n)) := by
  have hr : MemClass s w (α - κ)
      (fun n => along (G.radial n) (fun y => a n y 0)) := by
    simpa only [sub_eq_add_neg] using class_along (ha 0) G.radial_class
  have hc := (class_div_radius G (ha 0)).mono_exponent (show α - κ ≤ α by linarith)
  have hz := (class_along (ha 2) G.axial_class).mono_exponent
    (show α - κ ≤ α + 1 by linarith)
  apply class_congr ((hr.add hc).add hz)
  intro n x _
  simp only [strippedDivergence, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring


theorem wave_mean_weight {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → E}
    (hf : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) * s.zeta x) α f)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) : WaveClass s P α f := by
  apply hf.mono_weight (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP n x hx))
  intro n x hx
  exact mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) (hP n x hx)) (hζ x hx)


theorem wave_square_weight_wave {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → E}
    (hf : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) α f)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) : WaveClass s P α f := by
  apply hf.mono_weight (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP0 n x hx))
  intro n x hx
  have hs1 : Real.sqrt (s.zeta x) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (s.zeta x), Real.sq_sqrt (s.zeta_nonneg x hx), hζ x hx]
  have hw1 : Real.sqrt (s.zeta x) * P n x ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hs1 (hP1 n x hx) (hP0 n x hx) (by norm_num : (0 : ℝ) ≤ 1)
  exact mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) (hP0 n x hx)) hw1

theorem mean_advects_stripped_wave {s : StripData D} {P : ℕ → D → ℝ} {α μ κ : ℝ}
    (G : Geometry s κ) (hκ : κ ≤ 1) {m a : Family D}
    (hm : MeanVector s μ m) (ha : WaveVector s P α a)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (i : Fin 3) :
    WaveClass s P (α + μ) (fun n x => strippedTransport G m a n x i) := by
  have hr := mean_wave_cmul hm.1 (class_along (ha i) G.radial_class) hζ
  have hr' := hr.mono_exponent (show α + μ ≤ μ + 1 + (α + -κ) by linarith)
  have hc := mean_wave_cmul (class_div_radius G hm.2.1) (generator_class ha i) hζ
  have hc' : WaveClass s P (α + μ)
      (fun n x => m n x 1 / (G.radius n x : ℂ) * angularGenerator (a n x) i) := by
    simpa only [add_comm μ α] using hc
  have hz := mean_wave_cmul hm.2.2 (class_along (ha i) G.axial_class) hζ
  have hz' := hz.mono_exponent (show α + μ ≤ μ + (α + 1) by linarith)
  exact (hr'.add hc').add hz'

theorem wave_advects_stripped_mean {s : StripData D} {P : ℕ → D → ℝ} {α μ κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {m a : Family D}
    (hm : MeanVector s μ m) (ha : WaveVector s P α a)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) (i : Fin 3) :
    WaveClass s P (α + μ - κ) (fun n x => strippedTransport G a m n x i) :=
  wave_mean_weight (strippedTransport_class G hκ ha (meanVector_component hm) i) hζ hP






theorem normalDot_class {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {N : ℕ → D → EuclideanSpace ℝ (Fin 3)} {a : Family D}
    (hN : ∀ i, UnweightedClass s 0 (fun n x => N n x i))
    (ha : ∀ i, MemClass s w α (fun n x => a n x i)) :
    MemClass s w α (fun n x => normalDot (N n x) (a n x)) := by
  have h i : MemClass s w α (fun n x => (N n x i : ℂ) * a n x i) := by
    simpa only [zero_add, Complex.ofRealCLM_apply] using
      unweighted_cmul ((hN i).map Complex.ofRealCLM) (ha i)
  exact ((h 0).add (h 1)).add (h 2)

theorem phaseFactor_class {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {ν : ℕ → ℝ} {f : ℕ → D → ℂ} (hf : MemClass s w α f) (hν : BandBound s β ν) :
    MemClass s w (α + β) (fun n x => phaseFactor (ν n) * f n x) := by
  apply class_congr ((class_const_cmul hf Complex.I).band_smul hν)
  intro n x _
  simp only [phaseFactor, Complex.real_smul]
  ring

noncomputable def waveMeanCoefficient {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ν : ℕ → ℝ) (m a : Family D) : Family D := fun n x i =>
  strippedTransport G m a n x i + strippedTransport G a m n x i +
    phaseFactor (ν n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (m n x) * a n x i

/-- Both cross-advections, with the radial mean improvement explicitly used. -/
theorem wave_mean_bound {s : StripData D} {P : ℕ → D → ℝ} {α μ κ : ℝ}
    (G : Geometry s κ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2)
    {Φ : ℕ → D → ℝ} {ν : ℕ → ℝ} {m a : Family D}
    (hm : MeanVector s μ m) (ha : WaveVector s P α a)
    (hN : ∀ i, UnweightedClass s 0 (fun n x =>
      phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x i))
    (hν : BandBound s (-(1 / 2)) ν)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) :
    WaveVector s P (α + μ - 1 / 2) (waveMeanCoefficient G Φ ν m a) := by
  intro i
  have hma := (mean_advects_stripped_wave G (by linarith) hm ha hζ i).mono_exponent
    (show α + μ - 1 / 2 ≤ α + μ by linarith)
  have ham := (wave_advects_stripped_mean G hκ0 hm ha hζ hP i).mono_exponent
    (show α + μ - 1 / 2 ≤ α + μ - κ by linarith)
  have hdot := normalDot_class hN (meanVector_component hm)
  have hfreq := phaseFactor_class hdot hν
  have hphase := mean_wave_cmul hfreq (ha i) hζ
  have hphase' : WaveClass s P (α + μ - 1 / 2) (fun n x =>
      phaseFactor (ν n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (m n x) * a n x i) := by
    convert! hphase using 1
    ring
  exact (hma.add ham).add hphase'


theorem phaseFactor_ratio (ν ξ : ℝ) (hν : ν ≠ 0) :
    ((ξ / ν : ℝ) : ℂ) * phaseFactor ν = phaseFactor ξ := by
  have hc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  simp only [phaseFactor, Complex.ofReal_div]
  field_simp

/-- The exact divergence cancellation, before taking any norm or any jet. -/
theorem switched_longitudinal (R : D → ℝ) (Vr Vθ Vz : D → D) (ν ξ : ℝ)
    (hν : ν ≠ 0) {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode ν Φ a) x = 0) :
    phaseFactor ξ * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) =
      (ξ / ν) • (-strippedDivergence R Vr Vz a x) := by
  rw [← phaseFactor_ratio ν ξ hν, mul_assoc,
    longitudinal_identity R Vr Vθ Vz ν hΦ ha haθ hdiv]
  rfl

noncomputable def sameCoefficient {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ξ : ℕ → ℝ) (a b : Family D) : Family D := fun n x i =>
  strippedTransport G a b n x i + phaseFactor (ξ n) * normalDot
    (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (a n x) * b n x i


/-- All derivatives of the longitudinal contraction are estimated through
the actual divergence identity, including derivatives of the phase normal. -/
theorem same_label_raw_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a b : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n))
    (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (i : Fin 3) :
    MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ)
      (fun n x => sameCoefficient G Φ ξ a b n x i) := by
  have hs := strippedDivergence_class G hκ ha
  have hsw : WaveClass s P (α - κ) (fun n x =>
      (ξ n / ν n) • (-strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a n) x)) := by
    unfold WaveClass
    simpa only [add_zero] using (class_neg hs).band_smul hratio
  have hprod := class_cmul hsw (hb i)
  have hprod' : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ) (fun n x =>
      ((ξ n / ν n) • (-strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a n) x)) * b n x i) := by
    convert! hprod using 1
    ring
  have hp : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ) (fun n x =>
      phaseFactor (ξ n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (a n x) * b n x i) := by
    apply class_congr hprod'
    intro n x hx
    have hp := ((hΦ n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    have hd j := (((ha j).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    dsimp only
    rw [switched_longitudinal _ _ _ _ (ν n) (ξ n) (hν n) hp hd (haθ n 1 x hx) (hdiv n x hx)]
  exact (strippedTransport_class G hκ ha hb i).add hp



theorem int_abs_cast_one_le {j : ℤ} (hj : j ≠ 0) : (1 : ℝ) ≤ |(j : ℝ)| := by
  have hpos : (0 : ℤ) < |j| := abs_pos.mpr hj
  have hone : (1 : ℤ) ≤ |j| := by omega
  exact_mod_cast hone

theorem harmonic_ratio_bound {j l : ℤ} {M : ℝ} (hj : j ≠ 0)
    (hM : 0 ≤ M) (hl : |(l : ℝ)| ≤ M) : |(l : ℝ) / (j : ℝ)| ≤ M := by
  have hj1 := int_abs_cast_one_le hj
  rw [abs_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hj1)).mpr
  exact hl.trans (le_mul_of_one_le_right hM hj1)

theorem bandBound_harmonic_ratio (s : StripData D) {j l : ℕ → ℤ} {M : ℝ}
    (hj : ∀ n, j n ≠ 0) (hM : 0 ≤ M) (hl : ∀ n, |(l n : ℝ)| ≤ M) :
    BandBound s 0 (fun n => (l n : ℝ) / (j n : ℝ)) := by
  refine ⟨M, hM, 0, ?_⟩
  intro n
  simpa only [Real.norm_eq_abs, Real.rpow_zero, pow_zero, mul_one] using
    harmonic_ratio_bound (hj n) hM (hl n)

theorem frequency_ratio {k : ℝ} (hk : k ≠ 0) {j : ℤ} (hj : j ≠ 0) (l : ℤ) :
    (k * (l : ℝ)) / (k * (j : ℝ)) = (l : ℝ) / (j : ℝ) := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  field_simp

theorem bandBound_frequency_ratio (s : StripData D) {k : ℕ → ℝ} {j l : ℕ → ℤ} {M : ℝ}
    (hk : ∀ n, k n ≠ 0) (hj : ∀ n, j n ≠ 0) (hM : 0 ≤ M)
    (hl : ∀ n, |(l n : ℝ)| ≤ M) :
    BandBound s 0 (fun n => (k n * (l n : ℝ)) / (k n * (j n : ℝ))) := by
  simpa only [frequency_ratio (hk _) (hj _)] using bandBound_harmonic_ratio s hj hM hl

theorem bandBound_frequency {s : StripData D} {β : ℝ} {k : ℕ → ℝ} {j : ℕ → ℤ} {M : ℝ}
    (hk : BandBound s β k) (hM : 0 ≤ M) (hj : ∀ n, |(j n : ℝ)| ≤ M) :
    BandBound s β (fun n => k n * (j n : ℝ)) := by
  obtain ⟨C, hC, p, h⟩ := hk
  refine ⟨C * M, mul_nonneg hC hM, p, ?_⟩
  intro n
  rw [norm_mul]
  have hnonneg : 0 ≤ C * s.epsilon n ^ β * s.slow n ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) β).le)
      (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) p)
  calc
    _ ≤ (C * s.epsilon n ^ β * s.slow n ^ p) * M :=
      mul_le_mul (h n) (by simpa only [Real.norm_eq_abs] using hj n) (norm_nonneg _) hnonneg
    _ = _ := by ring


















/-- The complex operator restricts to the real cylindrical bilinear operator. -/
theorem transport_realLift (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u : D → Fin 3 → ℝ) {v : D → Fin 3 → ℝ} {x : D}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (i : Fin 3) :
    LinearWaveResidual.transport R Vr Vθ Vz
      (LinearWaveResidual.realLift u) (LinearWaveResidual.realLift v) x i =
        (LinearWaveResidual.realTransport R Vr Vθ Vz u v x i : ℂ) := by
  have hd (V : D → D) (j : Fin 3) := along_ofReal V (hv j)
  fin_cases i <;>
    simp [LinearWaveResidual.transport, LinearWaveResidual.realTransport,
      LinearWaveResidual.realLift, angularGenerator, LinearWaveResidual.realAngularGenerator,
      hd, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]






theorem divergence_congr {U : Set D} (hU : IsOpen U)
    (R : D → ℝ) (Vr Vθ Vz : D → D) {a b : D → ComplexVector}
    (hab : EqOn a b U) {x : D} (hx : x ∈ U) :
    cylindricalDivergence R Vr Vθ Vz a x = cylindricalDivergence R Vr Vθ Vz b x := by
  have hi (i : Fin 3) : EqOn (fun y => a y i) (fun y => b y i) U :=
    fun y hy => congrFun (hab hy) i
  unfold cylindricalDivergence
  rw [along_congr hU (hi 0) hx, along_congr hU (hi 1) hx,
    along_congr hU (hi 2) hx, hab hx]












/-- Finite harmonic sets generated by retention, conjugation and quadratic
interaction. The recursive definition retains zero harmonics as well. -/
noncomputable def stageHarmonics (initial : Finset ℤ) : ℕ → Finset ℤ
  | 0 => initial
  | stage + 1 =>
    let current := stageHarmonics initial stage
    current ∪ current.image (fun j => -j) ∪ (current.product current).image (fun p => p.1 + p.2)




end

end NavierStokes.WaveInteractionBounds
