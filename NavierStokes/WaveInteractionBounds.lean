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




theorem class_conj {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => star (f n x)) :=
  hf.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem class_const_cmul {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) (c : ℂ) :
    MemClass s w α (fun n x => c * f n x) :=
  hf.map (ContinuousLinearMap.mul ℝ ℂ c)








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


def AngularIndependent {s : StripData D} {κ : ℝ} (G : Geometry s κ) (a : Family D) : Prop :=
  ∀ n i x, x ∈ s.domain → along (G.angular n) (fun y => a n y i) x = 0

noncomputable def strippedTransport {s : StripData D} {κ : ℝ}
    (G : Geometry s κ) (a b : Family D) : Family D := fun n x i =>
  a n x 0 * along (G.radial n) (fun y => b n y i) x +
    (a n x 1 / (G.radius n x : ℂ)) * angularGenerator (b n x) i +
    a n x 2 * along (G.axial n) (fun y => b n y i) x



theorem inverse_radius_complex {s : StripData D} {κ : ℝ} (G : Geometry s κ) :
    UnweightedClass s 0 (fun n x => ((G.radius n x : ℂ))⁻¹) := by
  unfold UnweightedClass
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_inv] using
    G.inverse_radius_class.map Complex.ofRealCLM

















noncomputable def waveMeanCoefficient {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ν : ℕ → ℝ) (m a : Family D) : Family D := fun n x i =>
  strippedTransport G m a n x i + strippedTransport G a m n x i +
    phaseFactor (ν n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (m n x) * a n x i



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






















end

end NavierStokes.WaveInteractionBounds
