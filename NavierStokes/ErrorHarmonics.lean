import NavierStokes.HarmonicFields
import NavierStokes.LinearWaveBounds
import NavierStokes.CorrectionState
import NavierStokes.AxisymmetricResidual

/-!
# Explicit harmonic witnesses for the retained error fields

Every representation in this file is constructed from its source field.
Gaussian errors retain the original carrier and its conjugate, while actual
mean aliases occupy the zero mode. No full-residual identity is assumed.
-/

noncomputable section

namespace NavierStokes.ErrorHarmonics

open Set Filter Function MeasureTheory
open HarmonicFields CorrectionState
open scoped BigOperators ContDiff Topology ComplexConjugate

noncomputable def conjugatePair {D : Type} (j : ℤ) (a : D → ℂ) : Coefficients D := by
  let c : Coefficients D := AddMonoidAlgebra.single j (fun x => a x / 2)
  exact c + conjugateReverse c

theorem evaluate_conjugatePair {D : Type} (j : ℤ) (a : D → ℂ) (x : D) (φ : ℝ) :
    evaluate (conjugatePair j a) x φ = ((a x * character j φ).re : ℂ) := by
  rw [conjugatePair, evaluate_add, evaluate_conjugateReverse, evaluate_single,
    Complex.re_eq_add_conj]
  simp only [map_mul, map_div₀, map_ofNat]
  ring

theorem field_conjugatePair {D : Type} (j : ℤ) (a : D → ℂ) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (p : D × ℝ) :
    field (conjugatePair j a) k Φ kp p =
      ((a p.1 * character j (k * Φ p.1 + (kp : ℝ) * p.2)).re : ℂ) :=
  evaluate_conjugatePair j a p.1 _

theorem conjugatePair_symmetric {D : Type} (j : ℤ) (a : D → ℂ) :
    ConjugateSymmetric (conjugatePair j a) := by
  classical
  intro m x
  let c : Coefficients D := AddMonoidAlgebra.single j (fun x => a x / 2)
  change c (-m) x + conj (c (-(-m)) x) = conj (c m x + conj (c (-m) x))
  simp only [map_add, neg_neg, starRingEnd_self_apply]
  exact add_comm _ _

theorem band_single {D : Type} (j : ℤ) (a : D → ℂ) :
    HarmonicFields.BandLimited (AddMonoidAlgebra.single j a : Coefficients D) j.natAbs := by
  intro m hm
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
  exact he ▸ le_rfl

theorem band_conjugateReverse {D : Type} {c : Coefficients D} {N : ℕ}
    (hc : HarmonicFields.BandLimited c N) : HarmonicFields.BandLimited (conjugateReverse c) N := by
  intro j hj
  have hm : -j ∈ c.support := by
    by_contra hn
    have hz := Finsupp.notMem_support_iff.mp hn
    have hzero : conjugateReverse c j = 0 := by
      funext x
      simp only [conjugateReverse_apply, hz, Pi.zero_apply, map_zero]
    exact (Finsupp.mem_support_iff.mp hj) hzero
  simpa only [Int.natAbs_neg] using hc (-j) hm

theorem band_conjugatePair {D : Type} (j : ℤ) (a : D → ℂ) :
    HarmonicFields.BandLimited (conjugatePair j a) j.natAbs :=
  (band_single j (fun x => a x / 2)).add
    (band_conjugateReverse (band_single j (fun x => a x / 2)))


noncomputable def pairedBlock {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (a : ℕ → D → HarmonicCalculus.ComplexVector) : HarmonicBlock D where
  velocity n i := conjugatePair j (fun x => a n x i)
  pressure _ := 0
  frequency := k
  phase := Φ
  angularFrequency := kp

theorem pairedBlock_band {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (a : ℕ → D → HarmonicCalculus.ComplexVector) :
    HarmonicBlock.BandLimited (pairedBlock j k Φ kp a) j.natAbs := by
  refine ⟨fun n i => band_conjugatePair j (fun x => a n x i), ?_⟩
  intro n l hl
  simp [pairedBlock] at hl


theorem pairedBlock_evaluation {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (a : ℕ → D → HarmonicCalculus.ComplexVector) (n : ℕ) (p : D × ℝ) (i : Fin 3) :
    (pairedBlock j k Φ kp a).oscillation n p i =
      (a n p.1 i * character j (k n * Φ n p.1 + (kp n : ℝ) * p.2)).re := by
  have h := congrArg Complex.re (field_conjugatePair j (fun x => a n x i) (k n) (Φ n) (kp n) p)
  simp only [Complex.ofReal_re] at h
  exact h

noncomputable def zeroBlock {D : Type} (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : MeanVector D) : HarmonicBlock D where
  velocity n i := constantCoefficient (fun x => (a n x i : ℂ))
  pressure _ := 0
  frequency := k
  phase := Φ
  angularFrequency := kp



theorem zeroBlock_symmetric {D : Type} (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : MeanVector D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((zeroBlock k Φ kp a).velocity n i) := by
  intro j x
  classical
  by_cases hj : j = 0
  · simp [zeroBlock, constantCoefficient, hj]
  · simp [zeroBlock, constantCoefficient, hj]

section GaussianErrors

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Independence of the explicit angular coordinate. -/
def AngleIndependent (f : ℕ → D × ℝ → E) : Prop :=
  ∀ n x θ, f n (x, θ) = f n (x, 0)

theorem dfast_angleIndependent (d : LinearWaveBounds.GraphDirections (D × ℝ))
    {ψ : ℕ → D × ℝ → ℝ} (hψ : ∀ n, ContDiff ℝ ∞ (ψ n)) (hψa : AngleIndependent ψ) :
    AngleIndependent (d.Dfast ψ) := by
  intro n x θ
  let q : D → ℝ := fun y => ψ n (y, 0)
  let L : D × ℝ →L[ℝ] D := ContinuousLinearMap.fst ℝ D ℝ
  have hq : ContDiff ℝ ∞ q := (hψ n).comp (contDiff_id.prodMk contDiff_const)
  have he : ψ n = q ∘ L := funext (fun p => hψa n p.1 p.2)
  have hd (t : ℝ) := (((hq.differentiable (by simp)) x).hasFDerivAt).comp (x, t) L.hasFDerivAt
  simp only [LinearWaveBounds.GraphDirections.Dfast, LinearWaveBounds.GraphDirections.fastField,
    HarmonicCalculus.along, he, (hd θ).fderiv, (hd 0).fderiv]

theorem excludedSlotError_angleIndependent (d : LinearWaveBounds.GraphDirections (D × ℝ))
    {ψ : ℕ → D × ℝ → ℝ} {a source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector}
    (hψ : ∀ n, ContDiff ℝ ∞ (ψ n)) (hψa : AngleIndependent ψ)
    (ha : AngleIndependent a) (hs : AngleIndependent source) :
    AngleIndependent (LinearWaveBounds.excludedSlotError d ψ a source) := by
  intro n x θ
  simp only [LinearWaveBounds.excludedSlotError, dfast_angleIndependent d hψ hψa n x θ,
    hψa n x θ, ha n x θ, hs n x θ]



/-- The retained Gaussian term as a literal real carrier field. -/
noncomputable def gaussianField (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) (a source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector)
    (j : ℤ) (k : ℕ → ℝ) (Ψ : ℕ → D × ℝ → ℝ) : Oscillation D :=
  fun n p i => (HarmonicCalculus.vectorMode (k n * (j : ℝ)) (Ψ n)
    (LinearWaveBounds.excludedSlotError d ψ a source n) p i).re

noncomputable def gaussianBlock (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) (a source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector)
    (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  pairedBlock j k Φ kp (fun n x => LinearWaveBounds.excludedSlotError d ψ a source n (x, 0))


theorem gaussianBlock_band (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) (a source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector)
    (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) :
    HarmonicBlock.BandLimited (gaussianBlock d ψ a source j k Φ kp) j.natAbs :=
  pairedBlock_band j k Φ kp _


/-- The witness evaluates to the actual error, from primitive angular
independence and the actual phase identity. No error representation is assumed. -/
theorem gaussianBlock_represents (d : LinearWaveBounds.GraphDirections (D × ℝ))
    {ψ : ℕ → D × ℝ → ℝ} {a source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector}
    (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (Ψ : ℕ → D × ℝ → ℝ) (kp : ℕ → ℤ)
    (hψ : ∀ n, ContDiff ℝ ∞ (ψ n)) (hψa : AngleIndependent ψ)
    (ha : AngleIndependent a) (hs : AngleIndependent source)
    (hphase : ∀ n x θ, k n * Ψ n (x, θ) = k n * Φ n x + (kp n : ℝ) * θ) :
    (gaussianBlock d ψ a source j k Φ kp).oscillation = gaussianField d ψ a source j k Ψ := by
  funext n p i
  change (pairedBlock j k Φ kp _).oscillation n p i = _
  rw [pairedBlock_evaluation]
  change (LinearWaveBounds.excludedSlotError d ψ a source n (p.1, 0) i *
    character j (k n * Φ n p.1 + (kp n : ℝ) * p.2)).re =
      (LinearWaveBounds.excludedSlotError d ψ a source n p i * HarmonicCalculus.carrier
        (k n * (j : ℝ)) (Ψ n) p).re
  rw [← character_eq_carrier j (k n) (Ψ n) p, hphase n p.1 p.2]
  rw [excludedSlotError_angleIndependent d hψ hψa ha hs n p.1 p.2]



end GaussianErrors

section AliasErrors

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]












end AliasErrors

/-- Conjugacy is kept for both velocity and pressure coefficients. -/
def RealBlock {D : Type} (b : HarmonicBlock D) : Prop :=
  (∀ n i, ConjugateSymmetric (b.velocity n i)) ∧ ∀ n, ConjugateSymmetric (b.pressure n)







theorem symmetric_add {D : Type} {a b : Coefficients D}
    (ha : ConjugateSymmetric a) (hb : ConjugateSymmetric b) :
    ConjugateSymmetric (a + b) := by
  intro j x
  change a (-j) x + b (-j) x = conj (a j x + b j x)
  rw [map_add, ha j x, hb j x]

theorem band_sum {D ι : Type} (s : Finset ι) (a : ι → Coefficients D) (N : ℕ)
    (ha : ∀ l ∈ s, HarmonicFields.BandLimited (a l) N) :
    HarmonicFields.BandLimited (∑ l ∈ s, a l) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HarmonicFields.BandLimited]
  | @insert l s hl ih =>
    rw [Finset.sum_insert hl]
    exact (ha l (Finset.mem_insert_self _ _)).add
      (ih (fun m hm => ha m (Finset.mem_insert_of_mem hm)))

theorem symmetric_sum {D ι : Type} (s : Finset ι) (a : ι → Coefficients D)
    (ha : ∀ l ∈ s, ConjugateSymmetric (a l)) :
    ConjugateSymmetric (∑ l ∈ s, a l) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro j x; simp
  | @insert l s hl ih =>
    rw [Finset.sum_insert hl]
    exact symmetric_add (ha l (Finset.mem_insert_self _ _))
      (ih (fun m hm => ha m (Finset.mem_insert_of_mem hm)))

/-- Accumulation is coefficient addition within one fixed label. Distinct
labels are left distinct even if their numerical carriers coincide. -/
noncomputable def sumBlock {D ι : Type} (s : Finset ι)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (b : ι → HarmonicBlock D) :
    HarmonicBlock D where
  velocity n i := ∑ l ∈ s, (b l).velocity n i
  pressure n := ∑ l ∈ s, (b l).pressure n
  frequency := k
  phase := Φ
  angularFrequency := kp

theorem sumBlock_band {D ι : Type} (s : Finset ι)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (b : ι → HarmonicBlock D)
    (N : ℕ) (hb : ∀ l ∈ s, HarmonicBlock.BandLimited (b l) N) :
    HarmonicBlock.BandLimited (sumBlock s k Φ kp b) N :=
  ⟨fun n i => band_sum s _ N (fun l hl => (hb l hl).1 n i),
    fun n => band_sum s _ N (fun l hl => (hb l hl).2 n)⟩

theorem sumBlock_real {D ι : Type} (s : Finset ι)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (b : ι → HarmonicBlock D)
    (hb : ∀ l ∈ s, RealBlock (b l)) : RealBlock (sumBlock s k Φ kp b) :=
  ⟨fun n i => symmetric_sum s _ (fun l hl => (hb l hl).1 n i),
    fun n => symmetric_sum s _ (fun l hl => (hb l hl).2 n)⟩

theorem sumBlock_represents {D ι : Type} (s : Finset ι)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (b : ι → HarmonicBlock D)
    (hk : ∀ l ∈ s, (b l).frequency = k) (hΦ : ∀ l ∈ s, (b l).phase = Φ)
    (hkp : ∀ l ∈ s, (b l).angularFrequency = kp) :
    (sumBlock s k Φ kp b).oscillation = ∑ l ∈ s, (b l).oscillation := by
  classical
  funext n p i
  simp only [HarmonicBlock.oscillation, sumBlock, field, evaluate_eq_hom, map_sum,
    Finset.sum_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hk l hl, hΦ l hl, hkp l hl]


section FiniteStages

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Only primitive data are stored. The error field and its coefficients are
computed from the cutoff derivative, amplitudes, and carrier. -/
structure GaussianData (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  directions : LinearWaveBounds.GraphDirections (D × ℝ)
  cutoff : ℕ → D × ℝ → ℝ
  amplitude : ℕ → D × ℝ → HarmonicCalculus.ComplexVector
  source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector
  harmonic : ℤ
  phase : ℕ → D × ℝ → ℝ

noncomputable def GaussianData.error (g : GaussianData D) (k : ℕ → ℝ) : Oscillation D :=
  gaussianField g.directions g.cutoff g.amplitude g.source g.harmonic k g.phase

noncomputable def GaussianData.block (g : GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  gaussianBlock g.directions g.cutoff g.amplitude g.source g.harmonic k Φ kp

def GaussianData.Compatible (g : GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : Prop :=
  (∀ n, ContDiff ℝ ∞ (g.cutoff n)) ∧ AngleIndependent g.cutoff ∧
    AngleIndependent g.amplitude ∧ AngleIndependent g.source ∧
    ∀ n x θ, k n * g.phase n (x, θ) = k n * Φ n x + (kp n : ℝ) * θ

theorem GaussianData.block_represents (g : GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (hg : g.Compatible k Φ kp) :
    (g.block k Φ kp).oscillation = g.error k :=
  gaussianBlock_represents g.directions g.harmonic k Φ g.phase kp
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2






end FiniteStages

section AliasStages

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]













end AliasStages

section AxisymmetricBase

open ProblemStatement AxisymmetricFields















end AxisymmetricBase

end NavierStokes.ErrorHarmonics
