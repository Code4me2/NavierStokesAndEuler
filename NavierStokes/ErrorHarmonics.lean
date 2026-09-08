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

theorem pairedBlock_symmetric {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (a : ℕ → D → HarmonicCalculus.ComplexVector) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((pairedBlock j k Φ kp a).velocity n i) :=
  conjugatePair_symmetric j (fun x => a n x i)

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

theorem zeroBlock_evaluation {D : Type} (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : MeanVector D) (n : ℕ) (p : D × ℝ) (i : Fin 3) :
    (zeroBlock k Φ kp a).oscillation n p i = a n p.1 i := by
  change (field (constantCoefficient (fun x => (a n x i : ℂ))) (k n) (Φ n) (kp n) p).re = _
  unfold field constantCoefficient
  rw [evaluate_single, character_zero, mul_one, Complex.ofReal_re]

theorem zeroBlock_band {D : Type} (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : MeanVector D) : HarmonicBlock.BandLimited (zeroBlock k Φ kp a) 0 := by
  refine ⟨fun n i => band_constantCoefficient _, ?_⟩
  intro n l hl
  simp [zeroBlock] at hl

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

theorem slot_coordinate_angleIndependent {s : WeightedClasses.StripData (D × ℝ)}
    (g : GaussianTailFlat.SlotFamily s) (hangle : ∀ n, g.linear n ((0 : D), 1) = 0) :
    AngleIndependent g.coordinate := by
  intro n x θ
  have hp : (x, θ) = (x, 0) + θ • ((0 : D), 1) := by ext <;> simp
  simp only [GaussianTailFlat.SlotFamily.coordinate, hp, map_add, map_smul, hangle,
    smul_zero, add_zero]

theorem slot_cutoff_angleIndependent {s : WeightedClasses.StripData (D × ℝ)}
    (g : GaussianTailFlat.SlotFamily s) (hangle : ∀ n, g.linear n ((0 : D), 1) = 0) :
    AngleIndependent g.cutoff := by
  intro n x θ
  exact congrArg GaussianTailFlat.profile (slot_coordinate_angleIndependent g hangle n x θ)

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

/-- The pressure alias already used in the correction state, represented in
mode zero. Its metadata can be chosen to equal any associated label. -/
noncomputable def pressureAliasBlock (r : ReconstructionData) (c : Context (Lift S))
    (u : State (Lift S)) (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) :
    HarmonicBlock (Lift S) :=
  zeroBlock k Φ kp (fun n x => CorrectionState.pressureAlias r c u n (x, 0))




/-- The temporal alias retains its actual differentiated shifted integral. -/
noncomputable def temporalAliasBlock (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) : HarmonicBlock (Lift S) :=
  zeroBlock k Φ kp (fun n x => CorrectionState.temporalAlias r h c u n (x, 0))




/-- Replacing a pressure reconstruction changes the saved alias by its exact
new-minus-old value, which is again mode zero. -/
noncomputable def pressureAliasRefreshBlock (r : ReconstructionData)
    (c : Context (Lift S)) (oldState newState : State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) : HarmonicBlock (Lift S) :=
  zeroBlock k Φ kp (fun n x => CorrectionState.pressureAlias r c newState n (x, 0) -
    CorrectionState.pressureAlias r c oldState n (x, 0))



end AliasErrors

/-- Conjugacy is kept for both velocity and pressure coefficients. -/
def RealBlock {D : Type} (b : HarmonicBlock D) : Prop :=
  (∀ n i, ConjugateSymmetric (b.velocity n i)) ∧ ∀ n, ConjugateSymmetric (b.pressure n)

theorem pairedBlock_real {D : Type} (j : ℤ) (k : ℕ → ℝ) (Φ : ℕ → D → ℝ)
    (kp : ℕ → ℤ) (a : ℕ → D → HarmonicCalculus.ComplexVector) :
    RealBlock (pairedBlock j k Φ kp a) := by
  refine ⟨pairedBlock_symmetric j k Φ kp a, ?_⟩
  intro n l x
  simp [pairedBlock]

theorem zeroBlock_real {D : Type} (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (a : MeanVector D) : RealBlock (zeroBlock k Φ kp a) := by
  refine ⟨zeroBlock_symmetric k Φ kp a, ?_⟩
  intro n l x
  simp [zeroBlock]





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

noncomputable def accumulatedGaussianBlock (steps : ℕ) (g : ℕ → GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) : HarmonicBlock D :=
  sumBlock (Finset.range steps) k Φ kp (fun s => (g s).block k Φ kp)

theorem accumulatedGaussianBlock_represents (steps : ℕ) (g : ℕ → GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (hg : ∀ s < steps, (g s).Compatible k Φ kp) :
    (accumulatedGaussianBlock steps g k Φ kp).oscillation =
      ∑ s ∈ Finset.range steps, (g s).error k := by
  rw [accumulatedGaussianBlock, sumBlock_represents (Finset.range steps) k Φ kp
    (fun s => (g s).block k Φ kp)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  apply Finset.sum_congr rfl
  intro s hs
  exact (g s).block_represents k Φ kp (hg s (Finset.mem_range.mp hs))

theorem accumulatedGaussianBlock_band (steps : ℕ) (g : ℕ → GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (N : ℕ) (hj : ∀ s < steps, (g s).harmonic.natAbs ≤ N) :
    HarmonicBlock.BandLimited (accumulatedGaussianBlock steps g k Φ kp) N := by
  apply sumBlock_band
  intro s hs
  have he := gaussianBlock_band (g s).directions (g s).cutoff (g s).amplitude
    (g s).source (g s).harmonic k Φ kp
  exact ⟨fun n i => (he.1 n i).mono (hj s (Finset.mem_range.mp hs)),
    fun n => (he.2 n).mono (hj s (Finset.mem_range.mp hs))⟩

/-- This bounds the values of the occupied harmonics, not merely their count. -/
theorem accumulatedGaussianBlock_band_pow (steps : ℕ) (g : ℕ → GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ)
    (hj : ∀ s < steps, (g s).harmonic.natAbs ≤ 2 ^ s) :
    HarmonicBlock.BandLimited (accumulatedGaussianBlock steps g k Φ kp) (2 ^ steps) := by
  apply accumulatedGaussianBlock_band
  intro s hs
  exact (hj s hs).trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_of_lt hs))

theorem accumulatedGaussianBlock_real (steps : ℕ) (g : ℕ → GaussianData D)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) :
    RealBlock (accumulatedGaussianBlock steps g k Φ kp) := by
  apply sumBlock_real
  intro s hs
  exact pairedBlock_real (g s).harmonic k Φ kp _

end FiniteStages

section AliasStages

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Actual saved aliases after finitely many temporal stages and the current
pressure reconstruction. The state path may be produced by any correction rule. -/
noncomputable def accumulatedAlias (steps : ℕ) (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : ℕ → State (Lift S)) : Oscillation (Lift S) :=
  CorrectionState.pressureAlias r c (u steps) +
    ∑ s ∈ Finset.range steps, CorrectionState.temporalAlias r h c (u s)

noncomputable def accumulatedAliasBlock (steps : ℕ) (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : ℕ → State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) : HarmonicBlock (Lift S) :=
  zeroBlock k Φ kp (fun n x => accumulatedAlias steps r h c u n (x, 0))

theorem accumulatedAlias_angleIndependent (steps : ℕ) (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : ℕ → State (Lift S)) :
    AngleIndependent (accumulatedAlias steps r h c u) := by
  intro n x θ
  simp only [accumulatedAlias, Pi.add_apply, Finset.sum_apply, CorrectionState.pressureAlias,
    CorrectionState.temporalAlias]

theorem accumulatedAliasBlock_represents (steps : ℕ) (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : ℕ → State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) :
    (accumulatedAliasBlock steps r h c u k Φ kp).oscillation = accumulatedAlias steps r h c u := by
  funext n p i
  rw [accumulatedAliasBlock, zeroBlock_evaluation]
  exact congrFun (accumulatedAlias_angleIndependent steps r h c u n p.1 p.2).symm i

theorem accumulatedAliasBlock_band (steps : ℕ) (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : ℕ → State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) :
    HarmonicBlock.BandLimited (accumulatedAliasBlock steps r h c u k Φ kp) 0 :=
  zeroBlock_band k Φ kp _

theorem accumulatedAliasBlock_real (steps : ℕ) (r : ReconstructionData) (h : ℝ)
    (c : Context (Lift S)) (u : ℕ → State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) :
    RealBlock (accumulatedAliasBlock steps r h c u k Φ kp) := zeroBlock_real k Φ kp _



/-- The two retained error types for one label are added as actual finite
coefficient families. The base error is handled separately in the physical
decomposition and cancels from the good residual. -/
noncomputable def accumulatedErrorBlock (steps : ℕ) (g : ℕ → GaussianData (Lift S))
    (r : ReconstructionData) (h : ℝ) (c : Context (Lift S)) (u : ℕ → State (Lift S))
    (k : ℕ → ℝ) (Φ : ℕ → Lift S → ℝ) (kp : ℕ → ℤ) : HarmonicBlock (Lift S) where
  velocity n i := (accumulatedGaussianBlock steps g k Φ kp).velocity n i +
    (accumulatedAliasBlock steps r h c u k Φ kp).velocity n i
  pressure _ := 0
  frequency := k
  phase := Φ
  angularFrequency := kp




end AliasStages

section AxisymmetricBase

open ProblemStatement AxisymmetricFields

/-- Cartesian location of the cylindrical point `(r,z,θ)`. -/
noncomputable def polarSpace (r z θ : ℝ) : Space :=
  AxisymmetricResidual.pack (r * Real.cos θ) (r * Real.sin θ) z

noncomputable def polarProfile (q : ProfilePoint) : ProfilePoint :=
  (q.1, (q.2.1 ^ 2 / 2, q.2.2))

theorem profilePoint_polarSpace (q : ProfilePoint) (θ : ℝ) :
    profilePoint q.1 (polarSpace q.2.1 q.2.2 θ) = polarProfile q := by
  simp only [profilePoint, polarProfile, radialEnergy, polarSpace,
    AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one, AxisymmetricResidual.pack_two]
  congr 2
  calc
    _ = q.2.1 ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) / 2 := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- Components in the actual orthonormal radial/angular/axial frame. -/
noncomputable def cylindricalComponents (θ : ℝ) (v : Space) : Fin 3 → ℝ :=
  ![Real.cos θ * v 0 + Real.sin θ * v 1,
    -Real.sin θ * v 0 + Real.cos θ * v 1, v 2]

theorem cylindricalComponents_pack (r θ A B C : ℝ) :
    cylindricalComponents θ (AxisymmetricResidual.pack
      (r * Real.cos θ * A + r * Real.sin θ * B)
      (r * Real.sin θ * A - r * Real.cos θ * B) C) = ![r * A, -r * B, C] := by
  funext i
  fin_cases i
  · simp [cylindricalComponents]
    calc
      _ = r * A * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
  · simp [cylindricalComponents]
    calc
      _ = -r * B * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = _ := by simp only [Real.sin_sq_add_cos_sq, mul_one, neg_mul]
  · simp [cylindricalComponents]


/-- The literal Cartesian Navier--Stokes residual, expressed in its cylindrical
frame. This is not an independently specified error oracle. -/
noncomputable def axisymmetricBaseError (B F U P : ℕ → Profile) : Oscillation ProfilePoint :=
  fun n p => cylindricalComponents p.2
    (navierStokesResidual (AxisymmetricResidual.velocity (B n) (F n) (U n))
      (AxisymmetricResidual.pressure (P n)) p.1.1 (polarSpace p.1.2.1 p.1.2.2 p.2))

noncomputable def axisymmetricBaseValue (B F U P : ℕ → Profile) : MeanVector ProfilePoint :=
  fun n q => ![q.2.1 * AxisymmetricResidual.residualRadial (B n) (F n) (U n) (P n) (polarProfile q),
    -q.2.1 * AxisymmetricResidual.residualAngular (B n) (F n) (U n) (polarProfile q),
    AxisymmetricResidual.residualAxial (B n) (U n) (P n) (polarProfile q)]

theorem axisymmetricBaseError_eq_value (B F U P : ℕ → Profile) (n : ℕ)
    (q : ProfilePoint) (θ : ℝ)
    (hB : AxisymmetricResidual.SliceC2 (B n) q.1)
    (hF : AxisymmetricResidual.SliceC2 (F n) q.1)
    (hU : AxisymmetricResidual.SliceC2 (U n) q.1)
    (hP : AxisymmetricResidual.SliceDifferentiable (P n) q.1) :
    axisymmetricBaseError B F U P n (q, θ) = axisymmetricBaseValue B F U P n q := by
  unfold axisymmetricBaseError
  rw [AxisymmetricResidual.navierStokesResidual_velocity hB hF hU hP
    (polarSpace q.2.1 q.2.2 θ), profilePoint_polarSpace]
  simp only [polarSpace, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
  exact cylindricalComponents_pack q.2.1 θ
    (AxisymmetricResidual.residualRadial (B n) (F n) (U n) (P n) (polarProfile q))
    (AxisymmetricResidual.residualAngular (B n) (F n) (U n) (polarProfile q))
    (AxisymmetricResidual.residualAxial (B n) (U n) (P n) (polarProfile q))


noncomputable def axisymmetricBaseBlock (B F U P : ℕ → Profile)
    (k : ℕ → ℝ) (Φ : ℕ → ProfilePoint → ℝ) (kp : ℕ → ℤ) : HarmonicBlock ProfilePoint :=
  zeroBlock k Φ kp (axisymmetricBaseValue B F U P)




end AxisymmetricBase

end NavierStokes.ErrorHarmonics
