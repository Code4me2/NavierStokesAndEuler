import NavierStokes.UniformBlockBounds
import NavierStokes.UniformHarmonicInteraction

/-!
# Exact transport of mean bounds and residual coefficient classes

Pullback along `e : D ≃ₗᵢ[ℝ] E` uses the actual state/context construction
from `StateReindex`.  Every derivative norm and every scalar majorant is
unchanged.  In particular, uniform constants are chosen before the label
both before and after reassociation.
-/

noncomputable section

namespace NavierStokes.MeanBoundsReindex

open Set Function Filter WeightedClasses LabelSumBounds
open scoped ContDiff Topology

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem strip_roundtrip (e : D ≃ₗᵢ[ℝ] E) (s : StripData D) :
    ParticularWaveBounds.reindexStrip e (ParticularWaveBounds.reindexStrip e.symm s) = s := by
  cases s
  simp only [ParticularWaveBounds.reindexStrip, preimage_preimage, e.symm_apply_apply]
  rfl

theorem majorant_pull (e : D ≃ₗᵢ[ℝ] E) (s : StripData E) (w : ℕ → E → ℝ)
    (α C : ℝ) (p n : ℕ) (x : D) :
    majorant (ParticularWaveBounds.reindexStrip e s) (fun k y => w k (e y)) α C p n x =
      majorant s w α C p n (e x) := rfl



theorem meanClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {α : ℝ}
    {f : MeanIncrementBounds.Field E} (hf : MeanClass s α f) :
    MeanClass (ParticularWaveBounds.reindexStrip e s) α (StateReindex.field e f) :=
  ParticularWaveBounds.memClass_reindex e hf

theorem unweightedClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {α : ℝ}
    {f : MeanIncrementBounds.Field E} (hf : UnweightedClass s α f) :
    UnweightedClass (ParticularWaveBounds.reindexStrip e s) α (StateReindex.field e f) :=
  ParticularWaveBounds.memClass_reindex e hf

theorem operatorBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {o : MeanIncrementBounds.Operators E} {κ : ℝ}
    (ho : MeanIncrementBounds.OperatorBounds s o κ) :
    MeanIncrementBounds.OperatorBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.operators e o) κ := by
  refine ⟨ho.epsilon_eq, ?_, ?_, ho.radialFrequency, ho.fastCoefficient,
    ho.kappa_nonneg, fun x hx => ho.weight_le_one (e x) hx⟩
  · exact unweightedClass_pull e ho.radialProfile
  · exact unweightedClass_pull e ho.invRadius

theorem baseBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {b : MeanIncrementBounds.Triple E} (hb : MeanIncrementBounds.BaseBounds s b) :
    MeanIncrementBounds.BaseBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.triple e b) :=
  ⟨unweightedClass_pull e hb.radial, unweightedClass_pull e hb.angular,
    unweightedClass_pull e hb.axial⟩

theorem meanCumulativeBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {b : MeanIncrementBounds.Triple E} (hb : MeanIncrementBounds.CumulativeBounds s b) :
    MeanIncrementBounds.CumulativeBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.triple e b) :=
  ⟨meanClass_pull e hb.radial, meanClass_pull e hb.angular, meanClass_pull e hb.axial⟩


theorem context_operatorBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {c : CorrectionState.Context E} {κ : ℝ}
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ) :
    MeanIncrementBounds.OperatorBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.context e c).operators κ := operatorBounds_pull e ho

theorem context_baseBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {c : CorrectionState.Context E} (hb : MeanIncrementBounds.BaseBounds s c.base) :
    MeanIncrementBounds.BaseBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.context e c).base := baseBounds_pull e hb

theorem cumulativeBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {u : CorrectionState.State E} (hu : CorrectionState.CumulativeBounds s u) :
    CorrectionState.CumulativeBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.state e u) :=
  ⟨meanCumulativeBounds_pull e hu.velocity, meanClass_pull e hu.pressure⟩


/-! ## Returning solver classes to the original chart -/


/-- Returning a uniform class retains the same constants chosen before
both the label and the band. -/
theorem uniformClass_return {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : D ≃ₗᵢ[ℝ] E) {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → E → F}
    (hf : UniformClass (ParticularWaveBounds.reindexStrip e.symm s)
      (fun l n y => w l n (e.symm y)) α f) :
    UniformClass s w α (fun l n x => f l n (e x)) := by
  have hh := UniformBlockBounds.uniform_reindex e hf
  simpa only [strip_roundtrip, e.symm_apply_apply] using hh




/-! ## Uniform classes of the actual harmonic residual -/

theorem residualBlock_return (e : D ≃ₗᵢ[ℝ] E)
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) :
    StateReindex.block e
      (HarmonicResidual.residualBlock (StateReindex.context e.symm c) (StateReindex.state e.symm u)
        (StateReindex.block e.symm b) (StateReindex.blockCoefficients e.symm G)
        (StateReindex.blockCoefficients e.symm A)) =
      HarmonicResidual.residualBlock c u b G A := by
  rw [StateReindex.residualBlock_pull, StateReindex.block_roundtrip]

/-- Arbitrary solver block families return with their original common
weight and exponent.  Uniformity over labels is retained. -/
theorem uniformVelocity_return {ι : Type*} (e : D ≃ₗᵢ[ℝ] E) {s : StripData D}
    {P : ι → ℕ → D → ℝ} {α : ℝ} {b : ι → CorrectionState.HarmonicBlock E}
    (hb : UniformHarmonicInteraction.UniformVelocity
      (ParticularWaveBounds.reindexStrip e.symm s) (fun l n y => P l n (e.symm y)) α b) :
    UniformHarmonicInteraction.UniformVelocity s P α (fun l => StateReindex.block e (b l)) := by
  intro i j hj
  exact uniformClass_return e (hb i j hj)

theorem uniformVelocity_pull {ι : Type*} (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {P : ι → ℕ → E → ℝ} {α : ℝ} {b : ι → CorrectionState.HarmonicBlock E}
    (hb : UniformHarmonicInteraction.UniformVelocity s P α b) :
    UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e s)
      (fun l n x => P l n (e x)) α (fun l => StateReindex.block e (b l)) := by
  intro i j hj
  exact UniformBlockBounds.block_velocity_reindex e i j (hb i j hj)


/-- The actual residual is sent to the new chart along with its context,
state, carrier and both excluded error coefficient families. -/
theorem residualBlock_uniform_pull {ι : Type*} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData E} {P : ι → ℕ → E → ℝ} {α : ℝ}
    (c : CorrectionState.Context E) (u : CorrectionState.State E)
    (b : ι → CorrectionState.HarmonicBlock E) (G A : ι → HarmonicResidual.BlockCoefficients E)
    (hb : UniformHarmonicInteraction.UniformVelocity s P α
      (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l))) :
    UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e s)
      (fun l n x => P l n (e x)) α
      (fun l => HarmonicResidual.residualBlock (StateReindex.context e c)
        (StateReindex.state e u) (StateReindex.block e (b l))
        (StateReindex.blockCoefficients e (G l)) (StateReindex.blockCoefficients e (A l))) := by
  simpa only [StateReindex.residualBlock_pull] using uniformVelocity_pull e hb


/-- Actual residual classes proved in the associated solver chart return
to the original state without an extra operator-bounds hypothesis. -/
theorem residualBlock_uniform_return {ι : Type*} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : ι → CorrectionState.HarmonicBlock D) (G A : ι → HarmonicResidual.BlockCoefficients D)
    (hb : UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e.symm s)
      (fun l n y => P l n (e.symm y)) α
      (fun l => HarmonicResidual.residualBlock (StateReindex.context e.symm c)
        (StateReindex.state e.symm u) (StateReindex.block e.symm (b l))
        (StateReindex.blockCoefficients e.symm (G l))
        (StateReindex.blockCoefficients e.symm (A l)))) :
    UniformHarmonicInteraction.UniformVelocity s P α
      (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l)) := by
  simpa only [residualBlock_return] using uniformVelocity_return e hb

section Association

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


end Association

end NavierStokes.MeanBoundsReindex
