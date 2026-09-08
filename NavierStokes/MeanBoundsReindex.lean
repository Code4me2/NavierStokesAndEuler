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




theorem meanClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {α : ℝ}
    {f : MeanIncrementBounds.Field E} (hf : MeanClass s α f) :
    MeanClass (ParticularWaveBounds.reindexStrip e s) α (StateReindex.field e f) :=
  ParticularWaveBounds.memClass_reindex e hf

theorem unweightedClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {α : ℝ}
    {f : MeanIncrementBounds.Field E} (hf : UnweightedClass s α f) :
    UnweightedClass (ParticularWaveBounds.reindexStrip e s) α (StateReindex.field e f) :=
  ParticularWaveBounds.memClass_reindex e hf









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



section Association

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


end Association

end NavierStokes.MeanBoundsReindex
