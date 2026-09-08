import Euler.OrdinaryH3Envelope
import Euler.SmoothL2CoefficientPath

/-! Uniform H³ comparison and the actual no-gradient-escape consequence
for genuine ordinary Euler evolutions. No energy inequality is assumed. -/

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField EulerSmoothSobolev EulerVolterraConvolution Finset
open scoped ContDiff Topology BoundedContinuousFunction

variable {T : ℝ} {hT : 0 ≤ T}

def referenceNormPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => tensorNorm 4 (U.velocity t),by
    apply continuous_finsetSum
    intro n _
    exact (U.velocity_continuous n).norm⟩

def referenceSize (U : Evolution T hT) : ℝ := ‖U.referenceNormPath‖

theorem referenceSize_nonneg (U : Evolution T hT) : 0 ≤ U.referenceSize := norm_nonneg _

theorem referenceWordBound (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    WordBound 4 U.referenceSize (U.velocity t) := by
  have h := (U.referenceNormPath).norm_coe_le_norm t
  change ‖tensorNorm 4 (U.velocity t)‖ ≤ U.referenceSize at h
  rw [Real.norm_of_nonneg (tensorNorm_nonneg 4 (U.velocity t))] at h
  intro n hn w
  exact (wordBound_tensorNorm 4 (U.velocity t) n hn w).trans h

theorem gradient_continuous (U : Evolution T hT) (x : Space) :
    Continuous (fun t => fderiv ℝ (U.velocity t).field x) := by
  have h := (BoundedContinuousFunction.evalCLM ℝ x :
      (Space →ᵇ (Space →L[ℝ] Space)) →L[ℝ] (Space →L[ℝ] Space)).continuous.comp
    (continuous_finiteField (fun t => (U.velocity t).derivative)
      (continuous_jetLp_derivative U.velocity U.velocity_continuous))
  have he : (fun t => fderiv ℝ (U.velocity t).field x)=
      fun t => (BoundedContinuousFunction.evalCLM ℝ x)
        (finiteField ((U.velocity t).derivative)) := by
    funext t
    exact (finiteField_apply ((U.velocity t).derivative) x).symm
  rw [he]
  exact h

theorem eventually_h3_bound (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 (U.difference (V n) ⟨0,le_rfl,hT⟩) ≤ ε n) :
    ∀ᶠ n in atTop, ∀ t : Icc (0 : ℝ) T,
      tensorNorm 3 (U.difference (V n) t) ≤
        640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) := by
  have hb : Tendsto (fun n => 640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hlim.const_mul 640).mul_const
      (Real.exp (3*stabilityConstant U.referenceSize*T))
  have hs : ∀ᶠ n in atTop, 640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) ≤ 1/2 :=
    hb.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs] with n hn t
  exact U.h3_stability (V n) U.referenceSize (ε n) U.referenceWordBound (hε n) (hinit n) hn t

theorem sampled_h3_tendsto_zero (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 (U.difference (V n) ⟨0,le_rfl,hT⟩) ≤ ε n)
    (times : ℕ → Icc (0 : ℝ) T) :
    Tendsto (fun n => tensorNorm 3 (U.difference (V n) (times n))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => tensorNorm_nonneg 3 _))
    ((U.eventually_h3_bound V ε hε hlim hinit).mono (fun n hn => hn (times n)))
  simpa only [mul_zero,zero_mul] using (hlim.const_mul 640).mul_const
    (Real.exp (3*stabilityConstant U.referenceSize*T))


end EulerOrdinarySobolev.Evolution
