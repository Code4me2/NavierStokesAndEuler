import Euler.FiniteMetricEnergy
import Euler.TimeLp

/-! Actual L²-time convergence of finite Hilbert forcing norms. -/

noncomputable section

namespace EulerFamilyNormTime

open MeasureTheory InnerProductSpace EulerTimeLp EulerFiniteMetricEnergy
open scoped Topology

variable {I H : Type*} [Fintype I] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The ordinary finite family as its genuine Hilbert-sum norm model. -/
def familyHilbertMap : (I → H) →L[ℝ] PiLp 2 (fun _ : I => H) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => H)).symm.toContinuousLinearMap

/-- The actual root of the sum of squares equals the genuine finite L²-product norm. -/
theorem familyNorm_eq_piLp (u : I → H) : familyNorm u = ‖familyHilbertMap u‖ := by
  rw [PiLp.norm_eq_of_L2]
  rfl

/-- The finite forcing norm is Lipschitz, with a fixed base-cardinality constant. -/
theorem familyNorm_lipschitz : LipschitzWith ‖(familyHilbertMap : (I → H) →L[ℝ] PiLp 2 (fun _ : I => H))‖₊
    (familyNorm : (I → H) → ℝ) := by
  have h := lipschitzWith_one_norm.comp (familyHilbertMap : (I → H) →L[ℝ] PiLp 2 (fun _ : I => H)).lipschitzWith
  simpa only [one_mul, Function.comp_def, ← familyNorm_eq_piLp] using h

/-- The actual scalar finite-family norm represented in Bochner L² time. -/
def familyNormTime (T : ℝ) (u : TimeLp T (I → H)) : TimeLp T ℝ :=
  familyNorm_lipschitz.compLp (by simp [familyNorm, familySquaredNorm]) u

/-- This scalar Bochner element is the literal family forcing norm almost everywhere. -/
theorem familyNormTime_ae (T : ℝ) (u : TimeLp T (I → H)) :
    (familyNormTime T u : ℝ → ℝ) =ᵐ[timeMeasure T] fun t => familyNorm (u t) :=
  familyNorm_lipschitz.coeFn_compLp (by simp [familyNorm, familySquaredNorm]) u

/-- Strong L²-time forcing convergence gives strong convergence of its actual finite-family norm. -/
theorem familyNormTime_tendsto (T : ℝ) (u : ℕ → TimeLp T (I → H)) (v : TimeLp T (I → H))
    (hu : Filter.Tendsto u Filter.atTop (𝓝 v)) :
    Filter.Tendsto (fun n => familyNormTime T (u n)) Filter.atTop (𝓝 (familyNormTime T v)) :=
  (familyNorm_lipschitz.continuous_compLp (by simp [familyNorm, familySquaredNorm])).continuousAt.tendsto.comp hu


end EulerFamilyNormTime
