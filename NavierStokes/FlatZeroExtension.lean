import NavierStokes.FlatCutoff
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Jointly smooth zero extension from locally uniform Gaussian bounds

The bounds concern the actual full Fréchet derivative tensors of a function
on `U × (0,∞)`. They are uniform in a neighborhood of each parameter point.
Every tensor is extended by zero. One extra inverse power in the Gaussian
bound proves that its derivative at the edge is zero, using
`δ ≤ ‖(p,δ) - (p₀,0)‖`. No pointwise-to-joint limit inference is used.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.FlatZeroExtension

open FlatCutoff

variable {E F : Type*}

section Zero

variable [Zero F]

/-- Preserve positive edge distance and use zero on the other side. -/
def zeroExtension (f : E × ℝ → F) (p : E × ℝ) : F :=
  if 0 < p.2 then f p else 0


theorem zeroExtension_of_nonpos (f : E × ℝ → F) {p : E × ℝ} (hp : p.2 ≤ 0) :
    zeroExtension f p = 0 := ite_eq_right (not_lt_of_ge hp)

@[simp] theorem zeroExtension_edge (f : E × ℝ → F) (x : E) :
    zeroExtension f (x, 0) = 0 := zeroExtension_of_nonpos f le_rfl

variable [TopologicalSpace E]



end Zero

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem edge_div_pow_tendsto_zero {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun δ : ℝ => edge c δ / δ ^ N) (𝓝 0) (𝓝 0) := by
  simpa only [iteratedDeriv_zero] using weighted_iteratedDeriv_tendsto_zero hc 0 N












end NavierStokes.FlatZeroExtension
