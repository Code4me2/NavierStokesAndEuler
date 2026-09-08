import Euler.LpDerivativeBundling
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Pointwise multilinear L² fields define genuine bounded multilinear maps into L². -/

noncomputable section


namespace EulerLpDerivative

open MeasureTheory Filter

variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X) (n : ℕ)

def multilinearBundling : Lp (P [×n]→L[ℝ] V) 2 μ →L[ℝ] (P [×n]→L[ℝ] Lp V 2 μ) := by
  let ev : P [×n]→L[ℝ] ((P [×n]→L[ℝ] V) →L[ℝ] V) :=
    (ContinuousLinearMap.id ℝ (P [×n]→L[ℝ] V)).flipMultilinear
  let lift : ((P [×n]→L[ℝ] V) →L[ℝ] V) →L[ℝ]
      (Lp (P [×n]→L[ℝ] V) 2 μ →L[ℝ] Lp V 2 μ) :=
    ContinuousLinearMap.compLpL₂ (𝕜 := ℝ) (E := P [×n]→L[ℝ] V) (F := V)
      (G := (P [×n]→L[ℝ] V) →L[ℝ] V) 2 μ
      (ContinuousLinearMap.id ℝ ((P [×n]→L[ℝ] V) →L[ℝ] V))
  exact (lift.compContinuousMultilinearMap ev).flipLinear

theorem multilinearBundling_ae (D : Lp (P [×n]→L[ℝ] V) 2 μ) (v : Fin n → P) :
    multilinearBundling (P := P) (V := V) μ n D v =ᵐ[μ] fun x => D x v := by
  let L : (P [×n]→L[ℝ] V) →L[ℝ] V :=
    (ContinuousLinearMap.id ℝ (P [×n]→L[ℝ] V)).flipMultilinear v
  exact ContinuousLinearMap.coeFn_compLp (𝕜 := ℝ) (𝕜' := ℝ)
    (E := P [×n]→L[ℝ] V) (F := V) (σ := RingHom.id ℝ) L D



end EulerLpDerivative
