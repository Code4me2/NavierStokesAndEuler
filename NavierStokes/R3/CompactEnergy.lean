import NavierStokes.SolutionDifference
import NavierStokes.PeriodicIntegration
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import NavierStokes.R3.CompactTimeIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NavierStokes.ProblemStatement
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Support
import NavierStokes.WithTopLemmas

/-!
# Energy of compactly supported fields on Euclidean three-space

All integrals in this module are the standard Lebesgue volume integrals on
`ProblemStatement.Space`. Compact support supplies integrability; no finite
replacement measure or convention about nonintegrable functions is used.
-/


noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.SolutionDifference

theorem compact_inner_left {f g : Space → Space} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => ⟪f x, g x⟫_ℝ) := by
  apply hf.mono
  intro x hx
  contrapose! hx
  simp only [mem_support, not_not] at hx ⊢
  rw [hx, inner_zero_left]



theorem compact_component {f : Space → Space} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (fun x => f x i) :=
  hf.comp_left (g := fun v : Space => v i) rfl

theorem integrable_inner_left {f g : Space → Space} (hf : Continuous f)
    (hg : Continuous g) (hcf : HasCompactSupport f) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) :=
  (hf.inner hg).integrable_of_hasCompactSupport (compact_inner_left hcf)

theorem compact_partial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (spatialPartial i f) :=
  hf.fderiv_apply ℝ (coordinateVector i)

theorem integral_partial_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, spatialPartial i f x) = 0 := by
  have hi : Integrable (spatialPartial i f) :=
    (spatial_partial_contDiff hf i).continuous.integrable_of_hasCompactSupport
    (compact_partial hcf i)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Space => (1 : ℝ)) (g := f) (v := coordinateVector i)
    (by simp)
    (by simpa only [spatialPartial, one_mul] using! hi)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hcf)
    (fun x _ => differentiableAt_const (1 : ℝ)) (fun x _ => hf.differentiable (by simp) x)
  simpa [spatialPartial] using h

theorem integral_mul_partial {f g : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, f x * spatialPartial i g x) =
      -(∫ x, g x * spatialPartial i f x) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := f) (g := g) (v := coordinateVector i)
    (((spatial_partial_contDiff hf i).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (compact_partial hcf i).mul_right)
    ((hf.continuous.mul (spatial_partial_contDiff hg i).continuous).integrable_of_hasCompactSupport
      hcf.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)
  simpa only [spatialPartial, mul_comm] using h

/-- Integration against a compactly supported vector field transfers a
directional derivative to its divergence. -/
theorem integral_fderiv_apply {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hcv : HasCompactSupport v) :
    (∫ x, fderiv ℝ f x (v x)) =
      -(∫ x, f x * ∑ i : Fin 3, spatialPartial i v x i) := by
  have hleft : (fun x => fderiv ℝ f x (v x)) =
      (fun x => ∑ i : Fin 3, v x i * spatialPartial i f x) := by
    funext x
    exact fderiv_apply_eq_sum f x (v x)
  have hright : (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, f x * spatialPartial i v x i) := by
    funext x
    exact Finset.mul_sum _ _ _
  have hIl (i : Fin 3) : Integrable (fun x => v x i * spatialPartial i f x) :=
    ((component_contDiff hv i).continuous.mul (spatial_partial_contDiff hf i).continuous).integrable_of_hasCompactSupport
      (compact_component hcv i).mul_right
  have hIr (i : Fin 3) : Integrable (fun x => f x * spatialPartial i v x i) :=
    (hf.continuous.mul (component_contDiff (spatial_partial_contDiff hv i) i).continuous).integrable_of_hasCompactSupport
      (compact_component (compact_partial hcv i) i).mul_left
  rw [hleft, hright, integral_finsetSum _ (fun i _ => hIl i),
    integral_finsetSum _ (fun i _ => hIr i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := integral_mul_partial (component_contDiff hv i) hf (compact_component hcv i) i
  simpa only [spatialPartial, fderiv_component hv] using h



theorem integral_inner_partial {f g : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, ⟪f x, spatialPartial i g x⟫_ℝ) =
      -(∫ x, ⟪spatialPartial i f x, g x⟫_ℝ) := by
  have h := integral_partial_eq_zero (hf.inner ℝ hg) (compact_inner_left hcf) i
  have hfun : spatialPartial i (fun x => ⟪f x, g x⟫_ℝ) =
      (fun x => ⟪f x, spatialPartial i g x⟫_ℝ + ⟪spatialPartial i f x, g x⟫_ℝ) := by
    funext x
    exact fderiv_inner hf hg x (coordinateVector i)
  rw [hfun] at h
  dsimp only [spatialPartial] at h ⊢
  rw [integral_add (integrable_inner_left hf.continuous
      (spatial_partial_contDiff hg i).continuous hcf)
    (integrable_inner_left (spatial_partial_contDiff hf i).continuous hg.continuous
      (compact_partial hcf i))] at h
  exact eq_neg_of_add_eq_zero_left h
















end NavierStokesR3.CompactEnergy
