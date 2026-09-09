import Euler.GraphPressurePotential
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Radial reconstruction of a canonically normalized scalar potential. -/

noncomputable section

namespace EulerCanonicalGraphPotential

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace
open scoped ContDiff

/-- The scalar radial integral of a spatial vector field, based at the origin. -/
def radialPotential (V : Vector3 → Vector3) (x : Vector3) : ℝ :=
  ∫ s in (0 : ℝ)..1, ⟪V (s • x), x⟫_ℝ

/-- The radial integral is normalized to vanish at the origin. -/
theorem radialPotential_zero (V : Vector3 → Vector3) : radialPotential V 0 = 0 := by
  simp [radialPotential]

/-- The fundamental theorem of calculus identifies the radial integral with a normalized genuine potential. -/
theorem radialPotential_eq_sub (V : Vector3 → Vector3) (hV : Continuous V)
    (q : Vector3 → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x)
    (x : Vector3) : radialPotential V x = q x - q 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => q (r • x)) ⟪V (s • x), x⟫_ℝ s := by
    have h := ((hq.differentiable (by simp)) (s • x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x)
    simpa only [Function.comp_def, id_eq, one_smul, ← inner_gradient_left, hgrad] using h
  have hi : IntervalIntegrable (fun s : ℝ => ⟪V (s • x), x⟫_ℝ) volume 0 1 :=
    ((hV.comp (continuous_id.smul continuous_const)).inner continuous_const).intervalIntegrable 0 1
  simpa only [radialPotential, one_smul, zero_smul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi

/-- A radial reconstruction of a genuine smooth gradient is itself spatially smooth. -/
theorem radialPotential_smooth (V : Vector3 → Vector3) (hV : Continuous V)
    (q : Vector3 → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x) :
    ContDiff ℝ ∞ (radialPotential V) := by
  have he : radialPotential V = fun x => q x - q 0 :=
    funext (radialPotential_eq_sub V hV q hq hgrad)
  rw [he]
  exact hq.sub contDiff_const

/-- Radial normalization preserves the actual gradient. -/
theorem radialPotential_gradient (V : Vector3 → Vector3) (hV : Continuous V)
    (q : Vector3 → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x)
    (x : Vector3) : gradient (radialPotential V) x = V x := by
  have he : radialPotential V = fun x => q x - q 0 :=
    funext (radialPotential_eq_sub V hV q hq hgrad)
  rw [he, gradient, fderiv_sub_const]
  exact hgrad x


end EulerCanonicalGraphPotential
