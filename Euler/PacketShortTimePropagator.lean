import Euler.ShortTimeLinearGrowth
import Euler.PacketSourcePropagator
import Euler.PacketParentForwardBudget

/-! The first-packet homogeneous estimate follows from the actual constructed
coordinate evolution. Its coefficient is bounded by the source deformation
and its first time derivative; determinant one supplies the inverse bound.
The resulting forward budget has constant profile one and propagator cost two. -/

noncomputable section

namespace EulerPacketSourcePropagator

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerSourceForwardCoefficient EulerVolterraConvolution
  EulerTransverseGramInverse EulerPacketPiola EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

private local instance : NormedRing (U →L[ℝ] U) := inferInstance
private local instance : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

def shortTimeRate (C C₁ : ℝ) : ℝ := 2*(1+3*C^2)^2*C*C₁

theorem shortTimeRate_nonneg (C C₁ : ℝ) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) :
    0 ≤ shortTimeRate C C₁ := by
  unfold shortTimeRate
  positivity

variable (D : Data U)

theorem sourceGenerator_norm_le (C C₁ : ℝ) (hC : 0 ≤ C) (_hC₁ : 0 ≤ C₁)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det=1)
    (hF : ∀ t x, ‖D.F.field t x‖ ≤ C)
    (hF₁ : ∀ t x, ‖D.F₁.field t x‖ ≤ C₁)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower t x‖ ≤
      shortTimeRate C C₁ := by
  have hQ : ‖D.frame.field t x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using D.frame_spatial_bound 0 C
      (fun r y => by simpa only [norm_iteratedFDeriv_zero] using hF r y) t x
  have hQ₁ : ‖D.frameDerivative.field t x‖ ≤ C₁ := by
    simpa only [norm_iteratedFDeriv_zero] using D.frameDerivative_spatial_bound 0 C₁
      (fun r y => by simpa only [norm_iteratedFDeriv_zero] using hF₁ r y) t x
  have hi := (gramInverse_norm (D.frame.field t x) D.frameLower D.frameLower_pos
    (D.frame_lower t x)).trans (D.frameLower_inv_le_of_frame C hC hdet hF)
  have hprod : ‖(D.frame.field t x).adjoint.comp (D.frameDerivative.field t x)‖ ≤ C*C₁ := by
    apply (opNorm_comp_le _ _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul hQ hQ₁ (norm_nonneg _) hC
  change ‖(-2 : ℝ) • (gramInverse (D.frame.field t x) D.frameLower D.frameLower_pos
    (D.frame_lower t x)).comp ((D.frame.field t x).adjoint.comp (D.frameDerivative.field t x))‖ ≤ _
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left ((opNorm_comp_le _ _).trans
    (mul_le_mul hi hprod (norm_nonneg _) (sq_nonneg _))) (by norm_num)).trans_eq
  unfold shortTimeRate
  ring

/-- A localized coefficient bound suffices; no estimate outside S enters. -/
theorem propagator_norm_le_two (S : Set Space) (L : ℝ) (hL : 0 ≤ L)
    (hB : ∀ t : Icc (0 : ℝ) D.T, ∀ x ∈ S,
      ‖sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower t x‖ ≤ L)
    (hshort : L*D.T ≤ 1/2)
    (t s : Icc (0 : ℝ) D.T) (hst : s ≤ t) (x : Space) (hx : x ∈ S) :
    ‖propagator D t s x‖ ≤ 2 := by
  let B := sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
  apply (propagator D t s x).opNorm_le_bound (by norm_num)
  intro v
  let f' : ℝ → U := fun r => extendPath D.T D.T_pos.le B r x (coordinate D s x v r)
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt (coordinate D s x v) (f' r) (Icc (0 : ℝ) D.T) r := by
    simpa only [f',extendPath,projIcc_of_mem D.T_pos.le hr] using
      coordinate_hasDerivWithinAt D s ⟨r,hr⟩ x v
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      ‖f' r‖ ≤ L*‖coordinate D s x v r‖ := by
    simp only [f',extendPath,projIcc_of_mem D.T_pos.le hr]
    exact ((B ⟨r,hr⟩ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hB ⟨r,hr⟩ x hx) (norm_nonneg _))
  have h := EulerShortTimeLinearGrowth.norm_le_two D.T L hL (coordinate D s x v) f'
    hd hb hshort s t hst
  simpa only [coordinate_at,propagator_self] using h



end EulerPacketSourcePropagator
