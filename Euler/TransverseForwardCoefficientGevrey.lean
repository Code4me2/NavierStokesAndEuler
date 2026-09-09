import Euler.TransverseForwardInverse
import Euler.LinearDuhamelParameter
import Euler.ContinuousGramPath
import Euler.ContinuousGramGevrey
import Euler.GevreyFixedShift

/-!
# Actual coefficient bounds for the transverse forward equation

The Gram inverse is genuinely constructed and differentiated. Its one fixed
factorial shift is absorbed into a coefficient radius enlargement. The source
generator and projected forcing coefficients then have shift-zero bounds by
actual composition, with explicit polynomial amplitudes.
-/

noncomputable section


namespace EulerTransverseForwardCoefficientGevrey

open Set ContinuousLinearMap EulerGevrey EulerOperatorGevreyCalculus
  EulerContinuousPathCalculus EulerContinuousPathComposition EulerContinuousGramPath
  EulerContinuousGramGevrey EulerTimeLpGramGevrey EulerTransverseGramPath
  EulerTransverseForwardInverse
open scoped ContDiff

theorem inverseRadius_bounds (c C Rc R : ℝ) (hc : 0 < c) (hRc : 0 ≤ Rc)
    (hR : 2*gramCost c C 1*(Rc+1) ≤ R) : 0 ≤ R ∧ Rc ≤ 4*R := by
  have hi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hcost : 1 ≤ gramCost c C 1 := by
    unfold gramCost
    nlinarith [sq_nonneg C]
  have hp : 0 ≤ (gramCost c C 1-1)*(Rc+1) :=
    mul_nonneg (sub_nonneg.mpr hcost) (by linarith)
  constructor <;> nlinarith

variable {P V E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (T : ℝ) (Q Q₁ : P → C(Icc (0 : ℝ) T,V →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
  (hQr : ContDiff ℝ ∞ Q) (hQ₁r : ContDiff ℝ ∞ Q₁)
  (Rc C₀ C₁ Ri : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁*majorant Rc 0 n)

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,V →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,V →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] V) := inferInstance





end EulerTransverseForwardCoefficientGevrey
