import NavierStokes.CorrectionState
import NavierStokes.WaveInteractionBounds
import NavierStokes.HarmonicResidual

/-!
# Covariance of actual finite real harmonic fields

Angular integration is evaluated exactly before applying the weighted product
estimates. Real projection includes both conjugate harmonics. The constants are
uniform over a fixed bound on the harmonic index.
-/

noncomputable section

namespace NavierStokes.HarmonicCovariance

open Set Filter MeasureTheory CorrectionState
open scoped BigOperators ContDiff Topology

section CoefficientCovariance

open HarmonicFields WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


end CoefficientCovariance

section RealCoefficientCovariance

open HarmonicFields WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realAngularProduct_eq (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : D) :
    HarmonicResidual.realAngularMean (fun θ =>
      (field a k Φ kp (x, θ)).re * (field b k Φ kp (x, θ)).re) =
      (HarmonicFields.angularMean (fun θ =>
        field (HarmonicResidual.realCoefficients a) k Φ kp (x, θ) *
        field (HarmonicResidual.realCoefficients b) k Φ kp (x, θ))).re := by
  have hc := HarmonicFields.angularMean_field
    (HarmonicResidual.realCoefficients a * HarmonicResidual.realCoefficients b) k Φ hkp x
  simp only [HarmonicFields.field_mul] at hc
  rw [hc]
  simpa only [HarmonicFields.field_mul, HarmonicResidual.field_realCoefficients,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    HarmonicResidual.realAngularMean_field
      (HarmonicResidual.realCoefficients a * HarmonicResidual.realCoefficients b) k Φ hkp x







end RealCoefficientCovariance

end NavierStokes.HarmonicCovariance
