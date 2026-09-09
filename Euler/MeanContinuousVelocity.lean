import Euler.MeanVelocityPressure
import Euler.MeanTimeContinuousTranslation

/-!
# Uniform-time spatial bounds for the actual mean velocity

The continuous velocity is reconstructed from its actual L² value and actual
L² time derivative. Terminal-primitive uniqueness identifies this path with
the physical velocity already constructed by the strong mean inverse.
-/

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanTimeContinuousTranslation EulerTimeH1Reconstruction
  EulerTimeLp EulerVolterraConvolution EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The continuous time path constructed from the actual B and B_t. -/
def continuousVelocity : C(Icc (0 : ℝ) T, L2) :=
  reconstruction T hT (s.velocityField, s.velocityDerivative)

/-- This reconstruction is exactly the physical representative, at every time. -/
theorem continuousVelocity_eq_physicalPath (hTpos : 0 < T)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) : s.continuousVelocity t = s.physicalPath t := by
  have hh := s.physical_h1 hF
  exact reconstruction_eq_path T hTpos s.velocityField s.velocityDerivative s.physicalPath
    hh.1 hh.2.1 hh.2.2 t

/-- The actual continuous velocity inherits spatial regularity uniformly in time. -/
theorem continuousVelocity_translation_contDiff {n : ℕ∞ω}
    (hB : ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityField))
    (hBt : ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityDerivative)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a s.continuousVelocity) :=
  reconstruction_translation_contDiff T hT s.velocityField s.velocityDerivative hB hBt




end EulerMeanVariationalInverse.StrongMeanEvolution
