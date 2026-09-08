import Euler.MeanHarmonicDecomposition
import Euler.MeanMollificationHarmonic
import Euler.MeanHarmonicComponents
import Euler.MeanLocalL2Energy

/-! The proved harmonic interior bound for the actual weak L² solution. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal

/-- A scalar distributionally harmonic L² field has a uniform a.e. interior bound. -/
theorem weakScalarHarmonic_pointwise (f : Space → ℝ) (hf : MemLp f 2 volume)
    (hh : ScalarWeakHarmonicOn (Metric.ball (0 : Space) 1) f) :
    ∀ᵐ x ∂volume, x ∈ Metric.closedBall (0 : Space) (1/4 : ℝ) →
      f x ^ 2 ≤ harmonicQuarterBallConstant * lpNorm f 2 volume ^ 2 := by
  apply ae_bound_of_scalarMollification_bound f hf
  intro n x hx
  calc
    _ ≤ harmonicQuarterBallConstant *
        lpNorm (scalarMollification (interiorMollifier n) f) 2 volume ^ 2 :=
      harmonic_pointwise_quarterBall_sq _
        (scalarMollification_smooth (interiorMollifier n) f hf)
        (scalarMollification_memLp (interiorMollifier n) f hf)
        (interiorMollifier_harmonic f hf hh n) x hx
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (scalarMollification_energy_le (interiorMollifier n) f hf)
      harmonicQuarterBallConstant_nonneg


def weakHarmonicSmallBallConstant : ℝ := (Real.pi * 4 / 3) * harmonicQuarterBallConstant

theorem weakHarmonicSmallBallConstant_nonneg : 0 ≤ weakHarmonicSmallBallConstant := by
  unfold weakHarmonicSmallBallConstant
  exact mul_nonneg (by positivity) harmonicQuarterBallConstant_nonneg


end EulerMeanHarmonic
