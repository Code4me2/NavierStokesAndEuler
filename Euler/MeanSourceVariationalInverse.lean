import Euler.MeanBoundaryCoercivity
import Euler.MeanVariationalInverse

/-!
The mean inverse with the source's actual nonlocal boundary operator.
The boundary lower bound is proved from the spatial hypotheses (5), not an input.
-/

noncomputable section

namespace EulerMeanSourceInverse

open MeasureTheory Set InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanHarmonic EulerMeanBoundary EulerLiftedPressure EulerTimeLp
  EulerMeanVariationalInverse EulerTransverseVariationalInverse
open scoped NNReal

def effectiveNegativeBound (Be Bc r : ℝ) : ℝ :=
  Be + boundaryLocalizationC2 * Bc * r^3

theorem effectiveNegativeBound_nonneg (Be Bc r : ℝ)
    (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hr : 0 ≤ r) :
    0 ≤ effectiveNegativeBound Be Bc r := by
  unfold effectiveNegativeBound
  have hc := boundaryLocalizationC2_nonneg
  positivity

theorem source_smallness (T K Be Bc r : ℝ)
    (hsmall : K*(T^2/2) + Be*T + boundaryLocalizationC2*Bc*r^3*T ≤ 1/2) :
    K*(T^2/2) + effectiveNegativeBound Be Bc r * T ≤ 1/2 := by
  calc
    _ = K*(T^2/2) + Be*T + boundaryLocalizationC2*Bc*r^3*T := by
      unfold effectiveNegativeBound
      ring
    _ ≤ _ := hsmall

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
  (M : Space → Space →L[ℝ] Space) (hM : AEStronglyMeasurable M volume)
  (C : ℝ≥0) (hC : ∀ x, ‖M x‖ ≤ C)
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖^2 ≤ ⟪M x v, v⟫_ℝ)
  (FInv H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
  (hsmall : K*(T^2/2) + Be*T + boundaryLocalizationC2*Bc*r^3*T ≤ 1/2)

/-- This is the actual Lax–Milgram mean inverse, with spatial coercivity discharged. -/
def sourceMeanSolver : TimeLp T L2 →L[ℝ] meanDerivatives T hT FInv :=
  meanSolver T hT FInv H (coefficientOperator M hM C hC)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L K (effectiveNegativeBound Be Bc r)
    hK (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0 hH
    (scaled_mean_boundary_lower_bound ℓ hℓ M hM C hC Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall)




end EulerMeanSourceInverse
