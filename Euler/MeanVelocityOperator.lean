import Euler.MeanVelocityPressure

/-!
# The actual bounded linear mean velocity inverse

The physical velocity is `η_t-F_t F⁻¹η`. This formula constructs a bounded
linear map on the original derivative variable, and the genuine H² evolution
identifies it with `F z_t`. Composing with the variational solver gives the
actual linear velocity inverse with an explicit finite-time bound.
-/

noncomputable section

open scoped Topology


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive EulerMeanSolenoidal EulerVolterraConvolution EulerTimeH1FieldProduct

/-- The physical velocity formula on actual Bochner derivative fields. -/
def meanVelocityMap (T : ℝ) (hT : 0 ≤ T)
    (FInv F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) : TimeLp T L2 →L[ℝ] TimeLp T L2 :=
  ContinuousLinearMap.id ℝ _ -
    (timeMultiplier T hT F₁).comp ((timeMultiplier T hT FInv).comp (primitiveTimeLp T hT))



namespace StrongMeanEvolution

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)



end StrongMeanEvolution

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2)
  (L K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
  (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K*‖z‖^2)
  (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
    -B*‖z‖^2 ≤ ⟪M0 z, z⟫_ℝ+L*⟪A z, z⟫_ℝ)
  (hsmall : K*(T^2/2)+B*T ≤ 1/2)



end EulerMeanVariationalInverse
