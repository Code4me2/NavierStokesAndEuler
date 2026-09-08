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

/-- The bounded linear formula has its literal pointwise representative. -/
theorem meanVelocityMap_ae (T : ℝ) (hT : 0 ≤ T)
    (FInv F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T L2) :
    (meanVelocityMap T hT FInv F₁ u : ℝ → L2) =ᵐ[timeMeasure T]
      fun t => u t - extendPath T hT F₁ t (extendPath T hT FInv t (realPrimitive T u t)) := by
  filter_upwards [Lp.coeFn_sub u
      (timeMultiplier T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u))),
    timeMultiplier_ae T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u)),
    timeMultiplier_ae T hT FInv (primitiveTimeLp T hT u), primitiveTimeLp_ae T hT u]
    with t hsub hF₁ hInv hp
  simp only [Pi.sub_apply] at hsub
  change (u-timeMultiplier T hT F₁ (timeMultiplier T hT FInv (primitiveTimeLp T hT u))) t = _
  rw [hsub, hF₁, hInv, hp]


namespace StrongMeanEvolution

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- Differentiating the actual displacement reconstruction gives the kinetic identity. -/
theorem kinetic_ae
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    ∀ᵐ t ∂timeMeasure T,
      u t = extendPath T hT F₁ t (s.label t : L2) + s.physicalPath t := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, operatorPath_hasDerivAt_ae T hT F F₁ hF,
    s.label_derivative, realPrimitive_hasDerivAt_ae T u] with t ht hFt hzt hut
  have hzt' := solenoidalSpace.subtypeL.hasFDerivAt.comp_hasDerivAt t hzt
  have hprod := hFt.clm_apply hzt'
  have heq : realPrimitive T u =ᶠ[𝓝 t]
      fun r => extendPath T hT F r (s.label r : L2) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    have h := ((congrArg (fun x : L2 => F ⟨r, hr⟩ x) (s.label_eq ⟨r, hr⟩)).trans
      (hRight ⟨r, hr⟩ _)).symm
    simpa only [extendPath, projIcc_of_mem hT hr] using h
  exact hut.unique (hprod.congr_of_eventuallyEq heq)


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
