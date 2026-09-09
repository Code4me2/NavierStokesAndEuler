import Euler.EulerProof.PacketGrowth

/-!
# Packet frames, existence and stage bookkeeping

From the ray system to a single self-similar stage:

* `EulerPacketBridge` -- the bridge between the ideal velocities and the ray
  system (`idealVelocityFirst`).
* `EulerPacketFrameStability`, `EulerPacketFrameRenewal`,
  `EulerPacketFrameQuantitative` -- stability of the moving frame, its renewal
  across stages (`idealTargetPressure`, `idealTargetCross`) and the
  quantitative form of both.
* `EulerPacketExistence` -- a global Picard-Lindelof existence theorem
  (`GlobalPicard`) and its application to the scalar packet field.
* `EulerPacketStage`, `EulerPacketCoefficientControl`,
  `EulerPacketTargetCompression` -- the constants for one stage, control of the
  coefficients along it, and the compression of the target.

This is part 7 of 8 of the former monolithic `Euler.EulerProof`; see `Euler.EulerProof`
for the layout of the whole file.
-/

noncomputable section

section

open Set

namespace EulerPacketBridge

open EulerPacketGrowth EulerPacketPerturbation EulerPacketRay

/-- The first component of the ideal normalized velocity vector field. -/
noncomputable def idealVelocityFirst (β t U V : ℝ) : ℝ :=
  -2 * V + 2 * (β * t ^ 2) * (((β * t ^ 2) + β) * V + (-2 * β * t) * U) /
    (1 + (β * t ^ 2) ^ 2)

/-- The exact forced scalar flux equation obtained from the two velocity
components.  The forcing is the actual vector-field discrepancy. -/
theorem velocity_scalar_flux
    {β t u₁ v₁ : ℝ} {U V : ℝ → ℝ}
    (hU : HasDerivAt U u₁ t) (hV : HasDerivAt V v₁ t) :
    HasDerivAt V (-U t + (v₁ + U t)) t ∧
    HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * (-U s))
      (2 * (1 - β * (β * t ^ 2)) * V t + (1 + (β * t ^ 2) ^ 2) *
        (-u₁ + idealVelocityFirst β t (U t) (V t))) t := by
  refine ⟨hV.congr_deriv (by ring), ?_⟩
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply (hD.mul hU.neg).congr_deriv
  have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
  dsimp [idealVelocityFirst]
  field_simp
  ring

theorem continuousOn_idealVelocityFirst
    {β : ℝ} {I : Set ℝ} {U V : ℝ → ℝ}
    (hU : ContinuousOn U I) (hV : ContinuousOn V I) :
    ContinuousOn (fun t => idealVelocityFirst β t (U t) (V t)) I := by
  unfold idealVelocityFirst
  have hden : ∀ t ∈ I, 1 + (β * t ^ 2) ^ 2 ≠ 0 := by intro t _; positivity
  have hId : ContinuousOn (fun t : ℝ => t) I := continuousOn_id
  fun_prop



theorem continuousOn_velocity_rhs
    {ε : ℝ} {I : Set ℝ} {A C : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N U V : ℝ → ℝ}
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) I)
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) I)
    (hP : ContinuousOn P I) (hQ : ContinuousOn Q I) (hN : ContinuousOn N I)
    (hU : ContinuousOn U I) (hV : ContinuousOn V I)
    (hNne : ∀ t ∈ I, N t ≠ 0) :
    ContinuousOn (fun t => velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) I ∧
    ContinuousOn (fun t => velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) I := by
  have hW : ContinuousOn (fun t => velocityThird (P t) (Q t) (N t) (U t) (V t)) I := by
    unfold velocityThird
    exact ((hP.mul hU).add (hQ.mul hV)).neg.div hN hNne
  have hD : ContinuousOn (fun t => rayDenominator ε (P t) (Q t) (N t)) I := by
    unfold rayDenominator
    fun_prop
  have hDne : ∀ t ∈ I, rayDenominator ε (P t) (Q t) (N t) ≠ 0 := by
    intro t ht
    have hn : 0 < N t ^ 2 := sq_pos_of_ne_zero (hNne t ht)
    unfold rayDenominator
    positivity
  have hJ : ContinuousOn (fun t => velocityNumerator (A t) (P t) (Q t) (N t)
      (U t) (V t) (velocityThird (P t) (Q t) (N t) (U t) (V t))) I := by
    unfold velocityNumerator
    fun_prop
  constructor
  · exact ((((hCc 0 0).mul hU).add ((hCc 0 1).mul hV)).add
      ((hCc 0 2).mul hW)).neg.add (((hP.const_mul 2).mul hJ).div hD hDne)
  · exact ((((hCc 1 0).mul hU).add ((hCc 1 1).mul hV)).add
      ((hCc 1 2).mul hW)).neg.add (((hQ.const_mul (2 * ε ^ 2)).mul hJ).div hD hDne)


end EulerPacketBridge

end

section

open Set

namespace EulerPacketFrameStability

open Real EulerPacketGrowth EulerPacketPerturbation EulerPacketRay EulerPacketBridge

/-- Exact relation between the original and inverted logarithmic slopes. -/
theorem inverted_logarithmic_identity
    {ε y : ℝ} {V V₁ : ℝ → ℝ} (hε : ε ≠ 0) (hy : y ≠ 0)
    (hV : V (y⁻¹ / ε) ≠ 0) :
    y ^ 2 * (-ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y) - ε * y =
      V₁ (y⁻¹ / ε) / V (y⁻¹ / ε) := by
  have halg (v w : ℝ) (hv : v ≠ 0) :
      y ^ 2 * (-ε * (-v / y ^ 2 - w / (ε * y ^ 3)) / (v / y)) - ε * y = w / v := by
    field_simp
    ring
  exact halg (V (y⁻¹ / ε)) (V₁ (y⁻¹ / ε)) hV

/-- The logarithmic slope is bounded uniformly in the initial nonnegative
slope after time one. -/
theorem equation30_primary_logderivative_bound
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 1 ≤ t → |V₁ t / V t| ≤ 4 := by
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t htpos.le
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := equation30_positive (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨htpos.le, hpre⟩
    have hu := equation30_log_derivative_upper (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨htpos, hpre⟩
    have hnonneg : 0 ≤ V₁ t / V t := div_nonneg hp.2 hVp.le
    rw [abs_of_nonneg hnonneg]
    have hinv : 1 / t ≤ 1 := (div_le_one htpos).mpr ht
    linarith
  · have hεt : 1 ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp (le_of_not_ge hpre)
      nlinarith only [hh]
    let y := 1 / (ε * t)
    have hy : 0 < y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := by dsimp [y]; exact (div_le_one (by positivity)).mpr hεt
    have harg : y⁻¹ / ε = t := by dsimp [y]; rw [one_div, inv_inv]; field_simp
    have hz := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy hy1
    have hid := inverted_logarithmic_identity (V₁ := V₁) hεne (ne_of_gt hy)
      (show V (y⁻¹ / ε) ≠ 0 by rw [harg]; exact ne_of_gt hVp)
    rw [harg] at hid
    let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
    have hz0 : 0 ≤ z := hz.1
    have hz4 : z ≤ 4 := hz.2
    have hy2 : y ^ 2 ≤ 1 := by nlinarith only [hy.le, hy1]
    have hmul := mul_le_mul_of_nonneg_left hz4 (sq_nonneg y)
    have hepsy : 0 ≤ ε * y := mul_nonneg hε.le hy.le
    have hepsyUpper : ε * y ≤ 1 := by nlinarith only [hε, hεsmall, hy.le, hy1]
    have hzmul : 0 ≤ y ^ 2 * z := mul_nonneg (sq_nonneg y) hz0
    apply abs_le.mpr
    dsimp [z] at hmul hzmul
    constructor <;> nlinarith only [hid, hmul, hepsy, hepsyUpper, hzmul, hy2]

/-- The ideal pressure numerator has the sign required for the next-frame
construction, throughout the forward evolution. -/
theorem equation30_ideal_numerator_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 0 ≤ t → ε ^ 2 * V t ≤
      (ε ^ 2 * t ^ 2 + ε ^ 2) * V t + 2 * ε ^ 2 * t * V₁ t := by
  intro t ht
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := equation30_positive (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨ht, hpre⟩
    have h₁ := mul_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg t)) hVp.le
    have h₂ := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * ε ^ 2) ht) hp.2
    nlinarith only [h₁, h₂]
  · have hpost : 1 / ε ≤ t := le_of_not_ge hpre
    have hposit := equation30_post_inversion_positive_derivative hε hεsmall hV hflux hV0 hV₁0 t hpost
    have hεt : 1 ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp hpost
      nlinarith only [hh]
    have hεt2 : 1 ≤ ε ^ 2 * t ^ 2 := by nlinarith only [hεt]
    have hε2 : 2 * ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
    have h₁ := mul_nonneg (show 0 ≤ ε ^ 2 * t ^ 2 - 2 * ε ^ 2 by linarith) hVp.le
    have h₂ := mul_nonneg (by positivity : 0 ≤ 2 * ε ^ 2) hposit.le
    nlinarith only [h₁, h₂]

/-- Relative control of both components gives positivity and control of
the logarithmic ratio without dividing by an uncontrolled quantity. -/
theorem relative_state_error_consequences
    {U V Z Z₁ η : ℝ} (hZ : 0 < Z) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (herror : |V - Z| + |U + Z₁| ≤ η * Z) (hslope : |Z₁ / Z| ≤ 4) :
    0 < V ∧ |V / Z - 1| ≤ η ∧ |U / V + Z₁ / Z| ≤ 10 * η := by
  have hVerror : |V - Z| ≤ η * Z := by linarith [abs_nonneg (U + Z₁)]
  have hUerror : |U + Z₁| ≤ η * Z := by linarith [abs_nonneg (V - Z)]
  have hVlower : Z / 2 ≤ V := by
    have hh := (abs_le.mp hVerror).1
    have hm := mul_le_mul_of_nonneg_right hηsmall hZ.le
    nlinarith only [hh, hm]
  have hVp : 0 < V := by linarith only [hZ, hVlower]
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hVne : V ≠ 0 := ne_of_gt hVp
  have hZ₁abs : |Z₁| ≤ 4 * Z := by
    rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ] at hslope
    exact hslope
  refine ⟨hVp, ?_, ?_⟩
  · have hid : V / Z - 1 = (V - Z) / Z := by field_simp
    rw [hid, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    exact hVerror
  · have hnum : |U * Z + Z₁ * V| ≤ 5 * η * Z ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_right hUerror hZ.le
      have h₂ := mul_le_mul hZ₁abs hVerror (abs_nonneg _) (by positivity : 0 ≤ 4 * Z)
      have ht := abs_add_le ((U + Z₁) * Z) (Z₁ * (V - Z))
      rw [abs_mul, abs_mul, abs_of_pos hZ] at ht
      have hid : (U + Z₁) * Z + Z₁ * (V - Z) = U * Z + Z₁ * V := by ring
      rw [hid] at ht
      nlinarith only [ht, h₁, h₂]
    have hid : U / V + Z₁ / Z = (U * Z + Z₁ * V) / (V * Z) := by field_simp
    rw [hid, abs_div, abs_of_pos (mul_pos hVp hZ), div_le_iff₀ (mul_pos hVp hZ)]
    have hm := mul_le_mul_of_nonneg_right hVlower (by positivity : 0 ≤ 10 * η * Z)
    nlinarith only [hnum, hm]

/-- Stability relative to the growing primary solution, with constants
independent of its nonnegative initial slope. -/
theorem equation30_relative_state_consequences
    {ε lam δ t U V : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam) (ht : 1 ≤ t)
    (hδ : 0 ≤ δ) (hsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : |V - Z t| + |U + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V ∧ |V / Z t - 1| ≤ 2 * exp 6 * δ ∧
      |U / V + Z₁ t / Z t| ≤ 20 * exp 6 * δ := by
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0pos t (by linarith)
  have hlower := equation30_slope_uniform_lower hε hεsmall hlam hF hZ hfluxF hfluxZ
    hF0 hF₁0 hZ0 hZ₁0 t ht
  have hslope := equation30_primary_logderivative_bound hε hεsmall hZ hfluxZ hZ0 hZ₁0pos t ht
  have hη : 0 ≤ 2 * exp 6 * δ := by positivity
  have hηsmall : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hsmall]
  have hrelative : |V - Z t| + |U + Z₁ t| ≤ (2 * exp 6 * δ) * Z t := by
    calc
      |V - Z t| + |U + Z₁ t| ≤ δ * (1 + lam) * F t := herror
      _ = (2 * exp 6 * δ) * (((1 + lam) / (2 * exp 6)) * F t) := by field_simp
      _ ≤ (2 * exp 6 * δ) * Z t := mul_le_mul_of_nonneg_left hlower hη
  obtain ⟨hv, hratio, hs⟩ := relative_state_error_consequences hZpos hη hηsmall hrelative hslope
  refine ⟨hv, hratio, ?_⟩
  nlinarith only [hs]

/-- Division of the pressure-numerator error is safe once positivity and
the logarithmic-ratio bounds have been derived. -/
theorem pressure_ratio_error
    {Θ η j P₀ Q₀ β U V r₀ J : ℝ}
    (hΘ : 1 ≤ Θ) (_hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (hj : 0 ≤ j)
    (hV : 0 < V) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2) (hr₀ : |r₀| ≤ 4)
    (hr : |U / V - r₀| ≤ 10 * η)
    (hJ : |J - ((P₀ + β) * V + Q₀ * U)| ≤ j * (|U| + |V|)) :
    |J / V - (P₀ + β + Q₀ * r₀)| ≤ 10 * j + 20 * Θ ^ 2 * η := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hrabs : |U / V| ≤ 9 := by
    have hh := abs_add_le (U / V - r₀) r₀
    have hid : U / V - r₀ + r₀ = U / V := by ring
    rw [hid] at hh
    nlinarith only [hh, hr, hr₀, hηsmall]
  have hUabs : |U| ≤ 9 * V := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV] at hrabs
    exact hrabs
  have hJdiv : |(J - ((P₀ + β) * V + Q₀ * U)) / V| ≤ 10 * j := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]
    rw [abs_of_pos hV] at hJ
    have hm := mul_le_mul_of_nonneg_left hUabs hj
    nlinarith only [hJ, hm]
  have hQerr : |Q₀ * (U / V - r₀)| ≤ 20 * Θ ^ 2 * η := by
    rw [abs_mul]
    have hh := mul_le_mul hQ₀ hr (abs_nonneg _) (by positivity : 0 ≤ 2 * Θ ^ 2)
    nlinarith only [hh]
  have hid : J / V - (P₀ + β + Q₀ * r₀) =
      (J - ((P₀ + β) * V + Q₀ * U)) / V + Q₀ * (U / V - r₀) := by field_simp; ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hJdiv hQerr)


/-- The third normalized velocity ratio follows from orthogonality and
the already controlled ray and first velocity ratio. -/
theorem third_ratio_error
    {Θ ρ η P Q N P₀ Q₀ r r₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hr₀ : |r₀| ≤ 4) (hr : |r - r₀| ≤ 10 * η) :
    |r| ≤ 9 ∧ |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2 ∧
      |velocityThird P Q N r 1| ≤ 60 * Θ ^ 2 ∧
      |velocityThird P Q N r 1 - (-(P₀ * r₀ + Q₀))| ≤ (32 * ρ + 20 * η) * Θ ^ 2 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hrabs : |r| ≤ 9 := by
    have hh := abs_add_le (r - r₀) r₀
    have hid : r - r₀ + r₀ = r := by ring
    rw [hid] at hh
    nlinarith only [hh, hr, hr₀, hηsmall]
  have hw₀ : |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2 := by
    rw [abs_neg]
    have hh := abs_add_le (P₀ * r₀) Q₀
    rw [abs_mul] at hh
    have hm := mul_le_mul hP₀ hr₀ (abs_nonneg _) (sq_nonneg Θ)
    nlinarith only [hh, hm, hQ₀]
  obtain ⟨hn, _, _, _, hw, _, _⟩ :=
    ray_geometric_bounds (ε := 0) (U := r) (V := 1) hΘ hρ hρsmall hP₀ hQ₀ hP hQ hN
  have hwabs : |velocityThird P Q N r 1| ≤ 60 * Θ ^ 2 := by
    norm_num only [abs_one] at hw
    have hm := mul_le_mul_of_nonneg_left hrabs (by positivity : 0 ≤ 6 * Θ ^ 2)
    nlinarith only [hw, hm]
  have hNpos : 0 < N := by linarith only [hn]
  have hNne : N ≠ 0 := ne_of_gt hNpos
  let w₀ := -(P₀ * r₀ + Q₀)
  have hPr := abs_product_difference hP hr hP₀ hrabs
  have hNw : |(N - 1) * w₀| ≤ 6 * ρ * Θ ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hN hw₀ (abs_nonneg _) hρ
    nlinarith only [hh]
  have hsum : |(P * r - P₀ * r₀) + (Q - Q₀) + (N - 1) * w₀| ≤
      (16 * ρ + 10 * η) * Θ ^ 2 := by
    have h₁ := abs_add_le (P * r - P₀ * r₀) (Q - Q₀)
    have h₂ := abs_add_le ((P * r - P₀ * r₀) + (Q - Q₀)) ((N - 1) * w₀)
    have hm := mul_le_mul_of_nonneg_left hΘ2 (by positivity : 0 ≤ 10 * ρ)
    nlinarith only [h₁, h₂, hPr, hQ, hNw, hm]
  refine ⟨hrabs, hw₀, hwabs, ?_⟩
  have hid : velocityThird P Q N r 1 - w₀ =
      -((P * r - P₀ * r₀) + (Q - Q₀) + (N - 1) * w₀) / N := by
    dsimp [velocityThird, w₀]
    field_simp
    ring
  change |velocityThird P Q N r 1 - w₀| ≤ _
  rw [hid, abs_div, abs_neg, abs_of_pos hNpos, div_le_iff₀ hNpos]
  have hm := mul_le_mul_of_nonneg_left hn
    (by positivity : 0 ≤ (32 * ρ + 20 * η) * Θ ^ 2)
  nlinarith only [hsum, hm]

/-- A normalized parent-gradient row applied to the velocity ratios. -/
def rowAction (A : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (r w : ℝ) : ℝ :=
  A i 0 * r + A i 1 + A i 2 * w

/-- Rowwise control of the normalized parent action on the new velocity. -/
theorem normalized_action_error
    {Θ e β r w : ℝ} {A : Fin 3 → Fin 3 → ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hr : |r| ≤ 9) (hw : |w| ≤ 60 * Θ ^ 2)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e) :
    |rowAction A 0 r w - 1| ≤ 70 * e * Θ ^ 2 ∧
    |rowAction A 1 r w - r| ≤ 70 * e * Θ ^ 2 ∧
    |rowAction A 2 r w - β| ≤ 70 * e * Θ ^ 2 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hnorm : norm3 r 1 w ≤ 70 * Θ ^ 2 := by
    unfold norm3
    norm_num only [abs_one]
    nlinarith only [hr, hw, hΘ2]
  have hrow : ∀ i, |(A i 0 - idealVelocityEntry β i 0) * r +
      (A i 1 - idealVelocityEntry β i 1) * 1 + (A i 2 - idealVelocityEntry β i 2) * w| ≤
      70 * e * Θ ^ 2 := by
    intro i
    have hh := three_term_bound (p := r) (q := 1) (n := w) (hA i 0) (hA i 1) (hA i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm he
    nlinarith only [hh, hm]
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  norm_num [idealVelocityEntry, Fin.ext_iff] at h0 h1 h2
  constructor
  · convert! h0 using 1
    unfold rowAction
    congr 1
    ring
  constructor
  · convert! h1 using 1
    unfold rowAction
    congr 1
    ring
  · convert! h2 using 1
    unfold rowAction
    congr 1
    ring

/-- The cross-product numerator for the next normalized coupling.
The middle argument `Tq` denotes ε times the physical middle component. -/
def frameCrossNumerator (ε P Q N r w Tp Tq Tn : ℝ) : ℝ :=
  (-N + ε ^ 2 * Q * w) * Tp + (N * r - P * w) * Tq + (P - ε ^ 2 * Q * r) * Tn

/-- The ideal next-frame cross numerator in original scalar coordinates. -/
def idealCrossNumerator (β P Q r : ℝ) : ℝ :=
  -1 + β * P + (1 + P ^ 2) * r ^ 2 + P * Q * r

/-- Quantitative stability of the exact cross-product numerator. -/
theorem frame_cross_numerator_error
    {Θ ρ η σ ε β P Q N P₀ Q₀ r r₀ w Tp Tq Tn : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hσ : 0 ≤ σ)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hP : |P - P₀| ≤ ρ) (hQ : |Q| ≤ 3 * Θ ^ 2)
    (hN : |N - 1| ≤ ρ) (hr₀ : |r₀| ≤ 4) (hrabs : |r| ≤ 9)
    (hr : |r - r₀| ≤ 10 * η) (hwabs : |w| ≤ 60 * Θ ^ 2)
    (hw₀ : |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2)
    (hw : |w - (-(P₀ * r₀ + Q₀))| ≤ (32 * ρ + 20 * η) * Θ ^ 2)
    (hTp : |Tp - 1| ≤ σ) (hTq : |Tq - r₀| ≤ σ + 10 * η) (hTn : |Tn - β| ≤ σ)
    (hTpabs : |Tp| ≤ 2) (hTqabs : |Tq| ≤ 10) (hTnabs : |Tn| ≤ 2) :
    |frameCrossNumerator ε P Q N r w Tp Tq Tn - idealCrossNumerator β P₀ Q₀ r₀| ≤
      (1100 * ρ + 400 * η + 12 * σ + 500 * ε ^ 2) * Θ ^ 4 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
  have h24 : Θ ^ 2 ≤ Θ ^ 4 := pow_le_pow_right₀ hΘ (by decide)
  let w₀ := -(P₀ * r₀ + Q₀)
  let c₀ := -N + ε ^ 2 * Q * w
  let c₁ := N * r - P * w
  let c₂ := P - ε ^ 2 * Q * r
  let c₁₀ := r₀ - P₀ * w₀
  have hQw : |ε ^ 2 * Q * w| ≤ 180 * ε ^ 2 * Θ ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hQ hwabs (abs_nonneg _) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    nlinarith only [hm]
  have hQr : |ε ^ 2 * Q * r| ≤ 27 * ε ^ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hQ hrabs (abs_nonneg _) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    nlinarith only [hm]
  have hc₀ : |c₀ - (-1)| ≤ ρ + 180 * ε ^ 2 * Θ ^ 4 := by
    have hh := abs_add_le (-(N - 1)) (ε ^ 2 * Q * w)
    rw [abs_neg] at hh
    have hid : c₀ - (-1) = -(N - 1) + ε ^ 2 * Q * w := by dsimp [c₀]; ring
    rw [hid]
    linarith only [hh, hN, hQw]
  have hc₂ : |c₂ - P₀| ≤ ρ + 27 * ε ^ 2 * Θ ^ 2 := by
    have hh := abs_add_le (P - P₀) (-(ε ^ 2 * Q * r))
    rw [abs_neg] at hh
    have hid : c₂ - P₀ = (P - P₀) + -(ε ^ 2 * Q * r) := by dsimp [c₂]; ring
    rw [hid]
    linarith only [hh, hP, hQr]
  have hNr := abs_product_difference hN hr (by norm_num : |(1 : ℝ)| ≤ 1) hrabs
  have hPw := abs_product_difference hP hw hP₀ hwabs
  have hc₁ : |c₁ - c₁₀| ≤ (101 * ρ + 30 * η) * Θ ^ 4 := by
    have hh := abs_add_le (N * r - r₀) (-(P * w - P₀ * w₀))
    rw [abs_neg] at hh
    have hid : c₁ - c₁₀ = (N * r - r₀) + -(P * w - P₀ * w₀) := by dsimp [c₁, c₁₀]; ring
    rw [hid]
    have hm₁ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 9 * ρ)
    have hm₂ := mul_le_mul_of_nonneg_left h24 (by positivity : 0 ≤ 60 * ρ)
    have hm₃ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 10 * η)
    norm_num only [one_mul] at hNr
    nlinarith only [hh, hNr, hPw, hm₁, hm₂, hm₃]
  have hc₁₀ : |c₁₀| ≤ 10 * Θ ^ 4 := by
    have hh := abs_add_le r₀ (-(P₀ * w₀))
    rw [abs_neg, abs_mul] at hh
    have hm := mul_le_mul hP₀ hw₀ (abs_nonneg _) (sq_nonneg Θ)
    change |r₀ - P₀ * w₀| ≤ _
    have hid : r₀ + -(P₀ * w₀) = r₀ - P₀ * w₀ := by ring
    rw [hid] at hh
    nlinarith only [hh, hr₀, hm, hΘ4]
  have hS₀ := abs_product_difference hc₀ hTp (by norm_num : |(-1 : ℝ)| ≤ 1) hTpabs
  have hS₁ := abs_product_difference hc₁ hTq hc₁₀ hTqabs
  have hS₂ := abs_product_difference hc₂ hTn hP₀ hTnabs
  have hsum := abs_add_le (c₀ * Tp - (-1) * 1) (c₁ * Tq - c₁₀ * r₀)
  have hsum' := abs_add_le ((c₀ * Tp - (-1) * 1) + (c₁ * Tq - c₁₀ * r₀))
    (c₂ * Tn - P₀ * β)
  have hid : frameCrossNumerator ε P Q N r w Tp Tq Tn - idealCrossNumerator β P₀ Q₀ r₀ =
      (c₀ * Tp - (-1) * 1) + (c₁ * Tq - c₁₀ * r₀) + (c₂ * Tn - P₀ * β) := by
    dsimp [frameCrossNumerator, idealCrossNumerator, c₀, c₁, c₂, c₁₀, w₀]
    ring
  rw [hid]
  have hmρ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 4 * ρ)
  have hmσ := mul_le_mul_of_nonneg_left hΘ4 hσ
  have hmσ2 := mul_le_mul_of_nonneg_left h24 hσ
  have hmε := mul_le_mul_of_nonneg_left h24 (by positivity : 0 ≤ 54 * ε ^ 2)
  have hpρ : 0 ≤ 86 * ρ * Θ ^ 4 := by positivity
  have hpε : 0 ≤ 86 * ε ^ 2 * Θ ^ 4 := by positivity
  nlinarith only [hsum, hsum', hS₀, hS₁, hS₂, hmρ, hmσ, hmσ2, hmε, hpρ, hpε]

/-- The cross numerator bound with every velocity-ratio and parent-action
estimate derived from ray, state, and matrix coefficient errors. -/
theorem frame_cross_error_from_matrix
    {Θ ρ η e ε β P Q N P₀ Q₀ r r₀ : ℝ} {A : Fin 3 → Fin 3 → ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (he : 0 ≤ e)
    (hsmall : 70 * e * Θ ^ 2 ≤ 1) (hβ : |β| ≤ 1)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hr₀ : |r₀| ≤ 4) (hr : |r - r₀| ≤ 10 * η)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e) :
    let w := velocityThird P Q N r 1
    |frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w) -
      idealCrossNumerator β P₀ Q₀ r₀| ≤
        (1100 * ρ + 400 * η + 840 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4 := by
  let w := velocityThird P Q N r 1
  obtain ⟨hrabs, hw₀, hwabs, hw⟩ := third_ratio_error hΘ hρ hρsmall hη hηsmall
    hP₀ hQ₀ hP hQ hN hr₀ hr
  obtain ⟨hTp, hTq, hTn⟩ := normalized_action_error hΘ he hrabs hwabs hA
  have hTq' : |rowAction A 1 r w - r₀| ≤ 70 * e * Θ ^ 2 + 10 * η := by
    have hh := abs_add_le (rowAction A 1 r w - r) (r - r₀)
    have hid : rowAction A 1 r w - r + (r - r₀) = rowAction A 1 r w - r₀ := by ring
    rw [hid] at hh
    linarith only [hh, hTq, hr]
  have hTpabs : |rowAction A 0 r w| ≤ 2 := by
    have hh := abs_add_le (rowAction A 0 r w - 1) 1
    norm_num at hh
    linarith only [hh, hTp, hsmall]
  have hTqabs : |rowAction A 1 r w| ≤ 10 := by
    have hh := abs_add_le (rowAction A 1 r w - r) r
    have hid : rowAction A 1 r w - r + r = rowAction A 1 r w := by ring
    rw [hid] at hh
    linarith only [hh, hTq, hsmall, hrabs]
  have hTnabs : |rowAction A 2 r w| ≤ 2 := by
    have hh := abs_add_le (rowAction A 2 r w - β) β
    have hid : rowAction A 2 r w - β + β = rowAction A 2 r w := by ring
    rw [hid] at hh
    linarith only [hh, hTn, hsmall, hβ]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q - Q₀) Q₀
    have hid : Q - Q₀ + Q₀ = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    linarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hh := frame_cross_numerator_error (ε := ε) hΘ hρ hη
    (by positivity : 0 ≤ 70 * e * Θ ^ 2) hP₀ hP hQabs hN hr₀ hrabs hr hwabs hw₀ hw
    hTp hTq' hTn hTpabs hTqabs hTnabs
  dsimp only
  nlinarith only [hh]

/-- Squared norm of the normalized velocity direction. -/
def velocityDirectionNormSq (ε r w : ℝ) : ℝ := 1 + ε ^ 2 * (r ^ 2 + w ^ 2)

theorem velocity_direction_norm_bound
    {Θ ε r w : ℝ} (hΘ : 1 ≤ Θ) (hr : |r| ≤ 9) (hw : |w| ≤ 60 * Θ ^ 2) :
    1 ≤ velocityDirectionNormSq ε r w ∧
      velocityDirectionNormSq ε r w - 1 ≤ 3681 * ε ^ 2 * Θ ^ 4 := by
  have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
  have hr2 : r ^ 2 ≤ 81 := by
    have hh := (sq_le_sq₀ (abs_nonneg r) (by norm_num : (0 : ℝ) ≤ 9)).mpr hr
    rw [sq_abs] at hh
    norm_num at hh
    exact hh
  have hw2 : w ^ 2 ≤ 3600 * Θ ^ 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg w) (by positivity : 0 ≤ 60 * Θ ^ 2)).mpr hw
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hsum : r ^ 2 + w ^ 2 ≤ 3681 * Θ ^ 4 := by nlinarith only [hr2, hw2, hΘ4]
  have hm := mul_le_mul_of_nonneg_left hsum (sq_nonneg ε)
  unfold velocityDirectionNormSq
  constructor
  · nlinarith only [mul_nonneg (sq_nonneg ε) (add_nonneg (sq_nonneg r) (sq_nonneg w))]
  · nlinarith only [hm]

end EulerPacketFrameStability

end

section

open Set

namespace EulerPacketFrameRenewal

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability

/-- Square-root normalization preserves an error from the unit value. -/
theorem sqrt_unit_error
    {E d : ℝ} (hE : 1 ≤ E) (herror : E - 1 ≤ d) (hd : d ≤ 1) :
    1 ≤ sqrt E ∧ sqrt E ≤ 2 ∧ |sqrt E - 1| ≤ d := by
  have hs : 1 ≤ sqrt E := Real.one_le_sqrt.mpr hE
  have hself : sqrt E ≤ E := Real.sqrt_le_self_iff.mpr (Or.inr hE)
  refine ⟨hs, by linarith, ?_⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ sqrt E - 1)]
  linarith

/-- The ray square root is uniformly stable away from zero. -/
theorem sqrt_ray_error
    {D D₀ d : ℝ} (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀) (herror : |D - D₀| ≤ d) :
    1 / 2 ≤ sqrt D ∧ |sqrt D - sqrt D₀| ≤ d := by
  have hD0 : 0 ≤ D := by linarith
  have hD₀0 : 0 ≤ D₀ := by linarith
  have hsq := sq_sqrt hD0
  have hsq₀ := sq_sqrt hD₀0
  have hs0 := sqrt_nonneg D
  have hs₀ : 1 ≤ sqrt D₀ := Real.one_le_sqrt.mpr hD₀
  have hsum : 1 ≤ sqrt D + sqrt D₀ := by linarith
  have hid : (sqrt D - sqrt D₀) * (sqrt D + sqrt D₀) = D - D₀ := by nlinarith only [hsq, hsq₀]
  have hh : |sqrt D - sqrt D₀| * (sqrt D + sqrt D₀) ≤ d := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ sqrt D + sqrt D₀), ← abs_mul, hid]
    exact herror
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (sqrt D - sqrt D₀))
  constructor <;> nlinarith only [hD, hsq, hs0, hh, hm]

/-- Stability of the next-frame expansion coefficient under perturbation
of the pressure numerator and both normalization factors. -/
theorem expansion_quotient_error
    {D D₀ E J J₀ dD dE dJ M aerr : ℝ}
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀) (hE : 1 ≤ E)
    (hDE : |D - D₀| ≤ dD) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - J₀| ≤ dJ) (hJ₀ : |J₀| ≤ M) (hroot : sqrt D₀ ≤ M)
    (hideal : |J₀ / sqrt D₀ - 1| ≤ aerr) :
    |J / (sqrt D * sqrt E) - 1| ≤
      aerr + 4 * dJ + 4 * M * (2 * dD + M * dE) := by
  obtain ⟨hrootD, hrootDiff⟩ := sqrt_ray_error hD hD₀ hDE
  obtain ⟨hrootE, hrootE2, hrootEE⟩ := sqrt_unit_error hE hEE hdE
  have hrootD₀ : 1 ≤ sqrt D₀ := Real.one_le_sqrt.mpr hD₀
  have hM : 0 ≤ M := (abs_nonneg _).trans hJ₀
  have hden : 1 / 4 ≤ sqrt D * sqrt E := by
    have hh := mul_le_mul hrootD hrootE (by norm_num : (0 : ℝ) ≤ 1) (sqrt_nonneg D)
    nlinarith only [hh]
  have hdenDiff : |sqrt D * sqrt E - sqrt D₀| ≤ 2 * dD + M * dE := by
    have hh := abs_product_difference hrootDiff hrootEE
      (show |sqrt D₀| ≤ M by rw [abs_of_nonneg (sqrt_nonneg D₀)]; exact hroot)
      (show |sqrt E| ≤ 2 by rw [abs_of_nonneg (sqrt_nonneg E)]; exact hrootE2)
    simpa only [mul_one, mul_comm dD 2] using hh
  have hdiff := quotient_difference_bound hden hrootD₀ hJE hJ₀ hdenDiff
  have ht := abs_add_le (J / (sqrt D * sqrt E) - J₀ / sqrt D₀) (J₀ / sqrt D₀ - 1)
  have hid : J / (sqrt D * sqrt E) - J₀ / sqrt D₀ + (J₀ / sqrt D₀ - 1) =
      J / (sqrt D * sqrt E) - 1 := by ring
  rw [hid] at ht
  nlinarith only [ht, hdiff, hideal]

/-- Quotient stability when the reference denominator is at least one half. -/
theorem quotient_error_half_denominator
    {a a₀ b b₀ da db M : ℝ}
    (hb : 1 / 4 ≤ b) (hb₀ : 1 / 2 ≤ b₀)
    (ha : |a - a₀| ≤ da) (ha₀ : |a₀| ≤ M) (hbb : |b - b₀| ≤ db) :
    |a / b - a₀ / b₀| ≤ 8 * da + 16 * M * db := by
  have ha2 : |2 * a - 2 * a₀| ≤ 2 * da := by
    have hid : 2 * a - 2 * a₀ = 2 * (a - a₀) := by ring
    rw [hid, abs_mul]
    norm_num
    linarith only [ha]
  have ha₀2 : |2 * a₀| ≤ 2 * M := by rw [abs_mul]; norm_num; linarith only [ha₀]
  have hb2 : |2 * b - 2 * b₀| ≤ 2 * db := by
    have hid : 2 * b - 2 * b₀ = 2 * (b - b₀) := by ring
    rw [hid, abs_mul]
    norm_num
    linarith only [hbb]
  have hh := quotient_difference_bound (show (1 : ℝ) / 4 ≤ 2 * b by linarith)
    (show (1 : ℝ) ≤ 2 * b₀ by linarith) ha2 ha₀2 hb2
  have hbe : b ≠ 0 := by linarith
  have hb₀e : b₀ ≠ 0 := by linarith
  have h₁ : 2 * a / (2 * b) = a / b := by field_simp
  have h₂ : 2 * a₀ / (2 * b₀) = a₀ / b₀ := by field_simp
  rw [h₁, h₂] at hh
  nlinarith only [hh]

/-- Stability of the next coupling multiplied by the target scale squared. -/
theorem coupling_quotient_error
    {P₀ E J J₀ S S₀ dE dJ dS berr : ℝ}
    (hP₀ : 0 < P₀) (hE : 1 ≤ E) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - J₀| ≤ dJ) (hJEsmall : dJ ≤ P₀ / 4)
    (hJ₀ : 1 / 2 ≤ J₀ / P₀) (hJ₀upper : J₀ / P₀ ≤ 2)
    (hSE : |S - S₀| ≤ dS) (hS₀ : |S₀| ≤ 20)
    (hideal : |S₀ / (J₀ / P₀) - 1| ≤ berr) :
    |P₀ * S / (J * sqrt E) - 1| ≤ berr + 8 * dS + 640 * (dJ / P₀) + 640 * dE := by
  have hP₀ne : P₀ ≠ 0 := ne_of_gt hP₀
  obtain ⟨hrootE, hrootE2, hrootEE⟩ := sqrt_unit_error hE hEE hdE
  have hJscaled : |J / P₀ - J₀ / P₀| ≤ dJ / P₀ := by
    rw [← sub_div, abs_div, abs_of_pos hP₀]
    exact div_le_div_of_nonneg_right hJE hP₀.le
  have hJsmall : dJ / P₀ ≤ 1 / 4 := (div_le_iff₀ hP₀).mpr (by nlinarith only [hJEsmall])
  have hJlower : 1 / 4 ≤ J / P₀ := by
    have hh := (abs_le.mp hJscaled).1
    nlinarith only [hh, hJ₀, hJsmall]
  have hden : 1 / 4 ≤ (J / P₀) * sqrt E := by
    have hh := mul_le_mul hJlower hrootE (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ J / P₀)
    nlinarith only [hh]
  have hJ₀abs : |J₀ / P₀| ≤ 2 := by rw [abs_of_nonneg (by linarith : 0 ≤ J₀ / P₀)]; exact hJ₀upper
  have hdenDiff : |(J / P₀) * sqrt E - J₀ / P₀| ≤ 2 * (dJ / P₀) + 2 * dE := by
    have hh := abs_product_difference hJscaled hrootEE hJ₀abs
      (show |sqrt E| ≤ 2 by rw [abs_of_nonneg (sqrt_nonneg E)]; exact hrootE2)
    simpa only [mul_one, mul_comm (dJ / P₀) 2] using hh
  have hdiff := quotient_error_half_denominator hden hJ₀ hSE hS₀ hdenDiff
  have hJpos : 0 < J := by
    have hh : 0 < J / P₀ := by linarith only [hJlower]
    exact (div_pos_iff_of_pos_right hP₀).mp hh
  have hid : P₀ * S / (J * sqrt E) = S / ((J / P₀) * sqrt E) := by field_simp
  rw [hid]
  have ht := abs_add_le (S / ((J / P₀) * sqrt E) - S₀ / (J₀ / P₀)) (S₀ / (J₀ / P₀) - 1)
  have hsum : S / ((J / P₀) * sqrt E) - S₀ / (J₀ / P₀) + (S₀ / (J₀ / P₀) - 1) =
      S / ((J / P₀) * sqrt E) - 1 := by ring
  rw [hsum] at ht
  nlinarith only [ht, hdiff, hideal]

/-- Absolute bounds for the ideal inversion-coordinate frame quantities. -/
theorem ideal_frame_absolute_bounds
    {ε y z : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2) (hz : 0 ≤ z) (hzupper : z ≤ 4) :
    idealFrameDenominator ε y z ≤ 2 ∧ |idealFrameNumerator ε y z| ≤ 20 := by
  have hy2 : y ^ 2 ≤ 1 / 4 := by nlinarith only [hy, hysmall]
  have hy3 : y ^ 3 ≤ 1 / 8 := by
    have hh := pow_le_pow_left₀ hy hysmall 3
    norm_num at hh
    exact hh
  have hy4 : y ^ 4 ≤ 1 / 16 := by
    have hh := pow_le_pow_left₀ hy hysmall 4
    norm_num at hh
    exact hh
  have hz2 : z ^ 2 ≤ 16 := by nlinarith only [hz, hzupper]
  have hε2 : ε ^ 2 ≤ 1 / 16 := by nlinarith only [hε, hεsmall]
  have hT : ε ^ 2 * y ^ 2 ≤ 1 / 64 := by
    have hh := mul_le_mul hε2 hy2 (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith only [hh]
  have hZ : (1 + y ^ 4) * z ^ 2 ≤ 17 := by
    have hh := mul_le_mul (show 1 + y ^ 4 ≤ 17 / 16 by linarith only [hy4]) hz2
      (sq_nonneg z) (by norm_num : (0 : ℝ) ≤ 17 / 16)
    nlinarith only [hh]
  have hεz : ε * z ≤ 1 := by
    have hh := mul_le_mul hεsmall hzupper hz (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [hh]
  have hU : 2 * ε * z * y ^ 3 ≤ 1 / 4 := by
    have hh := mul_le_mul hεz hy3 (pow_nonneg hy 3) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hh]
  have hT0 : 0 ≤ ε ^ 2 * y ^ 2 := mul_nonneg (sq_nonneg ε) (sq_nonneg y)
  have hZ0 : 0 ≤ (1 + y ^ 4) * z ^ 2 := by positivity
  have hU0 : 0 ≤ 2 * ε * z * y ^ 3 := by positivity
  constructor
  · unfold idealFrameDenominator
    nlinarith only [hT0, hU]
  · unfold idealFrameNumerator
    apply abs_le.mpr
    constructor <;> nlinarith only [hT0, hZ0, hU0, hT, hZ, hU]

theorem target_sqrt_identity {y : ℝ} (hy : y ≠ 0) :
    sqrt (1 + (y⁻¹) ^ 4) = sqrt (1 + y ^ 4) / y ^ 2 := by
  have hid : 1 + (y⁻¹) ^ 4 = (1 + y ^ 4) / (y ^ 2) ^ 2 := by field_simp; ring
  rw [hid, Real.sqrt_div (by positivity : 0 ≤ 1 + y ^ 4), sqrt_sq (sq_nonneg y)]

/-- Ideal frame renewal expressed directly in the original scalar
solution and the target time, rather than in auxiliary Riccati variables. -/
theorem equation30_target_ideal_quantities
    {ε y : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    let t := y⁻¹ / ε
    let P₀ := ε ^ 2 * t ^ 2
    let Q₀ := -2 * ε ^ 2 * t
    let r₀ := -V₁ t / V t
    let J₀ := P₀ + ε ^ 2 + Q₀ * r₀
    let S₀ := idealCrossNumerator (ε ^ 2) P₀ Q₀ r₀
    1 ≤ P₀ ∧ 1 / 2 ≤ J₀ / P₀ ∧ J₀ / P₀ ≤ 2 ∧ |S₀| ≤ 20 ∧
      |J₀ / sqrt (1 + P₀ ^ 2) - 1| ≤ y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
      |S₀ / (J₀ / P₀) - 1| ≤ 1500 * ε := by
  let t := y⁻¹ / ε
  let P₀ := ε ^ 2 * t ^ 2
  let Q₀ := -2 * ε ^ 2 * t
  let r₀ := -V₁ t / V t
  let J₀ := P₀ + ε ^ 2 + Q₀ * r₀
  let S₀ := idealCrossNumerator (ε ^ 2) P₀ Q₀ r₀
  let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hyne : y ≠ 0 := ne_of_gt hy
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t ht0
  have hPr : P₀ = (y⁻¹) ^ 2 := by dsimp [P₀, t]; field_simp
  have hQr : Q₀ = -2 * ε * y⁻¹ := by dsimp [Q₀, t]; field_simp
  have hr : r₀ = ε * y - z * y ^ 2 := by
    have hh := inverted_logarithmic_identity (V₁ := V₁) hεne hyne (ne_of_gt hVp)
    dsimp [r₀, t, z]
    rw [neg_div]
    nlinarith only [hh]
  have hJr : J₀ = idealFrameDenominator ε y z / y ^ 2 := by
    dsimp [J₀]
    rw [hPr, hQr, hr]
    exact (ideal_frame_identities hyne).1
  have hSr : S₀ = idealFrameNumerator ε y z := by
    dsimp [S₀, idealCrossNumerator]
    rw [hPr, hQr, hr]
    convert! (ideal_frame_identities (ε := ε) (z := z) hyne).2 using 1
    ring
  have hR := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy (by linarith)
  have hB := equation30_ideal_frame_bounds hε hεsmall hV hflux hV0 hV₁0 y hy hysmall
  have hA := ideal_frame_absolute_bounds hε.le hεsmall hy.le hysmall hR.1 hR.2
  have hJP : J₀ / P₀ = idealFrameDenominator ε y z := by rw [hJr, hPr]; field_simp
  have hJroot : J₀ / sqrt (1 + P₀ ^ 2) = idealFrameDenominator ε y z / sqrt (1 + y ^ 4) := by
    rw [hJr, hPr]
    have hid : ((y⁻¹) ^ 2) ^ 2 = (y⁻¹) ^ 4 := by ring
    rw [hid, target_sqrt_identity hyne]
    field_simp
  have hyinv : 1 ≤ y⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hy).mpr (by linarith)
  change 1 ≤ P₀ ∧ 1 / 2 ≤ J₀ / P₀ ∧ J₀ / P₀ ≤ 2 ∧ |S₀| ≤ 20 ∧
    |J₀ / sqrt (1 + P₀ ^ 2) - 1| ≤ _ ∧ |S₀ / (J₀ / P₀) - 1| ≤ _
  rw [hJP, hSr, hJroot]
  refine ⟨?_, hB.1, hA.1, hA.2, hB.2.2.1, hB.2.2.2⟩
  rw [hPr]
  nlinarith only [hyinv]

/-- The perturbed target ray keeps the shear compression strictly negative
with the reciprocal target-time magnitude used in equation (35). -/
theorem perturbed_target_compression
    {β t ε H P Q N ρ : ℝ}
    (hβ : 0 < β) (ht : 0 < t) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hscale : 1 ≤ β * t ^ 2) (_hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2) (hρQ : ρ ≤ β * t)
    (hP : |P - β * t ^ 2| ≤ ρ) (hQ : |Q + 2 * β * t| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hεQ : |ε * Q| ≤ 1 / 2) :
    H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  have hPb := abs_le.mp hP
  have hQb := abs_le.mp hQ
  have hNb := abs_le.mp hN
  have hPlower : β * t ^ 2 / 2 ≤ P := by nlinarith only [hPb, hρsmall, hscale]
  have hPupper : P ≤ 3 / 2 * (β * t ^ 2) := by nlinarith only [hPb, hρsmall, hscale]
  have hPpos : 0 < P := by nlinarith only [hPlower, hscale]
  have hQupper : Q ≤ -β * t := by nlinarith only [hQb, hρQ]
  have hNabs : |N| ≤ 3 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hNb, hρsmall]
  have hPabs : |P| ≤ 3 / 2 * (β * t ^ 2) := by rwa [abs_of_pos hPpos]
  have hPsq : P ^ 2 ≤ 9 / 4 * (β * t ^ 2) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg P) (by positivity : 0 ≤ 3 / 2 * (β * t ^ 2))).mpr hPabs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hNsq : N ^ 2 ≤ 9 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg N) (by norm_num : (0 : ℝ) ≤ 3 / 2)).mpr hNabs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hεQsq : ε ^ 2 * Q ^ 2 ≤ 1 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg (ε * Q)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hεQ
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hscale2 : 1 ≤ (β * t ^ 2) ^ 2 := by nlinarith only [hscale]
  have hDupper : rayDenominator ε P Q N ≤ 5 * β ^ 2 * t ^ 4 := by
    unfold rayDenominator
    nlinarith only [hPsq, hNsq, hεQsq, hscale2]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  have hQP : Q * P ≤ -(β ^ 2 * t ^ 3) / 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hQupper hPpos.le
    have h₂ := mul_le_mul_of_nonneg_left hPlower (mul_nonneg hβ.le ht.le)
    nlinarith only [h₁, h₂]
  have hHε : 0 ≤ H * ε := mul_nonneg hH hε
  have hnum := mul_le_mul_of_nonneg_left hQP hHε
  have hnumtime := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 10 * t)
  have hden := mul_le_mul_of_nonneg_left hDupper hHε
  apply (div_le_div_iff₀ hDpos (by positivity : 0 < 10 * t)).mpr
  nlinarith only [hnumtime, hden]

/-- The coordinate quadratic form of a real three-by-three matrix. -/
def quadraticForm3 (B : Fin 3 → Fin 3 → ℝ) (p q n : ℝ) : ℝ :=
  p * (B 0 0 * p + B 0 1 * q + B 0 2 * n) +
  q * (B 1 0 * p + B 1 1 * q + B 1 2 * n) +
  n * (B 2 0 * p + B 2 1 * q + B 2 2 * n)

theorem quadratic_form_bound
    {B : Fin 3 → Fin 3 → ℝ} {G p q n : ℝ}
    (hB : ∀ i j, |B i j| ≤ G) :
    |quadraticForm3 B p q n| ≤ 3 * G * (p ^ 2 + q ^ 2 + n ^ 2) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hB 0 0)
  have hrow0 := three_term_bound (p := p) (q := q) (n := n) (hB 0 0) (hB 0 1) (hB 0 2)
  have hrow1 := three_term_bound (p := p) (q := q) (n := n) (hB 1 0) (hB 1 1) (hB 1 2)
  have hrow2 := three_term_bound (p := p) (q := q) (n := n) (hB 2 0) (hB 2 1) (hB 2 2)
  have h₀ := mul_le_mul_of_nonneg_left hrow0 (abs_nonneg p)
  have h₁ := mul_le_mul_of_nonneg_left hrow1 (abs_nonneg q)
  have h₂ := mul_le_mul_of_nonneg_left hrow2 (abs_nonneg n)
  have ht0 := abs_add_le (p * (B 0 0 * p + B 0 1 * q + B 0 2 * n))
    (q * (B 1 0 * p + B 1 1 * q + B 1 2 * n))
  have ht1 := abs_add_le
    (p * (B 0 0 * p + B 0 1 * q + B 0 2 * n) + q * (B 1 0 * p + B 1 1 * q + B 1 2 * n))
    (n * (B 2 0 * p + B 2 1 * q + B 2 2 * n))
  simp only [abs_mul] at ht0 ht1
  have hnorm : norm3 p q n ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + n ^ 2) := by
    have h₁ := sq_nonneg (|p| - |q|)
    have h₂ := sq_nonneg (|p| - |n|)
    have h₃ := sq_nonneg (|q| - |n|)
    have hp := sq_abs p
    have hq := sq_abs q
    have hn := sq_abs n
    unfold norm3
    nlinarith only [h₁, h₂, h₃, hp, hq, hn]
  have hm := mul_le_mul_of_nonneg_left hnorm hG
  unfold quadraticForm3 norm3 at *
  nlinarith only [h₀, h₁, h₂, ht0, ht1, hm]

/-- The full normalized compression is the negative shear term plus a
controlled contribution from the older gradient and the packet error. -/
theorem parent_ray_compression
    {B E : Fin 3 → Fin 3 → ℝ} {H ε P Q N G : ℝ}
    (hD : 0 < rayDenominator ε P Q N)
    (hB : ∀ i j, |B i j + E i j| ≤ G) :
    quadraticForm3 (parentEntry B E H) P (ε * Q) N / rayDenominator ε P Q N ≤
      H * ε * Q * P / rayDenominator ε P Q N + 3 * G := by
  have hid : quadraticForm3 (parentEntry B E H) P (ε * Q) N =
      H * ε * Q * P + quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N := by
    norm_num [quadraticForm3, parentEntry, Fin.ext_iff]
    ring
  have hb := quadratic_form_bound (p := P) (q := ε * Q) (n := N) hB
  have hquad : quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N ≤
      3 * G * rayDenominator ε P Q N := by
    have hh := le_abs_self (quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N)
    unfold rayDenominator
    nlinarith only [hh, hb]
  rw [hid, add_div]
  gcongr
  exact (div_le_iff₀ hD).mpr hquad

/-- The ideal pressure-to-velocity ratio at the inverse target scale. -/
noncomputable def idealTargetPressure (ε y : ℝ) (V V₁ : ℝ → ℝ) : ℝ :=
  let t := y⁻¹ / ε
  ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-V₁ t / V t)

/-- The ideal cross numerator at the inverse target scale. -/
noncomputable def idealTargetCross (ε y : ℝ) (V V₁ : ℝ → ℝ) : ℝ :=
  let t := y⁻¹ / ε
  idealCrossNumerator (ε ^ 2) (ε ^ 2 * t ^ 2) (-2 * ε ^ 2 * t) (-V₁ t / V t)

/-- Actual target-frame renewal, with all ideal quantities obtained from
the scalar equation and all perturbation losses displayed explicitly. -/
theorem equation30_target_frame_renewal
    {ε y D E J S dD dE dJ dS : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0)
    (hD : 1 / 4 ≤ D) (hE : 1 ≤ E)
    (hDE : |D - (1 + (y⁻¹) ^ 4)| ≤ dD) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - idealTargetPressure ε y V V₁| ≤ dJ) (hJEsmall : dJ ≤ (y⁻¹) ^ 2 / 4)
    (hSE : |S - idealTargetCross ε y V V₁| ≤ dS) :
    |J / (sqrt D * sqrt E) - 1| ≤
      y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 + 4 * dJ +
        16 * (y⁻¹) ^ 2 * dD + 16 * (y⁻¹) ^ 4 * dE ∧
    |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤
      1500 * ε + 8 * dS + 640 * (dJ / (y⁻¹) ^ 2) + 640 * dE := by
  let t := y⁻¹ / ε
  let P₀ := (y⁻¹) ^ 2
  let J₀ := idealTargetPressure ε y V V₁
  let S₀ := idealTargetCross ε y V V₁
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hPeq : ε ^ 2 * t ^ 2 = P₀ := by dsimp [t, P₀]; field_simp
  have hI := equation30_target_ideal_quantities hε hεsmall hy hysmall hV hflux hV0 hV₁0
  change 1 ≤ ε ^ 2 * t ^ 2 ∧ 1 / 2 ≤ J₀ / (ε ^ 2 * t ^ 2) ∧
    J₀ / (ε ^ 2 * t ^ 2) ≤ 2 ∧ |S₀| ≤ 20 ∧
    |J₀ / sqrt (1 + (ε ^ 2 * t ^ 2) ^ 2) - 1| ≤ _ ∧
    |S₀ / (J₀ / (ε ^ 2 * t ^ 2)) - 1| ≤ _ at hI
  rw [hPeq] at hI
  obtain ⟨hP₀, hJ₀lower, hJ₀upper, hS₀, hAideal, hBideal⟩ := hI
  have hP₀pos : 0 < P₀ := by linarith
  have hJ₀pos : 0 < J₀ := by
    have hh := (le_div_iff₀ hP₀pos).mp hJ₀lower
    nlinarith only [hh, hP₀pos]
  have hJ₀abs : |J₀| ≤ 2 * P₀ := by
    rw [abs_of_pos hJ₀pos]
    exact (div_le_iff₀ hP₀pos).mp hJ₀upper
  have hD₀ : 1 ≤ 1 + P₀ ^ 2 := by nlinarith [sq_nonneg P₀]
  have hroot : sqrt (1 + P₀ ^ 2) ≤ 2 * P₀ := by
    have hh := sq_sqrt (by positivity : 0 ≤ 1 + P₀ ^ 2)
    have hn := sqrt_nonneg (1 + P₀ ^ 2)
    nlinarith only [hh, hn, hP₀]
  have hD₀eq : 1 + P₀ ^ 2 = 1 + (y⁻¹) ^ 4 := by dsimp [P₀]; ring
  have hDE' : |D - (1 + P₀ ^ 2)| ≤ dD := by rwa [hD₀eq]
  have ha := expansion_quotient_error hD hD₀ hE hDE' hEE hdE hJE hJ₀abs hroot hAideal
  have hb := coupling_quotient_error hP₀pos hE hEE hdE hJE hJEsmall hJ₀lower hJ₀upper hSE hS₀ hBideal
  constructor
  · dsimp [P₀] at ha
    nlinarith only [ha]
  · exact hb

end EulerPacketFrameRenewal

end

section

open Set

namespace EulerPacketFrameQuantitative

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability EulerPacketFrameRenewal

/-- Comparison of the polynomial losses on a common time scale. -/
theorem scaled_power_le
    {Θ K e : ℝ} {n m : ℕ} (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hnm : n ≤ m) :
    e * Θ ^ n ≤ K * e * Θ ^ m := by
  have hpow := pow_le_pow_right₀ hΘ hnm
  have hm := mul_le_mul_of_nonneg_left hpow he
  have hKmul := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ e * Θ ^ m)
  nlinarith only [hm, hKmul]

/-- Explicit polynomial control of all target-frame perturbation losses. -/
theorem frame_error_polynomial_bounds
    {Θ K e ε P₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hP₀ : 1 ≤ P₀) (hP₀upper : P₀ ≤ Θ ^ 2) :
    let ρ := 800 * e * Θ ^ 5
    let η := K * e * Θ ^ 29
    let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
    let dE := 3681 * ε ^ 2 * Θ ^ 4
    let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
    let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
    ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
      4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
      8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40 := by
  let ρ := 800 * e * Θ ^ 5
  let η := K * e * Θ ^ 29
  let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  let dE := 3681 * ε ^ 2 * Θ ^ 4
  let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
  let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
  let M := K * e * Θ ^ 40
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hKp (n : ℕ) (hn : n ≤ 40) : K * e * Θ ^ n ≤ M := by
    have hh := pow_le_pow_right₀ hΘ hn
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ K * e)
    exact hm
  have he1 : e ≤ 1 := by
    have hh := hp 0 (by decide)
    norm_num at hh
    nlinarith only [hh, hMb]
  have hε1 : ε ≤ 1 := hεe.trans he1
  have hε2 : ε ^ 2 ≤ e := by nlinarith only [hε, hε1, hεe]
  have hεp (n : ℕ) (hn : n ≤ 40) : ε ^ 2 * Θ ^ n ≤ M := by
    have hh := mul_le_mul_of_nonneg_right hε2 (by positivity : 0 ≤ Θ ^ n)
    exact hh.trans (hp n hn)
  have hρb : ρ ≤ 1 / 2 := by have hh := hp 5 (by decide); dsimp [ρ]; nlinarith only [hh, hMb]
  have hηb : η ≤ 1 / 2 := by have hh := hKp 29 (by decide); dsimp [η]; nlinarith only [hh, hMb]
  have hAb : 210 * e * Θ ^ 2 ≤ 1 := by have hh := hp 2 (by decide); nlinarith only [hh, hMb]
  have hEb : dE ≤ 1 := by have hh := hεp 4 (by decide); dsimp [dE]; nlinarith only [hh, hMb]
  have hJbound : dJ ≤ 17490 * M := by
    have h4 := hp 4 (by decide)
    have h5 := hp 5 (by decide)
    have h31 := hKp 31 (by decide)
    dsimp [dJ, ρ, η]
    nlinarith only [h4, h5, h31]
  have hJb : dJ ≤ P₀ / 4 := by nlinarith only [hJbound, hMb, hP₀]
  have hD0 : 0 ≤ dD := by dsimp [dD, ρ]; positivity
  have hE0 : 0 ≤ dE := by dsimp [dE]; positivity
  have hJ0 : 0 ≤ dJ := by dsimp [dJ, ρ, η]; positivity
  have hP₀0 : 0 ≤ P₀ := by linarith
  have hP₀sq : P₀ ^ 2 ≤ Θ ^ 4 := by
    have hh := (sq_le_sq₀ hP₀0 (sq_nonneg Θ)).mpr hP₀upper
    nlinarith only [hh]
  have hPD : P₀ * dD ≤ 4809 * M := by
    have hm := mul_le_mul_of_nonneg_right hP₀upper hD0
    have h9 := hp 9 (by decide)
    have h6 := hεp 6 (by decide)
    dsimp [dD, ρ] at hm ⊢
    nlinarith only [hm, h9, h6]
  have hPE : P₀ ^ 2 * dE ≤ 3681 * M := by
    have hm := mul_le_mul_of_nonneg_right hP₀sq hE0
    have h8 := hεp 8 (by decide)
    dsimp [dE] at hm ⊢
    nlinarith only [hm, h8]
  have hSbound : dS ≤ 883420 * M := by
    have h9 := hp 9 (by decide)
    have h33 := hKp 33 (by decide)
    have h6 := hp 6 (by decide)
    have h4 := hεp 4 (by decide)
    dsimp [dS, ρ, η]
    nlinarith only [h9, h33, h6, h4]
  have hEbound : dE ≤ 3681 * M := by
    have hh := hεp 4 (by decide)
    dsimp [dE]
    nlinarith only [hh]
  have hJdiv : dJ / P₀ ≤ dJ := by
    apply (div_le_iff₀ (by linarith : 0 < P₀)).mpr
    nlinarith only [mul_nonneg hJ0 (sub_nonneg.mpr hP₀)]
  change ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
    4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
    8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40
  dsimp [M] at hJbound hPD hPE hSbound hEbound hM
  refine ⟨hρb, hηb, hAb, hEb, hJb, ?_, ?_⟩
  · nlinarith only [hJbound, hPD, hPE, hM]
  · nlinarith only [hSbound, hJbound, hJdiv, hEbound, hM]

/-- The source's `Θ^40` frame-renewal estimate, derived from coefficient,
ray, and relative state errors and the actual scalar initial value problem. -/
theorem frame_renewal_order40
    {σ y Θ K e ε P Q N r : ℝ} {A : Fin 3 → Fin 3 → ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (htΘ : y⁻¹ / σ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |P - (y⁻¹) ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * σ * y⁻¹| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5)
    (hr : |r + Z₁ (y⁻¹ / σ) / Z (y⁻¹ / σ)| ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |A i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    let w := velocityThird P Q N r 1
    let D := rayDenominator ε P Q N
    let E := velocityDirectionNormSq ε r w
    let J := velocityNumerator A P Q N r 1 w
    let S := frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w)
    |J / (sqrt D * sqrt E) - 1| ≤
      y ^ 4 + σ ^ 2 * y ^ 2 + 8 * σ * y ^ 3 + 30000000 * K * e * Θ ^ 40 ∧
    |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤ 1500 * σ + 30000000 * K * e * Θ ^ 40 := by
  let t := y⁻¹ / σ
  let P₀ := (y⁻¹) ^ 2
  let Q₀ := -2 * σ * y⁻¹
  let r₀ := -Z₁ t / Z t
  let ρ := 800 * e * Θ ^ 5
  let η := K * e * Θ ^ 29
  let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  let dE := 3681 * ε ^ 2 * Θ ^ 4
  let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
  let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
  let w := velocityThird P Q N r 1
  let D := rayDenominator ε P Q N
  let E := velocityDirectionNormSq ε r w
  let J := velocityNumerator A P Q N r 1 w
  let S := frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w)
  have hΘ0 : 0 ≤ Θ := by linarith
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hyinv0 : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
  have hyinv : 1 ≤ y⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hy).mpr (by linarith)
  have hyinvΘ : y⁻¹ ≤ Θ := by
    have hh := (div_le_iff₀ hσ).mp htΘ
    have hm := mul_le_mul_of_nonneg_left (show σ ≤ 1 by linarith) hΘ0
    nlinarith only [hh, hm]
  have ht : 1 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hσ).mpr
    nlinarith only [hyinv, hσsmall]
  have hP₀ : 1 ≤ P₀ := by dsimp [P₀]; nlinarith only [hyinv]
  have hP₀upper : P₀ ≤ Θ ^ 2 := (sq_le_sq₀ hyinv0 hΘ0).mpr hyinvΘ
  have hP₀abs : |P₀| ≤ Θ ^ 2 := by rw [abs_of_nonneg (by dsimp [P₀]; positivity)]; exact hP₀upper
  have hQ₀abs : |Q₀| ≤ 2 * Θ ^ 2 := by
    dsimp [Q₀]
    rw [abs_mul, abs_mul, abs_of_pos hσ, abs_of_nonneg hyinv0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hyinv0
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    nlinarith only [hm, hyinvΘ, hΘ2]
  have hσabs : |σ ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg σ)]; nlinarith only [hσ, hσsmall]
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hpoly := frame_error_polynomial_bounds hΘ hK he hε hεe hsmall hP₀ hP₀upper
  change ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
    4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
    8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40 at hpoly
  obtain ⟨hρsmall, hηsmall, hAsmall, hEsmall, hJsmall, hAbound, hBbound⟩ := hpoly
  have hQ' : |Q - Q₀| ≤ ρ := by
    have hid : Q - Q₀ = Q + 2 * σ * y⁻¹ := by dsimp [Q₀]; ring
    rwa [hid]
  have hr₀ : |r₀| ≤ 4 := by
    have hh := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 t ht
    simpa only [r₀, neg_div, abs_neg] using hh
  have hr' : |r - r₀| ≤ 10 * η := by
    simpa only [r₀, t, neg_div, sub_neg_eq_add] using hr
  obtain ⟨hrabs, _, hwabs, _⟩ := third_ratio_error hΘ hρ hρsmall hη hηsmall hP₀abs hQ₀abs hP hQ' hN hr₀ hr'
  obtain ⟨_, hp, hq, hn, hw, hDlower, hDerror⟩ :=
    ray_geometric_bounds (ε := ε) (U := r) (V := 1) hΘ hρ hρsmall hP₀abs hQ₀abs hP hQ' hN
  have hDE : |D - (1 + (y⁻¹) ^ 4)| ≤ dD := by
    have hid : 1 + P₀ ^ 2 = 1 + (y⁻¹) ^ 4 := by dsimp [P₀]; ring
    rw [hid] at hDerror
    exact hDerror
  have hEnorm := velocity_direction_norm_bound (ε := ε) hΘ hrabs hwabs
  have hEE : E - 1 ≤ dE := hEnorm.2
  have hE : 1 ≤ E := hEnorm.1
  have hcross := frame_cross_error_from_matrix (ε := ε) hΘ hρ hρsmall hη hηsmall
    (by positivity : 0 ≤ 3 * e) (by nlinarith only [hAsmall] : 70 * (3 * e) * Θ ^ 2 ≤ 1)
    hσabs hP₀abs hQ₀abs hP hQ' hN hr₀ hr' hA
  have hSE' : |S - idealCrossNumerator (σ ^ 2) P₀ Q₀ r₀| ≤ dS := by
    dsimp only at hcross
    dsimp [S, dS]
    nlinarith only [hcross]
  let j := 147 * e * Θ ^ 4 + 2 * ρ
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hJraw : |J - ((P₀ + σ ^ 2) * 1 + Q₀ * r)| ≤ j * (|r| + |(1 : ℝ)|) := by
    have hh := velocity_numerator_error hΘ hρ (by positivity : 0 ≤ 3 * e) hσabs hA hp hq hn hP hQ' hN hw
    dsimp [J, j, w, P₀]
    nlinarith only [hh]
  have hpressure := pressure_ratio_error hΘ hη hηsmall hj (by norm_num : (0 : ℝ) < 1)
    hQ₀abs hr₀ (by simpa only [div_one] using hr') hJraw
  have hJE' : |J - (P₀ + σ ^ 2 + Q₀ * r₀)| ≤ dJ := by
    simp only [div_one] at hpressure
    dsimp [j, dJ] at *
    nlinarith only [hpressure]
  have hPeq : σ ^ 2 * t ^ 2 = P₀ := by dsimp [t, P₀]; field_simp
  have hQeq : -2 * σ ^ 2 * t = Q₀ := by dsimp [t, Q₀]; field_simp
  have hJideal : idealTargetPressure σ y Z Z₁ = P₀ + σ ^ 2 + Q₀ * r₀ := by
    change σ ^ 2 * t ^ 2 + σ ^ 2 + (-2 * σ ^ 2 * t) * r₀ = _
    rw [hPeq, hQeq]
  have hSideal : idealTargetCross σ y Z Z₁ = idealCrossNumerator (σ ^ 2) P₀ Q₀ r₀ := by
    change idealCrossNumerator (σ ^ 2) (σ ^ 2 * t ^ 2) (-2 * σ ^ 2 * t) r₀ = _
    rw [hPeq, hQeq]
  have hJE : |J - idealTargetPressure σ y Z Z₁| ≤ dJ := by rwa [hJideal]
  have hSE : |S - idealTargetCross σ y Z Z₁| ≤ dS := by rwa [hSideal]
  have hrenew := equation30_target_frame_renewal hσ hσsmall hy hysmall hZ hfluxZ hZ0 hZ₁0
    hDlower hE hDE hEE hEsmall hJE hJsmall hSE
  change |J / (sqrt D * sqrt E) - 1| ≤ _ ∧ |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤ _
  constructor
  · have hh := hrenew.1
    dsimp [P₀] at hAbound
    nlinarith only [hh, hAbound]
  · have hh := hrenew.2
    exact hh.trans (by dsimp [P₀] at hBbound; nlinarith only [hBbound])

end EulerPacketFrameQuantitative

end

section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace EulerPacketExistence

section GlobalPicard

variable {E : Type*} [NormedAddCommGroup E]
  {a b : ℝ} (t₀ : Icc a b)

/-- Extend a continuous curve from a compact interval by endpoint values. -/
noncomputable def extendCurve (α : C(Icc a b, E)) (t : ℝ) : E :=
  α (projIcc a b (t₀.2.1.trans t₀.2.2) t)

theorem continuous_extendCurve (α : C(Icc a b, E)) : Continuous (extendCurve t₀ α) :=
  α.continuous.comp continuous_projIcc

theorem extendCurve_of_mem (α : C(Icc a b, E)) {t : ℝ} (ht : t ∈ Icc a b) :
    extendCurve t₀ α t = α ⟨t, ht⟩ := by
  simp only [extendCurve, projIcc_of_mem _ ht]

variable {f : ℝ → E → E} (hf : Continuous (uncurry f))

include hf

theorem continuous_comp_extendCurve (α : C(Icc a b, E)) :
    Continuous (fun t => f t (extendCurve t₀ α t)) :=
  hf.comp (continuous_id.prodMk (continuous_extendCurve t₀ α))

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The Volterra map on all continuous curves, without a spatial-radius
restriction.  Global Lipschitz continuity makes an iterate contractive. -/
noncomputable def picardStep (x : E) (α : C(Icc a b, E)) : C(Icc a b, E) :=
  ⟨fun t => x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s),
    (continuous_const.add (intervalIntegral.differentiable_integral_of_continuous
      (continuous_comp_extendCurve t₀ hf α)).continuous).comp continuous_subtype_val⟩

theorem picardStep_apply (x : E) (α : C(Icc a b, E)) (t : Icc a b) :
    picardStep t₀ hf x α t = x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s) := rfl

variable {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (f t))

include hLip

theorem picard_iterate_point_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist (((picardStep t₀ hf x)^[n]) α t) (((picardStep t₀ hf x)^[n]) β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, picardStep_apply,
      picardStep_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in uIoc t₀.1 t.1, K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hsi : s ∈ Icc a b := (uIcc_subset_Icc t₀.2 t.2) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, extendCurve_of_mem t₀ _ hsi, extendCurve_of_mem t₀ _ hsi]
        calc
          _ ≤ K * dist (((picardStep t₀ hf x)^[n]) α ⟨s, hsi⟩)
              (((picardStep t₀ hf x)^[n]) β ⟨s, hsi⟩) := (hLip s).dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [mul_pow] using hn ⟨s, hsi⟩
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem picard_iterate_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) :
    dist (((picardStep t₀ hf x)^[n]) α) (((picardStep t₀ hf x)^[n]) β) ≤
      (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! * dist α β := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply le_trans (picard_iterate_point_bound t₀ hf hLip x α β n t)
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity

theorem exists_picard_fixed_point (x : E) :
    ∃ α : C(Icc a b, E), IsFixedPt (picardStep t₀ hf x) α := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (b - t₀.1) (t₀.1 - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : (0 : ℝ) ≤ (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! := by
    have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity
  let C : ℝ≥0 := ⟨(K * max (b - t₀.1) (t₀.1 - a)) ^ n / n !, hnonneg⟩
  have hcontract : ContractingWith C ((picardStep t₀ hf x)^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun α β => picard_iterate_bound t₀ hf hLip x α β n⟩
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

/-- A globally Lipschitz time-dependent vector field has a solution on
every finite interval.  Full derivatives also hold at the endpoints. -/
theorem exists_solution_on_compact_interval (x : E) :
    ∃ α : ℝ → E, α t₀.1 = x ∧
      ∀ t ∈ Icc a b, HasDerivAt α (f t (α t)) t := by
  obtain ⟨α, hfixed⟩ := exists_picard_fixed_point t₀ hf hLip x
  let u : ℝ → E := fun t => x + ∫ s in t₀.1..t, f s (extendCurve t₀ α s)
  have heq : ∀ t ∈ Icc a b, u t = extendCurve t₀ α t := by
    intro t ht
    have hh := congrArg (fun v : C(Icc a b, E) => v ⟨t, ht⟩) hfixed
    rw [extendCurve_of_mem t₀ α ht]
    exact hh
  have hc := continuous_comp_extendCurve t₀ hf α
  refine ⟨u, by simp [u], ?_⟩
  intro t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right (a := t₀.1) (b := t) (hc.intervalIntegrable t₀.1 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  change HasDerivAt u (f t (u t)) t
  rw [heq t ht]
  exact hd

end GlobalPicard

/-- Global existence for a jointly continuous vector field with a uniform
global Lipschitz constant in the state variable.  Finite-interval solutions
are glued using the proved ODE uniqueness theorem. -/
theorem exists_global_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {K : ℝ≥0}
    (hf : Continuous (uncurry f)) (hLip : ∀ t, LipschitzWith K (f t)) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f t (u t)) t := by
  classical
  have hlocal : ∀ R : ℝ, 0 < R → ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc (-R) R, HasDerivAt u (f t (u t)) t := by
    intro R hR
    let t₀ : Icc (-R) R := ⟨0, by constructor <;> linarith⟩
    exact exists_solution_on_compact_interval t₀ hf hLip x
  choose v hv0 hvd using hlocal
  let u : ℝ → E := fun t => v (|t| + 1) (by positivity) t
  have hagree : ∀ R (hR : 0 < R), EqOn u (v R hR) (Ioo (-R) R) := by
    intro R hR s hs
    let R' := |s| + 1
    have hR' : 0 < R' := by dsimp [R']; positivity
    let B := min R R'
    have hB : 0 < B := lt_min hR hR'
    have hBR : B ≤ R := min_le_left _ _
    have hBR' : B ≤ R' := min_le_right _ _
    have hzero : (0 : ℝ) ∈ Ioo (-B) B := by constructor <;> linarith
    have hsB : s ∈ Ioo (-B) B := by
      apply abs_lt.mp
      apply lt_min (abs_lt.mpr hs)
      dsimp [R']
      linarith
    have heq := ODE_solution_unique_of_mem_Ioo (v := f) (s := fun _ => (univ : Set E))
      (fun t _ => (hLip t).lipschitzOnWith) hzero
      (fun t ht => ⟨hvd R hR t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (fun t ht => ⟨hvd R' hR' t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (by rw [hv0 R hR, hv0 R' hR'])
    exact (heq hsB).symm
  refine ⟨u, ?_, ?_⟩
  · exact hv0 (|0| + 1) (by positivity)
  · intro t
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      apply abs_lt.mp
      dsimp [R]
      linarith
    have heq : u =ᶠ[𝓝 t] v R hR := Filter.eventually_of_mem
      (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hagree R hR hs)
    have hd := hvd R hR t (Ioo_subset_Icc_self ht)
    rw [hagree R hR ht]
    exact hd.congr_of_eventuallyEq heq

/-- The displacement coefficient in the first-order form of equation (30). -/
noncomputable def scalarCoefficientA (β t : ℝ) : ℝ :=
  2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2)

/-- The velocity coefficient in the first-order form of equation (30). -/
noncomputable def scalarCoefficientB (β t : ℝ) : ℝ :=
  -(4 * β ^ 2 * t ^ 3) / (1 + (β * t ^ 2) ^ 2)

/-- The scalar equation as a globally Lipschitz two-dimensional system. -/
noncomputable def scalarVectorField (β t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2)

theorem scalar_coefficient_bounds
    {β t : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) :
    |scalarCoefficientA β t| ≤ 3 ∧ |scalarCoefficientB β t| ≤ 4 := by
  have hD : 0 < 1 + (β * t ^ 2) ^ 2 := by positivity
  have hx : 0 ≤ β * t ^ 2 := mul_nonneg hβ (sq_nonneg t)
  have hβx : β * (β * t ^ 2) ≤ β * t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hβupper hx
    simpa only [one_mul] using hh
  have hβx0 : 0 ≤ β * (β * t ^ 2) := mul_nonneg hβ hx
  constructor
  · unfold scalarCoefficientA
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    apply abs_le.mpr
    constructor <;> nlinarith only [hβx, hβx0, sq_nonneg (β * t ^ 2 - 1), sq_nonneg (β * t ^ 2)]
  · have hβ2 : β ^ 2 ≤ 1 := by nlinarith only [hβ, hβupper]
    have ht3 : β ^ 2 * |t| ^ 3 ≤ 1 + (β * t ^ 2) ^ 2 := by
      by_cases ht : |t| ≤ 1
      · have hh : |t| ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg t) ht 3
        have hm := mul_le_mul hβ2 hh (pow_nonneg (abs_nonneg t) 3) (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith only [hm, sq_nonneg (β * t ^ 2)]
      · have hh : |t| ^ 3 ≤ |t| ^ 4 := pow_le_pow_right₀ (le_of_not_ge ht) (by decide)
        have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg β)
        have ht4 : |t| ^ 4 = t ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t ^ 4)]
        rw [ht4] at hm
        nlinarith only [hm]
    unfold scalarCoefficientB
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (sq_nonneg β), abs_pow, abs_of_pos hD, div_le_iff₀ hD]
    nlinarith only [ht3]

theorem continuous_scalarVectorField (β : ℝ) : Continuous (uncurry (scalarVectorField β)) := by
  have hden : ∀ p : ℝ × (ℝ × ℝ), 1 + (β * p.1 ^ 2) ^ 2 ≠ 0 := by intro p; positivity
  unfold scalarVectorField scalarCoefficientA scalarCoefficientB Function.uncurry
  fun_prop

theorem lipschitz_scalarVectorField
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) (t : ℝ) :
    LipschitzWith 7 (scalarVectorField β t) := by
  obtain ⟨ha, hb⟩ := scalar_coefficient_bounds (t := t) hβ hβupper
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hfst : |x.1 - y.1| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsnd : |x.2 - y.2| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  change max (dist x.2 y.2)
    (dist (scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2)
      (scalarCoefficientA β t * y.1 + scalarCoefficientB β t * y.2)) ≤ (7 : ℝ) * dist x y
  apply max_le
  · rw [Real.dist_eq]
    nlinarith only [hsnd, dist_nonneg (x := x) (y := y)]
  · rw [Real.dist_eq]
    have h₁ := mul_le_mul ha hfst (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    have h₂ := mul_le_mul hb hsnd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have hh := abs_add_le (scalarCoefficientA β t * (x.1 - y.1))
      (scalarCoefficientB β t * (x.2 - y.2))
    rw [abs_mul, abs_mul] at hh
    have hid : scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2 -
        (scalarCoefficientA β t * y.1 + scalarCoefficientB β t * y.2) =
        scalarCoefficientA β t * (x.1 - y.1) + scalarCoefficientB β t * (x.2 - y.2) := by ring
    rw [hid]
    nlinarith only [h₁, h₂, hh]

/-- Global construction of equation (30) for arbitrary real initial data. -/
theorem equation30_exists_global
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) (v₀ v₁ : ℝ) :
    ∃ V V₁ : ℝ → ℝ, V 0 = v₀ ∧ V₁ 0 = v₁ ∧
      (∀ t, HasDerivAt V (V₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t) := by
  obtain ⟨u, hu0, hud⟩ := exists_global_solution (continuous_scalarVectorField β)
    (lipschitz_scalarVectorField hβ hβupper) (v₀, v₁)
  let V : ℝ → ℝ := fun t => (u t).1
  let V₁ : ℝ → ℝ := fun t => (u t).2
  refine ⟨V, V₁, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hu0
  · exact congrArg Prod.snd hu0
  · intro t
    exact (hud t).fst
  · intro t
    have hV₁ := (hud t).snd
    have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
      convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
      simp only [Pi.pow_apply, id_eq]
      ring
    have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
    apply (hD.mul hV₁).congr_deriv
    dsimp [scalarVectorField, scalarCoefficientA, scalarCoefficientB, V, V₁]
    field_simp
    ring


/-- Construction of the two exact fundamental solutions required by the
relative propagator and Duhamel estimates. -/
theorem equation30_exists_fundamental_system
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) :
    ∃ F F₁ G G₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ G 0 = 0 ∧ G₁ 0 = 1 ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧
      (∀ t, HasDerivAt G (G₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - β * (β * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - β * (β * t ^ 2)) * G t) t) := by
  obtain ⟨F, F₁, hF0, hF₁0, hF, hfluxF⟩ := equation30_exists_global hβ hβupper 1 0
  obtain ⟨G, G₁, hG0, hG₁0, hG, hfluxG⟩ := equation30_exists_global hβ hβupper 0 1
  exact ⟨F, F₁, G, G₁, hF0, hF₁0, hG0, hG₁0, hF, hG, hfluxF, hfluxG⟩

end EulerPacketExistence

end

section

open Set

namespace EulerPacketStage

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability
  EulerPacketFrameRenewal EulerPacketFrameQuantitative EulerPacketExistence




/-- Early forward amplitudes are exponentially small relative to target
amplitude, with the initial slope cancelling from the estimate.  This is
the finite-ODE amplification mechanism underlying equation (36). -/
theorem early_forward_exponential_suppression
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ U V : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (_hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1 / σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hδsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V T ∧ ∀ s ∈ Icc 0 1,
      (|U s| + |V s|) / V T ≤ 84 * exp 9 * Θ * exp (-(1 / (4 * σ))) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1 / σ) hTtarget
  have hT1 : 1 ≤ T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  have hx : 1 ≤ σ * T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh]
  have hxpos : 0 < σ * T := by positivity
  have hF₁0pos : 0 ≤ F₁ 0 := by rw [hF₁0]
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hσ hσsmall (fun t _ => hZ t)
    (fun t _ => hfluxZ t) hZ0 hZ₁0pos T hTpos.le
  have hc := equation30_relative_state_consequences hσ hσsmall hlam hT1 hδ hδsmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 (herror T ⟨hTpos.le, le_rfl⟩)
  have hVpos := hc.1
  have hVlower : Z T / 2 ≤ V T := by
    have hh := (abs_le.mp hc.2.1).1
    have hη : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hδsmall]
    have hratio : (1 : ℝ) / 2 ≤ V T / Z T := by nlinarith only [hh, hη]
    have hm := (le_div_iff₀ hZpos).mp hratio
    nlinarith only [hm]
  have hZlower := equation30_slope_uniform_lower hσ hσsmall hlam
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 T hT1
  have hgrowth := equation30_endpoint_exponential (sq_pos_of_pos hσ)
    (by nlinarith only [hσ, hσsmall] : σ ^ 2 ≤ 1 / 16)
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos
  rw [sqrt_sq hσ.le] at hgrowth
  have hpost := (equation30_post_inversion_lower hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos (σ * T) hx).1
  rw [mul_div_cancel_left₀ T hσne] at hpost
  have hFtarget : exp (1 / (4 * σ)) ≤ (σ * T) * F T := by
    have hh := (div_le_iff₀ hxpos).mp hpost
    nlinarith only [hgrowth, hh]
  have hexp6 : 0 < exp (6 : ℝ) := exp_pos _
  have hZscaled : (1 + lam) * F T ≤ 2 * exp 6 * Z T := by
    have hm := mul_le_mul_of_nonneg_left hZlower (by positivity : 0 ≤ 2 * exp (6 : ℝ))
    have hid : (2 * exp 6) * (((1 + lam) / (2 * exp 6)) * F T) = (1 + lam) * F T := by field_simp
    rw [hid] at hm
    nlinarith only [hm]
  have htarget : (1 + lam) * exp (1 / (4 * σ)) ≤ 4 * exp 6 * (σ * T) * V T := by
    have h₁ := mul_le_mul_of_nonneg_left hFtarget (by positivity : 0 ≤ 1 + lam)
    have h₂ := mul_le_mul_of_nonneg_left hZscaled hxpos.le
    have h₃ := mul_le_mul_of_nonneg_left hVlower (by positivity : 0 ≤ 4 * exp 6 * (σ * T))
    nlinarith only [h₁, h₂, h₃]
  refine ⟨hVpos, ?_⟩
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hT1⟩
  have hFpos := equation30_global_positive hσ hσsmall (fun t _ => hF t)
    (fun t _ => hfluxF t) hF0 hF₁0pos s hs.1
  have hFsmall := equation30_zero_slope_prefix_upper hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 s hs
  have hZstate := equation30_relative_propagator hσ hσsmall (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) hs.1 hs.2
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 (fun t _ => hZ t) (fun t _ => hfluxZ t)
  simp only [hF0, hZ0, hZ₁0, one_pow, div_one, abs_one, abs_of_nonneg hlam, mul_one] at hZstate
  have hδ1 : δ ≤ 1 := by
    have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hm, hδsmall]
  have hUtri := abs_add_le (U s + Z₁ s) (-Z₁ s)
  have hVtri := abs_add_le (V s - Z s) (Z s)
  rw [abs_neg] at hUtri
  have hUid : U s + Z₁ s + -Z₁ s = U s := by ring
  have hVid : V s - Z s + Z s = V s := by ring
  rw [hUid] at hUtri
  rw [hVid] at hVtri
  have hnorm : |U s| + |V s| ≤ 21 * exp 3 * (1 + lam) := by
    have herr := herror s hsT
    have hmδ := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ (1 + lam) * F s)
    have hmF := mul_le_mul_of_nonneg_right hFsmall (by positivity : 0 ≤ 21 * (1 + lam))
    nlinarith only [hUtri, hVtri, herr, hZstate, hmδ, hmF]
  have hscaled := mul_le_mul_of_nonneg_left htarget
    (by positivity : 0 ≤ 21 * exp 3 * exp (-(1 / (4 * σ))))
  have hexpCancel : exp (-(1 / (4 * σ))) * exp (1 / (4 * σ)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  have hexp9 : exp (9 : ℝ) = exp 3 * exp 6 := by rw [← exp_add]; norm_num
  have hscaled' : 21 * exp 3 * (1 + lam) ≤ 84 * exp 9 * (σ * T) * exp (-(1 / (4 * σ))) * V T := by
    have hid : (21 * exp 3 * exp (-(1 / (4 * σ)))) * ((1 + lam) * exp (1 / (4 * σ))) =
        21 * exp 3 * (1 + lam) := by
      calc
        _ = (21 * exp 3 * (1 + lam)) * (exp (-(1 / (4 * σ))) * exp (1 / (4 * σ))) := by ring
        _ = _ := by rw [hexpCancel, mul_one]
    rw [hid] at hscaled
    rw [hexp9]
    nlinarith only [hscaled]
  have hxΘ : σ * T ≤ Θ := by
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hTpos.le
    nlinarith only [hm, hT]
  have hmΘ := mul_le_mul_of_nonneg_right hxΘ
    (by positivity : 0 ≤ 84 * exp 9 * exp (-(1 / (4 * σ))) * V T)
  apply (div_le_iff₀ hVpos).mpr
  nlinarith only [hnorm, hscaled', hmΘ]

end EulerPacketStage

end

section

open Set

namespace EulerPacketCoefficientControl

open Real EulerPacketGrowth EulerPacketPerturbation EulerPacketRay EulerPacketStage

/-- A derivative bound controls the change of a scalar coefficient on
the entire finite time interval. -/
theorem motion_displacement_bound
    {Θ L : ℝ} {f f₁ : ℝ → ℝ} (_hΘ : 0 ≤ Θ) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc 0 Θ, HasDerivAt f (f₁ t) t)
    (hb : ∀ t ∈ Icc 0 Θ, |f₁ t| ≤ L) :
    ∀ t ∈ Icc 0 Θ, |f t - f 0| ≤ L * Θ := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t (Ico_subset_Icc_self ht))
  intro t ht
  have h := hh t ht
  simp only [Real.norm_eq_abs, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left ht.2 hL)

/-- A multiplicative differential bound keeps the normalized shear near
one.  Positivity or an a priori shear bound is not assumed. -/
theorem multiplicative_motion_bound
    {Θ k : ℝ} {H H₁ : ℝ → ℝ}
    (hΘ : 0 ≤ Θ) (hk : 0 ≤ k) (hsmall : k * Θ ≤ 1 / 2)
    (hH : ∀ t ∈ Icc 0 Θ, HasDerivAt H (H₁ t) t)
    (hH0 : H 0 = 1) (hb : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ k * |H t|) :
    ∀ t ∈ Icc 0 Θ, |H t| ≤ 2 ∧ |H t - 1| ≤ 2 * k * Θ := by
  have hc : ContinuousOn H (Icc 0 Θ) := fun t ht => (hH t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hci, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hΘ⟩⟩ hc.abs
  have hbound : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ k * |H c| := by
    intro t ht
    exact (hb t ht).trans (mul_le_mul_of_nonneg_left (hmax ht) hk)
  have hdiff := motion_displacement_bound hΘ (mul_nonneg hk (abs_nonneg _)) hH hbound
  have hcdiff := hdiff c hci
  rw [hH0] at hcdiff
  have htri := abs_add_le (H c - 1) 1
  norm_num at htri
  have hscaled := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (H c))
  have hM : |H c| ≤ 2 := by nlinarith only [hcdiff, htri, hscaled]
  intro t ht
  refine ⟨(hmax ht).trans hM, ?_⟩
  have hh := hdiff t ht
  rw [hH0] at hh
  have hm := mul_le_mul_of_nonneg_right hM (mul_nonneg hk hΘ)
  nlinarith only [hh, hm]

/-- Raw moving-frame coefficient motion implies the normalized error
bounds used in the ray and velocity reductions. -/
theorem normalized_motion_errors
    {a ε Θ G d β : ℝ} {B E : ℝ → Fin 3 → Fin 3 → ℝ}
    {h h₁ b₁ k₁ : ℝ → ℝ}
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hsmall : 16 * (ε * Θ * G ^ 2 + d) ≤ 1)
    (hB : ∀ t ∈ Icc 0 Θ, ∀ i j, |B t i j| ≤ G)
    (hE : ∀ t ∈ Icc 0 Θ, ∀ i j, |E t i j| ≤ d)
    (hb : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B s 0 1) (b₁ t) t)
    (hk : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B s 2 1) (k₁ t) t)
    (hbBound : ∀ t ∈ Icc 0 Θ, |b₁ t| ≤ 2 * ε * G ^ 2)
    (hkBound : ∀ t ∈ Icc 0 Θ, |k₁ t| ≤ 2 * ε * G ^ 2)
    (hShear : ∀ t ∈ Icc 0 Θ, HasDerivAt h (h₁ t) t)
    (hShearBound : ∀ t ∈ Icc 0 Θ, |h₁ t| ≤ (4 * ε * G) * |h t|)
    (hb0 : B 0 0 1 = a) (hk0 : B 0 2 1 = a * β) (hh0 : h 0 = a / ε ^ 2) :
    let e := 16 * (ε * Θ * G ^ 2 + d)
    ε ≤ e ∧ ∀ t ∈ Icc 0 Θ,
      (∀ i j, |ε * B t i j / a| ≤ e) ∧
      (∀ i j, |E t i j / a| ≤ e) ∧
      |ε ^ 2 * h t / a - 1| ≤ e ∧
      |B t 0 1 / a - 1| ≤ e ∧ |B t 2 1 / a - β| ≤ e := by
  let e := 16 * (ε * Θ * G ^ 2 + d)
  have haPos : 0 < a := by linarith
  have haNe : a ≠ 0 := ne_of_gt haPos
  have hεNe : ε ≠ 0 := ne_of_gt hε
  have hΘ0 : 0 ≤ Θ := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hG2 : G ≤ G ^ 2 := by nlinarith only [hG]
  have hΘG2 : G ^ 2 ≤ Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hΘ (sq_nonneg G)
    nlinarith only [hh]
  have hεG : ε * G ≤ ε * Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hG2.trans hΘG2) hε.le
    nlinarith only [hh]
  have hεBase : ε ≤ ε * Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hG hε.le
    nlinarith only [hh, hεG]
  have hbase0 : 0 ≤ ε * Θ * G ^ 2 := by positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hεe : ε ≤ e := by dsimp [e]; nlinarith only [hεBase, hd, hε]
  have hShearSmall : (4 * ε * G) * Θ ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ ε * Θ)
    nlinarith only [hh, hsmall, hd]
  let H : ℝ → ℝ := fun t => ε ^ 2 * h t / a
  let H₁ : ℝ → ℝ := fun t => ε ^ 2 * h₁ t / a
  have hH : ∀ t ∈ Icc 0 Θ, HasDerivAt H (H₁ t) t := by
    intro t ht
    exact ((hShear t ht).const_mul (ε ^ 2)).div_const a
  have hH0 : H 0 = 1 := by dsimp [H]; rw [hh0]; field_simp
  have hHbound : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ (4 * ε * G) * |H t| := by
    intro t ht
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hShearBound t ht) (sq_nonneg ε)) haPos.le
    dsimp [H₁, H]
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_pos haPos,
      abs_div, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_pos haPos]
    convert! hm using 1
    ring
  have hHclose := multiplicative_motion_bound hΘ0 (by positivity : 0 ≤ 4 * ε * G)
    hShearSmall hH hH0 hHbound
  have hBclose := motion_displacement_bound hΘ0 (by positivity : 0 ≤ 2 * ε * G ^ 2) hb hbBound
  have hKclose := motion_displacement_bound hΘ0 (by positivity : 0 ≤ 2 * ε * G ^ 2) hk hkBound
  refine ⟨hεe, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [abs_div, abs_mul, abs_of_pos hε, abs_of_pos haPos, div_le_iff₀ haPos]
    have hm := mul_le_mul_of_nonneg_left (hB t ht i j) hε.le
    have heA := mul_le_mul_of_nonneg_left ha he
    dsimp [e] at heA ⊢
    nlinarith only [hm, heA, hεG, hd, hbase0]
  · intro i j
    rw [abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hbb := hE t ht i j
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hbb, heA, hpos, hd]
  · have hh := (hHclose t ht).2
    have hm := mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ ε * Θ)
    dsimp [H, e] at hh ⊢
    nlinarith only [hh, hm, hd, hbase0]
  · have hh := hBclose t ht
    rw [hb0] at hh
    have hid : B t 0 1 / a - 1 = (B t 0 1 - a) / a := by field_simp
    rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hh, heA, hd, hpos]
  · have hh := hKclose t ht
    rw [hk0] at hh
    have hid : B t 2 1 / a - β = (B t 2 1 - a * β) / a := by field_simp
    rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hh, heA, hd, hpos]

/-- The exact raw moving-frame matrices satisfy the coefficient-error
hypotheses of the controlled-stage theorem. -/
theorem raw_frame_matrix_errors
    {a ε e β h : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hεe : ε ≤ e) (he : 0 ≤ e) (heSmall : e ≤ 1)
    (hB : ∀ i j, |ε * B i j / a| ≤ e) (hE : ∀ i j, |E i j / a| ≤ e)
    (hH : |ε ^ 2 * h / a - 1| ≤ e) (hα : |B 0 1 / a - 1| ≤ e)
    (hκ : |B 2 1 / a - β| ≤ e) :
    (∀ i j, |scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j - idealRayEntry β i j| ≤ 4 * e) ∧
    (∀ i j, |scaledVelocityEntry a ε (parentEntry B E h) i j - idealVelocityEntry β i j| ≤ 3 * e) ∧
    (∀ j,
      |scaledVelocityEntry a ε (fun i j => parentEntry B E h i j + frameSkew B i j) 0 j -
        idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |scaledVelocityEntry a ε (fun i j => parentEntry B E h i j + frameSkew B i j) 1 j -
        idealUnprojectedEntry 1 j| ≤ 5 * e) := by
  have hεupper : ε ≤ 1 := hεe.trans heSmall
  refine ⟨scaled_ray_entry_error ha hε hεupper he hB hE hH hκ, ?_, ?_⟩
  · intro i j
    rw [scaled_velocity_entry_identity ha]
    exact normalized_velocity_entry_error hε.le hεupper he hB hE hH hα hκ i j
  · intro j
    have hids := scaled_unprojected_entry_identity (B := B) (E := E) (h := h) (ε := ε) ha j
    have hbound := normalized_unprojected_entry_error hε.le hεe he heSmall hB hE hH hα
    constructor
    · rw [hids.1]
      exact hbound 0 j
    · rw [hids.2]
      exact hbound 1 j

end EulerPacketCoefficientControl

end

section

open Set

namespace EulerPacketTargetCompression

open Real EulerPacketRay EulerPacketFrameRenewal EulerPacketFrameQuantitative

/-- The common `Θ^40` smallness regime guarantees every sign and
denominator condition used in the perturbed target compression estimate. -/
theorem target_compression_order40
    {β t Θ K e ε H P Q N : ℝ}
    (hβ : 0 < β) (hβupper : β ≤ 1) (ht : 0 < t) (htΘ : t ≤ Θ)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hH : 0 ≤ H)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hscale : 1 ≤ β * t ^ 2)
    (hP : |P - β * t ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * β * t| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    0 < rayDenominator ε P Q N ∧
      H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  let ρ := 800 * e * Θ ^ 5
  let M := K * e * Θ ^ 40
  have hΘpos : 0 < Θ := by linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hρsmall : ρ ≤ 1 / 2 := by
    have hh := hp 5 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hρΘ : ρ * Θ ≤ 1 := by
    have hh := hp 6 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hβtΘ : 1 ≤ β * t * Θ := by
    have hh := mul_le_mul_of_nonneg_left htΘ (mul_nonneg hβ.le ht.le)
    nlinarith only [hh, hscale]
  have hρQ : ρ ≤ β * t := by
    apply (mul_le_mul_iff_right₀ hΘpos).mp
    nlinarith only [hρΘ, hβtΘ]
  have hQ₀ : |-2 * β * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos ht]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_right hβupper ht.le
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    nlinarith only [hh, htΘ, hΘ2]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q + 2 * β * t) (-2 * β * t)
    have hid : Q + 2 * β * t + -2 * β * t = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    change |Q + 2 * β * t| ≤ ρ at hQ
    nlinarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hεQ : |ε * Q| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hε]
    have hh := mul_le_mul hεe hQabs (abs_nonneg Q) he
    have hm := hp 2 (by decide)
    nlinarith only [hh, hm, hMb]
  have hPpos : 0 < P := by
    have hh := (abs_le.mp hP).1
    change ρ ≤ 1 / 2 at hρsmall
    dsimp [ρ] at hρsmall
    nlinarith only [hh, hρsmall, hscale]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  exact ⟨hDpos, perturbed_target_compression hβ ht hε hH hscale hρ hρsmall hρQ hP hQ hN hεQ⟩


end EulerPacketTargetCompression

end

end
