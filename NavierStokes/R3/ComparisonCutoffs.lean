import NavierStokes.R3.ComparisonSetup
import Common.Cutoffs

/-!
# Smooth spatial cutoffs for whole-space comparison

The cutoffs are the dilated radius-1-to-2 bump of `Common.Cutoffs`, instantiated
on `Space` under the names the comparison argument uses; the `weight = cutoff ^ 8`
of the localized energy and the `multiplier = cutoff ^ 2` that commutes the
pressure operator are specific to this library.  All scaled cutoffs are dilations
of the same bump, so the constants in their derivative estimates do not depend on
the radius.
-/


noncomputable section

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.ComparisonCutoffs

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)

/-- The unscaled cutoff. -/
def baseCutoff (x : Space) : ℝ := Common.Cutoffs.baseCutoff Space x

/-- The cutoff at spatial radius `R`; its estimates are stated for `0 < R`. -/
def cutoff (R : ℝ) (x : Space) : ℝ := Common.Cutoffs.cutoff Space R x

/-- The weight in the localized energy. -/
def weight (R : ℝ) (x : Space) : ℝ := cutoff R x ^ 8

/-- The multiplier used to commute the pressure operator. -/
def multiplier (R : ℝ) (x : Space) : ℝ := cutoff R x ^ 2

theorem baseCutoff_smooth : ContDiff ℝ ∞ baseCutoff := Common.Cutoffs.baseCutoff_smooth

theorem baseCutoff_hasCompactSupport : HasCompactSupport baseCutoff :=
  Common.Cutoffs.baseCutoff_hasCompactSupport

theorem cutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (cutoff R) := Common.Cutoffs.cutoff_smooth R

theorem cutoff_nonneg (R : ℝ) (x : Space) : 0 ≤ cutoff R x :=
  Common.Cutoffs.cutoff_nonneg R x

theorem cutoff_le_one (R : ℝ) (x : Space) : cutoff R x ≤ 1 :=
  Common.Cutoffs.cutoff_le_one R x

theorem cutoff_mem_Icc (R : ℝ) (x : Space) : cutoff R x ∈ Icc (0 : ℝ) 1 :=
  ⟨cutoff_nonneg R x, cutoff_le_one R x⟩

theorem norm_scaled {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖R⁻¹ • x‖ = ‖x‖ / R :=
  Common.Cutoffs.norm_inv_smul hR x

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    cutoff R x = 1 :=
  Common.Cutoffs.cutoff_eq_one hR hx

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Space} (hx : 2 * R ≤ ‖x‖) :
    cutoff R x = 0 :=
  Common.Cutoffs.cutoff_eq_zero hR hx

theorem cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoff R) :=
  Common.Cutoffs.cutoff_hasCompactSupport hR

theorem weight_smooth (R : ℝ) : ContDiff ℝ ∞ (weight R) :=
  (cutoff_smooth R).pow 8

theorem weight_nonneg (R : ℝ) (x : Space) : 0 ≤ weight R x :=
  pow_nonneg (cutoff_nonneg R x) 8

theorem weight_le_one (R : ℝ) (x : Space) : weight R x ≤ 1 :=
  pow_le_one₀ (cutoff_nonneg R x) (cutoff_le_one R x)

theorem weight_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (weight R) := by
  change HasCompactSupport ((fun a : ℝ => a ^ 8) ∘ cutoff R)
  exact (cutoff_hasCompactSupport hR).comp_left (by norm_num)

theorem weight_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    weight R x = 1 := by simp [weight, cutoff_eq_one hR hx]

/-- A fixed positive bound for the `n`th derivative of the unscaled bump. -/
def derivativeConstant (n : ℕ) : ℝ := Common.Cutoffs.derivativeConstant Space n

theorem derivativeConstant_pos (n : ℕ) : 0 < derivativeConstant n :=
  Common.Cutoffs.derivativeConstant_pos n

/-- Each spatial derivative contributes precisely one inverse power of the radius. -/
theorem cutoff_iteratedFDeriv_le {R : ℝ} (hR : 0 < R) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤ derivativeConstant n / R ^ n :=
  Common.Cutoffs.cutoff_iteratedFDeriv_le hR n x

theorem cutoff_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (cutoff R) x‖ ≤ derivativeConstant 1 / R :=
  Common.Cutoffs.cutoff_fderiv_le hR x

theorem cutoff_second_fderiv_le {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fderiv ℝ (cutoff R)) x‖ ≤ derivativeConstant 2 / R ^ 2 :=
  Common.Cutoffs.cutoff_second_fderiv_le hR x

/-- The scalar spatial Laplacian, using the fixed standard coordinate vectors. -/
def laplacian (f : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, NavierStokes.PeriodicIntegration.spatialPartial i
    (NavierStokes.PeriodicIntegration.spatialPartial i f) x

theorem fderiv_apply_derivative {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (x a b : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y b) x a =
      fderiv ℝ (fderiv ℝ f) x a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  simpa using congrArg (fun A : Space →L[ℝ] ℝ => A a)
    (fderiv_clm_apply hd (differentiableAt_const b))

theorem norm_partial_partial_le {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    ‖NavierStokes.PeriodicIntegration.spatialPartial i
      (NavierStokes.PeriodicIntegration.spatialPartial j f) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  change ‖fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i)‖ ≤ _
  rw [fderiv_apply_derivative hf]
  have hv (k : Fin 3) : ‖coordinateVector k‖ ≤ 1 := by
    simp [coordinateVector]
  exact ((fderiv ℝ (fderiv ℝ f) x (coordinateVector i)).unit_le_opNorm
    (coordinateVector j) (hv j)).trans
    ((fderiv ℝ (fderiv ℝ f) x).unit_le_opNorm (coordinateVector i) (hv i))

theorem eventually_cutoff_eq_one (x : Space) :
    ∀ᶠ R : ℝ in atTop, cutoff R x = 1 :=
  Common.Cutoffs.eventually_cutoff_eq_one x

theorem cutoff_tendsto_one (x : Space) :
    Tendsto (fun R : ℝ => cutoff R x) atTop (𝓝 1) :=
  Common.Cutoffs.cutoff_tendsto_one x

end NavierStokesR3.ComparisonCutoffs
