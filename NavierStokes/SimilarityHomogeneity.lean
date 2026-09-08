import NavierStokes.SimilarityProfile
import NavierStokes.Scaling

/-!
# Homogeneity of the actual similarity coordinates

The coordinate `q` is the positive branch constructed in
`SimilarityCoordinates`. Its scaling law follows from uniqueness of that
branch. The band coordinates below are `(R,(Z,T))`, with `T = τ / Q`.
Consequently the profile coordinate is `X = R² / (2 q(T,Z))`, not a fixed
function of `R` alone. Profile weights are transported exactly by a change
of band scale.
-/

noncomputable section

namespace NavierStokes.SimilarityHomogeneity

open SimilarityCoordinates
open scoped ContDiff

abbrev D := CoordinateAlgebra.D

/-- The scalar defining equation has the required anisotropic homogeneity. -/
theorem forwardScalar_scale {Q q : ℝ} (hQ : 0 < Q) (hq : 0 < q) (a z : ℝ) :
    forwardScalar a (Q ^ ((1 - a) / 2) * z) (Q * q) =
      Q * forwardScalar a z q := by
  have hp : (Q ^ ((1 - a) / 2)) ^ 2 * Q ^ a = Q := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ]
    rw [show (1 - a) / 2 * (2 : ℕ) + a = (1 : ℝ) by ring, Real.rpow_one]
  unfold forwardScalar
  rw [Real.mul_rpow hQ.le hq.le, mul_pow]
  calc
    Q * q - (Q ^ ((1 - a) / 2)) ^ 2 * z ^ 2 * (Q ^ a * q ^ a) =
        Q * q - ((Q ^ ((1 - a) / 2)) ^ 2 * Q ^ a) * (z ^ 2 * q ^ a) := by ring
    _ = Q * (q - z ^ 2 * q ^ a) := by rw [hp]; ring

/-- Exact scaling of the defined coordinate, obtained by positive-branch
uniqueness rather than by postulating homogeneity. -/
theorem coordinateQ_scale {a Q τ z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateQ a (Q * τ, Q ^ ((1 - a) / 2) * z) =
      Q * coordinateQ a (τ, z) := by
  have hs := coordinateQ_spec ha ha1 (p := (τ, z)) hτ
  apply (eq_coordinateQ ha ha1 (mul_pos hQ hτ) (mul_pos hQ hs.1) ?_).symm
  rw [forwardScalar_scale hQ hs.1, hs.2]

/-- The defined axial similarity parameter is invariant under scaling. -/
theorem coordinateEta_scale {a Q τ z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateEta a (Q * τ, Q ^ ((1 - a) / 2) * z) =
      coordinateEta a (τ, z) := by
  have hq := (coordinateQ_spec ha ha1 (p := (τ, z)) hτ).1
  unfold coordinateEta
  rw [coordinateQ_scale ha ha1 hQ hτ, Real.mul_rpow hQ.le hq.le]
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos hQ _).ne'

/-- Scaling `s` and `τ` by the same factor preserves the defined `X`. -/
theorem coordinateX_scale {a Q τ z s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateX a (Q * s) (Q * τ, Q ^ ((1 - a) / 2) * z) =
      coordinateX a s (τ, z) := by
  unfold coordinateX
  rw [coordinateQ_scale ha ha1 hQ hτ]
  exact mul_div_mul_left _ _ hQ.ne'

/-- The manuscript's exact `h,D` convention. -/
theorem coordinateQ_scale_h {h Q τ z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateQ (2 * h) (Q * τ, Q ^ D h * z) =
      Q * coordinateQ (2 * h) (τ, z) := by
  simpa only [SimilarityProfile.D_eq] using
    coordinateQ_scale (a := 2 * h) (by linarith) (by linarith) hQ hτ

theorem coordinateEta_scale_h {h Q τ z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateEta (2 * h) (Q * τ, Q ^ D h * z) =
      coordinateEta (2 * h) (τ, z) := by
  simpa only [SimilarityProfile.D_eq] using
    coordinateEta_scale (a := 2 * h) (by linarith) (by linarith) hQ hτ

theorem coordinateX_scale_h {h Q τ z s : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hτ : 0 < τ) :
    coordinateX (2 * h) (Q * s) (Q * τ, Q ^ D h * z) =
      coordinateX (2 * h) s (τ, z) := by
  simpa only [SimilarityProfile.D_eq] using
    coordinateX_scale (a := 2 * h) (s := s) (by linarith) (by linarith) hQ hτ

/-- Physical time is `t=1-τ`; physical points have layout `(t,(s,z))`. -/
noncomputable def physicalScale (h Q : ℝ) (p : SimilarityProfile.PhysicalPoint) :
    SimilarityProfile.PhysicalPoint :=
  (1 - Q * (1 - p.1), (Q * p.2.1, Q ^ D h * p.2.2))



theorem q_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.q h (physicalScale h Q p) = Q * SimilarityProfile.q h p := by
  change coordinateQ (2 * h) (1 - (1 - Q * (1 - p.1)), Q ^ D h * p.2.2) = _
  rw [show 1 - (1 - Q * (1 - p.1)) = Q * (1 - p.1) by ring]
  exact coordinateQ_scale_h hh hh1 hQ (sub_pos.mpr hp)

theorem eta_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.eta h (physicalScale h Q p) = SimilarityProfile.eta h p := by
  change coordinateEta (2 * h) (1 - (1 - Q * (1 - p.1)), Q ^ D h * p.2.2) = _
  rw [show 1 - (1 - Q * (1 - p.1)) = Q * (1 - p.1) by ring]
  exact coordinateEta_scale_h hh hh1 hQ (sub_pos.mpr hp)

theorem X_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.X h (physicalScale h Q p) = SimilarityProfile.X h p := by
  unfold SimilarityProfile.X
  rw [q_physicalScale hh hh1 hQ hp]
  change (Q * p.2.1) / (Q * SimilarityProfile.q h p) = _
  exact mul_div_mul_left _ _ hQ.ne'

theorem inner_physicalScale {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    SimilarityProfile.inner h (physicalScale h Q p) = SimilarityProfile.inner h p :=
  Prod.ext (X_physicalScale hh hh1 hQ hp) (eta_physicalScale hh hh1 hQ hp)


abbrev ChartPoint := ℝ × (ℝ × ℝ)

/-- A band chart is ordered `(R,(Z,T))`. -/
noncomputable def chartQ (h : ℝ) (p : ChartPoint) : ℝ :=
  coordinateQ (2 * h) (p.2.2, p.2.1)

noncomputable def chartEta (h : ℝ) (p : ChartPoint) : ℝ :=
  coordinateEta (2 * h) (p.2.2, p.2.1)

noncomputable def chartX (h : ℝ) (p : ChartPoint) : ℝ :=
  coordinateX (2 * h) (p.1 ^ 2 / 2) (p.2.2, p.2.1)

noncomputable def chartInner (h : ℝ) (p : ChartPoint) : ℝ × ℝ :=
  (chartX h p, chartEta h p)

/-- Transition from the band of scale `Q` to the band of scale `Q'`. -/
noncomputable def chartTransition (h Q Q' : ℝ) (p : ChartPoint) : ChartPoint :=
  ((Q / Q') ^ (1 / 2 : ℝ) * p.1,
    ((Q / Q') ^ D h * p.2.1, (Q / Q') * p.2.2))



theorem chartQ_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartQ h (chartTransition h Q Q' p) = (Q / Q') * chartQ h p :=
  coordinateQ_scale_h hh hh1 (div_pos hQ hQ') hp

theorem chartEta_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartEta h (chartTransition h Q Q' p) = chartEta h p :=
  coordinateEta_scale_h hh hh1 (div_pos hQ hQ') hp

theorem chartX_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartX h (chartTransition h Q Q' p) = chartX h p := by
  have hr : 0 < Q / Q' := div_pos hQ hQ'
  have hs : ((Q / Q') ^ (1 / 2 : ℝ) * p.1) ^ 2 / 2 =
      (Q / Q') * (p.1 ^ 2 / 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hr.le]
    norm_num
    ring
  change coordinateX (2 * h) (((Q / Q') ^ (1 / 2 : ℝ) * p.1) ^ 2 / 2)
    ((Q / Q') * p.2.2, (Q / Q') ^ D h * p.2.1) = _
  rw [hs]
  exact coordinateX_scale_h hh hh1 hr hp

theorem chartInner_transition {h Q Q' : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) (hQ' : 0 < Q') {p : ChartPoint} (hp : 0 < p.2.2) :
    chartInner h (chartTransition h Q Q' p) = chartInner h p :=
  Prod.ext (chartX_transition hh hh1 hQ hQ' hp) (chartEta_transition hh hh1 hQ hQ' hp)













/-- The usual open annular-chart domain; profile annulus restrictions can
be added using `chartX_mem_transition`. -/
noncomputable def chartDomain : Set ChartPoint := {p | 0 < p.1 ∧ 0 < p.2.2}













end NavierStokes.SimilarityHomogeneity
