import NavierStokes.PhysicalWaveSum
import NavierStokes.SolenoidalDiagonal

/-!
# Preservation of the axis value under annular corrections

Actual physical wave sums vanish on a neighborhood of each preterminal
axis point. Local finiteness, first in labels and then in diagonal stages,
therefore preserves the zeroth potential's curl. No uniform radius in the
stage number and no estimate on the final velocity are assumed.
-/

namespace NavierStokes.AxisPreservation

noncomputable section

open Set Filter Function ProblemStatement PhysicalWaveSum SolenoidalDiagonal
open scoped Topology BigOperators




/-- Only finitely many zero germs are intersected at each positive-scale
point. There is no common support radius assumed for every stage. -/
theorem potentialSum_eq_first_near {scales : ℕ → ℝ}
    (hscales : Tendsto scales atTop atTop) {q : SpaceTime → ℝ}
    {A : ℕ → VelocityField} {w : SpaceTime}
    (hq : ContinuousAt q w) (hpos : 0 < q w)
    (hzero : ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 w] fun _ => 0) :
    potentialSum scales q A =ᶠ[𝓝 w] cutStage scales q A 0 := by
  classical
  obtain ⟨N, hN⟩ := eventually_zero_tail hscales hq hpos A
  have hfinite : ∀ᶠ y in 𝓝 w, ∀ j ∈ (Finset.range N).erase 0, A j y = 0 :=
    (eventually_all_finset _).2 (fun j hj => hzero j (Finset.mem_erase.mp hj).1)
  filter_upwards [hN, hfinite] with y hlate hearly
  apply tsum_eq_single 0
  intro j hj
  by_cases hjN : j < N
  · have hjzero := hearly j (Finset.mem_erase.mpr ⟨hj, Finset.mem_range.mpr hjN⟩)
    simp only [cutStage, hjzero, smul_zero]
  · exact hlate j (Nat.le_of_not_gt hjN)

theorem velocitySum_eq_first {scales : ℕ → ℝ}
    (hscales : Tendsto scales atTop atTop) {q : SpaceTime → ℝ}
    {A : ℕ → VelocityField} {w : SpaceTime}
    (hq : ContinuousAt q w) (hpos : 0 < q w)
    (hzero : ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 w] fun _ => 0)
    (hsmall : |scales 0 * q w| < 1 / 2) :
    velocitySum scales q A w = SpatialCurl.spatialCurl (A 0) w := by
  have hfirst : cutStage scales q A 0 =ᶠ[𝓝 w] A 0 := by
    have hc := (SmoothCutoffs.scaledCutoff_eventually_one hsmall).comp_tendsto hq
    filter_upwards [hc] with y hy
    change SmoothCutoffs.scaledCutoff (scales 0) (q y) = 1 at hy
    simp only [cutStage, hy, one_smul]
  exact spatialCurl_eq_of_eventuallyEq
    ((potentialSum_eq_first_near hscales hq hpos hzero).trans hfirst)

theorem origin_eventually_eq_first {scales : ℕ → ℝ}
    (hscales : Tendsto scales atTop atTop) {q : SpaceTime → ℝ}
    {A : ℕ → VelocityField}
    (hq : ∀ t < 1, ContinuousAt q (t, 0))
    (hpos : ∀ t < 1, 0 < q (t, 0))
    (hzero : ∀ t < 1, ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 (t, 0)] fun _ => 0)
    (hlimit : Tendsto (fun t : ℝ => q (t, 0)) (𝓝[<] 1) (𝓝 0)) :
    (fun t : ℝ => velocitySum scales q A (t, 0)) =ᶠ[𝓝[<] 1]
      (fun t => SpatialCurl.spatialCurl (A 0) (t, 0)) := by
  have hl := ((tendsto_const_nhds.mul hlimit).abs :
    Tendsto (fun t : ℝ => |scales 0 * q (t, 0)|) (𝓝[<] 1) (𝓝 |scales 0 * 0|))
  simp only [mul_zero, abs_zero] at hl
  have hsmall := hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hbefore : ∀ᶠ t : ℝ in 𝓝[<] 1, t < 1 := self_mem_nhdsWithin
  filter_upwards [hsmall, hbefore] with t ht hbefore
  exact velocitySum_eq_first hscales (hq t hbefore) (hpos t hbefore)
    (hzero t hbefore) ht


theorem physicalQ_origin {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} (ht : t < 1) : physicalQ h (t, 0) = 1 - t := by
  change SimilarityCoordinates.coordinateQ (2 * h) (1 - t, 0) = 1 - t
  have hq := SimilarityCoordinates.coordinateQ_spec
    (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1)
    (p := (1 - t, 0)) (by simpa using sub_pos.mpr ht)
  simpa only [SimilarityCoordinates.forwardScalar, zero_pow (by norm_num : 2 ≠ 0),
    zero_mul, sub_zero] using hq.2

theorem physicalQ_origin_tendsto {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    Tendsto (fun t : ℝ => physicalQ h (t, 0)) (𝓝[<] 1) (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => 1 - t) (1 : ℝ) :=
      continuousAt_const.sub continuousAt_id
    simpa using hc.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Iio 1))
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Iio 1)] with t ht
  exact (physicalQ_origin hh hh1 ht).symm



end

end NavierStokes.AxisPreservation
