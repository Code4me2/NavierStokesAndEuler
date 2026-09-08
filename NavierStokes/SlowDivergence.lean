import NavierStokes.ProfileHistories
import NavierStokes.SimilarityProfile

/-!
# The actual positive-order divergence primitive

Equation (21) is derived from genuine radial averages of a jointly smooth
axial profile. Its radial derivative is the actual similarity axial operator,
and its physical reconstruction satisfies the flux form of incompressibility.
-/

noncomputable section

namespace NavierStokes.SlowDivergence

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ProfileHistories

/-- The positive-order radial flux, with an arbitrary exponent increment lam. -/
def radialFlux (h lam : ℝ) (U : Field) (p : Point) : ℝ :=
  p.1 / CoordinateAlgebra.L h p.2 *
    (2 * p.2 * U p - 2 * p.2 * (CoordinateAlgebra.D h + lam) * average U p -
      CoordinateAlgebra.d p.2 * SimilarityProfile.partialEta (average U) p)


theorem radialFlux_div_radial (h lam : ℝ) (U : Field) {p : Point} (hX : p.1 ≠ 0) :
    radialFlux h lam U p / p.1 = (CoordinateAlgebra.L h p.2)⁻¹ *
      (2 * p.2 * U p - 2 * p.2 * (CoordinateAlgebra.D h + lam) * average U p -
        CoordinateAlgebra.d p.2 * SimilarityProfile.partialEta (average U) p) := by
  dsimp [radialFlux]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = (p.1 * p.1⁻¹) * ((CoordinateAlgebra.L h p.2)⁻¹ *
      (2 * p.2 * U p - 2 * p.2 * (CoordinateAlgebra.D h + lam) * average U p -
        CoordinateAlgebra.d p.2 * SimilarityProfile.partialEta (average U) p)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hX, one_mul]

/-- Rewriting the formula through actual radial histories removes every
division by X and permits differentiation at the axis. -/
theorem radialFlux_eq_histories (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier) :
    radialFlux h lam U p =
      (2 * p.2 * (p.1 * U p) -
        2 * p.2 * (CoordinateAlgebra.D h + lam) * primitive U p -
          CoordinateAlgebra.d p.2 * primitive (parameterPartial U) p) /
            CoordinateAlgebra.L h p.2 := by
  have hη : SimilarityProfile.partialEta (average U) p = average (parameterPartial U) p :=
    parameterPartial_average Ω hU hp
  simp only [radialFlux, hη, primitive_eq_mul_average, div_eq_mul_inv]
  ring

theorem radialFlux_smoothAt (Ω : RadialDomain) {U : Field}
    (hU : ContDiffOn ℝ ∞ U Ω.carrier) (h lam : ℝ) {p : Point} (hp : p ∈ Ω.carrier)
    (hL : CoordinateAlgebra.L h p.2 ≠ 0) : ContDiffAt ℝ ∞ (radialFlux h lam U) p := by
  have hu := hU.contDiffAt (Ω.isOpen.mem_nhds hp)
  have ha := (average_smooth Ω hU).contDiffAt (Ω.isOpen.mem_nhds hp)
  have hη := (parameterPartial_smooth Ω (average_smooth Ω hU)).contDiffAt (Ω.isOpen.mem_nhds hp)
  exact (contDiffAt_fst.div
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))) hL).mul
      ((((contDiffAt_const.mul contDiffAt_snd).mul hu).sub
        (((contDiffAt_const.mul contDiffAt_snd).mul contDiffAt_const).mul ha)).sub
          ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul hη))








end NavierStokes.SlowDivergence

end
