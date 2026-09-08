import Euler.ClassicalPressureCurl

/-! A genuine smooth scalar graph pressure obtained from the closed lifted L² gradient space. -/

noncomputable section

namespace EulerGraphPressurePotential

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerClassicalPressureCurl EulerGraphPullback
  EulerSpatialSobolevInverse EulerPressureSpatialRegularity EulerSmoothPressureRepresentative
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The oscillating physical graph in the actual periodic cylinder. -/
def cylinderGraph (k : ℝ) (m : Vector3) (x : Vector3) : LiftDomain period :=
  (x, (k * ⟪m, x⟫_ℝ : ℝ))

omit [Fact (0 < period)] in
/-- Coordinate lifted symmetry implies symmetry on arbitrary spatial vectors. -/
theorem lifted_symmetry_of_coordinates (κ : ℝ) (m : Vector3)
    (L : LiftTangent →L[ℝ] Vector3)
    (hL : ∀ i j, (L (coordinateDirection κ m i)) j = (L (coordinateDirection κ m j)) i)
    (a b : Vector3) :
    ⟪L (transportDirection κ m a), b⟫_ℝ = ⟪L (transportDirection κ m b), a⟫_ℝ := by
  rw [← coordinateDirections_sum κ m a, ← coordinateDirections_sum κ m b, map_sum, map_sum]
  simp only [map_smul, sum_inner, real_inner_smul_left]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, Pi.star_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hL i j]
  ring

/-- A smooth representative of a lifted L² gradient has a genuine smooth scalar pressure on every physical graph. -/
theorem gradientSpace_has_graph_potential (κ k : ℝ) (hκ : k * κ = 1) (m : Vector3)
    (p : LiftL2 period) (hp : p ∈ gradientSpace period κ m)
    (g : LiftDomain period → Vector3)
    (hrep : (p : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∃ q : Vector3 → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = κ • g (cylinderGraph period k m x) := by
  let P : LiftTangent → Vector3 := localFieldLift period g 0
  have hclosed : ∀ z a b,
      ⟪fderiv ℝ P z (liftedDirection κ m a), b⟫_ℝ =
        ⟪fderiv ℝ P z (liftedDirection κ m b), a⟫_ℝ := by
    intro z a b
    have hcurl := gradientSpace_classical_curl_zero period κ m p hp g hrep hg (coveringMap period z)
    have hder : fderiv ℝ P z = fderiv ℝ (localFieldLift period g (coveringMap period z)) 0 :=
      (fderiv_localFieldLift_cover period g z).symm
    rw [hder]
    exact lifted_symmetry_of_coordinates κ m _ hcurl a b
  obtain ⟨q, hqs, hq⟩ := lifted_closed_field_has_graph_potential P (hg 0) k κ hκ m hclosed
  refine ⟨q, hqs, fun x => ?_⟩
  simpa only [P, localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add,
    graphMap_apply, cylinderGraph] using hq x


end EulerGraphPressurePotential
