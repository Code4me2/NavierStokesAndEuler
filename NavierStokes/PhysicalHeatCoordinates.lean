import NavierStokes.ParametricHeatTail
import NavierStokes.TerminalStress

/-!
# The heat edit in the actual implicit physical coordinates

The parameter is `eta = z / q^(1/2-h)`, where the positive implicit branch
satisfies `1-t = q - z^2*q^(2*h)`.  The quadratic-coordinate helper with
`q = tau + z^2` is not used here.  These identities connect the actual heat
edit to the terminal angular velocity, including its normalization.
-/

noncomputable section

namespace NavierStokes.PhysicalHeatCoordinates

open SimilarityProfile
open scoped ContDiff

theorem diffusion_eq_ratio {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) :
    ParametricHeatTail.diffusion (eta h p) = (1 - p.1) / q h p := by
  have hq := q_pos hh hh1 ht
  have he : 1 - p.1 = q h p * (1 - eta h p ^ 2) :=
    SimilarityCoordinates.tau_coordinate_identity (by linarith) (by linarith)
      (p := (1 - p.1, p.2.2)) (sub_pos.mpr ht)
  apply (eq_div_iff hq.ne').2
  change (1 - eta h p ^ 2) * q h p = 1 - p.1
  rw [mul_comm]
  exact he.symm

theorem heat_argument {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    2 * ParametricHeatTail.diffusion (eta h p) / X h p =
      2 * (1 - p.1) / p.2.1 := by
  rw [diffusion_eq_ratio hh hh1 ht]
  exact ParametricHeatTail.heat_ratio_physical (q_pos hh hh1 ht) hs

noncomputable def normalization (d : OutgoingTail.TailData) (K : ℝ) : ℝ :=
  HeatTailEdit.outgoingAmplitude d * K ^ HeatTailEdit.exponent d.h


noncomputable def editedAngular (d : OutgoingTail.TailData) (K : ℝ)
    (p : PhysicalPoint) : ℝ :=
  q d.h p ^ (-HeatTailEdit.exponent d.h) *
    ParametricHeatTail.physicalEdit d K (eta d.h p) (X d.h p)



theorem editedAngular_eq_pure_heat (d : OutgoingTail.TailData) {K : ℝ}
    (hK : 0 < K) (hh1 : d.h < 1 / 2) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hlate : 3 ≤ Real.log (X d.h p / K) + 1 / 5) :
    editedAngular d K p =
      TerminalStress.physicalHeat (normalization d K) (1 + d.h) p := by
  exact ParametricHeatTail.physicalEdit_eventual_heat_carrier d hK
    (q_pos d.h_pos hh1 ht) hs (diffusion_eq_ratio d.h_pos hh1 ht) hlate


/-- The normalized section is used only inside the physical time domain.
It supplies a direct profile-parameter comparison without `log(1-eta^2)`.
Endpoint extensions of profile factors are proved separately. -/
noncomputable def normalizedSection (x e : ℝ) : PhysicalPoint := (e ^ 2, (x, e))

theorem q_normalizedSection {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ^ 2 < 1) (x : ℝ) : q h (normalizedSection x e) = 1 := by
  apply (SimilarityCoordinates.eq_coordinateQ (by linarith) (by linarith)
    (p := (1 - e ^ 2, e)) (sub_pos.mpr he) (q := 1) (by norm_num) ?_).symm
  simp [SimilarityCoordinates.forwardScalar]

theorem eta_normalizedSection {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ^ 2 < 1) (x : ℝ) : eta h (normalizedSection x e) = e := by
  change e / q h (normalizedSection x e) ^ ((1 - 2 * h) / 2) = e
  rw [q_normalizedSection hh hh1 he x]
  simp

theorem X_normalizedSection {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : e ^ 2 < 1) (x : ℝ) : X h (normalizedSection x e) = x := by
  change x / q h (normalizedSection x e) = x
  rw [q_normalizedSection hh hh1 he x, div_one]


end NavierStokes.PhysicalHeatCoordinates
