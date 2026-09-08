import NavierStokes.ProfileHistories
import NavierStokes.SimilarityProfile
import NavierStokes.SlowDivergence
import NavierStokes.SlowExpansionResidual
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The leading stress and its genuine divergence

The lag variables in this file are the regular primitives constructed in
`ProfileHistories`. Every profile and physical derivative is a Fréchet
derivative. The physical identities keep the axial-viscosity remainder.
-/

noncomputable section

namespace NavierStokes.LeadingStress

open ProfileHistories
open SimilarityProfile (partialX partialEta pullback inner)
open CoordinateAlgebra (A L)
open scoped Topology ContDiff

variable {Ω : RadialDomain} (P : Profiles Ω)

/-- The angular source `S_q`; `Profiles.angularSource` is `H S_q`. -/
noncomputable def sourceTheta (h : ℝ) (w : Point) : ℝ :=
  P.angularSource h w / P.H w

/-- The axial source `S_n`. -/
noncomputable def sourceAxial (h : ℝ) (w : Point) : ℝ := P.axialSource h w

/-- The coefficient of the angular radial stress in Proposition 3.2. -/
noncomputable def theta (h : ℝ) (w : Point) : ℝ :=
  P.f w * w.1 * P.angularLag h w / L h w.2 + 2 * w.1 * partialX P.f w

/-- The coefficient of the axial radial stress in Proposition 3.2. -/
noncomputable def axial (h : ℝ) (w : Point) : ℝ :=
  Real.sqrt (2 * w.1) * (partialX P.U w + P.axialLag h w / (2 * L h w.2))

noncomputable def slopeA (w : Point) : ℝ := -2 * w.1 * partialX P.f w / P.f w
noncomputable def slopeB (w : Point) : ℝ := 2 * w.1 * partialX P.U w / P.E w

theorem theta_eq_lag_minus_slope (h : ℝ) {w : Point} (hf : P.f w ≠ 0) :
    theta P h w = P.f w * (w.1 * P.angularLag h w / L h w.2 - slopeA P w) := by
  unfold theta slopeA
  field_simp ; ring

theorem axial_eq_lag_plus_slope (h : ℝ) {w : Point} (hX : 0 < w.1)
    (hf : P.f w ≠ 0) :
    axial P h w = P.f w *
      (w.1 * P.axialLag h w / (L h w.2 * P.E w) + slopeB P w) := by
  have hr : Real.sqrt (2 * w.1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr2 : Real.sqrt (2 * w.1) ^ 2 = 2 * w.1 := Real.sq_sqrt (by positivity)
  unfold axial slopeB Profiles.E
  generalize hrdef : Real.sqrt (2 * w.1) = r at *
  by_cases hL : L h w.2 = 0
  · simp only [hL, mul_zero, zero_mul, div_zero, add_zero, zero_add]
    field_simp
    linear_combination partialX P.U w * hr2
  · field_simp
    linear_combination (2 * L h w.2 * partialX P.U w + P.axialLag h w) * hr2

theorem partialX_hasDerivAt {f : Field} {w : Point} (hf : DifferentiableAt ℝ f w) :
    HasDerivAt (fun x => f (x, w.2)) (partialX f w) w.1 := by
  exact hf.hasFDerivAt.comp_hasDerivAt w.1
    ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))

theorem partialX_H {w : Point} (hw : w ∈ Ω.carrier) :
    partialX P.H w = 2 * P.f w + 2 * w.1 * partialX P.f w := by
  have hf := partialX_hasDerivAt (P.f_smooth.differentiableOn (by simp) w hw
    |>.differentiableAt (Ω.isOpen.mem_nhds hw))
  have hH := partialX_hasDerivAt (P.H_smooth.differentiableOn (by simp) w hw
    |>.differentiableAt (Ω.isOpen.mem_nhds hw))
  have hd := ((hasDerivAt_id w.1).const_mul 2).mul hf
  exact (hH.unique hd).trans (by simp)

theorem theta_smoothAt (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (theta P h) w := by
  have hff := P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)
  have hfx : ContDiffAt ℝ ∞ (partialX P.f) w :=
    (radialPartial_smooth Ω P.f_smooth).contDiffAt (Ω.isOpen.mem_nhds hw)
  have hq := P.angularLag_smoothAt h hw hX (P.H_ne_zero hX hf)
  have hl : ContDiffAt ℝ ∞ (fun v : Point => L h v.2) w :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))
  exact ((((hff.mul contDiffAt_fst).mul hq).div hl hL).add
    ((contDiffAt_const.mul contDiffAt_fst).mul hfx))

theorem axial_smoothAt (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hL : L h w.2 ≠ 0) :
    ContDiffAt ℝ ∞ (axial P h) w := by
  have hux : ContDiffAt ℝ ∞ (partialX P.U) w :=
    (radialPartial_smooth Ω P.U_smooth).contDiffAt (Ω.isOpen.mem_nhds hw)
  have hn := P.axialLag_smoothAt h hw hX
  have hl : ContDiffAt ℝ ∞ (fun v : Point => 2 * L h v.2) w :=
    contDiffAt_const.mul (contDiffAt_const.sub
      (contDiffAt_const.mul (contDiffAt_snd.pow 2)))
  exact ((contDiffAt_const.mul contDiffAt_fst).sqrt (mul_ne_zero (by norm_num) hX)).mul
    (hux.add (hn.div hl (mul_ne_zero (by norm_num) hL)))

theorem partialX_theta (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    partialX (theta P h) w =
      (partialX P.f w * w.1 * P.angularLag h w + P.f w * P.angularLag h w +
        P.f w * w.1 * partialX (P.angularLag h) w) / L h w.2 +
        2 * partialX P.f w + 2 * w.1 * partialX (partialX P.f) w := by
  have hf' := partialX_hasDerivAt
    ((P.f_smooth.contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))
  have hfx : HasDerivAt (fun x => partialX P.f (x, w.2))
      (partialX (partialX P.f) w) w.1 := partialX_hasDerivAt
    (((radialPartial_smooth Ω P.f_smooth).contDiffAt
      (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))
  have hq := partialX_hasDerivAt
    ((P.angularLag_smoothAt h hw hX (P.H_ne_zero hX hf)).differentiableAt (by simp))
  have hd := (((hf'.fun_mul (hasDerivAt_id w.1)).fun_mul hq).div_const (L h w.2)).fun_add
    (((hasDerivAt_id w.1).const_mul 2).fun_mul hfx)
  have ht := partialX_hasDerivAt
    ((theta_smoothAt P h hw hX hf hL).differentiableAt (by simp))
  exact (ht.unique hd).trans (by simp only [id_eq, Prod.eta, mul_one]; ring)

/-- The unweighted angular identity, using the actual regular lag equation. -/
theorem theta_divergence_coefficient (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    partialX (theta P h) w + theta P h w / w.1 =
      P.f w * sourceTheta P h w / L h w.2 +
        2 * (w.1 * partialX (partialX P.f) w + 2 * partialX P.f w) := by
  have hq := P.angularLag_smoothAt h hw hX (P.H_ne_zero hX hf)
  have he := P.angularLag_equation h hw hX (P.H_ne_zero hX hf)
  rw [(partialX_hasDerivAt (hq.differentiableAt (by simp))).deriv] at he
  change w.1 * partialX (P.angularLag h) w +
    (1 + w.1 * partialX P.H w / P.H w) * P.angularLag h w = sourceTheta P h w at he
  rw [partialX_theta P h hw hX hf hL, ← he, partialX_H P hw]
  unfold theta Profiles.H
  field_simp ; ring


theorem partialX_axial (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : 0 < w.1) (hL : L h w.2 ≠ 0) :
    partialX (axial P h) w =
      (partialX P.U w + P.axialLag h w / (2 * L h w.2)) / Real.sqrt (2 * w.1) +
      Real.sqrt (2 * w.1) * (partialX (partialX P.U) w +
        partialX (P.axialLag h) w / (2 * L h w.2)) := by
  have hux : HasDerivAt (fun x => partialX P.U (x, w.2))
      (partialX (partialX P.U) w) w.1 := partialX_hasDerivAt
    (((radialPartial_smooth Ω P.U_smooth).contDiffAt
      (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp))
  have hn := partialX_hasDerivAt
    ((P.axialLag_smoothAt h hw hX.ne').differentiableAt (by simp))
  have hr := (Real.hasDerivAt_sqrt (show 2 * w.1 ≠ 0 by positivity)).comp w.1
    ((hasDerivAt_id w.1).const_mul 2)
  have hd := hr.fun_mul (hux.fun_add (hn.div_const (2 * L h w.2)))
  have ht := partialX_hasDerivAt
    ((axial_smoothAt P h hw hX.ne' hL).differentiableAt (by simp))
  exact (ht.unique hd).trans (by
    simp only [Prod.eta, mul_one, Function.comp_apply]
    ring)

/-- The axial profile divergence, obtained from the primitive-defined `N_s`. -/
theorem axial_divergence (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : 0 < w.1) (hL : L h w.2 ≠ 0) :
    Real.sqrt (2 * w.1) * partialX (axial P h) w +
        axial P h w / Real.sqrt (2 * w.1) =
      sourceAxial P h w / L h w.2 +
        2 * (w.1 * partialX (partialX P.U) w + partialX P.U w) := by
  have hn := P.axialLag_smoothAt h hw hX.ne'
  have he := P.axialLag_equation h hw hX.ne'
  rw [(partialX_hasDerivAt (hn.differentiableAt (by simp))).deriv] at he
  change w.1 * partialX (P.axialLag h) w + P.axialLag h w = sourceAxial P h w at he
  have hr : Real.sqrt (2 * w.1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr2 : Real.sqrt (2 * w.1) ^ 2 = 2 * w.1 := Real.sq_sqrt (by positivity)
  rw [partialX_axial P h hw hX hL, ← he]
  unfold axial
  generalize hrdef : Real.sqrt (2 * w.1) = r at *
  have hr4 : r ^ 4 = 4 * w.1 ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (2 * w.1) ^ 2 := by rw [hr2]
      _ = _ := by ring
  field_simp
  ring_nf
  simp only [hr2]
  ring

/-- The coefficient of the angular inviscid residual is the negative lag source. -/
theorem theta_transport_coefficient (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hX : w.1 ≠ 0) (hf : P.f w ≠ 0) (hL : L h w.2 ≠ 0) :
    SimilarityProfile.T h (-A h - 1 / 2) P.f w +
        SlowDivergence.radialFlux h 0 P.U w * (partialX P.f w + P.f w / w.1) +
        P.U w * SimilarityProfile.Z h (-A h - 1 / 2) P.f w =
      -P.f w * sourceTheta P h w / L h w.2 := by
  have hHx : radialPartial P.H w = 2 * P.f w + 2 * w.1 * partialX P.f w :=
    partialX_H P hw
  unfold sourceTheta Profiles.angularSource StressAlgebra.angularSource
  rw [hHx, P.parameterPartial_H hw, P.W_formula h hw]
  dsimp [SimilarityProfile.T, SimilarityProfile.Z, CoordinateAlgebra.timeCoeff,
    CoordinateAlgebra.axialCoeff, SlowDivergence.radialFlux, Profiles.H, Profiles.Ubar,
    CoordinateAlgebra.A, CoordinateAlgebra.D, StressAlgebra.axialExponent,
    StressAlgebra.coordinateFactor, CoordinateAlgebra.d, partialX, partialEta,
    radialPartial, parameterPartial]
  field_simp ; ring

/-- The axial inviscid residual includes the actual derivative of the constructed pressure. -/
theorem axial_transport_coefficient (h : ℝ) {w : Point} (hw : w ∈ Ω.carrier)
    (hL : L h w.2 ≠ 0) :
    SimilarityProfile.T h (-A h) P.U w +
        SlowDivergence.radialFlux h 0 P.U w * partialX P.U w +
        P.U w * SimilarityProfile.Z h (-A h) P.U w +
        SimilarityProfile.Z h (-2 * A h) P.pressure w =
      -sourceAxial P h w / L h w.2 := by
  have hπ : partialX P.pressure w = P.f w ^ 2 := P.radialPartial_pressure hw
  unfold sourceAxial Profiles.axialSource StressAlgebra.axialSource
  dsimp [SimilarityProfile.T, SimilarityProfile.Z, CoordinateAlgebra.timeCoeff,
    CoordinateAlgebra.axialCoeff]
  rw [hπ, P.W_formula h hw]
  dsimp [SlowDivergence.radialFlux, Profiles.Ubar, CoordinateAlgebra.A, CoordinateAlgebra.D,
    StressAlgebra.axialExponent, StressAlgebra.velocityExponent, StressAlgebra.coordinateFactor,
    CoordinateAlgebra.d, partialX, partialEta, radialPartial, parameterPartial]
  field_simp ; ring


/-- Cylindrical radial divergence `(∂r + k/r)S`, in the regular coordinate `s=r²/2`. -/
noncomputable def radialDivergence (k : ℝ) (S : SimilarityProfile.PhysicalProfile)
    (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  Real.sqrt (2 * p.2.1) * SimilarityProfile.partialS S p +
    k * S p / Real.sqrt (2 * p.2.1)



theorem physical_radius {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    Real.sqrt (2 * p.2.1) = SimilarityProfile.q h p ^ (1 / (2 : ℝ)) *
      Real.sqrt (2 * (inner h p).1) := by
  rw [← SlowExpansionResidual.q_mul_X hh hh1 hp,
    show 2 * (SimilarityProfile.q h p * (inner h p).1) =
      SimilarityProfile.q h p * (2 * (inner h p).1) by ring,
    Real.sqrt_mul (SimilarityProfile.q_pos hh hh1 hp).le, Real.sqrt_eq_rpow]

/-- The physical stress scaling produces exactly the cylindrical profile divergence. -/
theorem radialDivergence_pullback {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (k : ℝ) {S : Field} {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1)
    (hS : DifferentiableAt ℝ S (inner h p)) :
    radialDivergence k (pullback h b S) p = SimilarityProfile.q h p ^ (b - 1 / 2) *
      (Real.sqrt (2 * (inner h p).1) * partialX S (inner h p) +
        k * S (inner h p) / Real.sqrt (2 * (inner h p).1)) := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  have hprod : SimilarityProfile.q h p ^ (1 / (2 : ℝ)) *
      SimilarityProfile.q h p ^ (b - 1) = SimilarityProfile.q h p ^ (b - 1 / 2) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hdiv : SimilarityProfile.q h p ^ b / SimilarityProfile.q h p ^ (1 / (2 : ℝ)) =
      SimilarityProfile.q h p ^ (b - 1 / 2) := (Real.rpow_sub hq _ _).symm
  unfold radialDivergence
  rw [SimilarityProfile.partialS_pullback hh hh1 hp hS, physical_radius hh hh1 hp]
  unfold pullback
  calc
    _ = (SimilarityProfile.q h p ^ (1 / (2 : ℝ)) * SimilarityProfile.q h p ^ (b - 1)) *
        (Real.sqrt (2 * (inner h p).1) * partialX S (inner h p)) +
        (SimilarityProfile.q h p ^ b / SimilarityProfile.q h p ^ (1 / (2 : ℝ))) *
          (k * S (inner h p) / Real.sqrt (2 * (inner h p).1)) := by ring
    _ = _ := by rw [hprod, hdiv]; ring

theorem radius_mul_rpow {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) :
    Real.sqrt (2 * p.2.1) * SimilarityProfile.q h p ^ b =
      SimilarityProfile.q h p ^ (b + 1 / 2) * Real.sqrt (2 * (inner h p).1) := by
  rw [physical_radius hh hh1 hp]
  calc
    _ = (SimilarityProfile.q h p ^ (1 / (2 : ℝ)) * SimilarityProfile.q h p ^ b) *
        Real.sqrt (2 * (inner h p).1) := by ring
    _ = _ := by rw [← Real.rpow_add (SimilarityProfile.q_pos hh hh1 hp), add_comm]


noncomputable def fluxProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h 0 (SlowDivergence.radialFlux h 0 P.U)

noncomputable def swirlProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-A h - 1 / 2) P.f

noncomputable def axialProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-A h) P.U

noncomputable def pressureProfile (h : ℝ) : SimilarityProfile.PhysicalProfile :=
  pullback h (-2 * A h) P.pressure



noncomputable def physicalVelocity (h : ℝ) : ProblemStatement.VelocityField :=
  AxisymmetricResidual.velocity (RadialFluxResidual.radialB (fluxProfile P h))
    (swirlProfile P h) (axialProfile P h)

noncomputable def physicalPressure (h : ℝ) : ProblemStatement.PressureField :=
  AxisymmetricResidual.pressure (pressureProfile P h)



theorem inner_X_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (hp : p.1 < 1) (hs : 0 < p.2.1) :
    0 < (inner h p).1 := div_pos hs (SimilarityProfile.q_pos hh hh1 hp)












end NavierStokes.LeadingStress
