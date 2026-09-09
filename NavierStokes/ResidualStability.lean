import NavierStokes.ResidualCalculus
import NavierStokes.ResidualRegularity
import NavierStokes.SpatialCurl
import NavierStokes.JetBounds
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Stability of the actual Navier--Stokes residual under flat perturbations

Flatness and power growth below are bounds on norms of actual iterated
Fréchet derivatives. The differential and bilinear closure lemmas are proved
from the derivative identities and Leibniz estimates, not assumed.
-/

noncomputable section

namespace NavierStokes.ResidualStability

open Set Filter Function
open scoped Topology BigOperators ContDiff

section Scalar

variable {X : Type*} {l : Filter X} {q f g : X → ℝ}





end Scalar

section Jets

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]



variable {l : Filter D} {q : D → ℝ} {f : D → E} {g : D → F} {U : Set D}




theorem iteratedFDeriv_eqOn {f g : D → E} (hU : IsOpen U) (hfg : EqOn f g U)
    (m : ℕ) : EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) U := by
  intro x hx
  have h : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hfg hy
  have h' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using
    h'.iteratedFDerivWithin_eq h.self_of_nhds m



theorem norm_jet_linear_map (L : E →L[ℝ] F) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f x‖ := by
  change ‖iteratedFDeriv ℝ m (L ∘ f) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hf.contDiffAt (hU.mem_nhds hx))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)]
  exact L.norm_compContinuousMultilinearMap_le _










end Jets

section PhysicalOperators

open ProblemStatement

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Restrict a full spacetime derivative to the spatial directions. -/
def spaceRestriction (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (SpaceTime →L[ℝ] V) →L[ℝ] (Space →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ Space SpaceTime V).flip (ContinuousLinearMap.inr ℝ ℝ Space)

theorem space_fderiv_eq_full {f : SpaceTime → V} {z : SpaceTime}
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun y : Space => f (z.1, y)) z.2 = spaceRestriction V (fderiv ℝ f z) :=
  (hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv

theorem temporalDerivative_eq_full {f : VelocityField} {z : SpaceTime}
    (hf : DifferentiableAt ℝ f z) :
    temporalDerivative f z.1 z.2 = fderiv ℝ f z (1, 0) := by
  have h : fderiv ℝ (fun t : ℝ => f (t, z.2)) z.1 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ ℝ Space) :=
    (hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv
  exact congrArg (fun L : ℝ →L[ℝ] Space => L 1) h

variable {l : Filter SpaceTime} {q : SpaceTime → ℝ} {U : Set SpaceTime}






theorem spatialSlice_differentiable {f : SpaceTime → V}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {z : SpaceTime} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun y : Space => f (z.1, y)) z.2 :=
  ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).comp z.2
    (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt

theorem timeSlice_differentiable {f : SpaceTime → V}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {z : SpaceTime} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun t : ℝ => f (t, z.2)) z.1 :=
  ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).comp z.1
    (hasFDerivAt_prodMk_left z.1 z.2).differentiableAt

/-- Local version of the Laplacian additivity used in `ResidualCalculus`.
Only smoothness on the open domain is needed, not on an entire spatial slice. -/
theorem spatialLaplacian_add_on {u w : VelocityField} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    {z : SpaceTime} (hz : z ∈ U) :
    spatialLaplacian (fun y => u y + w y) z.1 z.2 =
      spatialLaplacian u z.1 z.2 + spatialLaplacian w z.1 z.2 := by
  unfold spatialLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y : Space => spatialDerivative (fun z => u z + w z) z.1 y (coordinateVector i))
      =ᶠ[𝓝 z.2] (fun y => spatialDerivative u z.1 y (coordinateVector i) +
        spatialDerivative w z.1 y (coordinateVector i)) := by
    have hmem : ∀ᶠ y : Space in 𝓝 z.2, (z.1, y) ∈ U :=
      (continuousAt_const.prodMk continuousAt_id) (hU.mem_nhds hz)
    filter_upwards [hmem] with y hy
    rw [ResidualCalculus.spatialDerivative_add u w z.1 y
      (spatialSlice_differentiable hU hu hy) (spatialSlice_differentiable hU hw hy)]
    rfl
  have hdu : ContDiffOn ℝ ∞
      (fun y => spatialDerivative u y.1 y.2 (coordinateVector i)) U :=
    (ResidualRegularity.contDiffOn_spatialDerivative hU hu).clm_apply contDiffOn_const
  have hdw : ContDiffOn ℝ ∞
      (fun y => spatialDerivative w y.1 y.2 (coordinateVector i)) U :=
    (ResidualRegularity.contDiffOn_spatialDerivative hU hw).clm_apply contDiffOn_const
  rw [heq.fderiv_eq, fderiv_fun_add
    (spatialSlice_differentiable hU hdu hz) (spatialSlice_differentiable hU hdw hz)]
  rfl

/-- The exact perturbation identity now holds on an arbitrary open spacetime
domain, using the concrete first-order identities from `ResidualCalculus`. -/
theorem residual_add_sub_on {u w : VelocityField} {p r : PressureField}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    {z : SpaceTime} (hz : z ∈ U) :
    navierStokesResidual (fun y => u y + w y) (fun y => p y + r y) z.1 z.2 -
      navierStokesResidual u p z.1 z.2 =
        temporalDerivative w z.1 z.2 - spatialLaplacian w z.1 z.2 + pressureGradient r z.1 z.2 +
          spatialDerivative u z.1 z.2 (w z) + spatialDerivative w z.1 z.2 (u z) +
          spatialDerivative w z.1 z.2 (w z) := by
  unfold navierStokesResidual
  rw [ResidualCalculus.temporalDerivative_add u w z.1 z.2
      (timeSlice_differentiable hU hu hz) (timeSlice_differentiable hU hw hz),
    ResidualCalculus.advection_add u w z.1 z.2
      (spatialSlice_differentiable hU hu hz) (spatialSlice_differentiable hU hw hz),
    spatialLaplacian_add_on hU hu hw hz,
    ResidualCalculus.pressureGradient_add p r z.1 z.2
      (spatialSlice_differentiable hU hp hz) (spatialSlice_differentiable hU hr hz)]
  unfold advection
  abel

/-- The difference of the two actual viscosity-one Navier--Stokes residuals. -/
def residualDifference (u w : VelocityField) (p r : PressureField) : VelocityField :=
  fun z => navierStokesResidual (fun y => u y + w y) (fun y => p y + r y) z.1 z.2 -
    navierStokesResidual u p z.1 z.2


end PhysicalOperators

section QuantitativeJetAlgebra

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_jet_add_le {U : Set D} {f g : D → E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  rw [fun_iteratedFDeriv_add_apply
    ((hf.contDiffAt (hU.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
    ((hg.contDiffAt (hU.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))]
  exact norm_add_le _ _

theorem norm_jet_neg (f : D → E) (x : D) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => -f y) x‖ = ‖iteratedFDeriv ℝ m f x‖ := by
  change ‖iteratedFDeriv ℝ m (-f) x‖ = _
  rw [iteratedFDeriv_neg_apply, norm_neg]

theorem norm_jet_sub_le {U : Set D} {f g : D → E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  simpa only [sub_eq_add_neg, norm_jet_neg] using norm_jet_add_le hU hf hg.neg hx m

theorem norm_jet_linear_map_fderiv (L : (D →L[ℝ] E) →L[ℝ] F)
    {U : Set D} {f : D → E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L (fderiv ℝ f y)) x‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
  have h := norm_jet_linear_map L hU (hf.fderiv_of_isOpen hU (by simp)) hx m
  simpa only [norm_iteratedFDeriv_fderiv] using h

/-- The pointwise finite-order form of the Leibniz estimate. The majorants
need only bound jets at this point; they may depend on the point and stage. -/
theorem norm_jet_bilinear_bound (L : E →L[ℝ] F →L[ℝ] G) {U : Set D}
    {f : D → E} {g : D → F} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) (m : ℕ) {A B : ℝ}
    (hA : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hB : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤ ‖L‖ * (2 : ℝ) ^ m * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hsum : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖) ≤
      (2 : ℝ) ^ m * A * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hA i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
            (Nat.cast_nonneg _))
          (hB (m - i) (Nat.sub_le _ _)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA0)
      _ = (2 : ℝ) ^ m * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose m
  exact (JetBounds.norm_iteratedFDeriv_bilinear_le_on L hU hf hg hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).trans
      ((mul_le_mul_of_nonneg_left hsum (norm_nonneg L)).trans_eq (by ring))

end QuantitativeJetAlgebra

-- The norm of a linear functional on the second-derivative space has three
-- nested continuous-linear-map types.

section FullJetExpression

open ProblemStatement

private local instance : NormedAddCommGroup (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) :=
  inferInstance
private local instance : NormedSpace ℝ (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) :=
  inferInstance

theorem norm_iteratedFDeriv_spatialCurl_le {U : Set SpaceTime} {A : VelocityField}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) {z : SpaceTime} (hz : z ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl A) z‖ ≤
      ‖SpatialCurl.curlLinear.comp (spaceRestriction Space)‖ *
        ‖iteratedFDeriv ℝ (m + 1) A z‖ := by
  have heq : EqOn (SpatialCurl.spatialCurl A)
      (fun y => (SpatialCurl.curlLinear.comp (spaceRestriction Space)) (fderiv ℝ A y)) U := by
    intro y hy
    unfold SpatialCurl.spatialCurl SpatialCurl.curl
    rw [space_fderiv_eq_full ((hA.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  rw [iteratedFDeriv_eqOn hU heq m hz]
  exact norm_jet_linear_map_fderiv _ hU hA hz m

def timeJet : (SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
  ContinuousLinearMap.apply ℝ Space (1, 0)

def laplaceJet : (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
  ∑ i : Fin 3,
    (ContinuousLinearMap.apply ℝ Space (0, coordinateVector i)).comp
      (ContinuousLinearMap.apply ℝ (SpaceTime →L[ℝ] Space) (0, coordinateVector i))

def pressureJet : (SpaceTime →L[ℝ] ℝ) →L[ℝ] Space :=
  ∑ i : Fin 3,
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i)).comp
      (ContinuousLinearMap.apply ℝ ℝ (0, coordinateVector i))

@[simp] theorem laplaceJet_apply (L : SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) :
    laplaceJet L = ∑ i : Fin 3, L (0, coordinateVector i) (0, coordinateVector i) := by
  simp [laplaceJet]

@[simp] theorem pressureJet_apply (L : SpaceTime →L[ℝ] ℝ) :
    pressureJet L = ∑ i : Fin 3, L (0, coordinateVector i) • coordinateVector i := by
  simp [pressureJet]

theorem spatialLaplacian_eq_full {U : Set SpaceTime} {w : VelocityField}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) {z : SpaceTime} (hz : z ∈ U) :
    spatialLaplacian w z.1 z.2 = laplaceJet (fderiv ℝ (fderiv ℝ w) z) := by
  rw [laplaceJet_apply]
  unfold spatialLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y : SpaceTime => spatialDerivative w y.1 y.2 (coordinateVector i))
      =ᶠ[𝓝 z] (fun y => fderiv ℝ w y (0, coordinateVector i)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    unfold spatialDerivative
    rw [space_fderiv_eq_full ((hw.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by simp)
  have hfirst : HasFDerivAt (fun y : SpaceTime => fderiv ℝ w y (0, coordinateVector i))
      ((ContinuousLinearMap.apply ℝ Space (0, coordinateVector i)).comp
        (fderiv ℝ (fderiv ℝ w) z)) z := by
    let ev : (SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
      ContinuousLinearMap.apply ℝ Space (0, coordinateVector i)
    change HasFDerivAt (ev ∘ fderiv ℝ w) (ev.comp (fderiv ℝ (fderiv ℝ w) z)) z
    exact ev.hasFDerivAt.comp z
      ((hD.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hslice := hfirst.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [ResidualRegularity.space_fderiv_congr heq]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.inr_apply] using
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) hslice.fderiv

theorem pressureGradient_eq_full {U : Set SpaceTime} {r : PressureField}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ r U) {z : SpaceTime} (hz : z ∈ U) :
    pressureGradient r z.1 z.2 = pressureJet (fderiv ℝ r z) := by
  rw [pressureJet_apply]
  unfold pressureGradient
  rw [space_fderiv_eq_full ((hr.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  rfl

def residualJetExpression (u w : VelocityField) (r : PressureField) : VelocityField :=
  fun z => timeJet (fderiv ℝ w z) - laplaceJet (fderiv ℝ (fderiv ℝ w) z) +
    pressureJet (fderiv ℝ r z) +
    spaceRestriction Space (fderiv ℝ u z) (w z) +
    spaceRestriction Space (fderiv ℝ w z) (u z) +
    spaceRestriction Space (fderiv ℝ w z) (w z)

theorem residualDifference_eq_jetExpression {U : Set SpaceTime}
    {u w : VelocityField} {p r : PressureField} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U) :
    EqOn (residualDifference u w p r) (residualJetExpression u w r) U := by
  intro z hz
  unfold residualDifference residualJetExpression
  rw [residual_add_sub_on hU hu hw hp hr hz,
    temporalDerivative_eq_full ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)),
    spatialLaplacian_eq_full hU hw hz, pressureGradient_eq_full hU hr hz]
  unfold spatialDerivative
  rw [space_fderiv_eq_full ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)),
    space_fderiv_eq_full ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  rfl

/-- Quantitative fixed-order stability, with only pointwise hypotheses on the
actual jets. The background needs `m+1` derivatives, the velocity perturbation
`m+2`, and the pressure perturbation `m+1`. The three majorants may depend on
the point and on a truncation stage. Every displayed operator norm is fixed
independently of the fields, stage, and physical scale. -/
theorem residualDifference_jet_bound {U : Set SpaceTime}
    {u w : VelocityField} {p r : PressureField} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    {z : SpaceTime} (hz : z ∈ U) (m : ℕ) {A W P : ℝ}
    (huBound : ∀ k : ℕ, k ≤ m + 1 → ‖iteratedFDeriv ℝ k u z‖ ≤ A)
    (hwBound : ∀ k : ℕ, k ≤ m + 2 → ‖iteratedFDeriv ℝ k w z‖ ≤ W)
    (hrBound : ∀ k : ℕ, k ≤ m + 1 → ‖iteratedFDeriv ℝ k r z‖ ≤ P) :
    ‖iteratedFDeriv ℝ m (residualDifference u w p r) z‖ ≤
      ‖timeJet‖ * W + ‖laplaceJet‖ * W + ‖pressureJet‖ * P +
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * A * W +
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * A +
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * W := by
  let T : VelocityField := fun y => timeJet (fderiv ℝ w y)
  let L : VelocityField := fun y => laplaceJet (fderiv ℝ (fderiv ℝ w) y)
  let R : VelocityField := fun y => pressureJet (fderiv ℝ r y)
  let C₁ : VelocityField := fun y => spaceRestriction Space (fderiv ℝ u y) (w y)
  let C₂ : VelocityField := fun y => spaceRestriction Space (fderiv ℝ w y) (u y)
  let C₃ : VelocityField := fun y => spaceRestriction Space (fderiv ℝ w y) (w y)
  have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by simp)
  have hDw : ContDiffOn ℝ ∞ (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by simp)
  have hDDw : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ w)) U :=
    hDw.fderiv_of_isOpen hU (by simp)
  have hDr : ContDiffOn ℝ ∞ (fderiv ℝ r) U := hr.fderiv_of_isOpen hU (by simp)
  have hTs : ContDiffOn ℝ ∞ T U := hDw.continuousLinearMap_comp timeJet
  have hLs : ContDiffOn ℝ ∞ L U := hDDw.continuousLinearMap_comp laplaceJet
  have hRs : ContDiffOn ℝ ∞ R U := hDr.continuousLinearMap_comp pressureJet
  have hC₁s : ContDiffOn ℝ ∞ C₁ U :=
    (hDu.continuousLinearMap_comp (spaceRestriction Space)).clm_apply hw
  have hC₂s : ContDiffOn ℝ ∞ C₂ U :=
    (hDw.continuousLinearMap_comp (spaceRestriction Space)).clm_apply hu
  have hC₃s : ContDiffOn ℝ ∞ C₃ U :=
    (hDw.continuousLinearMap_comp (spaceRestriction Space)).clm_apply hw
  have hT : ‖iteratedFDeriv ℝ m T z‖ ≤ ‖timeJet‖ * W := by
    apply (norm_jet_linear_map timeJet hU hDw hz m).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv]
    exact hwBound (m + 1) (by omega)
  have hL : ‖iteratedFDeriv ℝ m L z‖ ≤ ‖laplaceJet‖ * W := by
    apply (norm_jet_linear_map laplaceJet hU hDDw hz m).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    exact hwBound (m + 1 + 1) (by omega)
  have hR : ‖iteratedFDeriv ℝ m R z‖ ≤ ‖pressureJet‖ * P := by
    apply (norm_jet_linear_map pressureJet hU hDr hz m).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv]
    exact hrBound (m + 1) le_rfl
  have hu₀ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k u z‖ ≤ A :=
    fun k hk => huBound k (by omega)
  have hw₀ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k w z‖ ≤ W :=
    fun k hk => hwBound k (by omega)
  have hu₁ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k (fderiv ℝ u) z‖ ≤ A := by
    intro k hk
    rw [norm_iteratedFDeriv_fderiv]
    exact huBound (k + 1) (by omega)
  have hw₁ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k (fderiv ℝ w) z‖ ≤ W := by
    intro k hk
    rw [norm_iteratedFDeriv_fderiv]
    exact hwBound (k + 1) (by omega)
  have hC₁ : ‖iteratedFDeriv ℝ m C₁ z‖ ≤
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * A * W :=
    norm_jet_bilinear_bound (spaceRestriction Space) hU hDu hw hz m hu₁ hw₀
  have hC₂ : ‖iteratedFDeriv ℝ m C₂ z‖ ≤
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * A :=
    norm_jet_bilinear_bound (spaceRestriction Space) hU hDw hu hz m hw₁ hu₀
  have hC₃ : ‖iteratedFDeriv ℝ m C₃ z‖ ≤
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * W :=
    norm_jet_bilinear_bound (spaceRestriction Space) hU hDw hw hz m hw₁ hw₀
  have hTL := (norm_jet_sub_le hU hTs hLs hz m).trans (add_le_add hT hL)
  have hTLR := (norm_jet_add_le hU (hTs.sub hLs) hRs hz m).trans (add_le_add hTL hR)
  have h₁ := (norm_jet_add_le hU ((hTs.sub hLs).add hRs) hC₁s hz m).trans
    (add_le_add hTLR hC₁)
  have h₂ := (norm_jet_add_le hU (((hTs.sub hLs).add hRs).add hC₁s) hC₂s hz m).trans
    (add_le_add h₁ hC₂)
  have h₃ := (norm_jet_add_le hU ((((hTs.sub hLs).add hRs).add hC₁s).add hC₂s) hC₃s hz m).trans
    (add_le_add h₂ hC₃)
  rw [iteratedFDeriv_eqOn hU (residualDifference_eq_jetExpression hU hu hw hp hr) m hz]
  exact h₃

end FullJetExpression

section ScaleDomain

open ProblemStatement





end ScaleDomain

end NavierStokes.ResidualStability
