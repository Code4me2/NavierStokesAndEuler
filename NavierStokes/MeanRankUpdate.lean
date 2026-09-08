import NavierStokes.FiveRowRank
import NavierStokes.FiveProfileMoments
import NavierStokes.PressureStream
import NavierStokes.WeightedClasses
import NavierStokes.PhysicalCoordinateBounds
import NavierStokes.ParametricFlatFactor
import NavierStokes.ReservedPatches
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The physical five-row mean update

The update is the constructed power-moment inverse, transported with the
physical length and velocity scales. Each moment carries its own scale.
-/

noncomputable section

namespace NavierStokes.MeanRankUpdate

open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Topology

abbrev Debt := FiveRowRank.Debt

noncomputable def scaleField (ell U : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun r => U * f (r / ell)

/-- Pressure, angular moment, and axial moment have distinct length powers. -/
noncomputable def scaleDebt (ell U : ℝ) (d : Debt) : Debt :=
  ![U ^ 2 * d 0, ell ^ 3 * U ^ 2 * d 1, ell ^ 2 * U ^ 2 * d 2]

noncomputable def normalizeDebt (ell U : ℝ) (d : Debt) : Debt :=
  ![d 0 / U ^ 2, d 1 / (ell ^ 3 * U ^ 2), d 2 / (ell ^ 2 * U ^ 2)]

theorem scale_normalizeDebt {ell U : ℝ} (hell : ell ≠ 0) (hU : U ≠ 0) (d : Debt) :
    scaleDebt ell U (normalizeDebt ell U d) = d := by
  ext i
  fin_cases i <;> simp [scaleDebt, normalizeDebt] <;> field_simp


theorem integral_scaled {ell : ℝ} (hell : 0 < ell) (c : ℝ) (f : ℝ → ℝ) :
    (∫ r, c * f (r / ell)) = ell * c * ∫ x, f x := by
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_div, abs_of_pos hell, smul_eq_mul]
  ring

theorem scaleField_smooth (ell U : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scaleField ell U f) :=
  contDiff_const.mul (hf.comp (contDiff_id.div_const ell))

theorem scaleField_tsupport {ell : ℝ} (hell : 0 < ell) (U a b : ℝ) {f : ℝ → ℝ}
    (hs : tsupport f ⊆ Ioo a b) : tsupport (scaleField ell U f) ⊆ Ioo (ell * a) (ell * b) := by
  have hclosed : IsClosed {r : ℝ | r / ell ∈ tsupport f} :=
    (isClosed_tsupport f).preimage (continuous_id.div_const ell)
  have hsup : support (scaleField ell U f) ⊆ {r : ℝ | r / ell ∈ tsupport f} := by
    intro r hr
    apply subset_closure
    intro hf
    exact hr (by simp [scaleField, hf])
  intro r hr
  have hx := hs (closure_minimal hsup hclosed hr)
  exact ⟨by simpa only [mul_comm ell a] using (lt_div_iff₀ hell).1 hx.1,
    by simpa only [mul_comm ell b] using (div_lt_iff₀ hell).1 hx.2⟩


theorem scaled_angular_mass {ell : ℝ} (hell : 0 < ell) (U : ℝ) (f : ℝ → ℝ) :
    (∫ r, r ^ (2 : ℕ) * scaleField ell U f r) =
      ell ^ 3 * U * ∫ x, x ^ (2 : ℕ) * f x := by
  have he : (fun r => r ^ (2 : ℕ) * scaleField ell U f r) =
      (fun r => (ell ^ 2 * U) * ((r / ell) ^ (2 : ℕ) * f (r / ell))) := by
    funext r
    unfold scaleField
    field_simp [hell.ne']
  rw [he, integral_scaled hell (ell ^ 2 * U) (fun x => x ^ (2 : ℕ) * f x)]
  ring

theorem scaled_axial_mass {ell : ℝ} (hell : 0 < ell) (U : ℝ) (f : ℝ → ℝ) :
    (∫ r, r * scaleField ell U f r) = ell ^ 2 * U * ∫ x, x * f x := by
  have he : (fun r => r * scaleField ell U f r) =
      (fun r => (ell * U) * ((r / ell) * f (r / ell))) := by
    funext r
    unfold scaleField
    field_simp [hell.ne']
  rw [he, integral_scaled hell (ell * U) (fun x => x * f x)]
  ring

theorem scaled_pressure_row {ell : ℝ} (hell : 0 < ell) (U : ℝ) (V f : ℝ → ℝ) :
    (∫ r, (2 * scaleField ell U V r / r) * scaleField ell U f r) =
      U ^ 2 * ∫ x, (2 * V x / x) * f x := by
  have he : (fun r => (2 * scaleField ell U V r / r) * scaleField ell U f r) =
      (fun r => (U ^ 2 / ell) * ((2 * V (r / ell) / (r / ell)) * f (r / ell))) := by
    funext r
    by_cases hr : r = 0
    · simp [scaleField, hr]
    · unfold scaleField
      field_simp [hell.ne', hr]
  rw [he, integral_scaled hell (U ^ 2 / ell) (fun x => (2 * V x / x) * f x)]
  field_simp [hell.ne']

theorem scaled_angular_row {ell : ℝ} (hell : 0 < ell) (U : ℝ) (V G f g : ℝ → ℝ) :
    (∫ r, r ^ (2 : ℕ) *
      (scaleField ell U G r * scaleField ell U f r + scaleField ell U V r * scaleField ell U g r)) =
        ell ^ 3 * U ^ 2 * ∫ x, x ^ (2 : ℕ) * (G x * f x + V x * g x) := by
  have he : (fun r => r ^ (2 : ℕ) *
      (scaleField ell U G r * scaleField ell U f r + scaleField ell U V r * scaleField ell U g r)) =
      (fun r => (ell ^ 2 * U ^ 2) *
        ((r / ell) ^ (2 : ℕ) * (G (r / ell) * f (r / ell) + V (r / ell) * g (r / ell)))) := by
    funext r
    unfold scaleField
    field_simp [hell.ne']
  rw [he, integral_scaled hell (ell ^ 2 * U ^ 2) (fun x => x ^ (2 : ℕ) * (G x * f x + V x * g x))]
  ring

theorem scaled_axial_row {ell : ℝ} (hell : 0 < ell) (U : ℝ) (V G f g : ℝ → ℝ) :
    (∫ r, 2 * r * scaleField ell U G r * scaleField ell U g r -
      r * scaleField ell U V r * scaleField ell U f r) =
        ell ^ 2 * U ^ 2 * ∫ x, 2 * x * G x * g x - x * V x * f x := by
  have he : (fun r => 2 * r * scaleField ell U G r * scaleField ell U g r -
      r * scaleField ell U V r * scaleField ell U f r) =
      (fun r => (ell * U ^ 2) *
        (2 * (r / ell) * G (r / ell) * g (r / ell) - (r / ell) * V (r / ell) * f (r / ell))) := by
    funext r
    unfold scaleField
    field_simp [hell.ne']
  rw [he, integral_scaled hell (ell * U ^ 2) (fun x => 2 * x * G x * g x - x * V x * f x)]
  ring

theorem fiveRows_scaled {ell : ℝ} (hell : 0 < ell) (U : ℝ) {V G f g : ℝ → ℝ}
    {d : Debt} (h : FiveRowRank.FiveRows V G d f g) :
    FiveRowRank.FiveRows (scaleField ell U V) (scaleField ell U G)
      (scaleDebt ell U d) (scaleField ell U f) (scaleField ell U g) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [scaled_angular_mass hell, h1, mul_zero]
  · rw [scaled_axial_mass hell, h2, mul_zero]
  · rw [scaled_pressure_row hell, h3]
    simp only [scaleDebt, Matrix.cons_val_zero]
    ring
  · rw [scaled_angular_row hell, h4]
    simp only [scaleDebt, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  · rw [scaled_axial_row hell, h5]
    simp [scaleDebt]

noncomputable def angularIncrement (lam C a b ell U : ℝ) (d : Debt) : ℝ → ℝ :=
  scaleField ell U (FiveRowRank.deltaV lam C a b (normalizeDebt ell U d))

noncomputable def desiredAxialIncrement (lam C a b ell U : ℝ) (d : Debt) : ℝ → ℝ :=
  scaleField ell U (FiveRowRank.gamma lam C a b (normalizeDebt ell U d))

noncomputable def background (lam C ell U : ℝ) : ℝ → ℝ :=
  scaleField ell U (FiveRowRank.background lam C)

/-- Equation (35) in physical units, with no assumed rank or inverse. -/
theorem physical_five_rows {lam C a b ell U : ℝ} (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) (hell : 0 < ell) (hU : U ≠ 0) (d : Debt) :
    FiveRowRank.FiveRows (background lam C ell U) (fun _ => 0) d
      (angularIncrement lam C a b ell U d) (desiredAxialIncrement lam C a b ell U d) := by
  have h := fiveRows_scaled hell U
    (FiveRowRank.five_rows lam C a b (normalizeDebt ell U d) hlam hC ha hab)
  rw [scale_normalizeDebt hell.ne' hU] at h
  have hz : scaleField ell U (fun _ => 0) = (fun _ => 0) := by
    funext r
    simp [scaleField]
  rw [hz] at h
  exact h


theorem desiredAxialIncrement_smooth (lam C a b ell U : ℝ) (d : Debt) :
    ContDiff ℝ ∞ (desiredAxialIncrement lam C a b ell U d) :=
  scaleField_smooth ell U (FiveRowRank.gamma_contDiff _ _ _ _ _)

theorem angularIncrement_tsupport (lam C a b U : ℝ) {ell : ℝ} (hell : 0 < ell)
    (hab : a < b) (d : Debt) :
    tsupport (angularIncrement lam C a b ell U d) ⊆ Ioo (ell * a) (ell * b) :=
  scaleField_tsupport hell U a b (FiveRowRank.deltaV_tsupport_subset _ _ _ _ _ hab)

theorem desiredAxialIncrement_tsupport (lam C a b U : ℝ) {ell : ℝ} (hell : 0 < ell)
    (hab : a < b) (d : Debt) :
    tsupport (desiredAxialIncrement lam C a b ell U d) ⊆ Ioo (ell * a) (ell * b) :=
  scaleField_tsupport hell U a b (FiveRowRank.gamma_tsupport_subset _ _ _ _ _ hab)

theorem physical_rows_on_patch {lam C a b ell U : ℝ} (hlam : 0 < lam) (hC : C ≠ 0)
    (ha : 0 < a) (hab : a < b) (hell : 0 < ell) (hU : U ≠ 0) (d : Debt)
    (V G : ℝ → ℝ) (hV : ∀ r ∈ Ioo (ell * a) (ell * b), V r = background lam C ell U r)
    (hG : ∀ r ∈ Ioo (ell * a) (ell * b), G r = 0) :
    FiveRowRank.FiveRows V G d (angularIncrement lam C a b ell U d)
      (desiredAxialIncrement lam C a b ell U d) := by
  have h := physical_five_rows hlam hC ha hab hell hU d
  have hv0 : ∀ r, r ∉ Ioo (ell * a) (ell * b) → angularIncrement lam C a b ell U d r = 0 := by
    intro r hr
    by_contra hn
    exact hr (angularIncrement_tsupport lam C a b U hell hab d (subset_closure hn))
  have hg0 : ∀ r, r ∉ Ioo (ell * a) (ell * b) → desiredAxialIncrement lam C a b ell U d r = 0 := by
    intro r hr
    by_contra hn
    exact hr (desiredAxialIncrement_tsupport lam C a b U hell hab d (subset_closure hn))
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · rw [← h.2.2.1]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      dsimp only
      by_cases hr : r ∈ Ioo (ell * a) (ell * b)
      · rw [hV r hr]
      · rw [hv0 r hr]
        simp
  · rw [← h.2.2.2.1]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      dsimp only
      by_cases hr : r ∈ Ioo (ell * a) (ell * b)
      · rw [hV r hr, hG r hr]
      · rw [hv0 r hr, hg0 r hr]
        simp
  · rw [← h.2.2.2.2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      dsimp only
      by_cases hr : r ∈ Ioo (ell * a) (ell * b)
      · rw [hV r hr, hG r hr]
      · rw [hv0 r hr, hg0 r hr]
        simp

section Families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scaleFamily (ell U : E → ℝ) (H : E × ℝ → ℝ) : ℝ × E → ℝ :=
  fun p => U p.2 * H (p.2, p.1 / ell p.2)

theorem scaleFamily_contDiffOn {S : Set E} {ell U : E → ℝ} {H : E × ℝ → ℝ}
    (hl : ContDiffOn ℝ ∞ ell S) (hU : ContDiffOn ℝ ∞ U S)
    (hln : ∀ p ∈ S, ell p ≠ 0) (hH : ContDiffOn ℝ ∞ H (S ×ˢ univ)) :
    ContDiffOn ℝ ∞ (scaleFamily ell U H) (univ ×ˢ S) := by
  have hL : ContDiffOn ℝ ∞ (fun p : ℝ × E => ell p.2) (univ ×ˢ S) :=
    hl.comp contDiffOn_snd (fun _ hp => hp.2)
  have hV : ContDiffOn ℝ ∞ (fun p : ℝ × E => U p.2) (univ ×ˢ S) :=
    hU.comp contDiffOn_snd (fun _ hp => hp.2)
  have harg : ContDiffOn ℝ ∞ (fun p : ℝ × E => (p.2, p.1 / ell p.2)) (univ ×ˢ S) :=
    contDiffOn_snd.prodMk (contDiffOn_fst.div hL (fun _ hp => hln _ hp.2))
  exact hV.mul (hH.comp harg (fun p hp => ⟨hp.2, mem_univ _⟩))

noncomputable def angularFamily (lam a b : ℝ) (ell U C : E → ℝ) (d : E → Debt) :
    ℝ × E → ℝ :=
  scaleFamily ell U (fun p => FiveRowRank.deltaV lam (C p.1) a b
    (normalizeDebt (ell p.1) (U p.1) (d p.1)) p.2)

noncomputable def desiredAxialFamily (lam a b : ℝ) (ell U C : E → ℝ) (d : E → Debt) :
    ℝ × E → ℝ :=
  scaleFamily ell U (fun p => FiveRowRank.gamma lam (C p.1) a b
    (normalizeDebt (ell p.1) (U p.1) (d p.1)) p.2)

theorem normalizeDebt_contDiffOn {S : Set E} {ell U : E → ℝ} {d : E → Debt}
    (hl : ContDiffOn ℝ ∞ ell S) (hU : ContDiffOn ℝ ∞ U S)
    (hd : ContDiffOn ℝ ∞ d S) (hln : ∀ p ∈ S, ell p ≠ 0) (hUn : ∀ p ∈ S, U p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => normalizeDebt (ell p) (U p) (d p)) S := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (contDiffOn_pi.mp hd 0).div (hU.pow 2) (fun p hp => pow_ne_zero _ (hUn p hp))
  · exact (contDiffOn_pi.mp hd 1).div ((hl.pow 3).mul (hU.pow 2))
      (fun p hp => mul_ne_zero (pow_ne_zero _ (hln p hp)) (pow_ne_zero _ (hUn p hp)))
  · exact (contDiffOn_pi.mp hd 2).div ((hl.pow 2).mul (hU.pow 2))
      (fun p hp => mul_ne_zero (pow_ne_zero _ (hln p hp)) (pow_ne_zero _ (hUn p hp)))

theorem angularFamily_contDiffOn (lam a b : ℝ) {S : Set E} {ell U C : E → ℝ}
    {d : E → Debt} (hl : ContDiffOn ℝ ∞ ell S) (hU : ContDiffOn ℝ ∞ U S)
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hln : ∀ p ∈ S, ell p ≠ 0) (hUn : ∀ p ∈ S, U p ≠ 0)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (angularFamily lam a b ell U C d) (univ ×ˢ S) := by
  have hN : ContDiffOn ℝ ∞ (fun p => normalizeDebt (ell p) (U p) (d p)) S :=
    normalizeDebt_contDiffOn hl hU hd hln hUn
  have hR := FiveRowRank.deltaV_joint_contDiffOn lam a b (S := S) (C := C)
    (d := fun p => normalizeDebt (ell p) (U p) (d p)) hC hN hCn
  exact scaleFamily_contDiffOn (S := S) (ell := ell) (U := U)
    (H := fun p => FiveRowRank.deltaV lam (C p.1) a b
      (normalizeDebt (ell p.1) (U p.1) (d p.1)) p.2) hl hU hln hR

theorem desiredAxialFamily_contDiffOn (lam a b : ℝ) {S : Set E} {ell U C : E → ℝ}
    {d : E → Debt} (hl : ContDiffOn ℝ ∞ ell S) (hU : ContDiffOn ℝ ∞ U S)
    (hC : ContDiffOn ℝ ∞ C S) (hd : ContDiffOn ℝ ∞ d S)
    (hln : ∀ p ∈ S, ell p ≠ 0) (hUn : ∀ p ∈ S, U p ≠ 0)
    (hCn : ∀ p ∈ S, C p ≠ 0) :
    ContDiffOn ℝ ∞ (desiredAxialFamily lam a b ell U C d) (univ ×ˢ S) := by
  have hN : ContDiffOn ℝ ∞ (fun p => normalizeDebt (ell p) (U p) (d p)) S :=
    normalizeDebt_contDiffOn hl hU hd hln hUn
  have hR := FiveRowRank.gamma_joint_contDiffOn lam a b (S := S) (C := C)
    (d := fun p => normalizeDebt (ell p) (U p) (d p)) hC hN hCn
  exact scaleFamily_contDiffOn (S := S) (ell := ell) (U := U)
    (H := fun p => FiveRowRank.gamma lam (C p.1) a b
      (normalizeDebt (ell p.1) (U p.1) (d p.1)) p.2) hl hU hln hR

theorem angularFamily_contDiff (lam a b : ℝ) {ell U C : E → ℝ} {d : E → Debt}
    (hl : ContDiff ℝ ∞ ell) (hU : ContDiff ℝ ∞ U)
    (hC : ContDiff ℝ ∞ C) (hd : ContDiff ℝ ∞ d)
    (hln : ∀ p, ell p ≠ 0) (hUn : ∀ p, U p ≠ 0) (hCn : ∀ p, C p ≠ 0) :
    ContDiff ℝ ∞ (angularFamily lam a b ell U C d) := by
  simpa only [univ_prod_univ, contDiffOn_univ] using
    angularFamily_contDiffOn lam a b (S := univ) hl.contDiffOn hU.contDiffOn hC.contDiffOn hd.contDiffOn
      (fun p _ => hln p) (fun p _ => hUn p) (fun p _ => hCn p)

theorem desiredAxialFamily_contDiff (lam a b : ℝ) {ell U C : E → ℝ} {d : E → Debt}
    (hl : ContDiff ℝ ∞ ell) (hU : ContDiff ℝ ∞ U)
    (hC : ContDiff ℝ ∞ C) (hd : ContDiff ℝ ∞ d)
    (hln : ∀ p, ell p ≠ 0) (hUn : ∀ p, U p ≠ 0) (hCn : ∀ p, C p ≠ 0) :
    ContDiff ℝ ∞ (desiredAxialFamily lam a b ell U C d) := by
  simpa only [univ_prod_univ, contDiffOn_univ] using
    desiredAxialFamily_contDiffOn lam a b (S := univ) hl.contDiffOn hU.contDiffOn hC.contDiffOn hd.contDiffOn
      (fun p _ => hln p) (fun p _ => hUn p) (fun p _ => hCn p)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A common radial annulus follows from bounds on the physical length. -/
theorem desiredAxialFamily_supported (lam a b : ℝ) {ell U C : E → ℝ} (d : E → Debt)
    (hab : a < b) (hl : ∀ s, 0 < ell s) {lo hi : ℝ}
    (hlo : ∀ s, lo ≤ ell s * a) (hhi : ∀ s, ell s * b ≤ hi) :
    RadialAlias.RadiallySupported lo hi (desiredAxialFamily lam a b ell U C d) := by
  intro p hp
  have hs := desiredAxialIncrement_tsupport lam (C p.2) a b (U p.2) (hl p.2) hab (d p.2)
    (subset_closure hp)
  exact ⟨(hlo p.2).trans hs.1.le, hs.2.le.trans (hhi p.2)⟩


end Families

section SlowStream

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The slow source is independent of both periodic phase variables. -/
noncomputable def slowLift (f : ℝ × E → ℝ) : PressureStream.Lift E → ℝ :=
  fun p => f (p.1, p.2.1)

theorem slowLift_contDiff {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (slowLift f) :=
  hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem slowLift_supported {f : ℝ × E → ℝ} {a b : ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (slowLift f) := by
  intro p hp
  exact hs hp


omit [NormedSpace ℝ E] in
theorem radial_integral_eq_interval {a b : ℝ} {f : ℝ × E → ℝ}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f) (s : E) :
    (∫ r in a..b, f (r, s)) = ∫ r, f (r, s) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  have hc : Continuous (fun r => f (r, s)) := hf.comp (continuous_id.prodMk continuous_const)
  have ho : support (fun r => f (r, s)) ⊆ Ioo a b := by
    simpa only [interior_Icc] using hc.isOpen_support.subset_interior_iff.mpr
      (show support (fun r => f (r, s)) ⊆ Icc a b from fun r hr => hs hr)
  exact ho.trans Ioo_subset_Ioc_self

/-- With a slow source the transported total is the ordinary radial mass. -/
theorem slow_physicalTotal {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : PressureStream.Plane) {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (p : PressureStream.Lift E) (hp : a ≤ p.1) :
    PressureStream.physicalTotal d a M ((0 : E), v) (slowLift f) p =
      ∫ r, f (r, p.2.1) := by
  rw [PressureStream.physicalTotal_eq_integral ha hab hd ((0 : E), v)
    (slowLift_contDiff hf) (slowLift_supported hs) p hp]
  simpa [slowLift] using radial_integral_eq_interval hf.continuous hs p.2.1

/-- There is exactly zero compactification alias for a zero-mass slow source. -/
theorem slow_physicalAlias_zero {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : PressureStream.Plane) {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (hm : ∀ s, (∫ r, f (r, s)) = 0)
    (p : PressureStream.Lift E) :
    RadialPullback.physicalAlias d a b M ((0 : E), v) (slowLift f) p = 0 := by
  by_cases hp : a ≤ p.1
  · rw [RadialPullback.physicalAlias_eq_cutoff_derivative_global ha hab hd]
    change deriv (RadialPullback.physicalCutoff d a b) p.1 •
      PressureStream.physicalTotal d a M ((0 : E), v) (slowLift f) p = 0
    rw [slow_physicalTotal ha hab hd v hf hs p hp, hm, smul_zero]
  · exact TransportPrimitive.radial_zero_of_lt
      (RadialPullback.physicalAlias_supported ha hab hd M ((0 : E), v) (slowLift f))
      (lt_of_not_ge hp)

/-- The actual stream realizes the desired slow axial field, pointwise, including the axis. -/
theorem slow_streamGamma_eq_desired {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : PressureStream.Plane) {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (hm : ∀ s, (∫ r, r * f (r, s)) = 0)
    (p : PressureStream.Lift E) :
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : E), v)
      (PressureStream.streamPotential d a b M ((0 : E), v) (slowLift f)) p = slowLift f p := by
  rw [PressureStream.streamGamma_eq_desired_sub_alias_global ha hab hd ((0 : E), v)
    (slowLift_contDiff hf) (slowLift_supported hs)]
  have he : PressureStream.weightedSource (slowLift f) =
      slowLift (PressureStream.weightedSource f) := rfl
  rw [he, slow_physicalAlias_zero ha hab hd v (PressureStream.weightedSource_contDiff hf)
    (PressureStream.weightedSource_supported hs) hm, zero_div, sub_zero]

/-- The radial companion is the actual axial derivative of the same stream. -/
theorem slow_stream_divergence_zero {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : PressureStream.Plane) (w : E × PressureStream.Plane) {f : ℝ × E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (p : PressureStream.Lift E) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed d M) ((0 : E), v) w
      (PressureStream.streamBeta w
        (PressureStream.streamPotential d a b M ((0 : E), v) (slowLift f)))
      (PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : E), v)
        (PressureStream.streamPotential d a b M ((0 : E), v) (slowLift f))) p = 0 :=
  PressureStream.reconstructed_divergence_zero ha hab hd ((0 : E), v) w
    (slowLift_contDiff hf) (slowLift_supported hs) p

end SlowStream

section LinearConstruction

noncomputable def normalizeDebtLinearMap (ell U : ℝ) : Debt →ₗ[ℝ] Debt where
  toFun := normalizeDebt ell U
  map_add' d e := by
    ext i
    fin_cases i <;> simp [normalizeDebt, add_div]
  map_smul' c d := by
    ext i
    fin_cases i <;> simp [normalizeDebt, mul_div_assoc]

noncomputable def scaleFieldLinearMap (ell U : ℝ) : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun := scaleField ell U
  map_add' f g := by ext r; simp [scaleField, mul_add]
  map_smul' c f := by ext r; simp [scaleField]; ring

noncomputable def angularLinearMap (lam C a b ell U : ℝ) : Debt →ₗ[ℝ] (ℝ → ℝ) :=
  (scaleFieldLinearMap ell U).comp
    ((FiveRowRank.deltaVLinearMap lam C a b).comp (normalizeDebtLinearMap ell U))

noncomputable def axialLinearMap (lam C a b ell U : ℝ) : Debt →ₗ[ℝ] (ℝ → ℝ) :=
  (scaleFieldLinearMap ell U).comp
    ((FiveRowRank.gammaLinearMap lam C a b).comp (normalizeDebtLinearMap ell U))

theorem debt_eq_sum (d : Debt) : d = ∑ i : Fin 3, d i • (Pi.single i (1 : ℝ) : Debt) := by
  classical
  ext j
  simp [Pi.single_apply]

theorem linearMap_eq_sum {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (L : Debt →ₗ[ℝ] F) (d : Debt) : L d = ∑ i : Fin 3, d i • L (Pi.single i 1) := by
  simpa only [map_sum, map_smul] using congrArg L (debt_eq_sum d)

/-- The update is a fixed finite linear combination of constructed profiles. -/
theorem angularIncrement_eq_sum (lam C a b ell U : ℝ) (d : Debt) (r : ℝ) :
    angularIncrement lam C a b ell U d r =
      ∑ i : Fin 3, d i * angularIncrement lam C a b ell U (Pi.single i 1) r := by
  have h := congrFun (linearMap_eq_sum (angularLinearMap lam C a b ell U) d) r
  simpa only [angularLinearMap, LinearMap.comp_apply, scaleFieldLinearMap,
    normalizeDebtLinearMap, LinearMap.coe_mk, AddHom.coe_mk, FiveRowRank.deltaVLinearMap_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, angularIncrement] using h

theorem desiredAxialIncrement_eq_sum (lam C a b ell U : ℝ) (d : Debt) (r : ℝ) :
    desiredAxialIncrement lam C a b ell U d r =
      ∑ i : Fin 3, d i * desiredAxialIncrement lam C a b ell U (Pi.single i 1) r := by
  have h := congrFun (linearMap_eq_sum (axialLinearMap lam C a b ell U) d) r
  simpa only [axialLinearMap, LinearMap.comp_apply, scaleFieldLinearMap,
    normalizeDebtLinearMap, LinearMap.coe_mk, AddHom.coe_mk, FiveRowRank.gammaLinearMap_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, desiredAxialIncrement] using h






end LinearConstruction

section NormalizedGeometry

abbrev ModelPoint := PhysicalCoordinateBounds.Point

/-- The fixed shaped amplitude on the untouched patch. -/
noncomputable def shapedAmplitude (B η : ℝ) : ℝ := B / (1 + η ^ 2)

theorem shapedAmplitude_contDiff (B : ℝ) : ContDiff ℝ ∞ (shapedAmplitude B) :=
  contDiff_const.div (contDiff_const.add (contDiff_id.pow 2)) (fun η => by positivity)

theorem shapedAmplitude_ne_zero {B : ℝ} (hB : B ≠ 0) (η : ℝ) :
    shapedAmplitude B η ≠ 0 := div_ne_zero hB (by positivity)

noncomputable def modelLength (y : ModelPoint) : ℝ := Real.sqrt y.1
noncomputable def modelVelocity (A : ℝ) (y : ModelPoint) : ℝ := y.1 ^ (-A)
noncomputable def modelAmplitude (coord B : ℝ) (y : ModelPoint) : ℝ :=
  shapedAmplitude B (y.2.2 / y.1 ^ PhysicalCoordinateBounds.D coord)

theorem modelLength_contDiffOn :
    ContDiffOn ℝ ∞ modelLength PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  exact (contDiffAt_fst.sqrt (ne_of_gt hy)).contDiffWithinAt

theorem modelVelocity_contDiffOn (A : ℝ) :
    ContDiffOn ℝ ∞ (modelVelocity A) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  exact (contDiffAt_fst.rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt

theorem modelAmplitude_contDiffOn (coord B : ℝ) :
    ContDiffOn ℝ ∞ (modelAmplitude coord B) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  exact ((shapedAmplitude_contDiff B).contDiffAt.comp y
    (contDiffAt_snd.snd.div (contDiffAt_fst.rpow_const_of_ne (ne_of_gt hy))
      (Real.rpow_pos_of_pos hy _).ne')).contDiffWithinAt

noncomputable def angularModel (coord A B lam a b : ℝ) (d : Debt) (y : ModelPoint) : ℝ :=
  angularFamily lam a b modelLength (modelVelocity A) (modelAmplitude coord B) (fun _ => d)
    (y.2.1, y)

noncomputable def axialModel (coord A B lam a b : ℝ) (d : Debt) (y : ModelPoint) : ℝ :=
  desiredAxialFamily lam a b modelLength (modelVelocity A) (modelAmplitude coord B) (fun _ => d)
    (y.2.1, y)

theorem angularModel_contDiffOn (coord A B lam a b : ℝ) (hB : B ≠ 0) (d : Debt) :
    ContDiffOn ℝ ∞ (angularModel coord A B lam a b d) PhysicalCoordinateBounds.positiveTime := by
  have h := angularFamily_contDiffOn lam a b (S := PhysicalCoordinateBounds.positiveTime)
    (ell := modelLength) (U := modelVelocity A) (C := modelAmplitude coord B) (d := fun _ => d)
    modelLength_contDiffOn (modelVelocity_contDiffOn A) (modelAmplitude_contDiffOn coord B)
    contDiffOn_const (fun y hy => (Real.sqrt_pos.mpr hy).ne')
    (fun y hy => (Real.rpow_pos_of_pos hy _).ne')
    (fun y _ => shapedAmplitude_ne_zero hB _)
  exact h.comp (((contDiff_fst.comp contDiff_snd).prodMk contDiff_id).contDiffOn)
    (fun y hy => ⟨mem_univ _, hy⟩)

theorem axialModel_contDiffOn (coord A B lam a b : ℝ) (hB : B ≠ 0) (d : Debt) :
    ContDiffOn ℝ ∞ (axialModel coord A B lam a b d) PhysicalCoordinateBounds.positiveTime := by
  have h := desiredAxialFamily_contDiffOn lam a b (S := PhysicalCoordinateBounds.positiveTime)
    (ell := modelLength) (U := modelVelocity A) (C := modelAmplitude coord B) (d := fun _ => d)
    modelLength_contDiffOn (modelVelocity_contDiffOn A) (modelAmplitude_contDiffOn coord B)
    contDiffOn_const (fun y hy => (Real.sqrt_pos.mpr hy).ne')
    (fun y hy => (Real.rpow_pos_of_pos hy _).ne')
    (fun y _ => shapedAmplitude_ne_zero hB _)
  exact h.comp (((contDiff_fst.comp contDiff_snd).prodMk contDiff_id).contDiffOn)
    (fun y hy => ⟨mem_univ _, hy⟩)

noncomputable def modelBox (qlo qhi rlo rhi : ℝ) : Set ModelPoint :=
  Icc qlo qhi ×ˢ (Icc rlo rhi ×ˢ Icc (-1 : ℝ) 1)

noncomputable def modelToInverse (coord : ℝ) (y : ModelPoint) : ModelPoint :=
  (y.1, (y.2.1, y.2.2 * y.1 ^ PhysicalCoordinateBounds.D coord))

theorem modelToInverse_contDiffOn (coord : ℝ) :
    ContDiffOn ℝ ∞ (modelToInverse coord) PhysicalCoordinateBounds.positiveTime := by
  intro y hy
  exact (contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk
    (contDiffAt_snd.snd.mul (contDiffAt_fst.rpow_const_of_ne (ne_of_gt hy))))).contDiffWithinAt

theorem modelToInverse_slope {q : ℝ} (hq : 0 < q) (coord R η : ℝ) :
    SimilarityCoordinates.scalarSlope coord (modelToInverse coord (q, R, η)).2.2
      (modelToInverse coord (q, R, η)).1 = 1 - coord * η ^ 2 := by
  have hp : (q ^ PhysicalCoordinateBounds.D coord) ^ (2 : ℕ) * q ^ (coord - 1) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
    norm_num only [Nat.cast_ofNat]
    have he : PhysicalCoordinateBounds.D coord * (2 : ℝ) + (coord - 1) = 0 := by
      unfold PhysicalCoordinateBounds.D
      ring
    rw [he, Real.rpow_zero]
  simp only [modelToInverse, SimilarityCoordinates.scalarSlope, mul_pow]
  calc
    1 - η ^ 2 * (q ^ PhysicalCoordinateBounds.D coord) ^ 2 * coord * q ^ (coord - 1) =
      1 - coord * η ^ 2 * ((q ^ PhysicalCoordinateBounds.D coord) ^ 2 * q ^ (coord - 1)) := by ring
    _ = 1 - coord * η ^ 2 := by rw [hp, mul_one]

theorem modelBox_slope_pos {coord qlo qhi rlo rhi : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (hqlo : 0 < qlo) {y : ModelPoint} (hy : y ∈ modelBox qlo qhi rlo rhi) :
    0 < SimilarityCoordinates.scalarSlope coord (modelToInverse coord y).2.2
      (modelToInverse coord y).1 := by
  rw [modelToInverse_slope (hqlo.trans_le hy.1.1)]
  have hη : y.2.2 ^ 2 ≤ 1 := by nlinarith [hy.2.2.1, hy.2.2.2]
  nlinarith [mul_le_mul_of_nonneg_left hη hc.le]

theorem modelBox_image_isCompact {qlo qhi rlo rhi : ℝ} (hqlo : 0 < qlo) (coord : ℝ) :
    IsCompact (modelToInverse coord '' modelBox qlo qhi rlo rhi) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image_of_continuousOn
    ((modelToInverse_contDiffOn coord).continuousOn.mono (fun _ hy => hqlo.trans_le hy.1.1))

theorem inverseCoordinates_mem_modelBox {coord qlo qhi rlo rhi : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) {p : ModelPoint}
    (hp : p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : PhysicalCoordinateBounds.qCoord coord p ∈ Icc qlo qhi) (hR : p.2.1 ∈ Icc rlo rhi) :
    PhysicalCoordinateBounds.inverseCoordinates coord p ∈
      modelToInverse coord '' modelBox qlo qhi rlo rhi := by
  have hqpos := PhysicalCoordinateBounds.qCoord_pos hc hc1 hp
  have hη := SimilarityCoordinates.coordinateEta_abs_lt_one hc hc1
    (p := (p.1, p.2.2)) hp
  refine ⟨(PhysicalCoordinateBounds.qCoord coord p, p.2.1,
    PhysicalCoordinateBounds.etaCoord coord p), ⟨hq, hR, ?_⟩, ?_⟩
  · exact ⟨(abs_lt.mp hη).1.le, (abs_lt.mp hη).2.le⟩
  · simp only [modelToInverse, PhysicalCoordinateBounds.inverseCoordinates,
      PhysicalCoordinateBounds.etaCoord]
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hqpos _).ne']

/-- Actual inverse-coordinate jets remain bounded on a normalized closed
`q` interval, including both limiting values `η=±1`. -/
theorem inverse_kernel_jet_bound {coord qlo qhi rlo rhi : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hqlo : 0 < qlo) {g : ModelPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g PhysicalCoordinateBounds.positiveTime) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ PhysicalCoordinateBounds.positiveTime,
      PhysicalCoordinateBounds.qCoord coord p ∈ Icc qlo qhi → p.2.1 ∈ Icc rlo rhi →
      ‖iteratedFDeriv ℝ j (g ∘ PhysicalCoordinateBounds.inverseCoordinates coord) p‖ ≤ C := by
  have hK := modelBox_image_isCompact (qlo := qlo) (qhi := qhi) (rlo := rlo) (rhi := rhi) hqlo coord
  have hcont : ContinuousOn (PhysicalCoordinateBounds.inverseJet coord g j)
      (modelToInverse coord '' modelBox qlo qhi rlo rhi) := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hq : 0 < (modelToInverse coord z).1 := hqlo.trans_le hz.1.1
    exact (PhysicalCoordinateBounds.inverseJet_contDiffAt hq
      (modelBox_slope_pos hc hc1 hqlo hz).ne'
      (hg.contDiffAt (PhysicalCoordinateBounds.positiveTime_isOpen.mem_nhds hq)) j).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp hq hR
  rw [PhysicalCoordinateBounds.iteratedFDeriv_comp_inverse hc hc1 hg j hp]
  exact (hC _ (inverseCoordinates_mem_modelBox hc hc1 hp hq hR)).trans (le_max_left _ _)

end NormalizedGeometry

section ClassTools

variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finiteJetBounds_of_orderBounds (f : D → ℝ) (S : Set D)
    (h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ JetBounds.FiniteJetBound m f S C := by
  intro m
  induction m with
  | zero =>
      obtain ⟨C, hC, hb⟩ := h 0
      refine ⟨C, hC, ?_⟩
      intro j hj x hx
      have hj0 : j = 0 := by omega
      subst j
      exact hb x hx
  | succ m ih =>
      obtain ⟨A, hA, hAjet⟩ := ih
      obtain ⟨B, hB, hBjet⟩ := h (m + 1)
      refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
      intro j hj x hx
      by_cases hjm : j ≤ m
      · exact (hAjet j hjm x hx).trans (le_max_left _ _)
      · have hje : j = m + 1 := by omega
        subst j
        exact (hBjet x hx).trans (le_max_right _ _)

theorem iteratedFDeriv_comp_linear {f : F → ℝ} {S : Set F}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) (L : D →L[ℝ] F) (j : ℕ)
    {x : D} (hx : L x ∈ S) :
    iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hpre := hS.preimage L.continuous
  have hd := L.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn hpre.uniqueDiffOn hx
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le
  rwa [iteratedFDerivWithin_of_isOpen j hpre hx, iteratedFDerivWithin_of_isOpen j hS hx] at hd

theorem iteratedFDeriv_congr_germ {f g : D → ℝ} {x : D}
    (he : f =ᶠ[𝓝 x] g) (j : ℕ) : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
  have h : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using h.iteratedFDerivWithin_eq he.self_of_nhds j

/-- An interior support and genuine finite jet bounds convert! a fixed
coefficient to the weighted mean class. -/
theorem meanClass_of_interior_support (s : WeightedClasses.StripData D) (f : D → ℝ)
    (hf : ContDiffOn ℝ ∞ f s.domain)
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ JetBounds.FiniteJetBound m f s.domain C)
    {K : Set D} (hK : IsClosed K) (hzero : ∀ x ∈ s.domain, x ∉ K → f x = 0)
    (hz : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s.domain, x ∈ K → δ ≤ s.zeta x) :
    WeightedClasses.MeanClass s 0 (fun _ => f) := by
  obtain ⟨δ, hδ, hz⟩ := hz
  refine ⟨fun _ x hx => s.zeta_nonneg x hx, fun _ => hf, ?_⟩
  intro m
  obtain ⟨C, hC, hjet⟩ := hb m
  refine ⟨C / δ, div_nonneg hC hδ.le, 0, ?_⟩
  intro n x hx j hj
  simp only [WeightedClasses.majorant, Real.rpow_zero, pow_zero, mul_one]
  by_cases hxK : x ∈ K
  · calc
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := hjet j hj x hx
      _ = (C / δ) * δ := by field_simp
      _ ≤ (C / δ) * s.zeta x :=
        mul_le_mul_of_nonneg_left (hz x hx hxK) (div_nonneg hC hδ.le)
  · have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [s.isOpen_domain.mem_nhds hx, hK.isOpen_compl.mem_nhds hxK] with y hy hyK
      exact hzero y hy hyK
    rw [iteratedFDeriv_congr_germ he j, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg (div_nonneg hC hδ.le) (s.zeta_nonneg x hx)

end ClassTools

section ChartFields

abbrev ChartPoint := PressureStream.Lift PressureStream.Plane

/-- `(R,(T,Z),Y)` to the actual inverse-coordinate variables `(T,R,Z)`. -/
noncomputable def chartInput : ChartPoint →L[ℝ] ModelPoint :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ PressureStream.Plane PressureStream.Plane).comp
      (ContinuousLinearMap.snd ℝ ℝ (PressureStream.Plane × PressureStream.Plane))))).prod
  ((ContinuousLinearMap.fst ℝ ℝ (PressureStream.Plane × PressureStream.Plane)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.fst ℝ PressureStream.Plane PressureStream.Plane).comp
        (ContinuousLinearMap.snd ℝ ℝ (PressureStream.Plane × PressureStream.Plane)))))

@[simp] theorem chartInput_apply (p : ChartPoint) : chartInput p = (p.2.1.1, p.1, p.2.1.2) := rfl

theorem chartInput_norm_le_one : ‖chartInput‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [chartInput_apply, one_mul, Prod.norm_def]
  apply max_le
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))

noncomputable def chartQ (coord : ℝ) (p : ChartPoint) : ℝ :=
  PhysicalCoordinateBounds.qCoord coord (chartInput p)

noncomputable def chartEta (coord : ℝ) (p : ChartPoint) : ℝ :=
  PhysicalCoordinateBounds.etaCoord coord (chartInput p)

noncomputable def chartKernel (coord : ℝ) (g : ModelPoint → ℝ) : ChartPoint → ℝ :=
  (g ∘ PhysicalCoordinateBounds.inverseCoordinates coord) ∘ chartInput

noncomputable def chartAngular (coord A B lam a b : ℝ) (d : ChartPoint → Debt) (p : ChartPoint) : ℝ :=
  angularIncrement lam (shapedAmplitude B (chartEta coord p)) a b
    (Real.sqrt (chartQ coord p)) (chartQ coord p ^ (-A)) (d p) p.1

noncomputable def chartAxial (coord A B lam a b : ℝ) (d : ChartPoint → Debt) (p : ChartPoint) : ℝ :=
  desiredAxialIncrement lam (shapedAmplitude B (chartEta coord p)) a b
    (Real.sqrt (chartQ coord p)) (chartQ coord p ^ (-A)) (d p) p.1

theorem chartAngular_eq_sum (coord A B lam a b : ℝ) (d : ChartPoint → Debt) (p : ChartPoint) :
    chartAngular coord A B lam a b d p = ∑ i : Fin 3, d p i *
      chartKernel coord (angularModel coord A B lam a b (Pi.single i 1)) p :=
  angularIncrement_eq_sum _ _ _ _ _ _ _ _

theorem chartAxial_eq_sum (coord A B lam a b : ℝ) (d : ChartPoint → Debt) (p : ChartPoint) :
    chartAxial coord A B lam a b d p = ∑ i : Fin 3, d p i *
      chartKernel coord (axialModel coord A B lam a b (Pi.single i 1)) p :=
  desiredAxialIncrement_eq_sum _ _ _ _ _ _ _ _

theorem chartKernel_contDiffOn {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {S : Set ChartPoint} (hS : ∀ p ∈ S, chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    {g : ModelPoint → ℝ} (hg : ContDiffOn ℝ ∞ g PhysicalCoordinateBounds.positiveTime) :
    ContDiffOn ℝ ∞ (chartKernel coord g) S :=
  (PhysicalCoordinateBounds.pullback_contDiffOn hc hc1 hg).comp chartInput.contDiff.contDiffOn hS

/-- All stripped jets of the actual inverse-coordinate pullback are uniformly
bounded, with no band in either the coefficient or the constant. -/
theorem chartKernel_finiteJetBounds {coord qlo qhi rlo rhi : ℝ}
    (hc : 0 < coord) (hc1 : coord < 1) (hqlo : 0 < qlo) {S : Set ChartPoint}
    (hT : ∀ p ∈ S, chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ p ∈ S, chartQ coord p ∈ Icc qlo qhi) (hR : ∀ p ∈ S, p.1 ∈ Icc rlo rhi)
    {g : ModelPoint → ℝ} (hg : ContDiffOn ℝ ∞ g PhysicalCoordinateBounds.positiveTime) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ JetBounds.FiniteJetBound m (chartKernel coord g) S C := by
  apply finiteJetBounds_of_orderBounds
  intro j
  obtain ⟨C, hC, hb⟩ := inverse_kernel_jet_bound (qhi := qhi) (rlo := rlo) (rhi := rhi)
    hc hc1 hqlo hg j
  refine ⟨C, hC, ?_⟩
  intro p hp
  change ‖iteratedFDeriv ℝ j ((g ∘ PhysicalCoordinateBounds.inverseCoordinates coord) ∘ chartInput) p‖ ≤ C
  rw [iteratedFDeriv_comp_linear PhysicalCoordinateBounds.positiveTime_isOpen
    (PhysicalCoordinateBounds.pullback_contDiffOn hc hc1 hg) chartInput j (hT p hp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (g ∘ PhysicalCoordinateBounds.inverseCoordinates coord) (chartInput p)‖ *
        ‖chartInput‖ ^ j := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ j (g ∘ PhysicalCoordinateBounds.inverseCoordinates coord) (chartInput p))
        (fun _ => chartInput)
    _ ≤ C * 1 := mul_le_mul (hb _ (hT p hp) (hq p hp) (hR p hp))
      (pow_le_one₀ (norm_nonneg _) chartInput_norm_le_one) (pow_nonneg (norm_nonneg _) _) hC
    _ = C := mul_one _

end ChartFields

section RankClass

noncomputable def supportBand (a b qlo qhi : ℝ) : Set ChartPoint :=
  Prod.fst ⁻¹' Icc (Real.sqrt qlo * a) (Real.sqrt qhi * b)

theorem supportBand_isClosed (a b qlo qhi : ℝ) : IsClosed (supportBand a b qlo qhi) :=
  isClosed_Icc.preimage continuous_fst

theorem angular_kernel_zero {coord A B lam a b qlo qhi : ℝ} (ha : 0 < a) (hab : a < b)
    (hqlo : 0 < qlo) (d : Debt) {p : ChartPoint} (hq : chartQ coord p ∈ Icc qlo qhi)
    (hp : p ∉ supportBand a b qlo qhi) :
    chartKernel coord (angularModel coord A B lam a b d) p = 0 := by
  by_contra hn
  have hpos : 0 < chartQ coord p := hqlo.trans_le hq.1
  change angularIncrement lam (shapedAmplitude B (chartEta coord p)) a b
    (Real.sqrt (chartQ coord p)) (chartQ coord p ^ (-A)) d p.1 ≠ 0 at hn
  have hs := angularIncrement_tsupport lam (shapedAmplitude B (chartEta coord p)) a b
    (chartQ coord p ^ (-A)) (Real.sqrt_pos.mpr hpos) hab d (subset_closure hn)
  apply hp
  exact ⟨(mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq.1) ha.le).trans hs.1.le,
    hs.2.le.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq.2) (ha.trans hab).le)⟩

theorem axial_kernel_zero {coord A B lam a b qlo qhi : ℝ} (ha : 0 < a) (hab : a < b)
    (hqlo : 0 < qlo) (d : Debt) {p : ChartPoint} (hq : chartQ coord p ∈ Icc qlo qhi)
    (hp : p ∉ supportBand a b qlo qhi) :
    chartKernel coord (axialModel coord A B lam a b d) p = 0 := by
  by_contra hn
  have hpos : 0 < chartQ coord p := hqlo.trans_le hq.1
  change desiredAxialIncrement lam (shapedAmplitude B (chartEta coord p)) a b
    (Real.sqrt (chartQ coord p)) (chartQ coord p ^ (-A)) d p.1 ≠ 0 at hn
  have hs := desiredAxialIncrement_tsupport lam (shapedAmplitude B (chartEta coord p)) a b
    (chartQ coord p ^ (-A)) (Real.sqrt_pos.mpr hpos) hab d (subset_closure hn)
  apply hp
  exact ⟨(mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq.1) ha.le).trans hs.1.le,
    hs.2.le.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq.2) (ha.trans hab).le)⟩

/-- The scalar rank coefficients themselves are proved to lie in `M₀`.
All regularity and all finite jet bounds are derived from the constructed inverse. -/
theorem rank_kernels_meanClass (s : WeightedClasses.StripData ChartPoint)
    {coord A B lam a b qlo qhi rlo rhi : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (ha : 0 < a) (hab : a < b) (hB : B ≠ 0) (hqlo : 0 < qlo)
    (hT : ∀ p ∈ s.domain, chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ p ∈ s.domain, chartQ coord p ∈ Icc qlo qhi)
    (hR : ∀ p ∈ s.domain, p.1 ∈ Icc rlo rhi)
    (hz : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ s.domain, p ∈ supportBand a b qlo qhi → δ ≤ s.zeta p)
    (d : Debt) :
    WeightedClasses.MeanClass s 0 (fun _ => chartKernel coord (angularModel coord A B lam a b d)) ∧
      WeightedClasses.MeanClass s 0 (fun _ => chartKernel coord (axialModel coord A B lam a b d)) := by
  constructor
  · exact meanClass_of_interior_support s _
      (chartKernel_contDiffOn hc hc1 hT (angularModel_contDiffOn _ _ _ _ _ _ hB d))
      (chartKernel_finiteJetBounds hc hc1 hqlo hT hq hR (angularModel_contDiffOn _ _ _ _ _ _ hB d))
      (supportBand_isClosed a b qlo qhi)
      (fun p hp hnot => angular_kernel_zero ha hab hqlo d (hq p hp) hnot) hz
  · exact meanClass_of_interior_support s _
      (chartKernel_contDiffOn hc hc1 hT (axialModel_contDiffOn _ _ _ _ _ _ hB d))
      (chartKernel_finiteJetBounds hc hc1 hqlo hT hq hR (axialModel_contDiffOn _ _ _ _ _ _ hB d))
      (supportBand_isClosed a b qlo qhi)
      (fun p hp hnot => axial_kernel_zero ha hab hqlo d (hq p hp) hnot) hz

/-- Equation (35) maps the slow defect class `S_α` to `M_α` in every finite
stripped jet, uniformly over the band index. -/
theorem rank_update_meanClass (s : WeightedClasses.StripData ChartPoint)
    {coord A B lam a b qlo qhi rlo rhi α : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (ha : 0 < a) (hab : a < b) (hB : B ≠ 0) (hqlo : 0 < qlo)
    (hT : ∀ p ∈ s.domain, chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ p ∈ s.domain, chartQ coord p ∈ Icc qlo qhi)
    (hR : ∀ p ∈ s.domain, p.1 ∈ Icc rlo rhi)
    (hz : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ s.domain, p ∈ supportBand a b qlo qhi → δ ≤ s.zeta p)
    {d : ℕ → ChartPoint → Debt} (hd : WeightedClasses.UnweightedClass s α d) :
    WeightedClasses.MeanClass s α (fun n => chartAngular coord A B lam a b (d n)) ∧
      WeightedClasses.MeanClass s α (fun n => chartAxial coord A B lam a b (d n)) := by
  have hk (i : Fin 3) := rank_kernels_meanClass (A := A) (B := B) (lam := lam) s
    hc hc1 ha hab hB hqlo hT hq hR hz (Pi.single i 1)
  have hcoord (i : Fin 3) : WeightedClasses.UnweightedClass s α (fun n p => d n p i) :=
    hd.map (ContinuousLinearMap.proj i)
  constructor
  · have ht (i : Fin 3) : WeightedClasses.MemClass s (fun _ p => s.zeta p) α
        (fun n p => d n p i * chartKernel coord (angularModel coord A B lam a b (Pi.single i 1)) p) := by
      simpa only [add_zero, one_mul] using (hcoord i).mul (hk i).1
    have hs := WeightedClasses.MemClass.sum Finset.univ _
      (fun _ p hp => s.zeta_nonneg p hp) (fun i _ => ht i)
    have he : (fun n => chartAngular coord A B lam a b (d n)) =
        (fun n p => ∑ i : Fin 3, d n p i *
          chartKernel coord (angularModel coord A B lam a b (Pi.single i 1)) p) := by
      funext n p
      exact chartAngular_eq_sum _ _ _ _ _ _ _ _
    rw [he]
    exact hs
  · have ht (i : Fin 3) : WeightedClasses.MemClass s (fun _ p => s.zeta p) α
        (fun n p => d n p i * chartKernel coord (axialModel coord A B lam a b (Pi.single i 1)) p) := by
      simpa only [add_zero, one_mul] using (hcoord i).mul (hk i).2
    have hs := WeightedClasses.MemClass.sum Finset.univ _
      (fun _ p hp => s.zeta_nonneg p hp) (fun i _ => ht i)
    have he : (fun n => chartAxial coord A B lam a b (d n)) =
        (fun n p => ∑ i : Fin 3, d n p i *
          chartKernel coord (axialModel coord A B lam a b (Pi.single i 1)) p) := by
      funext n p
      exact chartAxial_eq_sum _ _ _ _ _ _ _ _
    rw [he]
    exact hs

end RankClass

section ConcreteStrip

noncomputable def normalizedDomain (coord qlo qhi rlo rhi : ℝ) : Set ChartPoint :=
  {p | chartInput p ∈ PhysicalCoordinateBounds.positiveTime ∧
    chartQ coord p ∈ Ioo qlo qhi ∧ p.1 ∈ Ioo rlo rhi}

theorem normalizedDomain_isOpen {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (qlo qhi rlo rhi : ℝ) : IsOpen (normalizedDomain coord qlo qhi rlo rhi) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have ht : chartInput ⁻¹' PhysicalCoordinateBounds.positiveTime ∈ 𝓝 p :=
    (PhysicalCoordinateBounds.positiveTime_isOpen.preimage chartInput.continuous).mem_nhds hp.1
  have hqcont : ContinuousAt (chartQ coord) p :=
    (PhysicalCoordinateBounds.qCoord_contDiffAt hc hc1 hp.1).continuousAt.comp
      chartInput.continuous.continuousAt
  have hq : (chartQ coord) ⁻¹' Ioo qlo qhi ∈ 𝓝 p :=
    hqcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hp.2.1)
  have hr : Prod.fst ⁻¹' Ioo rlo rhi ∈ 𝓝 p :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds hp.2.2
  exact inter_mem ht (inter_mem hq hr)




end ConcreteStrip

section PhysicalChart







end PhysicalChart

section FinalClass

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem meanClass_congr_on {s : WeightedClasses.StripData D} {α : ℝ}
    {f g : ℕ → D → ℝ} (hf : WeightedClasses.MeanClass s α f)
    (he : ∀ n x, x ∈ s.domain → g n x = f n x) : WeightedClasses.MeanClass s α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => he n x hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hgerm : g n =ᶠ[𝓝 x] f n := by
    filter_upwards [s.isOpen_domain.mem_nhds hx] with y hy
    exact he n y hy
  rw [iteratedFDeriv_congr_germ hgerm j]
  exact hb n x hx j hj


end FinalClass

section ShapedPatch

theorem square_half_power (lam R : ℝ) (hR : 0 < R) :
    (R ^ 2 / 2) ^ (-(1 / 2 + lam)) =
      (2 : ℝ) ^ (1 / 2 + lam) * R ^ (-1 - 2 * lam) := by
  have hX : 0 < R ^ 2 / 2 := by positivity
  rw [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hR, ← Real.exp_add,
    Real.log_div (pow_ne_zero 2 hR.ne') (by norm_num), Real.log_pow]
  congr 1
  ring



end ShapedPatch

section ActualStream

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only the input geometry and defect family occur in this record. -/
structure SmoothFamily (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  lam : ℝ
  a : ℝ
  b : ℝ
  length : E → ℝ
  velocity : E → ℝ
  amplitude : E → ℝ
  debt : E → Debt
  lam_pos : 0 < lam
  a_pos : 0 < a
  ordered : a < b
  length_pos : ∀ s, 0 < length s
  velocity_ne : ∀ s, velocity s ≠ 0
  amplitude_ne : ∀ s, amplitude s ≠ 0
  length_smooth : ContDiff ℝ ∞ length
  velocity_smooth : ContDiff ℝ ∞ velocity
  amplitude_smooth : ContDiff ℝ ∞ amplitude
  debt_smooth : ContDiff ℝ ∞ debt

namespace SmoothFamily

noncomputable def angular (F : SmoothFamily E) : ℝ × E → ℝ :=
  angularFamily F.lam F.a F.b F.length F.velocity F.amplitude F.debt

noncomputable def desired (F : SmoothFamily E) : ℝ × E → ℝ :=
  desiredAxialFamily F.lam F.a F.b F.length F.velocity F.amplitude F.debt

noncomputable def potential (F : SmoothFamily E) (power lo hi M : ℝ)
    (v : PressureStream.Plane) : PressureStream.Lift E → ℝ :=
  PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift F.desired)

noncomputable def radial (F : SmoothFamily E) (power lo hi M : ℝ)
    (v : PressureStream.Plane) (w : E × PressureStream.Plane) : PressureStream.Lift E → ℝ :=
  PressureStream.streamBeta w (F.potential power lo hi M v)

noncomputable def axial (F : SmoothFamily E) (power lo hi M : ℝ)
    (v : PressureStream.Plane) : PressureStream.Lift E → ℝ :=
  PressureStream.streamGamma (PressureStream.physicalSpeed power M) ((0 : E), v)
    (F.potential power lo hi M v)

theorem angular_smooth (F : SmoothFamily E) : ContDiff ℝ ∞ F.angular :=
  angularFamily_contDiff _ _ _ F.length_smooth F.velocity_smooth F.amplitude_smooth F.debt_smooth
    (fun s => (F.length_pos s).ne') F.velocity_ne F.amplitude_ne

theorem desired_smooth (F : SmoothFamily E) : ContDiff ℝ ∞ F.desired :=
  desiredAxialFamily_contDiff _ _ _ F.length_smooth F.velocity_smooth F.amplitude_smooth F.debt_smooth
    (fun s => (F.length_pos s).ne') F.velocity_ne F.amplitude_ne

theorem prescribed_five_rows (F : SmoothFamily E) (s : E) :
    FiveRowRank.FiveRows (background F.lam (F.amplitude s) (F.length s) (F.velocity s)) (fun _ => 0)
      (F.debt s) (fun r => F.angular (r, s)) (fun r => F.desired (r, s)) :=
  physical_five_rows F.lam_pos (F.amplitude_ne s) F.a_pos F.ordered (F.length_pos s) (F.velocity_ne s) (F.debt s)

theorem desired_supported (F : SmoothFamily E) {lo hi : ℝ}
    (hlo : ∀ s, lo ≤ F.length s * F.a) (hhi : ∀ s, F.length s * F.b ≤ hi) :
    RadialAlias.RadiallySupported lo hi F.desired :=
  desiredAxialFamily_supported _ _ _ _ F.ordered F.length_pos hlo hhi

theorem desired_mass_zero (F : SmoothFamily E) (s : E) : (∫ r, r * F.desired (r, s)) = 0 :=
  (F.prescribed_five_rows s).2.1


theorem potential_smooth (F : SmoothFamily E) {power lo hi M : ℝ}
    (hlo0 : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    (hlo : ∀ s, lo ≤ F.length s * F.a) (hhi : ∀ s, F.length s * F.b ≤ hi) :
    ContDiff ℝ ∞ (F.potential power lo hi M v) :=
  PressureStream.streamPotential_contDiff hlo0 horder hp ((0 : E), v)
    (slowLift_contDiff F.desired_smooth) (slowLift_supported (F.desired_supported hlo hhi))

theorem radial_smooth (F : SmoothFamily E) {power lo hi M : ℝ}
    (hlo0 : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    (w : E × PressureStream.Plane)
    (hlo : ∀ s, lo ≤ F.length s * F.a) (hhi : ∀ s, F.length s * F.b ≤ hi) :
    ContDiff ℝ ∞ (F.radial power lo hi M v w) :=
  PressureStream.streamBeta_contDiff hlo0 horder hp ((0 : E), v) w
    (slowLift_contDiff F.desired_smooth) (slowLift_supported (F.desired_supported hlo hhi))

theorem axial_exact (F : SmoothFamily E) {power lo hi M : ℝ}
    (hlo0 : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    (hlo : ∀ s, lo ≤ F.length s * F.a) (hhi : ∀ s, F.length s * F.b ≤ hi)
    (p : PressureStream.Lift E) : F.axial power lo hi M v p = F.desired (p.1, p.2.1) :=
  slow_streamGamma_eq_desired hlo0 horder hp v F.desired_smooth (F.desired_supported hlo hhi)
    F.desired_mass_zero p


theorem divergence_zero (F : SmoothFamily E) {power lo hi M : ℝ}
    (hlo0 : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    (w : E × PressureStream.Plane)
    (hlo : ∀ s, lo ≤ F.length s * F.a) (hhi : ∀ s, F.length s * F.b ≤ hi)
    (p : PressureStream.Lift E) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed power M) ((0 : E), v) w
      (F.radial power lo hi M v w) (F.axial power lo hi M v) p = 0 :=
  slow_stream_divergence_zero hlo0 horder hp v w F.desired_smooth (F.desired_supported hlo hhi) p

end SmoothFamily

theorem slow_streamPotential_eq_primitive {lo hi power M : ℝ}
    (hlo : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported lo hi f)
    (hm : ∀ s, (∫ r, r * f (r, s)) = 0) (p : PressureStream.Lift E) (hr : lo ≤ p.1) :
    PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift f) p =
      (∫ r in lo..p.1, r * f (r, p.2.1)) / p.1 := by
  unfold PressureStream.streamPotential PressureStream.divideRadius
  rw [RadialPullback.physicalCompact_eq_radialIntegral hlo horder hp
    (PressureStream.weightedSource_contDiff (slowLift_contDiff hf))
    (PressureStream.weightedSource_supported (slowLift_supported hs)) M ((0 : E), v) p hr]
  have he : (∫ r in lo..hi, r * f (r, p.2.1)) = 0 := by
    change (∫ r in lo..hi, PressureStream.weightedSource f (r, p.2.1)) = 0
    rw [radial_integral_eq_interval (PressureStream.weightedSource_contDiff hf).continuous
      (PressureStream.weightedSource_supported hs)]
    exact hm p.2.1
  simp [PressureStream.weightedSource, slowLift, he]

end ActualStream

namespace SmoothFamily

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


noncomputable def supportSet (F : SmoothFamily E) : Set (PressureStream.Lift E) :=
  {p | p.1 ∈ Icc (F.length p.2.1 * F.a) (F.length p.2.1 * F.b)}




end SmoothFamily

section ReservedMeanPatch




variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


end ReservedMeanPatch

section PrimitiveKernels

/-- A smooth formula for `r⁻¹∫₀ʳ s f(s) ds`, also defined at the axis. -/
noncomputable def scaledPrimitive (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * ∫ t in (0 : ℝ)..1, t * f (r * t)

theorem scaledPrimitive_eq_integral (f : ℝ → ℝ) {r : ℝ} (hr : r ≠ 0) :
    scaledPrimitive f r = (∫ s in (0 : ℝ)..r, s * f s) / r := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun s => s * f s) r
  simp only [smul_eq_mul, mul_zero, mul_one] at h
  have he : (fun t => r * t * f (r * t)) = (fun t => r * (t * f (r * t))) := by
    funext t
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  unfold scaledPrimitive
  rw [← h]
  field_simp

theorem scaledPrimitive_zero_of_support {l u r : ℝ} (hl : 0 < l) (_ : l < u)
    {f : ℝ → ℝ} (hs : tsupport f ⊆ Ioo l u) (hm : (∫ s, s * f s) = 0)
    (hr : r ∉ Ioo l u) : scaledPrimitive f r = 0 := by
  by_cases hrl : r ≤ l
  · have hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f (r * t) = 0 := by
      by_contra hn
      have hh := hs (subset_closure hn)
      have hle : r * t ≤ l := (mul_le_mul_of_nonneg_right hrl ht.1).trans
        (mul_le_of_le_one_right hl.le ht.2)
      exact (not_lt_of_ge hle) hh.1
    unfold scaledPrimitive
    have he : (∫ t in (0 : ℝ)..1, t * f (r * t)) = 0 := by
      calc
        _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp only
          rw [hz t (by simpa using ht), mul_zero]
        _ = 0 := by simp
    rw [he, mul_zero]
  · have hru : u ≤ r := le_of_not_gt (fun hh => hr ⟨lt_of_not_ge hrl, hh⟩)
    have hrpos : 0 < r := hl.trans (lt_of_not_ge hrl)
    rw [scaledPrimitive_eq_integral f hrpos.ne']
    have he : (∫ s in (0 : ℝ)..r, s * f s) = ∫ s, s * f s := by
      apply intervalIntegral.integral_eq_integral_of_support_subset
      intro s hs0
      have hfs : f s ≠ 0 := by
        intro hz
        exact hs0 (by simp [hz])
      have hsu := hs (subset_closure hfs)
      exact ⟨hl.trans hsu.1, hsu.2.le.trans hru⟩
    rw [he, hm, zero_div]







end PrimitiveKernels

section PrimitiveClass








end PrimitiveClass

section ExactPrimitive

theorem scaledPrimitive_zero_below {l r : ℝ} (hl : 0 ≤ l) {f : ℝ → ℝ}
    (hf : ∀ x, x ≤ l → f x = 0) (hr : r ≤ l) : scaledPrimitive f r = 0 := by
  unfold scaledPrimitive
  have he : (∫ t in (0 : ℝ)..1, t * f (r * t)) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
        have hrt : r * t ≤ l := (mul_le_mul_of_nonneg_right hr ht'.1).trans
          (mul_le_of_le_one_right hl ht'.2)
        dsimp only
        rw [hf _ hrt, mul_zero]
      _ = 0 := by simp
  rw [he, mul_zero]



variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The stream is the ordinary zero-axis primitive for a slow zero-mass
source. Thus neither its cutoff nor its transport parameter changes it. -/
theorem slow_streamPotential_eq_scaledPrimitive {lo hi power M : ℝ}
    (hlo : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported lo hi f)
    (hm : ∀ s, (∫ r, r * f (r, s)) = 0) (p : PressureStream.Lift E) :
    PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift f) p =
      scaledPrimitive (fun r => f (r, p.2.1)) p.1 := by
  have hc : Continuous (fun r => f (r, p.2.1)) :=
    hf.continuous.comp (continuous_id.prodMk continuous_const)
  have hsup : support (fun r => f (r, p.2.1)) ⊆ Ioo lo hi := by
    simpa only [interior_Icc] using hc.isOpen_support.subset_interior_iff.mpr
      (show support (fun r => f (r, p.2.1)) ⊆ Icc lo hi from fun r hr => hs hr)
  have hzero (r : ℝ) (hr : r ≤ lo) : f (r, p.2.1) = 0 := by
    by_contra hn
    exact (not_lt_of_ge hr) (hsup hn).1
  by_cases hr : lo ≤ p.1
  · rw [slow_streamPotential_eq_primitive hlo horder hp v hf hs hm p hr,
      scaledPrimitive_eq_integral _ (hlo.trans_le hr).ne']
    have hz : (∫ r in (0 : ℝ)..lo, r * f (r, p.2.1)) = 0 := by
      calc
        _ = ∫ _r in (0 : ℝ)..lo, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro r hri
          have hle : r ≤ lo := (by simpa only [uIcc_of_le hlo.le] using hri : r ∈ Icc 0 lo).2
          dsimp only
          rw [hzero _ hle, mul_zero]
        _ = 0 := by simp
    have hi : (∫ r in (0 : ℝ)..lo, r * f (r, p.2.1)) +
        (∫ r in lo..p.1, r * f (r, p.2.1)) = (∫ r in (0 : ℝ)..p.1, r * f (r, p.2.1)) :=
      intervalIntegral.integral_add_adjacent_intervals
      ((continuous_id.mul hc).intervalIntegrable 0 lo)
      ((continuous_id.mul hc).intervalIntegrable lo p.1)
    rw [hz, zero_add] at hi
    rw [hi]
  · rw [TransportPrimitive.radial_zero_of_lt
      (PressureStream.streamPotential_supported hlo horder hp ((0 : E), v)
        (slowLift_contDiff hf) (slowLift_supported hs)) (lt_of_not_ge hr),
      scaledPrimitive_zero_below hlo.le hzero (lt_of_not_ge hr).le]

theorem slow_streamPotential_congr_slice (lo hi power M : ℝ) (v : PressureStream.Plane)
    {f g : ℝ × E → ℝ} (p : PressureStream.Lift E) (he : ∀ r, f (r, p.2.1) = g (r, p.2.1)) :
    PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift f) p =
      PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift g) p := by
  simp [PressureStream.streamPotential, PressureStream.divideRadius, RadialPullback.physicalCompact,
    RadialPullback.pullback, TransportPrimitive.compactIntegral, TransportPrimitive.pastIntegral,
    TransportPrimitive.totalIntegral, TransportPrimitive.shift, RadialPullback.normalizeSource,
    RadialPullback.liftChart, PressureStream.weightedSource, slowLift, he]

/-- Only the radial slice is needed for this identity; no extension of the
slow data outside its open physical domain is assumed. -/
theorem slow_streamPotential_eq_scaledPrimitive_slice {lo hi power M : ℝ}
    (hlo : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    (f : ℝ × E → ℝ) (p : PressureStream.Lift E)
    (hf : ContDiff ℝ ∞ (fun r => f (r, p.2.1)))
    (hs : support (fun r => f (r, p.2.1)) ⊆ Icc lo hi)
    (hm : (∫ r, r * f (r, p.2.1)) = 0) :
    PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift f) p =
      scaledPrimitive (fun r => f (r, p.2.1)) p.1 := by
  let g : ℝ × E → ℝ := fun z => f (z.1, p.2.1)
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have hgs : RadialAlias.RadiallySupported lo hi g := fun z hz => hs hz
  rw [slow_streamPotential_congr_slice lo hi power M v (f := f) (g := g) p (fun _ => rfl)]
  exact slow_streamPotential_eq_scaledPrimitive hlo horder hp v hg hgs (fun _ => hm) p

end ExactPrimitive

section ActualChartStream






end ActualChartStream

section LocalSlowStream

theorem fderiv_apply_eq_of_line_eq {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f g : D → ℝ} {x : D} (v : D) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : ∀ t : ℝ, f (x + t • v) = g (x + t • v)) : fderiv ℝ f x v = fderiv ℝ g x v := by
  have hc : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [one_smul, zero_add, id_eq] using
      (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hfc := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
  have hgc := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
  have hfun : f ∘ (fun t : ℝ => x + t • v) = g ∘ (fun t : ℝ => x + t • v) := funext he
  rw [hfun] at hfc
  exact hfc.unique hgc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local differentiability hypothesis suffices for the true slow axial
identity; the source need only be smooth along its radial slice. -/
theorem slow_streamGamma_eq_desired_slice {lo hi power M : ℝ}
    (hlo : 0 < lo) (horder : lo < hi) (hp : 0 < power) (v : PressureStream.Plane)
    (f : ℝ × E → ℝ) (p : PressureStream.Lift E)
    (hf : ContDiff ℝ ∞ (fun r => f (r, p.2.1)))
    (hs : support (fun r => f (r, p.2.1)) ⊆ Icc lo hi)
    (hm : (∫ r, r * f (r, p.2.1)) = 0)
    (hΨ : DifferentiableAt ℝ (PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift f)) p) :
    PressureStream.streamGamma (PressureStream.physicalSpeed power M) ((0 : E), v)
      (PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift f)) p = f (p.1, p.2.1) := by
  let g : ℝ × E → ℝ := fun z => f (z.1, p.2.1)
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have hgs : RadialAlias.RadiallySupported lo hi g := fun z hz => hs hz
  have hΨg := PressureStream.streamPotential_contDiff (M := M) hlo horder hp ((0 : E), v)
    (slowLift_contDiff hg) (slowLift_supported hgs)
  let u := PressureStream.radialVector (PressureStream.physicalSpeed power M) ((0 : E), v) p
  have hDr := fderiv_apply_eq_of_line_eq u hΨ (hΨg.differentiable (by simp) p) (fun t => by
    apply slow_streamPotential_congr_slice lo hi power M v (f := f) (g := g) (p + t • u)
    intro r
    simp [g, u, PressureStream.radialVector])
  have hval := slow_streamPotential_congr_slice lo hi power M v (f := f) (g := g) p (fun r => rfl)
  have hAx := slow_streamGamma_eq_desired (M := M) hlo horder hp v hg hgs (fun _ => hm) p
  calc
    _ = PressureStream.streamGamma (PressureStream.physicalSpeed power M) ((0 : E), v)
        (PressureStream.streamPotential power lo hi M ((0 : E), v) (slowLift g)) p := by
      unfold PressureStream.streamGamma PressureStream.graphDr PressureStream.divideRadius
      rw [hDr, hval]
    _ = f (p.1, p.2.1) := hAx

end LocalSlowStream

section ActualChartIdentities




end ActualChartIdentities

section AllVelocityClasses


variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]



end AllVelocityClasses

end NavierStokes.MeanRankUpdate
