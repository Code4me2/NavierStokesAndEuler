import NavierStokes.PartitionedCovariance
import NavierStokes.FlatCovariance
import NavierStokes.WeightedQuotients
import NavierStokes.WeightedClasses

/-!
# Signed covariance updates with the constructed primary waves

The signed solve uses the existing primary square roots, pulse columns,
physical masks, covering powers, and angular phases.  Distinct labels are
separated by the constructed padded slots.  A signed square is retained as
a separate term; it is not included in the linear covariance identity.
-/

noncomputable section

namespace NavierStokes.SignedCovariance

open Set Function Filter MeasureTheory Matrix
open PartitionedCovariance
open scoped BigOperators Topology ContDiff

abbrev Vec2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Plane := TorusInverse.Plane

/-- The numerator is the actual inverse-matrix solve. -/
noncomputable def increment (H : Mat2) (T R : Vec2) (j : Fin 2) : ℝ :=
  (H⁻¹.mulVec R) j / (2 * SmoothCovariance.amplitudes H T j)

theorem increment_eq_inverse (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) (j : Fin 2) :
    increment H T R j = (H⁻¹.mulVec R) j / (2 * Real.sqrt ((H⁻¹.mulVec T) j)) := by
  rw [increment, (amplitudes_are_inverse_weights hcone j).2]

private theorem edge_zero_one : FlatCutoff.edge 0 1 = 1 := by
  rw [FlatCutoff.edge_of_pos 0 (by norm_num : (0 : ℝ) < 1)]
  norm_num

private theorem edge_matrix_zero (H : Mat2) :
    FlatCovariance.edgeMatrix 0 (fun _ => H) 1 = H := by
  ext i j
  simp [FlatCovariance.edgeMatrix, FlatCovariance.columns, edge_zero_one]

private theorem edge_target_zero (R : Vec2) :
    FlatCovariance.edgeTarget 0 (fun _ => R) 1 = R := by
  ext i
  simp [FlatCovariance.edgeTarget, FlatCovariance.scaledTarget, edge_zero_one]

/-- The scalar solve is the already proved flat-edge solve at unit edge weight. -/
theorem increment_eq_flat (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) :
    increment H T R = FlatCovariance.signedAmplitude 0 0 0
      (fun _ => H) (fun _ => T) (fun _ => R) 1 := by
  funext j
  simp only [increment, FlatCovariance.signedAmplitude, FlatCovariance.primaryAmplitude,
    FlatCovariance.inverseCoefficients, edge_matrix_zero, edge_target_zero]
  rw [SmoothCovariance.inverse_formula H T hcone.det_ne_zero]
  rfl

/-- Exact two-sided covariance, reusing `FlatCovariance.signed_cross_reconstruct`. -/
theorem cross_reconstruct (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) :
    H.mulVec (fun j => 2 * SmoothCovariance.amplitudes H T j * increment H T R j) = R := by
  have he := FlatCovariance.signed_cross_reconstruct
    (σ := 0) (τ := 0) (κ := 0) (G := fun _ => H) (T := fun _ => T)
    (R := fun _ => R) (x := 1) hcone
  rw [← increment_eq_flat H T R hcone] at he
  simp only [FlatCovariance.primaryAmplitude, FlatCovariance.inverseCoefficients,
    edge_matrix_zero, edge_target_zero] at he
  rw [SmoothCovariance.inverse_formula H T hcone.det_ne_zero] at he
  exact he


/-! ## A bilinear average of the actual waves -/





/-! ## The same physical masks, slots, and phases for arbitrary coefficients -/


noncomputable def tangentWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt}
    {U : UnsignedLabel} (P : PairData sys U) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (outer ε : ℝ) (a : Vec2) (q : ℝ) (x : SlotColoring.Position) (j i : Fin 2) : Plane → ℝ → ℝ :=
  wave (outer * (Real.sqrt ε * a j * mask D U q x))
    (SlotColoring.nativeIndex h U.1) (P.rawTangent hdet j i) (P.modes j) (P.phases j)






noncomputable def assembledTangentWith {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (i : Fin 2) (Y : Plane) (θ : ℝ) : ℝ :=
  ∑ᶠ v : UnsignedLabel × Fin 2, tangentWith (P v.1) hdet (outer v.1) (ε v.1) (a v.1) q x v.2 i Y θ






noncomputable def signedTangent {D h : ℝ} {vr vt : Plane} {sys : SlotSystem D h vr vt} {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (T R : UnsignedLabel → Vec2) (q : ℝ) (x : SlotColoring.Position) (i : Fin 2) : Plane → ℝ → ℝ :=
  assembledTangentWith P hdet outer ε (fun U => increment (P U).matrix (T U) (R U)) q x i

theorem cross_reconstruct_component (H : Mat2) (T R : Vec2)
    (hcone : SmoothCovariance.StrictCone H T) (i : Fin 2) :
    2 * (H.mulVec (fun j => SmoothCovariance.amplitudes H T j * increment H T R j)) i = R i := by
  have hc := congrFun (cross_reconstruct H T R hcone) i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc ⊢
  calc
    _ = H i 0 * (2 * SmoothCovariance.amplitudes H T 0 * increment H T R 0) +
      H i 1 * (2 * SmoothCovariance.amplitudes H T 1 * increment H T R 1) := by ring
    _ = _ := hc



/-! ## The physical signed target -/




/-! ## Uniform weighted jets from input classes and a primary lower bound -/

open WeightedClasses

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A polynomial reciprocal bound, imposed only on the positive primary
weight.  No regularity of a quotient by the envelope is assumed. -/
noncomputable def InverseControl (s : StripData E) (w g : ℕ → E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain →
    w n x / g n x ≤ C * s.growth n x ^ p

theorem inverseControl_of_lower {s : StripData E} {w g : ℕ → E → ℝ}
    (hg : ∀ n x, x ∈ s.domain → 0 < g n x) {c : ℝ} (hc : 0 < c) (p : ℕ)
    (hlower : ∀ n x, x ∈ s.domain → c * w n x / s.growth n x ^ p ≤ g n x) :
    InverseControl s w g := by
  refine ⟨c⁻¹, (inv_pos.mpr hc).le, p, ?_⟩
  intro n x hx
  have hG : 0 < s.growth n x ^ p := pow_pos (zero_lt_one.trans_le (s.one_le_growth n x)) _
  have hl := (div_le_iff₀ hG).mp (hlower n x hx)
  apply (div_le_iff₀ (hg n x hx)).mpr
  calc
    w n x = c⁻¹ * (c * w n x) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * (g n x * s.growth n x ^ p) := mul_le_mul_of_nonneg_left hl (inv_pos.mpr hc).le
    _ = _ := by ring

/-- A common finite envelope for input jets and the positive lower bound,
uniform in the discrete band and every point of the strip. -/
theorem class_input_envelope {s : StripData E} {w g r : ℕ → E → ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hr : MemClass s w 0 r)
    (hlower : InverseControl s w g) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain →
      1 ≤ C * s.growth n x ^ p ∧
      w n x / (C * s.growth n x ^ p) ≤ g n x ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (g n) x‖ ≤ w n x * (C * s.growth n x ^ p)) ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (r n) x‖ ≤ w n x * (C * s.growth n x ^ p)) := by
  obtain ⟨Cg, hCg, pg, hgj⟩ := hg.bounds m
  obtain ⟨Cr, hCr, pr, hrj⟩ := hr.bounds m
  obtain ⟨C0, hC0, p0, hl⟩ := hlower
  let C := Cg + Cr + C0 + 1
  let p := pg + pr + p0
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, p, ?_⟩
  intro n x hx
  have hm (A : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) (k : ℕ) (hkp : k ≤ p) :
      A * s.growth n x ^ k ≤ C * s.growth n x ^ p := by
    exact mul_le_mul hAC (pow_le_pow_right₀ (s.one_le_growth n x) hkp)
      (pow_nonneg (s.growth_nonneg n x) k) (zero_le_one.trans hC)
  have hB : 1 ≤ C * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (s.one_le_growth n x))
  refine ⟨hB, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (zero_lt_one.trans_le hB)).mpr
    have hl' : w n x / g n x ≤ C * s.growth n x ^ p :=
      (hl n x hx).trans (hm C0 hC0 (by dsimp [C]; linarith) p0 (by dsimp [p]; omega))
    simpa only [mul_comm] using (div_le_iff₀ (hp n x hx)).mp hl'
  · intro j hj
    calc
      _ ≤ Cg * s.growth n x ^ pg * w n x := by
        simpa only [majorant, Real.rpow_zero, mul_one] using hgj n x hx j hj
      _ ≤ (C * s.growth n x ^ p) * w n x := mul_le_mul_of_nonneg_right
        (hm Cg hCg (by dsimp [C]; linarith) pg (by dsimp [p]; omega)) (hw n x hx).le
      _ = _ := by ring
  · intro j hj
    calc
      _ ≤ Cr * s.growth n x ^ pr * w n x := by
        simpa only [majorant, Real.rpow_zero, mul_one] using hrj n x hx j hj
      _ ≤ (C * s.growth n x ^ p) * w n x := mul_le_mul_of_nonneg_right
        (hm Cr hCr (by dsimp [C]; linarith) pr (by dsimp [p]; omega)) (hw n x hx).le
      _ = _ := by ring

noncomputable def signedJetCost (j : ℕ) : ℝ :=
  WeightedQuotients.chooseSum j * WeightedQuotients.orderBound (-(1 / 2 : ℝ)) j / 2

noncomputable def prefixJetCost (m : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (m + 1), |signedJetCost j|

theorem prefixJetCost_pos (m : ℕ) : 0 < prefixJetCost m := by
  have hs := Finset.sum_nonneg (s := Finset.range (m + 1)) (fun j _ => abs_nonneg (signedJetCost j))
  dsimp [prefixJetCost]
  linarith

theorem signedJetCost_le {j m : ℕ} (hj : j ≤ m) : signedJetCost j ≤ prefixJetCost m := by
  have hs := Finset.single_le_sum (f := fun j => |signedJetCost j|)
    (fun k _ => abs_nonneg (signedJetCost k)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact (le_abs_self _).trans (hs.trans (by dsimp [prefixJetCost]; linarith))


/-- Derive the all-order signed quotient class from weighted input jets.
The weight is never differentiated or divided out as a variable function. -/
theorem signed_quotient_class_zero {s : StripData E} {w g r : ℕ → E → ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hr : MemClass s w 0 r)
    (hlower : InverseControl s w g) :
    MemClass s (fun n x => Real.sqrt (w n x)) 0
      (fun n x => r n x / (2 * Real.sqrt (g n x))) := by
  have hsmooth (n : ℕ) : ContDiffOn ℝ ∞
      (fun x => r n x / (2 * Real.sqrt (g n x))) s.domain :=
    (hr.smooth n).div (contDiffOn_const.mul ((hg.smooth n).sqrt (fun x hx => (hp n x hx).ne')))
      (fun x hx => mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hp n x hx)).ne')
  refine ⟨fun n x hx => Real.sqrt_nonneg _, hsmooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, henv⟩ := class_input_envelope hw hp hg hr hlower m
  refine ⟨prefixJetCost m * C ^ (2 * m + 2),
    mul_nonneg (prefixJetCost_pos m).le (pow_nonneg (zero_le_one.trans hC) _), p * (2 * m + 2), ?_⟩
  intro n x hx j hj
  obtain ⟨hB, hlo, hgj, hrj⟩ := henv n x hx
  have hb := WeightedQuotients.signed_jet_bound s.isOpen_domain (hg.smooth n) (hr.smooth n)
    (hp n) hx (hw n x hx) hB j hlo (fun k hk => hgj k (hk.trans hj)) (fun k hk => hrj k (hk.trans hj))
  calc
    _ ≤ Real.sqrt (w n x) * signedJetCost j * (C * s.growth n x ^ p) ^ (2 * j + 2) := hb
    _ ≤ Real.sqrt (w n x) * prefixJetCost m * (C * s.growth n x ^ p) ^ (2 * m + 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (signedJetCost_le hj) (Real.sqrt_nonneg _)
      · exact pow_le_pow_right₀ hB (by omega)
      · exact pow_nonneg (zero_le_one.trans hB) _
      · exact mul_nonneg (Real.sqrt_nonneg _) (prefixJetCost_pos m).le
    _ = majorant s (fun n x => Real.sqrt (w n x)) 0
        (prefixJetCost m * C ^ (2 * m + 2)) (p * (2 * m + 2)) n x := by
      simp only [majorant, Real.rpow_zero, mul_one, mul_pow, pow_mul]
      ring

/-- Discrete powers of epsilon pass through the quotient without a jet loss. -/
theorem signed_quotient_class {s : StripData E} {w g r : ℕ → E → ℝ} {β : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hp : ∀ n x, x ∈ s.domain → 0 < g n x)
    (hg : MemClass s w 0 g) (hr : MemClass s w β r)
    (hlower : InverseControl s w g) :
    MemClass s (fun n x => Real.sqrt (w n x)) β
      (fun n x => r n x / (2 * Real.sqrt (g n x))) := by
  have hr0 : MemClass s w 0 (fun n x => s.epsilon n ^ (-β) * r n x) := by
    simpa only [smul_eq_mul, add_neg_cancel] using hr.band_smul (bandBound_rpow s (-β))
  have hq0 := signed_quotient_class_zero hw hp hg hr0 hlower
  have hq := hq0.band_smul (bandBound_rpow s β)
  have heq : (fun n x => s.epsilon n ^ β • (s.epsilon n ^ (-β) * r n x / (2 * Real.sqrt (g n x)))) =
      (fun n x => r n x / (2 * Real.sqrt (g n x))) := by
    funext n x
    simp only [smul_eq_mul, ← mul_div_assoc, ← mul_assoc,
      ← Real.rpow_add (s.epsilon_pos n), add_neg_cancel, Real.rpow_zero, one_mul]
  simpa only [zero_add, heq] using hq


theorem memClass_congrOn {s : StripData E} {w f g : ℕ → E → ℝ} {β : ℝ}
    (hf : MemClass s w β f) (heq : ∀ n x, x ∈ s.domain → f n x = g n x) :
    MemClass s w β g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => (heq n x hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he : g n =ᶠ[𝓝 x] f n := by
    filter_upwards [s.isOpen_domain.mem_nhds hx] with y hy
    exact (heq n y hy).symm
  rw [WeightedQuotients.jet_congr he j]
  exact hb n x hx j hj

/-- The actual matrix-inverse signed coefficient has the half-weight class,
derived from the inverse numerator jets and positive primary inverse jets. -/
theorem increment_wave_class {s : StripData E} {H : ℕ → E → Mat2}
    {T R : ℕ → E → Vec2} {β : ℝ} (j : Fin 2)
    (hζ : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hcone : ∀ n x, x ∈ s.domain → SmoothCovariance.StrictCone (H n x) (T n x))
    (hY : MeanClass s 0 (fun n x => ((H n x)⁻¹.mulVec (T n x)) j))
    (hR : MeanClass s β (fun n x => ((H n x)⁻¹.mulVec (R n x)) j))
    (hlower : InverseControl s (fun _ x => s.zeta x)
      (fun n x => ((H n x)⁻¹.mulVec (T n x)) j)) :
    WaveClass s (fun _ _ => 1) β (fun n x => increment (H n x) (T n x) (R n x) j) := by
  have hq := signed_quotient_class (fun n x hx => hζ x hx)
    (fun n x hx => (amplitudes_are_inverse_weights (hcone n x hx) j).1) hY hR hlower
  have he := memClass_congrOn hq
    (fun n x hx => (increment_eq_inverse (H n x) (T n x) (R n x) (hcone n x hx) j).symm)
  simpa only [WaveClass, mul_one] using he







end Weighted

/-! ## A quantitative bound for the complete assembled signed square -/





/-! ## Smooth edge extension of the actual inverse amplitudes -/

section Edge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]













end Edge

end NavierStokes.SignedCovariance
