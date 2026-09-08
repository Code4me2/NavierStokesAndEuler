import NavierStokes.CommonCoverSolve
import NavierStokes.PhysicalGraphBounds
import NavierStokes.WeightedClasses
import NavierStokes.SimilarityHomogeneity

/-!
# Uniform stripped jets on a common cover

The input of the copy solve is evaluated on the common torus.  The two actual
argument maps below include the integration time as a variable.  Their affine
derivatives, the native time scale, and adjacent-band changes give estimates
whose constants precede the band, copy, and source.  No native periodicity of
the source is used.
-/

namespace NavierStokes.CommonCoverClass

noncomputable section

open Set Function
open scoped ContDiff BigOperators Topology
open TorusInverse

abbrev CCS := CommonCoverSolve.Geometry

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

section Envelopes

variable {X Y V W : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A point-dependent bound on a finite prefix of actual Fréchet jets. -/
def EnvelopeJets (m : ℕ) (f : X → V) (envelope : X → ℝ) : Prop :=
  ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ envelope x

theorem EnvelopeJets.nonneg {m : ℕ} {f : X → V} {e : X → ℝ}
    (hf : EnvelopeJets m f e) (x : X) : 0 ≤ e x :=
  (norm_nonneg _).trans (hf 0 (Nat.zero_le _) x)

theorem EnvelopeJets.mono {m : ℕ} {f : X → V} {e e' : X → ℝ}
    (hf : EnvelopeJets m f e) (he : ∀ x, e x ≤ e' x) : EnvelopeJets m f e' :=
  fun j hj x => (hf j hj x).trans (he x)

theorem affine_jet_bound {f : Y → V} (hf : ContDiff ℝ ∞ f)
    (L : X →L[ℝ] Y) (c : Y) {K : ℝ} (hK : 1 ≤ K) (hL : ‖L‖ ≤ K)
    (m : ℕ) (x : X) {A : ℝ}
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (c + L x)‖ ≤ A) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun z => f (c + L z)) x‖ ≤ A * K ^ m := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  intro j hj
  refine (CommonCoverSolve.norm_iteratedFDeriv_affine_le hf L c x j).trans ?_
  exact mul_le_mul (hb j hj)
    ((pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_right₀ hK hj))
    (pow_nonneg (norm_nonneg _) _) hA

theorem EnvelopeJets.affine {m : ℕ} {f : Y → V} {e : Y → ℝ}
    (hb : EnvelopeJets m f e) (hf : ContDiff ℝ ∞ f)
    (L : X →L[ℝ] Y) (c : Y) {K : ℝ} (hK : 1 ≤ K) (hL : ‖L‖ ≤ K) :
    EnvelopeJets m (fun x => f (c + L x)) (fun x => e (c + L x) * K ^ m) := by
  intro j hj x
  exact affine_jet_bound hf L c hK hL m x (fun i hi => hb i hi _) j hj

/-- The weight is evaluated at the same point in both factors; it need not
be differentiated in this bound. -/
theorem clm_apply_jet_bound {f : X → V →L[ℝ] W} {g : X → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (m : ℕ) (x : X)
    {A B : ℝ} (hA : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hB : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => f y (g y)) x‖ ≤ 2 ^ m * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  intro j hj
  refine (norm_iteratedFDeriv_clm_apply hf hg x (nat_le_infty j)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hA i (hij.trans hj)) (by positivity))
        (hB (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (mul_nonneg (by positivity) hA0)
    _ = 2 ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ m * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA0) hB0

theorem EnvelopeJets.clm_apply {m : ℕ} {f : X → V →L[ℝ] W} {g : X → V}
    {A B : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hA : EnvelopeJets m f A) (hB : EnvelopeJets m g B) :
    EnvelopeJets m (fun x => f x (g x)) (fun x => 2 ^ m * A x * B x) :=
  fun j hj x => clm_apply_jet_bound hf hg m x (fun i hi => hA i hi x)
    (fun i hi => hB i hi x) j hj

end Envelopes

section Arguments

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Joint slow/common-coordinate/integration-time space. -/
abbrev Joint (P : Type) := (P × Plane) × ℝ

noncomputable def nativeArgument (g : CCS) (k : Frequency) (w : Joint P) : P × Plane :=
  (w.1.1, ((g.coordinates k w.1.2).1, w.2))

noncomputable def sourceArgument (g : CCS) (k : Frequency) (w : Joint P) : P × Plane :=
  (w.1.1, g.path k w.1.2 w.2)

noncomputable def nativeLinear (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : CCS) : Joint P →L[ℝ] P × Plane :=
  ((ContinuousLinearMap.fst ℝ P Plane).comp (ContinuousLinearMap.fst ℝ (P × Plane) ℝ)).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (g.coordinateLinear.comp ((ContinuousLinearMap.snd ℝ P Plane).comp
        (ContinuousLinearMap.fst ℝ (P × Plane) ℝ)))).prod
      (ContinuousLinearMap.snd ℝ (P × Plane) ℝ))

noncomputable def sourceLinear (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : CCS) : Joint P →L[ℝ] P × Plane :=
  ((ContinuousLinearMap.fst ℝ P Plane).comp (ContinuousLinearMap.fst ℝ (P × Plane) ℝ)).prod
    (g.pointLinear.comp ((ContinuousLinearMap.snd ℝ P Plane).comp (nativeLinear P g)))

@[simp] theorem nativeLinear_apply (g : CCS) (w : Joint P) :
    nativeLinear P g w = (w.1.1, ((g.coordinateLinear w.1.2).1, w.2)) := rfl

@[simp] theorem sourceLinear_apply (g : CCS) (w : Joint P) :
    sourceLinear P g w =
      (w.1.1, g.pointLinear ((g.coordinateLinear w.1.2).1, w.2)) := rfl

theorem nativeArgument_affine (g : CCS) (k : Frequency) (w : Joint P) :
    nativeArgument g k w = nativeArgument g k 0 + nativeLinear P g w := by
  simp only [nativeArgument, g.coordinates_eq_affine k w.1.2, nativeLinear_apply]
  ext <;> simp

theorem sourceArgument_affine (g : CCS) (k : Frequency) (w : Joint P) :
    sourceArgument g k w = sourceArgument g k 0 + sourceLinear P g w := by
  have ha : ((g.coordinates k w.1.2).1, w.2) =
      ((g.coordinates k 0).1, 0) + ((g.coordinateLinear w.1.2).1, w.2) := by
    rw [g.coordinates_eq_affine k w.1.2]
    ext <;> simp
  simp only [sourceArgument, CommonCoverSolve.Geometry.path, ha, g.point_add,
    sourceLinear_apply, CommonCoverSolve.Geometry.pointLinear,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  ext <;> simp


theorem sourceArgument_smooth (g : CCS) (k : Frequency) :
    ContDiff ℝ ∞ (sourceArgument (P := P) g k) := by
  have he : sourceArgument (P := P) g k =
      fun w => sourceArgument g k 0 + sourceLinear P g w :=
    funext (sourceArgument_affine g k)
  rw [he]
  exact contDiff_const.add (sourceLinear P g).contDiff

/-- One common affine cost for both maps. Its value is independent of the
copy index and of the slow parameter space. -/
noncomputable def argumentCost (g : CCS) : ℝ :=
  1 + ‖g.coordinateLinear‖ + ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖)

theorem one_le_argumentCost (g : CCS) : 1 ≤ argumentCost g := by
  unfold argumentCost
  have h : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
  linarith [norm_nonneg g.coordinateLinear]


theorem norm_sourceLinear_le (g : CCS) : ‖sourceLinear P g‖ ≤ argumentCost g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (one_le_argumentCost g))
  intro w
  rw [sourceLinear_apply, Prod.norm_def]
  have hcoord : ‖(g.coordinateLinear w.1.2).1‖ ≤ ‖g.coordinateLinear‖ * ‖w‖ :=
    (norm_fst_le _).trans ((g.coordinateLinear.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((norm_snd_le w.1).trans (norm_fst_le w)) (norm_nonneg _)))
  have hpair : ‖((g.coordinateLinear w.1.2).1, w.2)‖ ≤
      (1 + ‖g.coordinateLinear‖) * ‖w‖ := by
    rw [Prod.norm_def]
    apply max_le
    · exact hcoord.trans (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg g.coordinateLinear])
        (norm_nonneg _))
    · exact (norm_snd_le w).trans
        (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg g.coordinateLinear]))
  have h1 : ‖w‖ ≤ argumentCost g * ‖w‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_argumentCost g)
  apply max_le ((norm_fst_le w.1).trans ((norm_fst_le w).trans h1))
  calc
    _ ≤ ‖g.pointLinear‖ * ‖((g.coordinateLinear w.1.2).1, w.2)‖ := g.pointLinear.le_opNorm _
    _ ≤ ‖g.pointLinear‖ * ((1 + ‖g.coordinateLinear‖) * ‖w‖) :=
      mul_le_mul_of_nonneg_left hpair (norm_nonneg _)
    _ ≤ argumentCost g * ‖w‖ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold argumentCost
      linarith [norm_nonneg g.coordinateLinear]



omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem sourceArgument_slow (g : CCS) (k : Frequency) (w : Joint P) :
    (sourceArgument g k w).1 = w.1.1 := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem nativeArgument_slow (g : CCS) (k : Frequency) (w : Joint P) :
    (nativeArgument g k w).1 = w.1.1 := rfl

end Arguments

section BandGeometry

/-- The fixed native basis has columns `v_r,v_t`; only the second column is
multiplied by the actual time coefficient. -/
noncomputable def scaledBasis (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) :
    Plane ≃L[ℝ] Plane := (TorusAverages.transverseChart ci hci).trans B

theorem scaledBasis_apply (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) (z : Plane) :
    scaledBasis B ci hci z = B (z.1, ci * z.2) := by
  change B (TorusAverages.transverseChart ci hci z) = _
  rw [TorusAverages.transverseChart_apply]

theorem scaledBasis_transverse (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) :
    scaledBasis B ci hci (0, 1) = ci • B (0, 1) := by
  rw [scaledBasis_apply, ← map_smul]
  congr 1
  ext <;> simp

theorem norm_transverseChart_le {ci : ℝ} (hci : ci ≠ 0) (habs : |ci| ≤ 1) :
    ‖(TorusAverages.transverseChart ci hci : Plane →L[ℝ] Plane)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [ContinuousLinearEquiv.coe_coe, TorusAverages.transverseChart_apply, one_mul, Prod.norm_def]
  apply max_le (norm_fst_le z)
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right habs (norm_nonneg z.2)).trans (by simpa using norm_snd_le z)

theorem norm_inverse_transverseChart_le (ci : ℝ) (hci : ci ≠ 0) :
    ‖((TorusAverages.transverseChart ci hci).symm : Plane →L[ℝ] Plane)‖ ≤ 1 + |ci⁻¹| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [ContinuousLinearEquiv.coe_coe, TorusAverages.transverseChart_symm_apply, Prod.norm_def]
  apply max_le
  · exact (norm_fst_le z).trans
      (le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg (ci⁻¹)]))
  · rw [div_eq_mul_inv, norm_mul, Real.norm_eq_abs (ci⁻¹), mul_comm]
    exact (mul_le_mul_of_nonneg_left (norm_snd_le z) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith : |ci⁻¹| ≤ 1 + |ci⁻¹|) (norm_nonneg _))

theorem norm_scaledBasis_le (B : Plane ≃L[ℝ] Plane) {ci : ℝ}
    (hci : ci ≠ 0) (habs : |ci| ≤ 1) :
    ‖(scaledBasis B ci hci : Plane →L[ℝ] Plane)‖ ≤ ‖(B : Plane →L[ℝ] Plane)‖ := by
  change ‖(B : Plane →L[ℝ] Plane).comp
    (TorusAverages.transverseChart ci hci : Plane →L[ℝ] Plane)‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left (norm_transverseChart_le hci habs) (norm_nonneg B.toContinuousLinearMap))

theorem norm_inverse_scaledBasis_le (B : Plane ≃L[ℝ] Plane) (ci : ℝ) (hci : ci ≠ 0) :
    ‖((scaledBasis B ci hci).symm : Plane →L[ℝ] Plane)‖ ≤
      (1 + |ci⁻¹|) * ‖(B.symm : Plane →L[ℝ] Plane)‖ := by
  change ‖((TorusAverages.transverseChart ci hci).symm : Plane →L[ℝ] Plane).comp
    (B.symm : Plane →L[ℝ] Plane)‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_inverse_transverseChart_le ci hci) (norm_nonneg _))

noncomputable def bandGeometry (B : Plane ≃L[ℝ] Plane) (h : ℝ) (n gap : ℕ)
    (center : Plane) : CCS where
  gap := gap
  basis := scaledBasis B (ChartScales.timeCoefficient h n) (ChartScales.timeCoefficient_pos h n).ne'
  center := center


noncomputable def geometryCost (B : Plane ≃L[ℝ] Plane) (D : ℕ) : ℝ :=
  1 + CommonCoverSolve.coveringBound D * ‖(B : Plane →L[ℝ] Plane)‖ +
    (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ * CommonCoverSolve.coveringBound D

theorem geometryCost_one_le (B : Plane ≃L[ℝ] Plane) (D : ℕ) : 1 ≤ geometryCost B D := by
  have h1 : 0 ≤ CommonCoverSolve.coveringBound D * ‖(B : Plane →L[ℝ] Plane)‖ :=
    mul_nonneg (CommonCoverSolve.coveringBound_pos D).le (norm_nonneg _)
  have h2 : 0 ≤ (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
      CommonCoverSolve.coveringBound D := by
    exact mul_nonneg (mul_nonneg (by linarith [ChartScales.Tg_pos]) (norm_nonneg _))
      (CommonCoverSolve.coveringBound_pos D).le
  unfold geometryCost
  linarith

/-- This constant depends on the fixed native basis and the covering-gap
budget, and is chosen before the band, center, copy, or source. -/
noncomputable def bandArgumentCost (B : Plane ≃L[ℝ] Plane) (D : ℕ) : ℝ :=
  (1 + geometryCost B D) ^ 2

theorem bandArgumentCost_one_le (B : Plane ≃L[ℝ] Plane) (D : ℕ) : 1 ≤ bandArgumentCost B D := by
  have h := geometryCost_one_le B D
  unfold bandArgumentCost
  nlinarith

theorem bandGeometry_argumentCost_le (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) :
    argumentCost (bandGeometry B h n gap center) ≤ bandArgumentCost B D * ChartScales.S n := by
  let g := bandGeometry B h n gap center
  have hS : 1 ≤ ChartScales.S n := PhysicalGraphBounds.S_ge_one (by omega)
  have hS0 : 0 < ChartScales.S n := zero_lt_one.trans_le hS
  have hci : |ChartScales.timeCoefficient h n| ≤ 1 := by
    rw [abs_of_pos (ChartScales.timeCoefficient_pos h n)]
    exact (ChartScales.timeCoefficient_bounds h hh hn).2.trans
      ((div_le_one hS0).mpr hS)
  have hinv : 1 + |(ChartScales.timeCoefficient h n)⁻¹| ≤
      (1 + ChartScales.Tg) * ChartScales.S n := by
    rw [abs_of_pos (inv_pos.mpr (ChartScales.timeCoefficient_pos h n))]
    have hb := ChartScales.timeCoefficient_inv_upper h hh hn
    nlinarith
  have hb : ‖(g.basis : Plane →L[ℝ] Plane)‖ ≤ ‖(B : Plane →L[ℝ] Plane)‖ :=
    norm_scaledBasis_le B _ hci
  have hbi : ‖(g.basis.symm : Plane →L[ℝ] Plane)‖ ≤
      ((1 + ChartScales.Tg) * ChartScales.S n) * ‖(B.symm : Plane →L[ℝ] Plane)‖ :=
    (norm_inverse_scaledBasis_le B _ _).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hC0 : 0 ≤ CommonCoverSolve.coveringBound D := (CommonCoverSolve.coveringBound_pos D).le
  have hK : 1 ≤ geometryCost B D := geometryCost_one_le B D
  have hK0 : 0 ≤ geometryCost B D := zero_le_one.trans hK
  have hcoeff : (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
      CommonCoverSolve.coveringBound D ≤ geometryCost B D := by
    unfold geometryCost
    linarith [mul_nonneg hC0 (norm_nonneg (B : Plane →L[ℝ] Plane))]
  have hpoint : ‖g.pointLinear‖ ≤ geometryCost B D := by
    refine (g.norm_pointLinear_le hd).trans ?_
    refine (mul_le_mul_of_nonneg_left hb hC0).trans ?_
    unfold geometryCost
    have ht : 0 ≤ (1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
        CommonCoverSolve.coveringBound D := by
      exact mul_nonneg (mul_nonneg (by linarith [ChartScales.Tg_pos]) (norm_nonneg _)) hC0
    linarith
  have hcoord : ‖g.coordinateLinear‖ ≤ geometryCost B D * ChartScales.S n := by
    refine (g.norm_coordinateLinear_le hd).trans ?_
    calc
      _ ≤ (((1 + ChartScales.Tg) * ChartScales.S n) * ‖(B.symm : Plane →L[ℝ] Plane)‖) *
          CommonCoverSolve.coveringBound D := mul_le_mul_of_nonneg_right hbi hC0
      _ = ((1 + ChartScales.Tg) * ‖(B.symm : Plane →L[ℝ] Plane)‖ *
          CommonCoverSolve.coveringBound D) * ChartScales.S n := by ring
      _ ≤ geometryCost B D * ChartScales.S n := mul_le_mul_of_nonneg_right hcoeff hS0.le
  change 1 + ‖g.coordinateLinear‖ + ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) ≤ _
  calc
    _ ≤ 1 + geometryCost B D * ChartScales.S n +
        geometryCost B D * (1 + geometryCost B D * ChartScales.S n) := by
      exact add_le_add (add_le_add_right hcoord _) (mul_le_mul hpoint (add_le_add_right hcoord _)
        (by positivity) hK0)
    _ ≤ bandArgumentCost B D * ChartScales.S n := by
      unfold bandArgumentCost
      nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hS)]

end BandGeometry

section CurrentEvaluation

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reinsert the actual current slot time after solving the joint equation. -/
noncomputable def currentArgument (g : CCS) (k : Frequency) (p : P × Plane) : Joint P :=
  (p, (g.coordinates k p.2).2)

noncomputable def currentLinear (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : CCS) : P × Plane →L[ℝ] Joint P :=
  (ContinuousLinearMap.id ℝ (P × Plane)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P Plane)))

@[simp] theorem currentLinear_apply (g : CCS) (p : P × Plane) :
    currentLinear P g p = (p, (g.coordinateLinear p.2).2) := rfl

theorem currentArgument_affine (g : CCS) (k : Frequency) (p : P × Plane) :
    currentArgument g k p = currentArgument g k 0 + currentLinear P g p := by
  simp only [currentArgument, g.coordinates_eq_affine k p.2, currentLinear_apply]
  ext <;> simp

theorem currentArgument_smooth (g : CCS) (k : Frequency) :
    ContDiff ℝ ∞ (currentArgument (P := P) g k) := by
  have he : currentArgument (P := P) g k =
      fun p => currentArgument g k 0 + currentLinear P g p :=
    funext (currentArgument_affine g k)
  rw [he]
  exact contDiff_const.add (currentLinear P g).contDiff

theorem norm_currentLinear_le (g : CCS) : ‖currentLinear P g‖ ≤ argumentCost g := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (one_le_argumentCost g))
  intro p
  rw [currentLinear_apply, Prod.norm_def]
  refine max_le (le_mul_of_one_le_left (norm_nonneg _) (one_le_argumentCost g)) ?_
  have hc : ‖g.coordinateLinear‖ ≤ argumentCost g := by
    unfold argumentCost
    have hp : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
    linarith
  exact (norm_snd_le (g.coordinateLinear p.2)).trans ((g.coordinateLinear.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))))


end CurrentEvaluation

section BandInputs

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]









end BandInputs

section DyadicChanges

/-- The exact ratio `(Q_n / Q_m)^a`, written without a division. -/
noncomputable def bandRatio (a : ℝ) (n m : ℕ) : ℝ :=
  (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * a)


theorem bandRatio_eq_rpow (a : ℝ) (n m : ℕ) :
    bandRatio a n m = (ChartScales.Q n / ChartScales.Q m) ^ a := by
  rw [Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  unfold bandRatio ChartScales.Q SlotColoring.dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring







abbrev SlowPoint := ℝ × (ℝ × ℝ)

/-- Actual `(R,Z,T)` chart change from band `n` to band `m`. -/
noncomputable def bandChart (D : ℝ) (n m : ℕ) : SlowPoint →L[ℝ] SlowPoint :=
  (bandRatio (1 / 2) n m • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    ((bandRatio D n m • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))).prod
      (bandRatio 1 n m • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))

@[simp] theorem bandChart_apply (D : ℝ) (n m : ℕ) (x : SlowPoint) :
    bandChart D n m x = (bandRatio (1 / 2) n m * x.1,
      (bandRatio D n m * x.2.1, bandRatio 1 n m * x.2.2)) := rfl

theorem bandChart_formula (D : ℝ) (n m : ℕ) (x : SlowPoint) :
    bandChart D n m x = ((ChartScales.Q n / ChartScales.Q m) ^ (1 / 2 : ℝ) * x.1,
      ((ChartScales.Q n / ChartScales.Q m) ^ D * x.2.1,
        (ChartScales.Q n / ChartScales.Q m) * x.2.2)) := by
  simp only [bandChart_apply, bandRatio_eq_rpow, Real.rpow_one]



noncomputable def chartCost (D : ℝ) : ℝ := 1 + (2 : ℝ) ^ (4 * (1 + |D|))





/-- Coarsest of a pair of simultaneously active levels. -/
noncomputable def commonIndex (h : ℝ) (n m : ℕ) : ℕ := min (ChartScales.nativeIndex h n) (ChartScales.nativeIndex h m)



end DyadicChanges

section ClassTransport

variable {X Y V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_affine_jet_le_on {f : Y → V} {U : Set Y} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (L : X →L[ℝ] Y) (c : Y) {x : X}
    (hx : c + L x ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z => f (c + L z)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (c + L x)‖ * ‖L‖ ^ j := by
  have hU' : IsOpen ((fun y : Y => c + y) ⁻¹' U) :=
    hU.preimage (continuous_const.add continuous_id)
  have hf' : ContDiffOn ℝ ∞ (fun y => f (c + y)) ((fun y : Y => c + y) ⁻¹' U) :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)
  have hb := PhysicalGraphBounds.norm_jet_comp_linear hU' hf' L hx j
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left] using hb

/-- All hypotheses other than the source class concern the actual affine
maps and the prescribed weights/scales. No derivative bound on the
pulled-back source is a premise. Polynomial map and edge costs do not change
the small-scale exponent. -/
theorem memClass_affine_transport
    (s : WeightedClasses.StripData Y) (t : WeightedClasses.StripData X)
    {w : ℕ → Y → ℝ} {v : ℕ → X → ℝ} {α : ℝ} {f : ℕ → Y → V}
    (hf : WeightedClasses.MemClass s w α f)
    (index : ℕ → ℕ) (L : ℕ → X →L[ℝ] Y) (c : ℕ → Y)
    (hmap : ∀ n x, x ∈ t.domain → c n + L n x ∈ s.domain)
    (hweight : ∀ n x, x ∈ t.domain → w (index n) (c n + L n x) = v n x)
    {Ce Cg CL : ℝ} (hCe : 0 ≤ Ce) (hCg : 1 ≤ Cg) (hCL : 1 ≤ CL) (r l : ℕ)
    (heps : ∀ n, s.epsilon (index n) ^ α ≤ Ce * t.epsilon n ^ α)
    (hgrowth : ∀ n x, x ∈ t.domain →
      s.growth (index n) (c n + L n x) ≤ Cg * t.growth n x ^ r)
    (hlinear : ∀ n x, x ∈ t.domain → ‖L n‖ ≤ CL * t.growth n x ^ l) :
    WeightedClasses.MemClass t v α (fun n x => f (index n) (c n + L n x)) := by
  have hv : ∀ n x, x ∈ t.domain → 0 ≤ v n x := by
    intro n x hx
    rw [← hweight n x hx]
    exact hf.weight_nonneg _ _ (hmap n x hx)
  refine ⟨hv, ?_, ?_⟩
  · intro n
    exact (hf.smooth (index n)).comp
      (contDiff_const.add (L n).contDiff).contDiffOn (hmap n)
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hf.bounds m
    refine ⟨A * Ce * Cg ^ p * CL ^ m, by positivity, r * p + l * m, ?_⟩
    intro n x hx j hj
    have htarget := t.growth_nonneg n x
    have hsource := s.growth_nonneg (index n) (c n + L n x)
    have hCL0 : 0 ≤ CL := zero_le_one.trans hCL
    have hCg0 : 0 ≤ Cg := zero_le_one.trans hCg
    have hpow : ‖L n‖ ^ j ≤ CL ^ m * t.growth n x ^ (l * m) := by
      calc
        _ ≤ (CL * t.growth n x ^ l) ^ j := pow_le_pow_left₀ (norm_nonneg _) (hlinear n x hx) j
        _ ≤ (CL * t.growth n x ^ l) ^ m :=
          pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hCL
            (one_le_pow₀ (t.one_le_growth n x))) hj
        _ = _ := by rw [mul_pow, ← pow_mul]
    have hgpow : s.growth (index n) (c n + L n x) ^ p ≤
        Cg ^ p * t.growth n x ^ (r * p) := by
      simpa only [mul_pow, ← pow_mul] using
        pow_le_pow_left₀ hsource (hgrowth n x hx) p
    have hstart := norm_affine_jet_le_on s.isOpen_domain (hf.smooth (index n))
      (L n) (c n) (hmap n x hx) j
    refine hstart.trans ?_
    calc
      _ ≤ WeightedClasses.majorant s w α A p (index n) (c n + L n x) * ‖L n‖ ^ j :=
        mul_le_mul_of_nonneg_right (hb _ _ (hmap n x hx) j hj) (pow_nonneg (norm_nonneg _) _)
      _ = (A * s.epsilon (index n) ^ α * s.growth (index n) (c n + L n x) ^ p * v n x) *
          ‖L n‖ ^ j := by rw [WeightedClasses.majorant, hweight n x hx]
      _ ≤ (A * (Ce * t.epsilon n ^ α) * (Cg ^ p * t.growth n x ^ (r * p)) * v n x) *
          (CL ^ m * t.growth n x ^ (l * m)) := by
        have hv0 := hv n x hx
        have htε : 0 ≤ t.epsilon n ^ α := (Real.rpow_pos_of_pos (t.epsilon_pos n) α).le
        gcongr
        exact heps n
      _ = WeightedClasses.majorant t v α (A * Ce * Cg ^ p * CL ^ m)
          (r * p + l * m) n x := by
        unfold WeightedClasses.majorant
        rw [pow_add]
        ring

/-- A strip over a linear parameter projection. Its weights are the actual
base weights, so retaining the parameter preserves them exactly. -/
noncomputable def parameterStrip (s : WeightedClasses.StripData Y) (L : X →L[ℝ] Y) :
    WeightedClasses.StripData X where
  domain := L ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage L.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta x := s.delta (L x)
  delta_pos _ hx := s.delta_pos _ hx
  zeta x := s.zeta (L x)
  zeta_smooth := s.zeta_smooth.comp L.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg _ hx := s.zeta_nonneg _ hx

@[simp] theorem parameterStrip_growth (s : WeightedClasses.StripData Y) (L : X →L[ℝ] Y)
    (n : ℕ) (x : X) : (parameterStrip s L).growth n x = s.growth n (L x) := rfl

end ClassTransport

section SourceClasses

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def sourceStrip (s : WeightedClasses.StripData P) : WeightedClasses.StripData (P × Plane) :=
  parameterStrip s (ContinuousLinearMap.fst ℝ P Plane)



end SourceClasses

section CommonBandChanges

/-- Either direction of a bounded covering change. The inverse is a map on
the universal cover; no extra periodicity is imposed on its input. -/
noncomputable def coverChange (forward : Bool) (d : ℕ) : Plane →L[ℝ] Plane :=
  if forward then (CommonCoverSolve.coverPower d : Plane →L[ℝ] Plane)
  else ((CommonCoverSolve.coverPower d).symm : Plane →L[ℝ] Plane)

theorem norm_coverChange_le (forward : Bool) {d D : ℕ} (hd : d ≤ D) :
    ‖coverChange forward d‖ ≤ CommonCoverSolve.coveringBound D := by
  cases forward
  · exact CommonCoverSolve.inverseCoveringNorm_le_bound hd
  · exact CommonCoverSolve.coveringNorm_le_bound hd

noncomputable def bandCommonChart (D : ℝ) (n m : ℕ) (forward : Bool) (gap : ℕ) :
    SlowPoint × Plane →L[ℝ] SlowPoint × Plane :=
  (bandChart D n m).prodMap (coverChange forward gap)

@[simp] theorem bandCommonChart_apply (D : ℝ) (n m : ℕ) (forward : Bool) (gap : ℕ)
    (x : SlowPoint × Plane) :
    bandCommonChart D n m forward gap x = (bandChart D n m x.1, coverChange forward gap x.2) := rfl

noncomputable def commonChartCost (D : ℝ) (gapBound : ℕ) : ℝ :=
  chartCost D + CommonCoverSolve.coveringBound gapBound





end CommonBandChanges

section PhysicalProfileWeights




noncomputable def profileDomain (h a b : ℝ) : Set SlowPoint :=
  {x | x ∈ SimilarityHomogeneity.chartDomain ∧ SimilarityHomogeneity.chartX h x ∈ Ioo a b}








end PhysicalProfileWeights

section MeshChanges



noncomputable def meshLinear (D : ℝ) (L M : SlotColoring.Label) :
    SlotColoring.Position →L[ℝ] SlotColoring.Position :=
  ContinuousLinearMap.pi (fun j : Fin 3 =>
    (SlotColoring.width D j L.1 / SlotColoring.width D j M.1) •
      (ContinuousLinearMap.proj j : SlotColoring.Position →L[ℝ] ℝ))



@[simp] theorem meshLinear_apply (D : ℝ) (L M : SlotColoring.Label)
    (x : SlotColoring.Position) (j : Fin 3) :
    meshLinear D L M x j = (SlotColoring.width D j L.1 / SlotColoring.width D j M.1) * x j := rfl


theorem mesh_ratioBound_pos (D : ℝ) : 0 < SlotColoring.ratioBound D := by
  unfold SlotColoring.ratioBound
  positivity







end MeshChanges

section NativeInstantiation






end NativeInstantiation

end

end NavierStokes.CommonCoverClass
