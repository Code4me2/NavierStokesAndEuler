import NavierStokes.GaussianEnvelope
import NavierStokes.SmoothCutoffs
import NavierStokes.WeightedRadialPrimitive
import NavierStokes.WeightedClasses
import NavierStokes.PhysicalGraphBounds

/-!
# The actual Gaussian slot-cutoff errors

The profile is a constructed smooth bump, with the plateau and support radii
from Section 8.2.  No error field is set to zero: local vanishing on the plateau,
the Gaussian bound off that plateau, and higher Leibniz estimates are used.
-/

noncomputable section

namespace NavierStokes.GaussianTailFlat

open Set Filter Function
open scoped ContDiff Topology BigOperators

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-- The fixed profile has plateau radius `1/5` and support radius `1/3`. -/
noncomputable def profileBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 1 / 5
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def profile : ℝ → ℝ := profileBump

theorem profile_contDiff : ContDiff ℝ ∞ profile := profileBump.contDiff

theorem profile_mem_Icc (v : ℝ) : profile v ∈ Icc (0 : ℝ) 1 :=
  ⟨profileBump.nonneg, profileBump.le_one⟩

theorem profile_one {v : ℝ} (hv : |v - 1 / 2| ≤ 1 / 5) : profile v = 1 := by
  apply profileBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, profileBump] using hv

theorem profile_zero {v : ℝ} (hv : 1 / 3 ≤ |v - 1 / 2|) : profile v = 0 := by
  apply profileBump.zero_of_le_dist
  simpa [Real.dist_eq, profileBump] using hv

theorem profile_eventually_one {v : ℝ} (hv : |v - 1 / 2| < 1 / 5) :
    profile =ᶠ[𝓝 v] fun _ => 1 := by
  apply profileBump.eventuallyEq_one_of_mem_ball
  simpa [Metric.mem_ball, Real.dist_eq, profileBump] using hv

theorem profile_eventually_zero {v : ℝ} (hv : 1 / 3 < |v - 1 / 2|) :
    profile =ᶠ[𝓝 v] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  change v ∉ tsupport (profileBump : ℝ → ℝ)
  rw [profileBump.tsupport_eq]
  simpa [Metric.mem_closedBall, Real.dist_eq, profileBump] using (not_le.mpr hv)


theorem profile_iteratedDeriv_compact (m : ℕ) :
    HasCompactSupport (iteratedDeriv m profile) := by
  induction m with
  | zero => exact profileBump.hasCompactSupport
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem profile_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖iteratedFDeriv ℝ m profile v‖ ≤ C := by
  obtain ⟨C, hC⟩ := (profile_iteratedDeriv_compact m).exists_bound_of_continuous
    (profile_contDiff.continuous_iteratedDeriv m (nat_le_infty m))
  refine ⟨max C 0, le_max_right _ _, fun v => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hC v).trans (le_max_left _ _)

noncomputable def slotCutoff (L : ℝ) (v : ℝ) : ℝ := profile (v / L)

theorem slotCutoff_contDiff (L : ℝ) : ContDiff ℝ ∞ (slotCutoff L) :=
  profile_contDiff.comp (contDiff_id.div_const L)


theorem slot_normalized_distance {L : ℝ} (hL : 0 < L) (v : ℝ) :
    |v / L - 1 / 2| = |v - L / 2| / L := by
  have he : v / L - 1 / 2 = (v - L / 2) / L := by
    apply (eq_div_iff hL.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  rw [he, abs_div, abs_of_pos hL]

theorem slotCutoff_one {L v : ℝ} (hL : 0 < L) (hv : |v - L / 2| ≤ L / 5) :
    slotCutoff L v = 1 := by
  apply profile_one
  rw [slot_normalized_distance hL]
  apply (div_le_iff₀ hL).2
  linarith

theorem slotCutoff_zero {L v : ℝ} (hL : 0 < L) (hv : L / 3 ≤ |v - L / 2|) :
    slotCutoff L v = 0 := by
  apply profile_zero
  rw [slot_normalized_distance hL]
  apply (le_div_iff₀ hL).2
  linarith




/-- The square root of the actual flat edge is another member of that family. -/
theorem sqrt_edge (c x : ℝ) : Real.sqrt (FlatCutoff.edge c x) = FlatCutoff.edge (c / 2) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos _ hx]
  · rw [FlatCutoff.edge_of_pos _ (lt_of_not_ge hx),
      FlatCutoff.edge_of_pos _ (lt_of_not_ge hx)]
    rw [← Real.exp_half]
    congr 1
    ring

theorem sqrt_zeta (cL cR R x : ℝ) :
    Real.sqrt (WeightedRadialPrimitive.zeta cL cR R x) =
      WeightedRadialPrimitive.zeta (cL / 2) (cR / 2) R x := by
  rw [WeightedRadialPrimitive.zeta, Real.sqrt_mul (FlatCutoff.edge_nonneg _ _),
    sqrt_edge, sqrt_edge]
  rfl

/-- A single constant covers the entire slow shell, including approach to
either edge.  This is derived from the constructed `FlatCutoff.edge`. -/
theorem sqrt_zeta_inverse_power_bounded {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (R : ℝ) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioo (0 : ℝ) R,
      Real.sqrt (WeightedRadialPrimitive.zeta cL cR R x) *
        (max 1 (WeightedRadialPrimitive.delta R x)⁻¹) ^ k ≤ C := by
  obtain ⟨C, hC, hb⟩ := WeightedRadialPrimitive.weight_uniform_bound
    (cL := cL / 2) (cR := cR / 2)
    (div_pos hcL (by norm_num)) (div_pos hcR (by norm_num)) R k
  refine ⟨C, hC, fun x hx => ?_⟩
  have hd := WeightedRadialPrimitive.delta_pos hx
  have hm : (1 : ℝ) ≤ (WeightedRadialPrimitive.delta R x)⁻¹ :=
    (one_le_inv₀ hd).2 (WeightedRadialPrimitive.delta_le_one R x)
  rw [max_eq_right hm, sqrt_zeta]
  simpa only [WeightedRadialPrimitive.weight, div_eq_mul_inv, inv_pow] using hb x hx

/-! ## Exponential decay along the actual bands -/

/-- An elementary global bound, including the finite initial part of a sequence. -/
theorem polynomial_exp_bound {c : ℝ} (hc : 0 < c) (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ p * Real.exp (-c * x) ≤
      ((p.factorial : ℝ) / c ^ p) * Real.exp c := by
  have hfac : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hb := (div_le_iff₀ hfac).1
    (Real.pow_div_factorial_le_exp (c * (1 + x))
      (mul_nonneg hc.le (by linarith : 0 ≤ 1 + x)) p)
  have hp : 0 < c ^ p := pow_pos hc p
  calc
    _ = ((c * (1 + x)) ^ p / c ^ p) * Real.exp (-c * x) := by
      rw [mul_pow, mul_div_cancel_left₀ _ (ne_of_gt hp)]
    _ ≤ ((Real.exp (c * (1 + x)) * p.factorial) / c ^ p) * Real.exp (-c * x) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) (Real.exp_pos _).le
    _ = ((p.factorial : ℝ) / c ^ p) *
        (Real.exp (c * (1 + x)) * Real.exp (-c * x)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem Q_rpow_eq_exp (N : ℝ) (n : ℕ) :
    ChartScales.Q n ^ N = Real.exp (-(N * Real.log 2) * (n : ℝ)) := by
  unfold ChartScales.Q SlotColoring.dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Every polynomial in `S=n²` times a Gaussian tail is bounded by every
real power of the actual dyadic `Q=2⁻ⁿ`. No asymptotic surrogate is used. -/
theorem gaussian_beats_Q_power {c : ℝ} (hc : 0 < c) (p : ℕ) (N : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (1 + ChartScales.S n) ^ p * Real.exp (-c * ChartScales.S n) ≤
        C * ChartScales.Q n ^ N := by
  let A : ℝ := N * Real.log 2
  let K : ℝ := A ^ 2 / (2 * c)
  let B : ℝ := ((p.factorial : ℝ) / (c / 2) ^ p) * Real.exp (c / 2)
  refine ⟨B * Real.exp K, by dsimp [B]; positivity, ?_⟩
  intro n
  have hlin : A * (n : ℝ) ≤ c / 2 * (n : ℝ) ^ 2 + K := by
    have hs := sq_nonneg (c * (n : ℝ) - A)
    have hc2 : 0 < 2 * c := by positivity
    suffices A * (n : ℝ) - c / 2 * (n : ℝ) ^ 2 ≤ K by linarith
    dsimp [K]
    apply (le_div_iff₀ hc2).2
    nlinarith
  have hexp : Real.exp (-c * ChartScales.S n) ≤
      Real.exp (-(c / 2) * ChartScales.S n) * Real.exp K * ChartScales.Q n ^ N := by
    rw [Q_rpow_eq_exp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    dsimp [ChartScales.S, A] at *
    linarith
  calc
    _ ≤ (1 + ChartScales.S n) ^ p *
        (Real.exp (-(c / 2) * ChartScales.S n) * Real.exp K * ChartScales.Q n ^ N) :=
      mul_le_mul_of_nonneg_left hexp (by unfold ChartScales.S; positivity)
    _ = ((1 + ChartScales.S n) ^ p * Real.exp (-(c / 2) * ChartScales.S n)) *
        Real.exp K * ChartScales.Q n ^ N := by ring
    _ ≤ B * Real.exp K * ChartScales.Q n ^ N := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact polynomial_exp_bound (by linarith : 0 < c / 2) p (sq_nonneg (n : ℝ))
    _ = _ := by ring

theorem gaussian_length_comparison {c κ L S : ℝ} (hc : 0 ≤ c) (hL : κ * S ≤ L) :
    Real.exp (-(c / 25) * L) ≤ Real.exp (-(c * κ / 25) * S) := by
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hL hc]

/-- A fixed power loss consumes only half of a Gaussian tail. -/
theorem fixed_power_gaussian_bound {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ChartScales.Q n ^ r * Real.exp (-c * ChartScales.S n) ≤
        C * Real.exp (-(c / 2) * ChartScales.S n) := by
  obtain ⟨C, hC, hb⟩ := gaussian_beats_Q_power (by linarith : 0 < c / 2) 0 (-r)
  refine ⟨C, hC, fun n => ?_⟩
  have he : Real.exp (-c * ChartScales.S n) =
      Real.exp (-(c / 2) * ChartScales.S n) * Real.exp (-(c / 2) * ChartScales.S n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb' : Real.exp (-(c / 2) * ChartScales.S n) ≤ C * ChartScales.Q n ^ (-r) := by
    simpa only [pow_zero, one_mul] using hb n
  have hQ := ChartScales.Q_pos n
  calc
    _ = (ChartScales.Q n ^ r * Real.exp (-(c / 2) * ChartScales.S n)) *
        Real.exp (-(c / 2) * ChartScales.S n) := by rw [he]; ring
    _ ≤ (ChartScales.Q n ^ r * (C * ChartScales.Q n ^ (-r))) *
        Real.exp (-(c / 2) * ChartScales.S n) := by gcongr
    _ = _ := by
      rw [show ChartScales.Q n ^ r * (C * ChartScales.Q n ^ (-r)) =
        C * (ChartScales.Q n ^ r * ChartScales.Q n ^ (-r)) by ring,
        ← Real.rpow_add hQ, add_neg_cancel, Real.rpow_zero, mul_one]

/-! ## The actual cutoff products and all their stripped derivatives -/

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_jet_bounds {g : ℝ → ℝ}
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C := by
  classical
  choose C hC hb using hb
  refine ⟨∑ j ∈ Finset.range (m + 1), C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j hj x
  exact (hb j x).trans (Finset.single_le_sum (fun i _ => hC i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem profileDeriv_contDiff : ContDiff ℝ ∞ (deriv profile) :=
  (contDiff_infty_iff_deriv.mp profile_contDiff).2

theorem profileDeriv_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (deriv profile) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := profile_jet_bounded (m + 1)
  refine ⟨C, hC, fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ'] using hb x

theorem omittedProfile_contDiff : ContDiff ℝ ∞ (fun x => 1 - profile x) :=
  contDiff_const.sub profile_contDiff

theorem omittedProfile_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ m (fun y => 1 - profile y) x‖ ≤ C := by
  cases m with
  | zero =>
    refine ⟨1, zero_le_one, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (by
      linarith [(profile_mem_Icc x).2] : 0 ≤ 1 - profile x)]
    linarith [(profile_mem_Icc x).1]
  | succ m =>
    obtain ⟨C, hC, hb⟩ := profile_jet_bounded (m + 1)
    refine ⟨C, hC, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_const_sub (Nat.succ_pos m) (1 : ℝ)]
    change ‖iteratedDeriv (m + 1) (fun y => -profile y) x‖ ≤ C
    rw [iteratedDeriv_fun_neg, norm_neg]
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb x

theorem norm_affine_comp_jet_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (A : D →L[ℝ] ℝ) (b : ℝ) (x : D) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => g (b + A y)) x‖ ≤
      ‖iteratedFDeriv ℝ j g (b + A x)‖ * ‖A‖ ^ j := by
  have hh : ContDiff ℝ ∞ (fun z => g (b + z)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hd := A.iteratedFDeriv_comp_right hh x (i := j) (nat_le_infty j)
  change ‖iteratedFDeriv ℝ j ((fun z => g (b + z)) ∘ A) x‖ ≤ _
  rw [hd]
  simpa only [iteratedFDeriv_comp_add_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using
    (iteratedFDeriv ℝ j (fun z => g (b + z)) (A x)).norm_compContinuousLinearMap_le
      (fun _ : Fin j => A)

open WeightedClasses

/-- The offset never enters the bound. Thus translated copies have the same
constants, even when their centers differ by arbitrarily many periods. -/
theorem affine_profile_memClass (s : StripData D) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    (A : ℕ → D →L[ℝ] ℝ) (b : ℕ → ℝ)
    (hA : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ n, ‖A n‖ ≤ K * s.slow n ^ p) :
    UnweightedClass s 0 (fun n x => g (b n + A n x)) := by
  obtain ⟨K, hK, p, hA⟩ := hA
  refine ⟨fun _ _ _ => zero_le_one,
    fun n => (hg.comp (contDiff_const.add (A n).contDiff)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := finite_jet_bounds hb m
  refine ⟨C * K ^ m, by positivity, p * m, ?_⟩
  intro n x hx j hj
  have hgrowth := s.one_le_growth n x
  have hbase : 1 ≤ K * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hgrowth)
  have hAn : ‖A n‖ ≤ K * s.growth n x ^ p :=
    (hA n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
      (zero_le_one.trans hK))
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g (b n + A n x)‖ * ‖A n‖ ^ j :=
      norm_affine_comp_jet_le hg (A n) (b n) x j
    _ ≤ C * (K * s.growth n x ^ p) ^ m :=
      mul_le_mul (hb j hj _) ((pow_le_pow_left₀ (norm_nonneg _) hAn j).trans
        (pow_le_pow_right₀ hbase hj)) (pow_nonneg (norm_nonneg _) _) hC
    _ = majorant s (fun _ _ => 1) 0 (C * K ^ m) (p * m) n x := by
      simp only [majorant, Real.rpow_zero, mul_one, mul_pow, ← pow_mul]
      ring

/-- The two excluded errors, retained as actual functions. `θ` is the
normalized slot coordinate `v/L`. -/
noncomputable def cutoffError (L : ℝ) (θ : D → ℝ) (u f : D → E) (x : D) : E :=
  (L⁻¹ * deriv profile (θ x)) • u x + (1 - profile (θ x)) • f x



omit [NormedSpace ℝ D] in
theorem cutoffError_eventually_zero (L : ℝ) {θ : D → ℝ} (u f : D → E) {x : D}
    (hθ : ContinuousAt θ x) (hx : |θ x - 1 / 2| < 1 / 5) :
    cutoffError L θ u f =ᶠ[𝓝 x] fun _ => 0 := by
  have hprofile := (profile_eventually_one hx).comp_tendsto hθ
  have hderiv := (profile_eventually_one hx).deriv.comp_tendsto hθ
  filter_upwards [hprofile, hderiv] with y hy hdy
  have hy' : profile (θ y) = 1 := by simpa using hy
  have hdy' : deriv profile (θ y) = 0 := by simpa using hdy
  simp [cutoffError, hy', hdy']

theorem cutoffError_jet_zero_on_plateau (L : ℝ) {θ : D → ℝ} (u f : D → E) {x : D}
    (hθ : ContinuousAt θ x) (hx : |θ x - 1 / 2| < 1 / 5) (j : ℕ) :
    iteratedFDeriv ℝ j (cutoffError L θ u f) x = 0 := by
  have he := cutoffError_eventually_zero L u f hθ hx
  have he' : cutoffError L θ u f =ᶠ[𝓝[univ] x] fun _ => 0 := by
    simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using
    he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j

/-- This class bound is derived by all-order Leibniz, from the actual wave
and source classes and the constructed cutoff profile. -/
theorem cutoffError_mem_wave {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {u f : ℕ → D → E} (hu : WaveClass s P α u) (hf : WaveClass s P α f)
    (L : ℕ → ℝ) (A : ℕ → D →L[ℝ] ℝ) (b : ℕ → ℝ)
    (hA : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ n, ‖A n‖ ≤ K * s.slow n ^ p)
    (hL : BandBound s 0 (fun n => (L n)⁻¹)) :
    WaveClass s P α (fun n => cutoffError (L n) (fun x => b n + A n x) (u n) (f n)) := by
  have hd := (affine_profile_memClass s profileDeriv_contDiff profileDeriv_jet_bounded A b hA).band_smul hL
  have ho := affine_profile_memClass s omittedProfile_contDiff omittedProfile_jet_bounded A b hA
  have hdu := hd.smul hu
  have hof := ho.smul hf
  have hdu' : WaveClass s P α
      (fun n x => ((L n)⁻¹ * deriv profile (b n + A n x)) • u n x) := by
    simpa only [UnweightedClass, WaveClass, zero_add, add_zero, one_mul, smul_eq_mul] using hdu
  have hof' : WaveClass s P α
      (fun n x => (1 - profile (b n + A n x)) • f n x) := by
    simpa only [UnweightedClass, WaveClass, zero_add, one_mul] using hof
  exact hdu'.add hof'

/-- A slow weight controlled by the actual two-sided exponential-flat edge.
The comparison permits additional cutoffs of size at most one. -/
structure FlatEdges (s : StripData D) where
  leftDecay : ℝ
  rightDecay : ℝ
  left_pos : 0 < leftDecay
  right_pos : 0 < rightDecay
  width : ℝ
  position : D → ℝ
  position_mem : ∀ x ∈ s.domain, position x ∈ Ioo 0 width
  delta_eq : ∀ x ∈ s.domain, s.delta x = WeightedRadialPrimitive.delta width (position x)
  zeta_le : ∀ x ∈ s.domain,
    s.zeta x ≤ WeightedRadialPrimitive.zeta leftDecay rightDecay width (position x)

theorem FlatEdges.uniform_weight {s : StripData D} (e : FlatEdges s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s.domain,
      Real.sqrt (s.zeta x) * (max 1 (s.delta x)⁻¹) ^ k ≤ C := by
  obtain ⟨C, hC, hb⟩ := sqrt_zeta_inverse_power_bounded e.left_pos e.right_pos e.width k
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [e.delta_eq x hx]
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (e.zeta_le x hx))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) k)).trans
      (hb (e.position x) (e.position_mem x hx))

/-- Only the actual scale identity and a polynomial slow-scale upper bound
are used. The exponent may be any real number. -/
structure BandScaleControl (s : StripData D) where
  power : ℝ
  epsilon_eq : ∀ n, s.epsilon n = ChartScales.Q n ^ power
  constant : ℝ
  constant_one_le : 1 ≤ constant
  degree : ℕ
  slow_le : ∀ n, s.slow n ≤ constant * (1 + ChartScales.S n) ^ degree

/-- Native slot data before restriction to the physical graph.  The cutoff
coordinate is affine, and no spatial derivatives of a band index occur. -/
structure SlotFamily (s : StripData D) where
  length : ℕ → ℝ
  length_pos : ∀ n, 0 < length n
  linear : ℕ → D →L[ℝ] ℝ
  offset : ℕ → ℝ
  linear_bound : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ n, ‖linear n‖ ≤ K * s.slow n ^ p
  inverse_length_bound : BandBound s 0 (fun n => (length n)⁻¹)
  length_scale : ℝ
  length_scale_pos : 0 < length_scale
  length_lower : ∀ n, length_scale * ChartScales.S n ≤ length n

namespace SlotFamily

noncomputable def coordinate {s : StripData D} (g : SlotFamily s) (n : ℕ) (x : D) : ℝ :=
  g.offset n + g.linear n x

noncomputable def cutoff {s : StripData D} (g : SlotFamily s) (n : ℕ) (x : D) : ℝ :=
  profile (g.coordinate n x)

noncomputable def error {s : StripData D} (g : SlotFamily s) (u f : ℕ → D → E)
    (n : ℕ) : D → E := cutoffError (g.length n) (g.coordinate n) (u n) (f n)

theorem coordinate_contDiff {s : StripData D} (g : SlotFamily s) (n : ℕ) :
    ContDiff ℝ ∞ (g.coordinate n) := contDiff_const.add (g.linear n).contDiff

theorem cutoff_memClass {s : StripData D} (g : SlotFamily s) :
    UnweightedClass s 0 g.cutoff :=
  affine_profile_memClass s profile_contDiff profile_jet_bounded g.linear g.offset g.linear_bound

theorem error_mem_wave {s : StripData D} (g : SlotFamily s) {P : ℕ → D → ℝ}
    {α : ℝ} {u f : ℕ → D → E} (hu : WaveClass s P α u) (hf : WaveClass s P α f) :
    WaveClass s P α (g.error u f) :=
  cutoffError_mem_wave hu hf g.length g.linear g.offset g.linear_bound g.inverse_length_bound

/-- The derivative in a direction with `D(v)=1` is the exact coefficient
used in the retained cutoff error, because `v=L θ`. -/
theorem cutoff_directional {s : StripData D} (g : SlotFamily s) (n : ℕ) (x w : D)
    (hw : g.linear n w = (g.length n)⁻¹) :
    fderiv ℝ (g.cutoff n) x w =
      (g.length n)⁻¹ * deriv profile (g.coordinate n x) := by
  have hp := (profile_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    (x := g.coordinate n x)
  have hθ : HasFDerivAt (g.coordinate n) (g.linear n) x :=
    (g.linear n).hasFDerivAt.const_add (g.offset n)
  have hd := hp.hasFDerivAt.comp x hθ
  have he := congrArg (fun A : D →L[ℝ] ℝ => A w) hd.fderiv
  unfold cutoff
  simpa [hw, mul_comm, Function.comp_def] using he

theorem error_eq_directional {s : StripData D} (g : SlotFamily s) (u f : ℕ → D → E)
    (n : ℕ) (x w : D) (hw : g.linear n w = (g.length n)⁻¹) :
    g.error u f n x =
      fderiv ℝ (g.cutoff n) x w • u n x + (1 - g.cutoff n x) • f n x := by
  rw [g.cutoff_directional n x w hw]
  rfl

/-- Uniform polynomial-times-Gaussian bound for the two exact cutoff products.
The only field estimates assumed are the original wave/source classes and
the Gaussian upper bound for their common envelope. -/
theorem error_gaussian_bound {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {u f : ℕ → D → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (g.error u f n) x‖ ≤
        C * (1 + ChartScales.S n) ^ d *
          Real.exp (-(c * g.length_scale / 50) * ChartScales.S n) := by
  obtain ⟨A, hA, p, hb⟩ := (g.error_mem_wave hu hf).bounds m
  obtain ⟨B, hB, hweight⟩ := edges.uniform_weight p
  have hscale := g.length_scale_pos
  have hconstant := scales.constant_one_le
  have hdec : 0 < c * g.length_scale / 25 := by positivity
  obtain ⟨C, hC, hgauss⟩ := fixed_power_gaussian_bound hdec (scales.power * α)
  refine ⟨A * B * scales.constant ^ p * C, by positivity, scales.degree * p, ?_⟩
  intro n x hx j hj
  have hQ := ChartScales.Q_pos n
  by_cases hmid : |g.coordinate n x - 1 / 2| < 1 / 5
  · have hz := cutoffError_jet_zero_on_plateau (g.length n) (u n) (f n)
      (g.coordinate_contDiff n).continuous.continuousAt hmid j
    change iteratedFDeriv ℝ j (g.error u f n) x = 0 at hz
    rw [hz, norm_zero]
    have hS : 0 ≤ ChartScales.S n := sq_nonneg _
    positivity
  have htail : 1 / 5 ≤ |g.coordinate n x - 1 / 2| := le_of_not_gt hmid
  have hsq : (1 / 25 : ℝ) ≤ (g.coordinate n x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : P n x ≤ Real.exp (-(c * g.length_scale / 25) * ChartScales.S n) := by
    apply (hP n x hx).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (g.length_lower n))
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (g.length_pos n).le)]
  have hslow0 : 0 ≤ s.slow n := zero_le_one.trans (s.one_le_slow n)
  have hK0 : 0 ≤ scales.constant := zero_le_one.trans scales.constant_one_le
  have hslowp : s.slow n ^ p ≤
      scales.constant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p) := by
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ hslow0 (scales.slow_le n) p
  have hmajor : majorant s (fun n x => Real.sqrt (s.zeta x) * P n x) α A p n x ≤
      (A * B * scales.constant ^ p) * ChartScales.Q n ^ (scales.power * α) *
        ((1 + ChartScales.S n) ^ (scales.degree * p) *
          Real.exp (-(c * g.length_scale / 25) * ChartScales.S n)) := by
    rw [majorant, StripData.growth, mul_pow, scales.epsilon_eq,
      ← Real.rpow_mul hQ.le]
    calc
      _ = (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) * P n x := by ring
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) *
            Real.exp (-(c * g.length_scale / 25) * ChartScales.S n) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) * B *
            Real.exp (-(c * g.length_scale / 25) * ChartScales.S n) := by
        gcongr
        exact hweight x hx
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) *
          (scales.constant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p))) * B *
            Real.exp (-(c * g.length_scale / 25) * ChartScales.S n) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * P n x) α A p n x := hb n x hx j hj
    _ ≤ _ := hmajor
    _ = (A * B * scales.constant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (ChartScales.Q n ^ (scales.power * α) *
          Real.exp (-(c * g.length_scale / 25) * ChartScales.S n)) := by ring
    _ ≤ (A * B * scales.constant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (C * Real.exp (-((c * g.length_scale / 25) / 2) * ChartScales.S n)) := by
      have hS : 0 ≤ ChartScales.S n := sq_nonneg _
      exact mul_le_mul_of_nonneg_left (hgauss n) (by positivity)
    _ = _ := by
      rw [show c * g.length_scale / 25 / 2 = c * g.length_scale / 50 by ring]
      ring

/-- Every prescribed dyadic power is gained, for all actual stripped jets. -/
theorem error_stripped_bound {s : StripData D} (g : SlotFamily s)
    (edges : FlatEdges s) (scales : BandScaleControl s)
    {P : ℕ → D → ℝ} {α c : ℝ} {u f : ℕ → D → E}
    (hu : WaveClass s P α u) (hf : WaveClass s P α f) (hc : 0 < c)
    (hP : ∀ n x, x ∈ s.domain →
      P n x ≤ Real.exp (-c * (g.coordinate n x - 1 / 2) ^ 2 * g.length n))
    (m : ℕ) (N : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (g.error u f n) x‖ ≤ C * ChartScales.Q n ^ N := by
  obtain ⟨A, hA, d, ha⟩ := g.error_gaussian_bound edges scales hu hf hc hP m
  have hscale := g.length_scale_pos
  obtain ⟨B, hB, hb⟩ := gaussian_beats_Q_power (by positivity : 0 < c * g.length_scale / 50) d N
  refine ⟨A * B, by positivity, fun n x hx j hj => ?_⟩
  calc
    _ ≤ A * (1 + ChartScales.S n) ^ d *
        Real.exp (-(c * g.length_scale / 50) * ChartScales.S n) := ha n x hx j hj
    _ = A * ((1 + ChartScales.S n) ^ d *
        Real.exp (-(c * g.length_scale / 50) * ChartScales.S n)) := by ring
    _ ≤ A * (B * ChartScales.Q n ^ N) := mul_le_mul_of_nonneg_left (hb n) hA
    _ = _ := by ring


end SlotFamily

/-- The true native slot length is uniformly comparable from below to
`1+n²`; finitely many small bands are included by a finite minimum. -/
theorem native_slot_length_lower (r0 h : ℝ) (hr0 : 0 < r0) (hh : 0 ≤ h) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ,
      κ * (1 + ChartScales.S n) ≤ ChartScales.slotLength r0 h n := by
  have hL (n : ℕ) : 0 < ChartScales.slotLength r0 h n :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos h n)
  have hS (n : ℕ) : 0 < 1 + ChartScales.S n := by unfold ChartScales.S; positivity
  obtain ⟨i, hi, hmin⟩ := (Finset.range 4).exists_min_image
    (fun n => ChartScales.slotLength r0 h n / (1 + ChartScales.S n))
    (by exact ⟨0, by decide⟩)
  refine ⟨min r0 (ChartScales.slotLength r0 h i / (1 + ChartScales.S i)),
    lt_min hr0 (div_pos (hL i) (hS i)), ?_⟩
  intro n
  rcases lt_or_ge n 4 with hn | hn
  · apply (le_div_iff₀ (hS n)).1
    exact (min_le_right _ _).trans (hmin n (Finset.mem_range.mpr hn))
  · have hSn : 1 ≤ ChartScales.S n := by
      have hnn : (4 : ℝ) ≤ n := by exact_mod_cast hn
      unfold ChartScales.S
      nlinarith
    calc
      _ ≤ r0 * (1 + ChartScales.S n) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hS n).le
      _ ≤ 2 * r0 * ChartScales.S n := by nlinarith
      _ ≤ ChartScales.slotLength r0 h n := (ChartScales.slotLength_bounds r0 h hr0.le hh hn).1

/-- Actual native slots. `η` is the fixed longitudinal coordinate functional;
only the centers depend on the band. Normalizing `v` by `L` cancels `ci`. -/
noncomputable def actualSlotFamily (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) : SlotFamily s := by
  let κ := Classical.choose (native_slot_length_lower r0 h hr0 hh)
  have hκ := Classical.choose_spec (native_slot_length_lower r0 h hr0 hh)
  have hL (n : ℕ) : 0 < ChartScales.slotLength r0 h n :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos h n)
  have hκL (n : ℕ) : κ ≤ ChartScales.slotLength r0 h n := by
    apply le_trans _ (hκ.2 n)
    have hn : 0 ≤ ChartScales.S n := sq_nonneg _
    nlinarith [hκ.1]
  refine {
    length := ChartScales.slotLength r0 h
    length_pos := hL
    linear := fun _ => (2 * r0)⁻¹ • η
    offset := fun n => (r0 - center n) / (2 * r0)
    linear_bound := ?_
    inverse_length_bound := ?_
    length_scale := κ
    length_scale_pos := hκ.1
    length_lower := ?_
  }
  · refine ⟨max 1 ‖(2 * r0)⁻¹ • η‖, le_max_left _ _, 0, fun n => ?_⟩
    simpa only [pow_zero, mul_one] using le_max_right 1 ‖(2 * r0)⁻¹ • η‖
  · refine ⟨κ⁻¹, (inv_pos.mpr hκ.1).le, 0, fun n => ?_⟩
    simp only [Real.rpow_zero, pow_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hL n))]
    simpa only [one_div] using one_div_le_one_div_of_le hκ.1 (hκL n)
  · intro n
    apply le_trans _ (hκ.2 n)
    nlinarith [hκ.1]

@[simp] theorem actualSlotFamily_length (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) (n : ℕ) :
    (actualSlotFamily s r0 h hr0 hh η center).length n = ChartScales.slotLength r0 h n := rfl

theorem actualSlotFamily_coordinate (s : StripData D) (r0 h : ℝ)
    (hr0 : 0 < r0) (hh : 0 ≤ h) (η : D →L[ℝ] ℝ) (center : ℕ → ℝ) (n : ℕ) (x : D) :
    (actualSlotFamily s r0 h hr0 hh η center).coordinate n x =
      (η x - center n + r0) / (2 * r0) := by
  change (r0 - center n) / (2 * r0) + ((2 * r0)⁻¹ • η) x = _
  simp only [_root_.smul_apply, smul_eq_mul]
  ring


/-- The reference Gaussian envelope, extended by zero away from its slot.
This is a weight, not a redefinition of either retained error. -/
noncomputable def referenceSlotEnvelope (lam u L θ : ℝ) : ℝ :=
  if θ ∈ Icc (0 : ℝ) 1 then
    GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2) (L * θ)
  else 0

theorem referenceSlotEnvelope_bound {lam u L : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) (θ : ℝ) :
    referenceSlotEnvelope lam u L θ ≤
      Real.exp (-(u * GaussianEnvelope.referenceMinSlope lam u / 2) * (θ - 1 / 2) ^ 2 * L) := by
  by_cases hθ : θ ∈ Icc (0 : ℝ) 1
  · rw [referenceSlotEnvelope, ite_eq_left hθ]
    have ht : L * θ ∈ Icc (0 : ℝ) L := ⟨mul_nonneg hL.le hθ.1, by nlinarith [hθ.2]⟩
    apply (GaussianEnvelope.reference_gaussian_bounds hlam hu hL ht).2.trans_eq
    congr 1
    field_simp [hL.ne']
  · rw [referenceSlotEnvelope, ite_eq_right hθ]
    exact (Real.exp_pos _).le

/-! ## Restriction to the actual physical graph and carrier -/

namespace SlotFamily



open PhysicalGraphBounds ProblemStatement





end SlotFamily

/-! ## The two summands separately -/

namespace SlotFamily




private theorem jet_eq_zero_of_eventually {u : D → E} {x : D}
    (he : u =ᶠ[𝓝 x] fun _ => 0) (j : ℕ) : iteratedFDeriv ℝ j u x = 0 := by
  have he' : u =ᶠ[𝓝[univ] x] fun _ => 0 := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using
    he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j







end SlotFamily

end NavierStokes.GaussianTailFlat
