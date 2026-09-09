import NavierStokes.LabelSumBounds
import NavierStokes.LinearWaveBounds
import Mathlib.Data.Countable.Defs

/-!
# Uniform primary weights and curl estimates

A single enumeration of the joint band/label index transfers the existing
weighted analysis without losing any inverse-edge factors.  The reindexed
strip retains the same domain, edge distance, and vanishing weight.  Every
constant is chosen before both the original band and the label.
-/

noncomputable section

namespace NavierStokes.UniformPrimaryWeights

open Set Function Filter WeightedClasses LabelSumBounds
open scoped ContDiff Topology BigOperators

variable {ι E F G : Type*} {D : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Only the discrete scales are reindexed. The spatial edge geometry and
its possibly vanishing weight are exactly the original ones. -/
noncomputable def reindexedStrip (s : StripData D) (e : ℕ → ℕ × ι) : StripData D where
  domain := s.domain
  isOpen_domain := s.isOpen_domain
  epsilon k := s.epsilon (e k).1
  epsilon_pos k := s.epsilon_pos (e k).1
  epsilon_le_one k := s.epsilon_le_one (e k).1
  slow k := s.slow (e k).1
  one_le_slow k := s.one_le_slow (e k).1
  delta := s.delta
  delta_pos := s.delta_pos
  zeta := s.zeta
  zeta_smooth := s.zeta_smooth
  zeta_nonneg := s.zeta_nonneg

noncomputable def pull (e : ℕ → ℕ × ι) (f : ι → ℕ → D → E) : ℕ → D → E :=
  fun k => f (e k).2 (e k).1

@[simp] theorem reindexed_growth (s : StripData D) (e : ℕ → ℕ × ι) (k : ℕ) (x : D) :
    (reindexedStrip s e).growth k x = s.growth (e k).1 x := rfl

@[simp] theorem reindexed_majorant (s : StripData D) (e : ℕ → ℕ × ι)
    (w : ι → ℕ → D → ℝ) (α C : ℝ) (p k : ℕ) (x : D) :
    majorant (reindexedStrip s e) (pull e w) α C p k x =
      majorant s (w (e k).2) α C p (e k).1 x := rfl

theorem pull_class {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → D → E} (hf : UniformClass s w α f) (e : ℕ → ℕ × ι) :
    MemClass (reindexedStrip s e) (pull e w) α (pull e f) := by
  refine ⟨fun k => hf.weight_nonneg (e k).2 (e k).1,
    fun k => hf.smooth (e k).2 (e k).1, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun k => hb (e k).2 (e k).1⟩

/-- Surjectivity is the reason the constants also control every original
label. It is never replaced by a separate bound for each label. -/
theorem uniform_of_pull {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → D → E} {e : ℕ → ℕ × ι} (he : Surjective e)
    (hf : MemClass (reindexedStrip s e) (pull e w) α (pull e f)) :
    UniformClass s w α f := by
  refine ⟨?_, ?_, ?_⟩
  · intro l n x hx
    obtain ⟨k, hk⟩ := he (n, l)
    simpa only [pull, hk] using hf.weight_nonneg k x hx
  · intro l n
    obtain ⟨k, hk⟩ := he (n, l)
    have h := hf.smooth k
    simp only [pull, hk] at h
    exact h
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
    obtain ⟨k, hk⟩ := he (n, l)
    simpa only [reindexed_majorant, pull, hk] using hb k x hx j hj

noncomputable def enumeration (ι : Type*) [Countable ι] [Nonempty ι] : ℕ → ℕ × ι :=
  Classical.choose (exists_surjective_nat (ℕ × ι))

theorem enumeration_surjective (ι : Type*) [Countable ι] [Nonempty ι] :
    Surjective (enumeration ι) := Classical.choose_spec (exists_surjective_nat (ℕ × ι))







section WeightedOperations

variable [Countable ι] [Nonempty ι]
  {s : StripData D} {w g r : ι → ℕ → D → ℝ} {β : ℝ}



end WeightedOperations

section Calculus

variable {s : StripData D} {w v : ι → ℕ → D → ℝ} {α β : ℝ}

theorem fderiv_class {f : ι → ℕ → D → E} (hf : UniformClass s w α f) :
    UniformClass s w α (fun l n => fderiv ℝ (f l n)) := by
  refine ⟨hf.weight_nonneg, fun l n =>
    (contDiffOn_infty_iff_fderiv_of_isOpen s.isOpen_domain).mp (hf.smooth l n) |>.2, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds (m + 1)
  refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hb l n x hx (j + 1) (Nat.add_le_add_right hj 1)




theorem along_class {V : ι → ℕ → D → D} {f : ι → ℕ → D → E}
    (hV : UniformClass s (fun _ _ _ => 1) β V) (hf : UniformClass s w α f) :
    UniformClass s w (α + β) (fun l n => HarmonicCalculus.along (V l n) (f l n)) := by
  have h := (fderiv_class hf).bilinear hV (ContinuousLinearMap.apply ℝ E).flip
  simp only [mul_one] at h ⊢
  exact h

theorem class_of_single {w : ℕ → D → ℝ} {f : ℕ → D → E} (hf : MemClass s w α f) :
    UniformClass s (fun _ : ι => w) α (fun _ : ι => f) := by
  refine ⟨fun _ => hf.weight_nonneg, fun _ => hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun _ => hb⟩

noncomputable def UniformBandBound (s : StripData D) (β : ℝ) (a : ι → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n,
    ‖a l n‖ ≤ C * s.epsilon n ^ β * s.slow n ^ p

theorem pull_bandBound {a : ι → ℕ → ℝ} (ha : UniformBandBound s β a)
    (e : ℕ → ℕ × ι) : BandBound (reindexedStrip s e) β (fun k => a (e k).2 (e k).1) := by
  obtain ⟨C, hC, p, hb⟩ := ha
  exact ⟨C, hC, p, fun k => hb (e k).2 (e k).1⟩



end Calculus

section Covariance

variable [Countable ι] [Nonempty ι]
  {s : StripData D} {r : ι → ℕ → ℝ}
  {H : ι → ℕ → D → SmoothCovariance.Mat2}
  {T : ι → ℕ → D → SmoothCovariance.Vec2} {w : ι → ℕ → D → ℝ}



end Covariance


section Primary

variable [Countable ι] [Nonempty ι] {s : StripData D}
  {P : ι → ℕ → D → ℝ} {H : ι → ℕ → D → SmoothCovariance.Mat2}
  {T : ι → ℕ → D → SmoothCovariance.Vec2}
  {mask : ι → ℕ → D → ℝ} {v : ι → ℕ → D → ProblemStatement.Space}


end Primary

section Curl

open CurlClassBounds

variable {s : StripData D} {w : ι → ℕ → D → ℝ} {α κ : ℝ}

theorem component_class {a : ι → ℕ → D → ComplexVector}
    (ha : UniformClass s w α a) (i : Fin 3) :
    UniformClass s w α (fun l n x => a l n x i) := ha.map (ContinuousLinearMap.proj i)






/-- The half-power frequency gain is uniform even when the nonzero
integer harmonic varies with the label. -/
theorem harmonic_inverse_bandBound (s : StripData D) (j : ι → ℕ → ℤ)
    (hj : ∀ l n, j l n ≠ 0) :
    UniformBandBound s (1 / 2) (fun l n => 1 / (carrierFrequency s n * (j l n : ℝ))) := by
  refine ⟨1, zero_le_one, 0, fun l n => ?_⟩
  have hk := carrierFrequency_pos s n
  have hjabs : (1 : ℝ) ≤ |(j l n : ℝ)| := by exact_mod_cast Int.one_le_abs (hj l n)
  have hden : carrierFrequency s n ≤ carrierFrequency s n * |(j l n : ℝ)| :=
    le_mul_of_one_le_right hk.le hjabs
  simp only [Real.norm_eq_abs, abs_div, abs_one, abs_mul, abs_of_pos hk, pow_zero, mul_one, one_mul]
  calc
    1 / (carrierFrequency s n * |(j l n : ℝ)|) ≤ 1 / carrierFrequency s n :=
      div_le_div_of_nonneg_left zero_le_one hk hden
    _ ≤ Real.sqrt (s.epsilon n) :=
      (Scaling.reciprocal_frequency_bounds (s.epsilon_pos n) (s.epsilon_le_one n)).2
    _ = _ := Real.sqrt_eq_rpow _

end Curl

section ActualPhase

open PrimaryPulseBounds PhaseJetBounds

variable {U : Domain (ℕ × ι) PhaseCalculus.Slow}











end ActualPhase


section ActualCutoff

open PrimaryPulseBounds PhaseJetBounds

variable {U : Domain (ℕ × ι) PhaseCalculus.Slow}



end ActualCutoff




end NavierStokes.UniformPrimaryWeights
