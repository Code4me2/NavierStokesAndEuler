import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rapid radial modulation

Concrete chain rules, shear identities, and estimates for the modulation in
Proposition 6.2. Frequencies are positive real numbers; hence the results apply
in particular to positive integer frequencies. All derivatives are genuine
`deriv`/`fderiv` derivatives, rather than formal differential symbols.
-/

noncomputable section

namespace NavierStokes.RadialModulation

open Set MeasureTheory
open scoped ContDiff Topology

abbrev PhasePoint := ℝ × ℝ × ℝ
abbrev BaseProfile := ℝ → ℝ → ℝ
abbrev PrimitiveProfile := PhasePoint → ℝ

def phasePoint (n X η : ℝ) : PhasePoint := (X, η, n * Real.log X)
def partialX (A : PrimitiveProfile) (z : PhasePoint) : ℝ := fderiv ℝ A z (1, 0, 0)
def partialEta (A : PrimitiveProfile) (z : PhasePoint) : ℝ := fderiv ℝ A z (0, 1, 0)
def partialTheta (A : PrimitiveProfile) (z : PhasePoint) : ℝ := fderiv ℝ A z (0, 0, 1)

def modulatedE (n : ℝ) (E : BaseProfile) (A : PrimitiveProfile) (X η : ℝ) : ℝ :=
  E X η * Real.exp (A (phasePoint n X η) / n)

def modulatedU (n : ℝ) (U : BaseProfile) (B : PrimitiveProfile) (X η : ℝ) : ℝ :=
  U X η + B (phasePoint n X η) / n

/-- The logarithmic graph and modulated angular profile are genuinely smooth
at every positive radius (indeed at every nonzero radius). -/
theorem modulatedE_contDiffAt
    (E : BaseProfile) (A : PrimitiveProfile) (n X η : ℝ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) (hA : ContDiff ℝ ∞ A) (hX : X ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (modulatedE n E A)) (X, η) := by
  have hgraph : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => phasePoint n z.1 z.2) (X, η) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk
      (contDiffAt_const.mul (contDiffAt_fst.log hX)))
  exact hE.contDiffAt.mul (((hA.contDiffAt.comp (X, η) hgraph).div_const n).exp)

theorem modulatedU_contDiffAt
    (U : BaseProfile) (B : PrimitiveProfile) (n X η : ℝ)
    (hU : ContDiff ℝ ∞ (Function.uncurry U)) (hB : ContDiff ℝ ∞ B) (hX : X ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (modulatedU n U B)) (X, η) := by
  have hgraph : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => phasePoint n z.1 z.2) (X, η) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk
      (contDiffAt_const.mul (contDiffAt_fst.log hX)))
  exact hU.contDiffAt.add ((hB.contDiffAt.comp (X, η) hgraph).div_const n)

/-- The rapid radial phase contributes exactly `(n/X) A_θ`. -/
theorem phase_hasDerivAt_X
    (A : PrimitiveProfile) (n X η : ℝ) (hX : X ≠ 0)
    (hA : DifferentiableAt ℝ A (phasePoint n X η)) :
    HasDerivAt (fun r => A (phasePoint n r η))
      (partialX A (phasePoint n X η) +
        (n / X) * partialTheta A (phasePoint n X η)) X := by
  have hg := (hasDerivAt_id X).prodMk
    ((hasDerivAt_const X η).prodMk ((Real.hasDerivAt_log hX).const_mul n))
  have hc := hA.hasFDerivAt.comp_hasDerivAt X hg
  have hv : (1, (0, n * X⁻¹)) =
      (1, 0, 0) + (n / X) • ((0, 0, 1) : PhasePoint) := by
    ext <;> simp [div_eq_mul_inv]
  rw [hv, map_add, map_smul] at hc
  simpa only [id_eq, phasePoint, Function.comp_def, partialX, partialTheta, smul_eq_mul] using hc


/-- Exact radial derivative of the multiplicative angular modulation. -/
theorem modulatedE_hasDerivAt_X
    (E : BaseProfile) (A : PrimitiveProfile) (n X η : ℝ) (hn : n ≠ 0) (hX : X ≠ 0)
    (hE : DifferentiableAt ℝ (fun r => E r η) X)
    (hA : DifferentiableAt ℝ A (phasePoint n X η)) :
    HasDerivAt (fun r => modulatedE n E A r η)
      (Real.exp (A (phasePoint n X η) / n) *
        (deriv (fun r => E r η) X + E X η *
          (partialX A (phasePoint n X η) / n + partialTheta A (phasePoint n X η) / X))) X := by
  have hd := hE.hasDerivAt.mul (((phase_hasDerivAt_X A n X η hX hA).div_const n).exp)
  apply hd.congr_deriv
  field_simp

/-- Exact radial derivative of the additive axial modulation. -/
theorem modulatedU_hasDerivAt_X
    (U : BaseProfile) (B : PrimitiveProfile) (n X η : ℝ) (hn : n ≠ 0) (hX : X ≠ 0)
    (hU : DifferentiableAt ℝ (fun r => U r η) X)
    (hB : DifferentiableAt ℝ B (phasePoint n X η)) :
    HasDerivAt (fun r => modulatedU n U B r η)
      (deriv (fun r => U r η) X + partialX B (phasePoint n X η) / n +
        partialTheta B (phasePoint n X η) / X) X := by
  have hd := hU.hasDerivAt.add ((phase_hasDerivAt_X B n X η hX hB).div_const n)
  apply hd.congr_deriv
  field_simp; ring



/-- Exact angular shear: the only error after the primitive prescription is
the slow radial derivative of `A`, divided by frequency. -/
theorem angular_shear_exact
    (E : BaseProfile) (A : PrimitiveProfile) (n X η aL : ℝ)
    (hn : n ≠ 0) (hX : X ≠ 0) (hE0 : E X η ≠ 0)
    (hE : DifferentiableAt ℝ (fun r => E r η) X)
    (hA : DifferentiableAt ℝ A (phasePoint n X η))
    (hprescribed : partialTheta A (phasePoint n X η) =
      -(aL - (1 - 2 * X * deriv (fun r => E r η) X / E X η)) / 2) :
    1 - 2 * X * deriv (fun r => modulatedE n E A r η) X / modulatedE n E A X η =
      aL - 2 * X * partialX A (phasePoint n X η) / n := by
  rw [(modulatedE_hasDerivAt_X E A n X η hn hX hE hA).deriv]
  unfold modulatedE
  rw [hprescribed]
  field_simp [Real.exp_ne_zero]; ring

/-- Exact axial shear, including the multiplicative correction caused by the
changed angular velocity in its denominator. -/
theorem axial_shear_exact
    (E U : BaseProfile) (A B : PrimitiveProfile) (n X η bL : ℝ)
    (hn : n ≠ 0) (hX : X ≠ 0) (hE0 : E X η ≠ 0)
    (hU : DifferentiableAt ℝ (fun r => U r η) X)
    (hB : DifferentiableAt ℝ B (phasePoint n X η))
    (hprescribed : partialTheta B (phasePoint n X η) =
      E X η * (bL - 2 * X * deriv (fun r => U r η) X / E X η) / 2) :
    2 * X * deriv (fun r => modulatedU n U B r η) X / modulatedE n E A X η =
      (bL + 2 * X * partialX B (phasePoint n X η) / (n * E X η)) /
        Real.exp (A (phasePoint n X η) / n) := by
  rw [(modulatedU_hasDerivAt_X U B n X η hn hX hU hB).deriv]
  unfold modulatedE
  rw [hprescribed]
  field_simp [Real.exp_ne_zero]; ring



/-- The primitive is an actual interval integral. -/
def periodicPrimitive (q : ℝ → ℝ) (θ : ℝ) : ℝ := intervalIntegral q 0 θ volume

theorem periodicPrimitive_hasDerivAt
    (q : ℝ → ℝ) (hq : Continuous q) (θ : ℝ) :
    HasDerivAt (periodicPrimitive q) (q θ) θ := by
  exact intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 θ)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

/-- Zero mean is precisely what removes the drift of the integral primitive. -/
theorem periodicPrimitive_periodic
    (q : ℝ → ℝ) (hq : Continuous q) (hperiodic : Function.Periodic q 1)
    (hzero : intervalIntegral q 0 1 volume = 0) :
    Function.Periodic (periodicPrimitive q) 1 := by
  intro θ
  simpa only [periodicPrimitive, zero_add, hzero, add_zero] using
    hperiodic.intervalIntegral_add_eq_add 0 θ (fun a b => hq.intervalIntegrable a b)


/-- Subtracting the primitive's mean fixes the zero-mean normalization. -/
def zeroMeanPrimitive (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  periodicPrimitive q θ - intervalIntegral (periodicPrimitive q) 0 1 volume

theorem zeroMeanPrimitive_hasDerivAt
    (q : ℝ → ℝ) (hq : Continuous q) (θ : ℝ) :
    HasDerivAt (zeroMeanPrimitive q) (q θ) θ := by
  exact (periodicPrimitive_hasDerivAt q hq θ).sub_const _

theorem zeroMeanPrimitive_integral
    (q : ℝ → ℝ) (hq : Continuous q) :
    intervalIntegral (zeroMeanPrimitive q) 0 1 volume = 0 := by
  have hd : Differentiable ℝ (periodicPrimitive q) :=
    fun θ => (periodicPrimitive_hasDerivAt q hq θ).differentiableAt
  have hc : Continuous (periodicPrimitive q) := hd.continuous
  unfold zeroMeanPrimitive
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1)]
  simp



/-! ### Uniform bounds for every fixed parameter jet -/

/-- Coordinates are amplitude, radius, parameter, periodic angle. -/
abbrev FamilyPoint := ℝ × PhasePoint

def etaDirection : FamilyPoint := (0, 0, 1, 0)
def amplitudeDirection : FamilyPoint := (1, 0, 0, 0)

/-- Iterated genuine directional derivatives in the parameter coordinate. -/
def etaJet : ℕ → (FamilyPoint → ℝ) → FamilyPoint → ℝ
  | 0, F => F
  | k + 1, F => fun z => fderiv ℝ (etaJet k F) z etaDirection

theorem etaJet_contDiff (F : FamilyPoint → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    ContDiff ℝ ∞ (etaJet k F) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- The directional jet is exactly the ordinary iterated derivative along η. -/
theorem etaJet_eq_iteratedDeriv
    (F : FamilyPoint → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) (ε X η θ : ℝ) :
    iteratedDeriv k (fun e => F (ε, X, e, θ)) η = etaJet k F (ε, X, η, θ) := by
  induction k generalizing η with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    rw [show iteratedDeriv k (fun e => F (ε, X, e, θ)) =
      (fun e => etaJet k F (ε, X, e, θ)) from funext ih]
    have hd := ((etaJet_contDiff F hF k).differentiable (by simp) (ε, X, η, θ)).hasFDerivAt
    have hg := (hasDerivAt_const η ε).prodMk
      ((hasDerivAt_const η X).prodMk
        ((hasDerivAt_id η).prodMk (hasDerivAt_const η θ)))
    exact (hd.comp_hasDerivAt η hg).deriv

/-- A smooth periodic family varies by `C_k/n` in each fixed η derivative,
uniformly on compact radius/parameter sets and all angles. The constant is
proved to exist by compactness of the actual next derivative, then the MVT. -/
theorem uniform_periodic_family_eta_jets
    (F : FamilyPoint → ℝ) (hF : ContDiff ℝ ∞ F)
    (hperiodic : ∀ ε X η, Function.Periodic (fun θ => F (ε, X, η, θ)) 1)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη, ∀ θ : ℝ,
      |iteratedDeriv k (fun e => F (1 / n, X, e, θ)) η -
        iteratedDeriv k (fun e => F (0, X, e, θ)) η| ≤ C / n := by
  have hj := etaJet_contDiff F hF k
  have hdj : ContDiff ℝ ∞ (fderiv ℝ (etaJet k F)) := hj.fderiv_right (by simp)
  have hd : Continuous (fun z => fderiv ℝ (etaJet k F) z amplitudeDirection) :=
    (hdj.clm_apply contDiff_const).continuous
  have hcompact : IsCompact ((Icc (0 : ℝ) 1) ×ˢ (KX ×ˢ (Kη ×ˢ Icc (0 : ℝ) 1))) :=
    isCompact_Icc.prod (hKX.prod (hKη.prod isCompact_Icc))
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn hd.continuousOn
  let C := max C₀ 0
  have hlocal : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ X ∈ KX, ∀ η ∈ Kη,
      ∀ θ ∈ Icc (0 : ℝ) 1,
      |etaJet k F (ε, X, η, θ) - etaJet k F (0, X, η, θ)| ≤ C * ε := by
    intro ε hε X hX η hη θ hθ
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun a => etaJet k F (a, X, η, θ))
          (fderiv ℝ (etaJet k F) (s, X, η, θ) amplitudeDirection) (Icc (0 : ℝ) 1) s := by
      intro s hs
      have hg := (hasDerivAt_id s).prodMk (hasDerivAt_const s ((X, η, θ) : PhasePoint))
      exact (((hj.differentiable (by simp) (s, X, η, θ)).hasFDerivAt).comp_hasDerivAt
        s hg).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (etaJet k F) (s, X, η, θ) amplitudeDirection‖ ≤ C := by
      intro s hs
      exact (hC₀ (s, X, η, θ) ⟨hs, hX, hη, hθ⟩).trans (le_max_left _ _)
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩) hε
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hε.1] using hm
  refine ⟨C, le_max_right _ _, ?_⟩
  intro n hn X hX η hη θ
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hε : 1 / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg zero_le_one hn0.le, (div_le_one hn0).mpr hn⟩
  have hθ : Int.fract θ ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩
  have heq : ∀ ε, (fun e => F (ε, X, e, θ)) = (fun e => F (ε, X, e, Int.fract θ)) := by
    intro ε
    funext e
    symm
    simpa only [Int.fract, mul_one] using
      (hperiodic ε X e).sub_int_mul_eq (x := θ) (Int.floor θ)
  rw [heq (1 / n), heq 0, etaJet_eq_iteratedDeriv F hF, etaJet_eq_iteratedDeriv F hF]
  have h := hlocal (1 / n) hε X hX η hη (Int.fract θ) hθ
  simpa only [mul_one_div] using h

def angularFamily (E : BaseProfile) (A : PrimitiveProfile) (z : FamilyPoint) : ℝ :=
  E z.2.1 z.2.2.1 * Real.exp (z.1 * A z.2)

def axialFamily (U : BaseProfile) (B : PrimitiveProfile) (z : FamilyPoint) : ℝ :=
  U z.2.1 z.2.2.1 + z.1 * B z.2

/-- Uniform `O(1/n)` closeness in every fixed actual η derivative of E.
Taking `KX = [Xa,Xb]` with `0 < Xa` gives the manuscript's compact positive annulus. -/
theorem uniform_modulatedE_eta_jets
    (E : BaseProfile) (A : PrimitiveProfile)
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) (hA : ContDiff ℝ ∞ A)
    (hperiodic : ∀ X η, Function.Periodic (fun θ => A (X, η, θ)) 1)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
      |iteratedDeriv k (modulatedE n E A X) η - iteratedDeriv k (E X) η| ≤ C / n := by
  have hF : ContDiff ℝ ∞ (angularFamily E A) := by
    unfold angularFamily
    change ContDiff ℝ ∞ (fun z : FamilyPoint =>
      (Function.uncurry E) (z.2.1, z.2.2.1) * Real.exp (z.1 * A z.2))
    have hbase : ContDiff ℝ ∞ (fun z : FamilyPoint => (z.2.1, z.2.2.1)) :=
      contDiff_snd.fst.prodMk contDiff_snd.snd.fst
    exact (hE.comp hbase).mul ((contDiff_fst.mul (hA.comp contDiff_snd)).exp)
  have hP : ∀ ε X η, Function.Periodic (fun θ => angularFamily E A (ε, X, η, θ)) 1 := by
    intro ε X η θ
    simp only [angularFamily, hperiodic X η θ]
  obtain ⟨C, hC, hbound⟩ := uniform_periodic_family_eta_jets
    (angularFamily E A) hF hP KX Kη hKX hKη k
  refine ⟨C, hC, ?_⟩
  intro n hn X hX η hη
  unfold modulatedE
  simpa only [angularFamily, phasePoint, zero_mul, Real.exp_zero, mul_one,
    div_eq_mul_inv, one_mul, mul_comm (n⁻¹)] using hbound n hn X hX η hη (n * Real.log X)

/-- Uniform `O(1/n)` closeness in every fixed actual η derivative of U. -/
theorem uniform_modulatedU_eta_jets
    (U : BaseProfile) (B : PrimitiveProfile)
    (hU : ContDiff ℝ ∞ (Function.uncurry U)) (hB : ContDiff ℝ ∞ B)
    (hperiodic : ∀ X η, Function.Periodic (fun θ => B (X, η, θ)) 1)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
      |iteratedDeriv k (modulatedU n U B X) η - iteratedDeriv k (U X) η| ≤ C / n := by
  have hF : ContDiff ℝ ∞ (axialFamily U B) := by
    unfold axialFamily
    change ContDiff ℝ ∞ (fun z : FamilyPoint =>
      (Function.uncurry U) (z.2.1, z.2.2.1) + z.1 * B z.2)
    have hbase : ContDiff ℝ ∞ (fun z : FamilyPoint => (z.2.1, z.2.2.1)) :=
      contDiff_snd.fst.prodMk contDiff_snd.snd.fst
    exact (hU.comp hbase).add (contDiff_fst.mul (hB.comp contDiff_snd))
  have hP : ∀ ε X η, Function.Periodic (fun θ => axialFamily U B (ε, X, η, θ)) 1 := by
    intro ε X η θ
    simp only [axialFamily, hperiodic X η θ]
  obtain ⟨C, hC, hbound⟩ := uniform_periodic_family_eta_jets
    (axialFamily U B) hF hP KX Kη hKX hKη k
  refine ⟨C, hC, ?_⟩
  intro n hn X hX η hη
  unfold modulatedU
  simpa only [axialFamily, phasePoint, zero_mul, add_zero,
    div_eq_mul_inv, one_mul, mul_comm (n⁻¹)] using hbound n hn X hX η hη (n * Real.log X)

end NavierStokes.RadialModulation
