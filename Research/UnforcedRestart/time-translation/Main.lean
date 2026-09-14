import NavierStokes.SolutionDifference
import NavierStokes.ComparatorBridge

/-! Time translation of actual viscosity-one operators. No existence assertion. -/
noncomputable section
open Set
open scoped ContDiff
namespace UnforcedRestart.TimeTranslation
open NavierStokes.ProblemStatement

/-- Time remains the first coordinate. No amplitude or viscosity change. -/
def shift {V : Type*} (t₀ : ℝ) (g : SpaceTime → V) : SpaceTime → V :=
  fun z => g (t₀ + z.1, z.2)

theorem shift_initial {V : Type*} (t₀ : ℝ) (g : SpaceTime → V) (x : Space) :
    shift t₀ g (0, x) = g (t₀, x) := by simp [shift]

theorem horizon_pos {t₀ : ℝ} (ht₀ : t₀ < 1) : 0 < 1 - t₀ := sub_pos.mpr ht₀

theorem shifted_time_interior {t₀ s : ℝ} (ht₀ : 0 < t₀)
    (hs : s ∈ Ico 0 (1 - t₀)) : t₀ + s ∈ Ioo (0 : ℝ) 1 := by
  constructor <;> linarith [hs.1, hs.2]

theorem shift_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ContDiffOn ℝ ∞ (shift t₀ g) (Ico 0 (1 - t₀) ×ˢ univ) := by
  apply hg.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
  intro z hz
  exact ⟨⟨add_nonneg ht₀ hz.1.1, by linarith [hz.1.2]⟩, mem_univ _⟩

theorem shift_smooth_slab {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    {t₀ S : ℝ} (ht₀ : 0 ≤ t₀) (hS : S < 1 - t₀) :
    ContDiffOn ℝ ∞ (shift t₀ g) (Icc 0 S ×ˢ univ) := by
  apply (shift_smooth hg ht₀).mono
  intro z hz
  exact ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hS⟩, hz.2⟩

theorem shift_spatialDerivative (t₀ : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    spatialDerivative (shift t₀ u) s x = spatialDerivative u (t₀ + s) x := rfl

theorem shift_divergence (t₀ : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    spatialDivergence (shift t₀ u) s x = spatialDivergence u (t₀ + s) x := rfl

theorem shift_advection (t₀ : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    advection (shift t₀ u) s x = advection u (t₀ + s) x := rfl

theorem shift_laplacian (t₀ : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    spatialLaplacian (shift t₀ u) s x = spatialLaplacian u (t₀ + s) x := rfl

theorem shift_gradient (t₀ : ℝ) (p : PressureField) (s : ℝ) (x : Space) :
    pressureGradient (shift t₀ p) s x = pressureGradient p (t₀ + s) x := rfl

/-- Full time differentiability at the old time is an explicit premise. -/
theorem shift_hasDerivAt (t₀ : ℝ) (u : VelocityField) (s : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun t => u (t, x)) (t₀ + s)) :
    HasDerivAt (fun r => shift t₀ u (r, x)) (temporalDerivative u (t₀ + s) x) s := by
  simpa only [shift, temporalDerivative, deriv, Function.comp_def, one_smul] using
    hu.hasDerivAt.scomp s ((hasDerivAt_id s).const_add t₀)

theorem shift_temporalDerivative (t₀ : ℝ) (u : VelocityField) (s : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun t => u (t, x)) (t₀ + s)) :
    temporalDerivative (shift t₀ u) s x = temporalDerivative u (t₀ + s) x :=
  (shift_hasDerivAt t₀ u s x hu).deriv

/-- Includes s=0, unlike the baseline positive-time Comparator bridge. -/
theorem shift_derivWithin (t₀ : ℝ) (u : VelocityField) {s : ℝ} (hs : 0 ≤ s)
    (x : Space) (hu : DifferentiableAt ℝ (fun t => u (t, x)) (t₀ + s)) :
    derivWithin (fun r => shift t₀ u (r, x)) (Ici 0) s =
      temporalDerivative u (t₀ + s) x :=
  (shift_hasDerivAt t₀ u s x hu).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Ici 0 s hs)

theorem shift_residual (t₀ : ℝ) (u : VelocityField) (p : PressureField)
    (s : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun t => u (t, x)) (t₀ + s)) :
    navierStokesResidual (shift t₀ u) (shift t₀ p) s x =
      navierStokesResidual u p (t₀ + s) x := by
  simp only [navierStokesResidual, shift_temporalDerivative t₀ u s x hu,
    shift_advection, shift_laplacian, shift_gradient]

/-- Presingular smoothness supplies full differentiability even at NEW time zero,
because the OLD restart time is strictly positive. -/
theorem old_time_differentiable {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u preSingularDomain) {t₀ s : ℝ}
    (ht₀ : 0 < t₀) (hs : s ∈ Ico 0 (1 - t₀)) (x : Space) :
    DifferentiableAt ℝ (fun t => u (t, x)) (t₀ + s) := by
  exact ((smooth_at_interior hu (shifted_time_interior ht₀ hs) x).comp (t₀ + s)
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

/-- Applies to actual CandidateProperties; no terminal zero-force premise. -/
theorem candidate_shift_equation {u f : VelocityField} {p : PressureField}
    (h : CandidateProperties u p f) {t₀ s : ℝ} (ht₀ : 0 < t₀)
    (hs : s ∈ Ico 0 (1 - t₀)) (x : Space) :
    navierStokesResidual (shift t₀ u) (shift t₀ p) s x = shift t₀ f (s, x) := by
  rw [shift_residual t₀ u p s x (old_time_differentiable h.velocity_smooth ht₀ hs x)]
  exact h.navier_stokes (t₀ + s) (shifted_time_interior ht₀ hs) x

/-- Real boundary convention, at all nonnegative presingular shifted times. -/
theorem candidate_shift_within_equation {u f : VelocityField} {p : PressureField}
    (h : CandidateProperties u p f) {t₀ s : ℝ} (ht₀ : 0 < t₀)
    (hs : s ∈ Ico 0 (1 - t₀)) (x : Space) :
    derivWithin (fun r => shift t₀ u (r, x)) (Ici 0) s +
      advection (shift t₀ u) s x - spatialLaplacian (shift t₀ u) s x +
      pressureGradient (shift t₀ p) s x = shift t₀ f (s, x) := by
  rw [shift_derivWithin t₀ u hs.1 x (old_time_differentiable h.velocity_smooth ht₀ hs x)]
  exact h.navier_stokes (t₀ + s) (shifted_time_interior ht₀ hs) x

/-- Conditional on literal vanishing on the ENTIRE old terminal interval. -/
theorem candidate_shift_unforced {u f : VelocityField} {p : PressureField}
    (h : CandidateProperties u p f) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hf : ∀ t ∈ Ico t₀ 1, ∀ x : Space, f (t, x) = 0)
    {s : ℝ} (hs : s ∈ Ico 0 (1 - t₀)) (x : Space) :
    navierStokesResidual (shift t₀ u) (shift t₀ p) s x = 0 := by
  rw [candidate_shift_equation h ht₀ hs x]
  exact hf (t₀ + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩ x

#print axioms shift
#print axioms shift_initial
#print axioms horizon_pos
#print axioms shifted_time_interior
#print axioms shift_smooth
#print axioms shift_smooth_slab
#print axioms shift_spatialDerivative
#print axioms shift_divergence
#print axioms shift_advection
#print axioms shift_laplacian
#print axioms shift_gradient
#print axioms shift_hasDerivAt
#print axioms shift_temporalDerivative
#print axioms shift_derivWithin
#print axioms shift_residual
#print axioms old_time_differentiable
#print axioms candidate_shift_equation
#print axioms candidate_shift_within_equation
#print axioms candidate_shift_unforced
end UnforcedRestart.TimeTranslation
