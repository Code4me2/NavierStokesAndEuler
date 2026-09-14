import NavierStokes.SmoothCutoffs
import NavierStokes.TimeLocalization
import NavierStokes.CandidateFromLimits
import NavierStokes.R3CompactCandidate

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace UnforcedRestart.SmoothForceCutoff
open NavierStokes.ProblemStatement

/-- A genuine smooth switch OFF, not a sharp indicator. -/
def shutdown (t₀ t₁ t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t - t₀) / (t₁ - t₀))

theorem shutdown_smooth (t₀ t₁ : ℝ) : ContDiff ℝ ∞ (shutdown t₀ t₁) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

theorem shutdown_bounds (t₀ t₁ t : ℝ) : shutdown t₀ t₁ t ∈ Icc (0 : ℝ) 1 := by
  have h := Real.smoothTransition.nonneg ((t - t₀) / (t₁ - t₀))
  have h' := Real.smoothTransition.le_one ((t - t₀) / (t₁ - t₀))
  constructor <;> dsimp [shutdown] <;> linarith

theorem shutdown_early {t₀ t₁ t : ℝ} (h : t₀ < t₁) (ht : t ≤ t₀) :
    shutdown t₀ t₁ t = 1 := by
  have hz : (t - t₀) / (t₁ - t₀) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr h).le
  simp [shutdown, Real.smoothTransition.zero_of_nonpos hz]

theorem shutdown_late {t₀ t₁ t : ℝ} (h : t₀ < t₁) (ht : t₁ ≤ t) :
    shutdown t₀ t₁ t = 0 := by
  have hz : 1 ≤ (t - t₀) / (t₁ - t₀) :=
    (le_div_iff₀ (sub_pos.mpr h)).mpr (by linarith)
  simp [shutdown, Real.smoothTransition.one_of_one_le hz]

theorem shutdown_derivative_support {t₀ t₁ : ℝ} (h : t₀ < t₁) (n : ℕ) :
    Function.support (iteratedDeriv (n + 1) (shutdown t₀ t₁)) ⊆ Icc t₀ t₁ := by
  intro t ht
  change iteratedDeriv (n + 1) (shutdown t₀ t₁) t ≠ 0 at ht
  by_contra hn
  have halt : t < t₀ ∨ t₁ < t := by
    simpa only [mem_Icc, not_and_or, not_le] using hn
  rcases halt with he | hl
  · have heq : shutdown t₀ t₁ =ᶠ[𝓝 t] (fun _ => 1) := by
      filter_upwards [Iio_mem_nhds he] with s hs
      exact shutdown_early h hs.le
    exact ht (by rw [heq.iteratedDeriv_eq (n + 1),
      NavierStokes.SmoothCutoffs.iteratedDeriv_const_succ])
  · have heq : shutdown t₀ t₁ =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds hl] with s hs
      exact shutdown_late h hs.le
    exact ht (by rw [heq.iteratedDeriv_eq (n + 1),
      NavierStokes.SmoothCutoffs.iteratedDeriv_const_succ])

def cutForce (t₀ t₁ : ℝ) (f : VelocityField) : VelocityField :=
  fun z => shutdown t₀ t₁ z.1 • f z

theorem cutForce_smoothOn (t₀ t₁ : ℝ) (f : VelocityField) (D : Set SpaceTime)
    (hf : ContDiffOn ℝ ∞ f D) : ContDiffOn ℝ ∞ (cutForce t₀ t₁ f) D :=
  ((shutdown_smooth t₀ t₁).comp contDiff_fst).contDiffOn.smul hf

theorem cutForce_early {t₀ t₁ t : ℝ} (h : t₀ < t₁) (ht : t ≤ t₀)
    (f : VelocityField) (x : Space) : cutForce t₀ t₁ f (t, x) = f (t, x) := by
  simp [cutForce, shutdown_early h ht]

theorem cutForce_late {t₀ t₁ t : ℝ} (h : t₀ < t₁) (ht : t₁ ≤ t)
    (f : VelocityField) (x : Space) : cutForce t₀ t₁ f (t, x) = 0 := by
  simp [cutForce, shutdown_late h ht]

theorem cutForce_support (t₀ t₁ : ℝ) (f : VelocityField) :
    Function.support (cutForce t₀ t₁ f) ⊆ Function.support f := by
  intro z hz
  change f z ≠ 0
  intro he
  exact hz (by simp [cutForce, he])

theorem cutForce_periodic (t₀ t₁ : ℝ) (f : VelocityField) (times : Set ℝ)
    (hf : UnitSpatialPeriodsOn times f) : UnitSpatialPeriodsOn times (cutForce t₀ t₁ f) := by
  intro t ht x i
  change shutdown t₀ t₁ t • f (t, x + coordinateVector i) = _
  rw [hf t ht x i]
  rfl

theorem cutForce_time_support {t₀ t₁ : ℝ} (h : t₀ < t₁) (h₁ : 0 ≤ t₁)
    (f : VelocityField) : CompactFutureTimeSupport (cutForce t₀ t₁ f) :=
  ⟨t₁, h₁, fun _ ht x => cutForce_late h ht f x⟩

theorem cutForce_supportedIn (t₀ t₁ : ℝ) {f : VelocityField} {K : Set Space}
    (hf : NavierStokes.CompactSpatialForceDecay.SupportedIn K f) :
    NavierStokes.CompactSpatialForceDecay.SupportedIn K (cutForce t₀ t₁ f) := by
  intro t ht x hx
  simp [cutForce, hf t ht x hx]

/-- Admissible whole-space force obtained from any actual compact candidate. -/
theorem compact_candidate_cut_admissible {t₀ t₁ : ℝ} (h : t₀ < t₁) (h₁ : 0 ≤ t₁)
    {u f : VelocityField} {p : PressureField}
    (hc : NavierStokes.R3CompactCandidate.Properties u p f) :
    NavierStokes.Comparator.ForceConditionDecay
      (NavierStokes.ComparatorBridge.toComparator (cutForce t₀ t₁ f)) := by
  obtain ⟨K, hK, hs⟩ := hc.force_support
  exact NavierStokes.CompactSpatialForceDecay.forceConditionDecay hK
    (cutForce_smoothOn t₀ t₁ f futureDomain hc.force_smooth)
    (cutForce_supportedIn t₀ t₁ hs) (cutForce_time_support h h₁ f)

/-- Exact defect of the OLD velocity for the NEW force. No existence assertion. -/
theorem old_residual_defect (t₀ t₁ t : ℝ) (x : Space)
    (u f : VelocityField) (p : PressureField)
    (heq : navierStokesResidual u p t x = f (t, x)) :
    navierStokesResidual u p t x - cutForce t₀ t₁ f (t, x) =
      (1 - shutdown t₀ t₁ t) • f (t, x) := by
  rw [heq]
  simp [cutForce, sub_smul]

theorem old_solves_cut_iff (t₀ t₁ t : ℝ) (x : Space)
    (u f : VelocityField) (p : PressureField)
    (heq : navierStokesResidual u p t x = f (t, x)) :
    navierStokesResidual u p t x = cutForce t₀ t₁ f (t, x) ↔
      (1 - shutdown t₀ t₁ t) • f (t, x) = 0 := by
  rw [← old_residual_defect t₀ t₁ t x u f p heq, sub_eq_zero]

#print axioms shutdown
#print axioms shutdown_smooth
#print axioms shutdown_bounds
#print axioms shutdown_early
#print axioms shutdown_late
#print axioms shutdown_derivative_support
#print axioms cutForce
#print axioms cutForce_smoothOn
#print axioms cutForce_early
#print axioms cutForce_late
#print axioms cutForce_support
#print axioms cutForce_periodic
#print axioms cutForce_time_support
#print axioms cutForce_supportedIn
#print axioms compact_candidate_cut_admissible
#print axioms old_residual_defect
#print axioms old_solves_cut_iff
end UnforcedRestart.SmoothForceCutoff
