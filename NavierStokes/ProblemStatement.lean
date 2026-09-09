import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Statement of the candidate forced Navier--Stokes construction

This module states the primary existential assertion of Candidate Theorem 1.1.
`candidateStatement` is a proposition, not an axiom: nothing is assumed here and
no witness is constructed here. It is *proved* elsewhere in this repository, by
`NavierStokes.ActualCandidateAssembly.selected_candidate`, which
`NavierStokes/ComparatorTheorem.lean` consumes.

The unit torus is represented by periodic functions on Euclidean three-space.
Time is the first coordinate in `SpaceTime`. Smoothness at time zero is relative
to the indicated closed half-domain. The PDE uses ordinary Frechet derivatives
and is imposed only at interior times `0 < t < 1`; the initial value is imposed
separately at `t = 0`. No arbitrary extension to negative time is differentiated
at the time-zero boundary.

The `ContDiff` scope's `∞` means all finite differentiability orders. In this
Mathlib version `⊤` would instead impose the stronger analytic order.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace NavierStokes.ProblemStatement

/-- Three-dimensional real Euclidean space with its Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The first coordinate is time; the second is the lifted spatial coordinate. -/
abbrev SpaceTime := ℝ × Space

abbrev VelocityField := SpaceTime → Space
abbrev PressureField := SpaceTime → ℝ

/-- The standard unit coordinate vectors, fixing both the metric and periods. -/
def coordinateVector (i : Fin 3) : Space := EuclideanSpace.single i 1

/-- Physical spacetime before the proposed singular time, including initial time. -/
def preSingularDomain : Set SpaceTime := Ico 0 1 ×ˢ univ

/-- The physical domain on which the prescribed force must be smooth. -/
def futureDomain : Set SpaceTime := Ici 0 ×ˢ univ

/-- Invariance under each of the three unit coordinate shifts. Quantifying over
every spatial point also gives the corresponding negative shifts. -/
def UnitSpatialPeriodsOn {V : Type*} (times : Set ℝ) (g : SpaceTime → V) : Prop :=
  ∀ t ∈ times, ∀ x : Space, ∀ i : Fin 3,
    g (t, x + coordinateVector i) = g (t, x)

/-- Ordinary time derivative, evaluated on the positive unit time direction.
It is used in the PDE only for `0 < t < 1`. -/
def temporalDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s : ℝ => u (s, x)) t 1

/-- Spatial Frechet derivative with time held fixed. -/
def spatialDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (fun y : Space => u (t, y)) x

/-- `(u · ∇)u`, the spatial derivative applied to the velocity vector. -/
def advection (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative u t x (u (t, x))

/-- Euclidean divergence `∑ᵢ ∂ᵢuᵢ`. -/
def spatialDivergence (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, (spatialDerivative u t x (coordinateVector i)) i

/-- Euclidean gradient `∑ᵢ (∂ᵢp)eᵢ`. -/
def pressureGradient (p : PressureField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    (fderiv ℝ (fun y : Space => p (t, y)) x (coordinateVector i)) • coordinateVector i

/-- Componentwise Euclidean Laplacian `∑ᵢ ∂ᵢ∂ᵢu`. -/
def spatialLaplacian (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : Space => spatialDerivative u t y (coordinateVector i))
      x (coordinateVector i)

/-- The physical Navier--Stokes residual at viscosity exactly one. -/
def navierStokesResidual (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + advection u t x - spatialLaplacian u t x +
    pressureGradient p t x

/-- A common finite upper endpoint for the force's future time support,
uniformly over space. Spatial support is not required to be compact in the lift. -/
def CompactFutureTimeSupport (f : VelocityField) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ x : Space, f (t, x) = 0

/-- Pointwise expression of unbounded speed arbitrarily near time one from
below. Both the threshold and the time-neighborhood radius are arbitrary. -/
def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖

/-- Every field in this proposition is an explicit regularity, periodicity,
support, equation, initial-value, or blow-up condition. No existence is asserted
by introducing the proposition. -/
structure CandidateProperties (u : VelocityField) (p : PressureField)
    (f : VelocityField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiffOn ℝ ∞ f futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ico 0 1) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p
  force_periodic : UnitSpatialPeriodsOn (Ici 0) f
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u

/-- The primary existential content of Candidate Theorem 1.1.
There is no proof, witness, or axiom asserting this proposition in this module;
it is proved by `NavierStokes.ActualCandidateAssembly.selected_candidate`.
Maximal lifespan, Sobolev blow-up, and force derivative decay are corollaries
proved in `NavierStokes/CandidateConsequences.lean`; they are not part of the
delivered argument, which uses only `speed_unbounded`. -/
def candidateStatement : Prop :=
  ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField,
    CandidateProperties u p f

/-- Relative smoothness gives ordinary smoothness at every interior spacetime
point, where the ordinary derivatives in the equation are evaluated. -/
theorem smooth_at_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    ContDiffAt ℝ ∞ g (t, x) := by
  exact hg.contDiffAt (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) Filter.univ_mem)


/-- The residual definition reduces to zero for zero velocity and pressure. -/
@[simp] theorem zero_residual (t : ℝ) (x : Space) :
    navierStokesResidual (fun _ => 0) (fun _ => 0) t x = 0 := by
  simp [navierStokesResidual, temporalDerivative, advection, spatialLaplacian,
    spatialDerivative, pressureGradient]



/-- The quantified blow-up condition excludes every uniform finite bound on
the physical presingular domain. This does not assert that the condition holds. -/
theorem unbounded_speed_excludes_uniform_bound {u : VelocityField}
    (h : SpeedUnboundedAtOne u) :
    ¬ ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, ‖u (t, x)‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hpositive : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  obtain ⟨t, x, ht, _, hlarge⟩ := h (max C 1) hpositive 1 zero_lt_one
  have hbound := (hC t ⟨ht.1.le, ht.2⟩ x).trans (le_max_left C 1)
  exact (not_lt_of_ge hbound) hlarge

/-- The common last step of both exclusion arguments, (C) and (D). A
competitor `v` continuous on `[0,1] × K` with `K` compact is bounded there. If
the candidate `u` agrees with `v` on `K` before time one, and every value of
`u` before time one is either zero or attained somewhere on `K`, then `u` is
bounded before time one, which `SpeedUnboundedAtOne` forbids. On the torus `K`
is the unit cube (periodicity); on `ℝ³` it is the candidate's spatial support. -/
theorem SpeedUnboundedAtOne.false_of_agree {u v : VelocityField}
    (h : SpeedUnboundedAtOne u) {K : Set Space} (hK : IsCompact K)
    (hv : ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ K))
    (hagree : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ K, u (t, x) = v (t, x))
    (hred : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      u (t, x) = 0 ∨ ∃ y ∈ K, u (t, x) = u (t, y)) : False := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hv
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h (max M 1) hpos 1 zero_lt_one
  have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  rcases hred t ht' x with hzero | ⟨y, hy, hxy⟩
  · rw [hzero, norm_zero] at hlarge
    exact absurd hlarge (not_lt.mpr hpos.le)
  · rw [hxy, hagree t ht' y hy] at hlarge
    exact absurd hlarge
      (not_lt.mpr ((hM (t, y) ⟨⟨ht.1.le, ht.2.le⟩, hy⟩).trans (le_max_left M 1)))

/-! ### One solution vocabulary

The candidate contract, the finite-lifespan classical solutions used for the
periodic exclusion, and the global solutions obtained from a hypothetical
comparator solution all share the same five conditions on a time set `I`.
`Solution` names them once; the other notions extend or project to it. -/

/-- A smooth solution of the viscosity-one equation with zero initial datum on
the time set `I`. The equation is imposed at the positive times of `I`; the
initial value separately at `t = 0`. -/
structure Solution (I : Set ℝ) (f : VelocityField) (u : VelocityField)
    (p : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u (I ×ˢ univ)
  pressure_smooth : ContDiffOn ℝ ∞ p (I ×ˢ univ)
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  divergence_free : ∀ t ∈ I, ∀ x : Space, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ I, 0 < t → ∀ x : Space, navierStokesResidual u p t x = f (t, x)

theorem Solution.mono {I J : Set ℝ} {f u : VelocityField} {p : PressureField}
    (h : Solution I f u p) (hJ : J ⊆ I) : Solution J f u p where
  velocity_smooth := h.velocity_smooth.mono (prod_mono hJ subset_rfl)
  pressure_smooth := h.pressure_smooth.mono (prod_mono hJ subset_rfl)
  zero_initial_velocity := h.zero_initial_velocity
  divergence_free := fun t ht => h.divergence_free t (hJ ht)
  navier_stokes := fun t ht => h.navier_stokes t (hJ ht)

/-- The candidate contract, projected to the shared solution vocabulary. -/
theorem CandidateProperties.toSolution {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) : Solution (Ico 0 1) f u p where
  velocity_smooth := h.velocity_smooth
  pressure_smooth := h.pressure_smooth
  zero_initial_velocity := h.zero_initial_velocity
  divergence_free := h.divergence_free
  navier_stokes := fun t ht ht0 x => h.navier_stokes t ⟨ht0, ht.2⟩ x

/-- A global smooth periodic solution of the viscosity-one equation with zero
datum: what a hypothetical comparator solution for option (D) becomes after
the coordinate swap and viscosity normalization of `ComparatorBridge`. -/
structure GlobalSolutionOne (f : VelocityField) (v : VelocityField) (p : PressureField) : Prop
    extends Solution (Ici 0) f v p where
  velocity_periodic : UnitSpatialPeriodsOn (Ici 0) v
  pressure_periodic : UnitSpatialPeriodsOn (Ici 0) p

end NavierStokes.ProblemStatement
