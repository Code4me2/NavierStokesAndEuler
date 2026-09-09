import Euler.Solution

/-!
# Showcase statements outside the deliverable closure

Restatements of the Euler result in the development's own vocabulary, kept
as documented provenance. None of them is consumed by `Euler.Solution`; this
module imports it and is therefore outside the closure of the two delivered
theorems. Every statement here was formerly in `Euler.EulerSingularity`,
`Euler.EulerFiniteLifespan`, `Euler.EulerC1Breakdown` or `Euler.EulerC1Limsup`.
-/

noncomputable section

namespace EulerPacketInduction

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open scoped ContDiff ENNReal Topology

def HasSmoothEulerSolution (u₀ : Space → Space) (T : ℝ) : Prop :=
  ∃ hT : 0 < T, ∃ U : Evolution T hT.le,
    (U.velocity ⟨0,le_rfl,hT.le⟩).field=u₀

theorem hasSmoothEulerSolution_iff (A : SmoothL2Field Space) (T : ℝ) :
    HasSmoothEulerSolution A.field T ↔ HasEulerEvolution A T := by
  constructor
  · rintro ⟨hT,U,hU⟩
    exact ⟨hT,U,field_ext hU⟩
  · rintro ⟨hT,U,hU⟩
    exact ⟨hT,U,congrArg SmoothL2Field.field hU⟩

abbrev MaximalTime : Type := lifespan.Time

def maximalC1Norm (t : MaximalTime) : ℝ := lifespan.maximalC1Norm t

theorem maximalC1Norm_limsup :
    Filter.limsup (fun t : MaximalTime => ENNReal.ofReal (maximalC1Norm t))
      (Filter.comap (fun t : MaximalTime => (t : ℝ)) (𝓝[<] lifespan.duration))=⊤ :=
  lifespan.maximalC1Norm_limsup

def maximalVorticityDensity (r : ℝ) : ℝ := lifespan.maximalVorticityDensity r

theorem initialDatum_existence_iff (T : ℝ) :
    HasSmoothEulerSolution initialDatum.field T ↔ 0 < T ∧ T < lifespan.duration :=
  (hasSmoothEulerSolution_iff initialDatum T).trans (lifespan.hasEulerEvolution_iff T)

theorem maximalVorticity_integral_infinite :
    (∫⁻ r in Ico (0 : ℝ) lifespan.duration, ENNReal.ofReal (maximalVorticityDensity r))=⊤ :=
  lifespan.vorticity_lintegral_eq_top

/-- The two breakdown conclusions for the actual constructed datum and
the actual maximal smooth solution. No unproved estimate is a premise. -/
theorem initialDatum_singularity :
    ContDiff ℝ ∞ initialDatum.field ∧ HasCompactSupport initialDatum.field ∧
      initialDatum.field ≠ 0 ∧ (∀ x, divergence initialDatum.field x=0) ∧
      0 < lifespan.duration ∧ lifespan.duration ≤ 1 ∧
      (∀ T : ℝ, HasSmoothEulerSolution initialDatum.field T ↔
        0 < T ∧ T < lifespan.duration) ∧
      Filter.limsup (fun t : MaximalTime => ENNReal.ofReal (maximalC1Norm t))
        (Filter.comap (fun t : MaximalTime => (t : ℝ)) (𝓝[<] lifespan.duration))=⊤ ∧
      (∫⁻ r in Ico (0 : ℝ) lifespan.duration,
        ENNReal.ofReal (maximalVorticityDensity r))=⊤ :=
  ⟨initialDatum.smooth,initialDatum_compact,initialDatum_nonzero,initialDatum_divergence,
    lifespan.duration_pos,lifespan_le_one,initialDatum_existence_iff,
    maximalC1Norm_limsup,maximalVorticity_integral_infinite⟩

/-- An existential form of the manuscript's claim. Every restriction of
the one maximal field is an actual Euler evolution. Its time and space
regularity, scalar pressure, and norm meanings are proved in the imported
ordinary-Euler interfaces, rather than assumed as construction inputs. -/
theorem exists_compact_smooth_euler_singularity :
    ∃ (A : SmoothL2Field Space) (L : FiniteLifespan A),
      ContDiff ℝ ∞ A.field ∧ HasCompactSupport A.field ∧ A.field ≠ 0 ∧
      (∀ x, divergence A.field x=0) ∧ 0 < L.duration ∧ L.duration ≤ 1 ∧
      (∀ T : ℝ, HasScalarEulerEvolution A T ↔ 0 < T ∧ T < L.duration) ∧
      L.maximalVelocity L.initialTime=A.field ∧
      (∀ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration),
        ∃ U : Evolution S hS.le,
          U.velocity=(fun t => L.maximalField (L.shorterTime S hSL t)) ∧
          U.pressureForce=(fun t => L.maximalPressureField (L.shorterTime S hSL t)) ∧
          U.velocity ⟨0,le_rfl,hS.le⟩=A) ∧
      Filter.limsup (fun t : L.Time => ENNReal.ofReal (L.maximalC1Norm t))
        (Filter.comap (fun t : L.Time => (t : ℝ)) (𝓝[<] L.duration))=⊤ ∧
      (∫⁻ r in Ico (0 : ℝ) L.duration, ENNReal.ofReal (L.maximalVorticityDensity r))=⊤ :=
  ⟨initialDatum,lifespan,initialDatum.smooth,initialDatum_compact,initialDatum_nonzero,
    initialDatum_divergence,lifespan.duration_pos,lifespan_le_one,
    lifespan.hasScalarEulerEvolution_iff,lifespan.maximalVelocity_initial,
    lifespan.maximal_restriction_is_evolution,lifespan.maximalC1Norm_limsup,
    lifespan.vorticity_lintegral_eq_top⟩

end EulerPacketInduction
