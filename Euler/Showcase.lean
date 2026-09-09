import Euler.Solution

/-!
# Showcase statements outside the deliverable closure

Restatements of the Euler result in the development's own vocabulary, kept
as documented provenance. None of them is consumed by `Euler.Solution`; this
module imports it and is therefore outside the closure of the two delivered
theorems. Every statement here was formerly in `Euler.EulerSingularity`,
`Euler.EulerFiniteLifespan`, `Euler.EulerC1Breakdown` or `Euler.EulerC1Limsup`,
except the final section, which records the Beale--Kato--Majda route to the
step-3 contradiction that `Euler.CompactVorticityContradiction` used to take
before it was rerouted through the maximality of the lifespan.
-/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanCutoffCurl

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- The Beale--Kato--Majda route to the step-3 contradiction: a compact `K`
that carries all the canonical vorticity, and a comparison field continuous
on `[0,T*] × K` agreeing with it there, bound the vorticity supremum
uniformly below the maximal time, contradicting the proved BKM criterion.
Not used by the delivered theorems, which contradict maximality instead. -/
theorem false_of_vorticity_agree_on_compact (w : ℝ → Space → Space)
    (K : Set Space) (hK : IsCompact K)
    (hw : ContinuousOn (fun z : ℝ × Space => w z.1 z.2) (Icc 0 L.duration ×ˢ K))
    (hagree : ∀ (t : L.Time), ∀ x ∈ K, vectorCurl (L.maximalVelocity t) x = w t x)
    (hconf : ∀ t : L.Time, tsupport (vectorCurl (L.maximalVelocity t)) ⊆ K) : False := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hw
  have hcurl : ∀ (t : L.Time) x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ max M 0 := by
    intro t x
    by_cases hx : x ∈ K
    · rw [hagree t x hx]
      exact (hM ((t : ℝ), x) ⟨⟨t.property.1, t.property.2.le⟩, hx⟩).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hconf t hm)), norm_zero]
      exact le_max_right _ _
  obtain ⟨S, hS, hSL, t, hlarge⟩ := L.vorticityIntegral_unbounded (max M 0 * L.duration)
  have hbound : ∀ s x, ‖vectorCurl ((L.evolution S hS hSL).velocity s).field x‖ ≤ max M 0 := by
    intro s x
    rw [← L.maximalVelocity_eq_evolution S hS hSL s]
    exact hcurl _ x
  have hupper := (L.evolution S hS hSL).vorticityIntegral_le_const (max M 0) hbound t
  have ht : (t : ℝ) ≤ L.duration := t.property.2.trans hSL.le
  exact (not_lt_of_ge (hupper.trans (mul_le_mul_of_nonneg_left ht (le_max_right _ _)))) hlarge

/-- The step-3 conclusion re-derived along the BKM route, for comparison
with `Euler.ComparatorBridge.no_global_solution_of_confined_vorticity`. -/
theorem no_global_solution_of_confined_vorticity_bkm (K : Set Space) (hK : IsCompact K)
    (hconf : ∀ t : L.Time, tsupport (vectorCurl (L.maximalVelocity t)) ⊆ K) :
    ¬ ∃ v p, Euler.EulerExistenceAndSmoothnessR3 A.field v p := by
  rintro ⟨v, p, h⟩
  have hcompact (t : L.Time) : HasCompactSupport (vectorCurl (L.maximalVelocity t)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hconf t)
  have hmatch := Euler.ComparatorBridge.comparator_agrees_with_canonical L h hcompact
  refine L.false_of_vorticity_agree_on_compact (fun t x => vectorCurl (v · t) x) K hK
    (h.vorticity_continuousOn.mono (fun z hz => ⟨hz.1.1, mem_univ _⟩)) ?_ hconf
  intro t x _
  rw [hmatch t]

end EulerOrdinarySobolev.FiniteLifespan

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
