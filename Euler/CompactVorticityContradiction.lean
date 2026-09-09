import Euler.ComparatorLocalEvolution

/-!
# Step 3: confined vorticity contradicts maximality of the lifespan

The last step of the top of the Euler argument. A global Comparator solution
agrees with the canonical maximal solution below `T*` (step 2), so its
vorticity is confined to the compact set `K` below `T*`; joint continuity of
the vorticity carries the confinement to `T*` itself, the short-time
compact-vorticity persistence restarted at `T*` carries it a little past
`T*`, and the local conversion of `ComparatorLocalEvolution` then turns the
Comparator solution into an ordinary Euler evolution on `[0, T* + δ]`. No
such evolution exists, because `T*` is maximal (`FiniteLifespan.maximal`).
The proved Beale--Kato--Majda criterion is not used here; the BKM-based
contradiction is kept as a corollary in `Euler.Showcase`.
-/

noncomputable section

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerMeanCutoffCurl

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- A closed set carrying the vorticity of a Comparator solution at every
time in `[0, T)` also carries it at time `T`, by joint continuity of the
vorticity in time and space. This passes the confinement of step 2 to the
endpoint of the lifespan. -/
theorem vorticity_support_subset_at_endpoint (T : ℝ) (hT : 0 < T)
    (K : Set Space) (hK : IsClosed K)
    (hsupport : ∀ t ∈ Ico (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K) :
    tsupport (vectorCurl (v · T)) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hout
  let g : ℝ → Space := fun r => vectorCurl (v · (projIcc 0 T hT.le r : ℝ)) x
  have hproj : Continuous (fun r : ℝ => ((projIcc 0 T hT.le r : ℝ), x)) :=
    (continuous_subtype_val.comp (continuous_projIcc (a := (0 : ℝ)) (b := T) (h := hT.le))).prodMk
      continuous_const
  have hg : Continuous g :=
    h.vorticity_continuousOn.comp_continuous hproj
      (fun r => ⟨(projIcc 0 T hT.le r).property.1, mem_univ x⟩)
  have hzero : Ico (0 : ℝ) T ⊆ {r | g r = 0} := by
    intro r hr
    show vectorCurl (v · (projIcc 0 T hT.le r : ℝ)) x = 0
    rw [projIcc_of_mem hT.le ⟨hr.1, hr.2.le⟩]
    exact image_eq_zero_of_notMem_tsupport (fun hm => hout (hsupport r hr hm))
  have hcl := closure_minimal hzero (isClosed_eq hg continuous_const)
  rw [closure_Ico hT.ne] at hcl
  have hend : g T = 0 := hcl ⟨hT.le, le_rfl⟩
  apply hx
  simpa only [g, projIcc_right] using hend

end Euler.EulerExistenceAndSmoothnessR3

namespace Euler.ComparatorBridge

variable {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

/-- Step 3 of the top of the Euler argument: no global Comparator solution
starts from the datum of a finite lifespan whose canonical vorticity is
confined to one compact set. Steps 2 and 3 are composed here: after the
identification, the Comparator solution is an ordinary Euler evolution on
`[0, T* + δ]`, contradicting the maximality of `T*`. -/
theorem no_global_solution_of_confined_vorticity {A : SmoothL2Field Space}
    (L : FiniteLifespan A) (K : Set Space) (hK : IsCompact K)
    (hconf : ∀ t : L.Time, tsupport (vectorCurl (L.maximalVelocity t)) ⊆ K) :
    ¬ ∃ v p, EulerExistenceAndSmoothnessR3 A.field v p := by
  rintro ⟨v, p, h⟩
  have hcompact (t : L.Time) : HasCompactSupport (vectorCurl (L.maximalVelocity t)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hconf t)
  have hmatch := comparator_agrees_with_canonical L h hcompact
  have hpos := L.duration_pos
  -- confinement below the lifespan, transported to the Comparator solution
  have hbelow : ∀ t ∈ Ico (0 : ℝ) L.duration, tsupport (vectorCurl (v · t)) ⊆ K := by
    intro t ht
    rw [← hmatch ⟨t, ht⟩]
    exact hconf ⟨t, ht⟩
  -- confinement at the lifespan itself
  have hend := h.vorticity_support_subset_at_endpoint L.duration hpos K hK.isClosed hbelow
  -- compact vorticity for a short time past the lifespan
  obtain ⟨δ, B, hδ, hpast⟩ :=
    (h.shiftTime L.duration hpos.le).local_compact_vorticity_of_truncationFamily
      (h.shiftTime L.duration hpos.le).finiteEnergyTruncationFamily
      (hK.of_isClosed_subset (isClosed_tsupport _) hend)
  have hsupport : ∀ t ∈ Icc (0 : ℝ) (L.duration + δ),
      tsupport (vectorCurl (v · t)) ⊆ K ∪ Metric.closedBall 0 B := by
    intro t ht
    rcases lt_or_ge t L.duration with hlt | hge
    · exact (hbelow t ⟨ht.1, hlt⟩).trans subset_union_left
    · have hs := hpast (t - L.duration) ⟨sub_nonneg.mpr hge, by linarith [ht.2]⟩
      have heq : L.duration + (t - L.duration) = t := by ring
      simp only [heq] at hs
      exact hs.trans subset_union_right
  -- the Comparator solution is an ordinary evolution past the lifespan
  obtain ⟨U, hU⟩ := exists_evolution_of_commonCompactCurl h (L.duration + δ) (by linarith)
    (K ∪ Metric.closedBall 0 B) (hK.union (isCompact_closedBall _ _)) hsupport
  refine L.maximal (L.duration + δ) (by linarith) ⟨by linarith, U, ?_⟩
  apply field_ext
  rw [hU]
  funext x
  exact h.initial_condition x

end Euler.ComparatorBridge
