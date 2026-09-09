import NavierStokes.ComparatorBridge
import NavierStokes.CompactSpatialForceDecay
import NavierStokes.PeriodicUniqueness
import NavierStokes.WithTopLemmas

/-!
# Force decay for the periodic comparator from compact future time support

The comparator's periodic force condition asks for polynomial decay in time of
every one-sided spacetime jet of the force. The candidate's force is smooth,
periodic and vanishes after a finite time, so each jet is continuous and
periodic on a closed slab — hence bounded there by compactness of the cube —
and zero afterwards. `ComparatorBridge.decay_of_slab_bound` turns this into
the decay; `CompactSpatialForceDecay` is the same argument for option (C) with
compactness supplied by spatial support instead of periodicity.
`forceConditionPeriodic` is the (D) adapter's force-condition step, the mirror
of `CompactSpatialForceDecay.forceConditionDecay`.
-/

noncomputable section

namespace NavierStokes.PeriodicForceDecay

open Set Filter Function ProblemStatement
open scoped ContDiff Topology Pointwise

theorem future_uniqueDiff : UniqueDiffOn ℝ futureDomain :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- The physical full spacetime jet, including its one-sided value at time zero. -/
noncomputable def futureJet (f : VelocityField) (m : ℕ) :=
  iteratedFDerivWithin ℝ m f futureDomain

theorem futureJet_continuous {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (m : ℕ) :
    ContinuousOn (futureJet f m) futureDomain :=
  hf.continuousOn_iteratedFDerivWithin (natCast_le_infty m) future_uniqueDiff

private theorem future_spatial_translate (e : Space) :
    ((0, e) : SpaceTime) +ᵥ futureDomain = futureDomain := by
  ext z
  change z ∈ (fun w : SpaceTime => (0, e) + w) '' futureDomain ↔ z ∈ futureDomain
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [futureDomain, mem_prod, mem_Ici, mem_univ, and_true,
      Prod.fst_add, Prod.fst_zero, zero_add] using hw
  · intro hz
    refine ⟨z - (0, e), ?_, ?_⟩
    · simpa only [futureDomain, mem_prod, mem_Ici, mem_univ, and_true,
        Prod.fst_sub, sub_zero] using hz
    · simpa only [add_comm] using sub_add_cancel z ((0, e) : SpaceTime)

theorem futureJet_periodic {f : VelocityField}
    (hp : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) (m : ℕ) :
    UnitSpatialPeriodsOn (Ici (0 : ℝ)) (futureJet f m) := by
  intro t ht x i
  have he : EqOn (fun z : SpaceTime => f (z + (0, coordinateVector i))) f futureDomain := by
    rintro ⟨s,y⟩ hz
    simpa only [Prod.mk_add_mk, add_zero] using hp s hz.1 y i
  have hc := iteratedFDerivWithin_congr (𝕜 := ℝ) he (show (t, x) ∈ futureDomain from ⟨ht, mem_univ _⟩) m
  have hs := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ) (f := f)
    (s := futureDomain) m (0, coordinateVector i) (t, x)
  rw [future_spatial_translate] at hs
  simpa only [futureJet, Prod.mk_add_mk, add_zero] using hs.symm.trans hc

theorem futureJet_eq_full {f : VelocityField} {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (m : ℕ) (hf : ContDiffAt ℝ ∞ f (t, x)) :
    futureJet f m (t, x) = iteratedFDeriv ℝ m f (t, x) :=
  iteratedFDerivWithin_eq_iteratedFDeriv future_uniqueDiff (hf.of_le (natCast_le_infty m))
    ⟨ht, mem_univ _⟩

/-- Compact future time support gives arbitrary polynomial decay of the
physical one-sided jets, using only future smoothness and future periodicity. -/
theorem futureJet_decay {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hp : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) (hs : CompactFutureTimeSupport f)
    (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨T, hT, hzero⟩ := hs
  obtain ⟨M, _, hM⟩ := PeriodicUniqueness.periodic_bound_on_slab (a := 0) (b := T)
    ((futureJet_continuous hf m).mono (fun _ hz => ⟨hz.1.1, hz.2⟩))
    (fun t ht x i => futureJet_periodic hp m t ht.1 x i)
  obtain ⟨C, hC, hb⟩ := ComparatorBridge.decay_of_slab_bound
    (J := futureJet f m) (w := fun z => (1 + z.1) ^ K)
    (fun t ht _ => Real.rpow_pos_of_pos (by linarith) K)
    (fun t ht x => CompactSpatialForceDecay.jet_zero_after hzero m ht x)
    ⟨M * (1 + T) ^ K, fun t ht x => mul_le_mul (hM t ht x)
      (Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) hK)
      (Real.rpow_nonneg (by linarith [ht.1]) K) (le_trans (norm_nonneg _) (hM t ht x))⟩
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv]
  exact hb t ht x

/-- The comparator's periodic force condition for the swapped force; the
mirror of `CompactSpatialForceDecay.forceConditionDecay`. -/
theorem forceConditionPeriodic {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hp : UnitSpatialPeriodsOn (Ici 0) f) (hs : CompactFutureTimeSupport f) :
    Comparator.ForceConditionPeriodic (ComparatorBridge.toComparator f) :=
  ComparatorBridge.forceConditionPeriodic_of_decay hf hp (futureJet_decay hf hp hs)

end NavierStokes.PeriodicForceDecay
