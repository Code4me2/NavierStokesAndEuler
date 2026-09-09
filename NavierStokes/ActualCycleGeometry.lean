import NavierStokes.ActualInitialization
import NavierStokes.ActualCycleExcluded

/-!
# The actual fixed geometry for every correction cycle

The numerical data, strip, gauge, and operators below are the ones used by
`ActualInitialization`.  In particular, compatibility with the excluded-alias
estimates is proved independently of the particular and signed wave choices.
-/

noncomputable section

namespace NavierStokes.ActualCycleGeometry

open CorrectionInitialization CorrectionStep WeightedClasses


/-- Initialization supplies all numerical hypotheses of the similarity
estimates, including the actual finite-window common index. -/
noncomputable def similarityData : ActualCycleExcluded.SimilarityData where
  h := ActualPrimary.h
  h_pos := ActualPrimary.outgoing.data.h_pos
  inner := PrimaryTargetBounds.leftRadius ActualPrimary.nominal
  outer := PrimaryTargetBounds.rightRadius ActualPrimary.nominal
  inner_pos := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  inner_lt_outer := PrimaryTargetBounds.radii_ordered ActualPrimary.nominal
  leftWeight := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4
  rightWeight := 1
  left_pos := div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)
  right_pos := zero_lt_one
  baseScale := 1
  baseScale_ne := one_ne_zero
  region := ActualPrimary.standardRegion
  index := CommonWindow.index ActualPrimary.h
  gap := CommonWindow.gap ActualPrimary.h
  index_lower := CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le
  index_upper := fun n => (CommonWindow.index_le_native ActualPrimary.h n).trans (Nat.le_add_right _ _)
  slow := BaseContextAssembly.slowScale
  slow_one := BaseContextAssembly.one_le_slowScale
  slow_scale := fun _ => le_max_right _ _


theorem strip_eq_geometry : similarityData.strip = ActualInitialization.geometry.strip := rfl

/-- The normalization factor is exactly one, so the similarity gauge agrees
with the common reconstruction used by initialization. -/
theorem gauge_eq : similarityData.gauge = ActualPrimary.commonGauge :=
  ActualInitialCoherence.commonGauge_eq_similarity.symm

theorem gauge_eq_geometry : similarityData.gauge = ActualInitialization.geometry.gauge :=
  gauge_eq















end NavierStokes.ActualCycleGeometry
