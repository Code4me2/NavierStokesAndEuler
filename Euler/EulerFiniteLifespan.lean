import Euler.PacketFiniteLifespan
import Euler.PacketFirstStageSupport
import Euler.PacketInitialDatumSupport
import Euler.OrdinaryEulerNontriviality

/-! The canonical datum is compactly supported, nonzero, and its maximal
lifespan is at most one. These are the facts about the datum that the
delivered statements quote beside its finite lifespan. -/

noncomputable section

namespace EulerPacketInduction

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerPacketBaseGuardScales
open scoped ContDiff

theorem initialDatum_support : tsupport initialDatum.field ⊆ Metric.closedBall 0 2 :=
  Stage.initialDataLimit_support_of_physical packets le_rfl le_rfl
    (constructionScales.firstForwardStage_initial_support le_rfl le_rfl)

theorem initialDatum_compact : HasCompactSupport initialDatum.field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) initialDatum_support

theorem lifespan_le_one : lifespan.duration ≤ 1 :=
  lifespan_le_base.trans constructionScales.time_small

theorem initialDatum_nonzero : initialDatum.field ≠ 0 := lifespan.initial_nonzero

end EulerPacketInduction
