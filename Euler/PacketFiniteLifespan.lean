import Euler.PacketInfiniteConstruction
import Euler.PacketStageInitialLimit
import Euler.PacketStageContradiction
import Euler.OrdinaryEulerLocalExistence
import Euler.OrdinaryEulerLifespan

/-!
# The canonical datum and its finite lifespan

Step 1 of the top of the Euler argument. The initial velocities of the
actual packet family converge in every Sobolev order to `initialDatum`;
the limit is solenoidal because the solenoidal subspace is closed, so the
general local existence theorem gives a short ordinary Euler evolution.
No evolution reaches any packet horizon, and the horizons decrease, so the
maximal lifespan is at most their infimum.
-/

noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerPacketBaseGuardScales EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerSmoothL2Series
open scoped Topology

/-- The smooth L² limit of the initial velocities of the packet family. -/
def initialDatum : SmoothL2Field Space := Stage.initialDataLimit packets le_rfl le_rfl

theorem initialDatum_Hm (s : ℕ) :
    Tendsto (fun n => derivativeSum s
      ((fun x => (packets n).state.evolution.velocity (0,x))-initialDatum.field))
      atTop (𝓝 0) :=
  Stage.initialDataLimit_Hm packets le_rfl le_rfl
    (fun n hn => stages_initial_step constructionScales le_rfl le_rfl n hn) s

/-- The limit of solenoidal fields is solenoidal: the solenoidal subspace of
L² is closed and the stage data converge to `initialDatum` in L². -/
theorem initialDatum_solenoidal : initialDatum.toLp ∈ solenoidalSpace := by
  let V : ℕ → SmoothL2Field Space :=
    fun n => (packets n).state.regularity.velocity (packets n).parent.zeroTime
  have hnorm (n : ℕ) : ‖(V n).toLp-initialDatum.toLp‖ =
      derivativeSum 0 ((fun x => (packets n).state.evolution.velocity (0,x))-initialDatum.field) := by
    rw [← toLp_fieldSub,← tensorNorm_zero,tensorNorm_eq_derivativeSum]
    congr 1
    funext x
    rw [fieldSub_field]
    exact congrArg (fun r => r-initialDatum.field x)
      ((packets n).state.regularity.velocity_match (packets n).parent.zeroTime x).symm
  have hlim : Tendsto (fun n => (V n).toLp) atTop (𝓝 initialDatum.toLp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [hnorm] using initialDatum_Hm 0
  exact gradientSpace.isClosed_orthogonal.mem_of_tendsto hlim
    (Eventually.of_forall (fun n => (packets n).state.regularity.velocity_solenoidal _))

theorem initialDatum_divergence (x : Space) : divergence initialDatum.field x=0 :=
  solenoidal_representative_divergence initialDatum.toLp initialDatum_solenoidal
    initialDatum.field initialDatum.smooth initialDatum.toLp_ae x

/-- Short-time existence for the datum is the general local existence theorem. -/
theorem initialDatum_local : ∃ T, HasEulerEvolution initialDatum T :=
  ⟨regularizedTime initialDatum,regularizedTime_pos initialDatum,
    localEvolution initialDatum initialDatum_solenoidal,
    localEvolution_initial initialDatum initialDatum_solenoidal⟩

theorem packets_horizon_succ (n : ℕ) :
    (packets (n+1)).parent.T = (packets n).nextHorizon := by
  rw [(packets (n+1)).horizon_eq]
  have ht : (packets (n+1)).time = (packets n).nextTime :=
    stages_time constructionScales le_rfl le_rfl n
  rw [ht]
  rfl

theorem packets_horizon_antitone : Antitone (fun n => (packets n).parent.T) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [packets_horizon_succ]
  exact (packets n).nextHorizon_le

/-- No ordinary Euler evolution from the datum reaches the horizon of any
packet stage: the later stages have shorter horizons. -/
theorem initialDatum_no_packet_horizon (N : ℕ) :
    ¬ HasEulerEvolution initialDatum (packets N).parent.T := by
  rintro ⟨hT,U,hU⟩
  exact GrowthData.no_evolution_of_eventually_covering (fun n => (packets n).toGrowthData)
    initialDatum.field (initialDatum_Hm 3) (packets N).parent.T hT.le
    (eventually_atTop.mpr ⟨N,fun n hn => packets_horizon_antitone hn⟩)
    ⟨U,congrArg SmoothL2Field.field hU⟩

theorem initialDatum_finite_lifespan :
    ∃ L : FiniteLifespan initialDatum, L.duration ≤ (packets 0).parent.T :=
  exists_finite_lifespan initialDatum (packets 0).parent.T (packets 0).parent.T_pos
    initialDatum_local (initialDatum_no_packet_horizon 0)

/-- The maximal lifespan of the canonical datum. -/
def lifespan : FiniteLifespan initialDatum := initialDatum_finite_lifespan.choose

theorem lifespan_le_packet_horizon (n : ℕ) :
    lifespan.duration ≤ (packets n).parent.T := by
  by_contra h
  exact initialDatum_no_packet_horizon n
    (lifespan.shorter (packets n).parent.T (packets n).parent.T_pos (lt_of_not_ge h))

/-- The maximal lifespan is at most the infimum of the packet horizons, that
is, at most the accumulation time of the activations. -/
theorem lifespan_le_iInf_horizon : lifespan.duration ≤ ⨅ n, (packets n).parent.T :=
  le_ciInf lifespan_le_packet_horizon

theorem lifespan_le_base :
    lifespan.duration ≤ baseHorizon constructionScales.J constructionScales.X :=
  (lifespan_le_packet_horizon 0).trans (packets 0).horizon_le

end EulerPacketInduction
