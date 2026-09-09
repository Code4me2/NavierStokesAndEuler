import Euler.PacketStageGrowth
import Euler.ParentOrdinaryEvolution
import Euler.OrdinaryEulerVaryingHorizon
import Euler.SmoothL2Series

/-! Step 1 of the top of the Euler argument, in its general form: a family
of packet stages whose initial velocities converge in H³ to a datum `u₀`
excludes any ordinary Euler evolution from `u₀` on a horizon `T` that
eventually contains the stage horizons. Each stage is compared with the
restriction of the hypothetical evolution to its own horizon; H³ stability
would then bound the activation gradients, which diverge. Only the
`GrowthData` part of the invariant is read. -/

noncomputable section

namespace EulerPacketInduction.GrowthData

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerSmoothL2Series
  EulerPacketInductionScales EulerPacketSourceScaleActual EulerPacketBaseGuardScales
open scoped Topology

variable {c B : ℝ} {S : Scales c B} (P : ∀ n, GrowthData S n) (u₀ : Space → Space)
  (hinit : Tendsto (fun n => derivativeSum 3
    ((fun x => (P n).state.evolution.velocity (0,x))-u₀)) atTop (𝓝 0))

include P hinit

/-- No ordinary Euler evolution starts from the H³ limit of the stage data
on a horizon that eventually dominates the stage horizons. The finitely many
stages whose horizon exceeds `T` are discarded by reindexing. -/
theorem no_evolution_of_eventually_covering (T : ℝ) (hT : 0 ≤ T)
    (hcover : ∀ᶠ n in atTop, (P n).parent.T ≤ T) :
    ¬ ∃ U : Evolution T hT, (U.velocity ⟨0,le_rfl,hT⟩).field=u₀ := by
  rintro ⟨U,hU₀⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hcover
  let durations : ℕ → ℝ := fun n => (P (n+N)).parent.T
  let hD : ∀ n, 0 ≤ durations n := fun n => (P (n+N)).parent.T_pos.le
  let hDT : ∀ n, durations n ≤ T := fun n => hN (n+N) (by omega)
  let V : ∀ n, Evolution (durations n) (hD n) :=
    fun n => (P (n+N)).state.regularity.ordinaryEvolution
  let times : ∀ n, Icc (0 : ℝ) (durations n) :=
    fun n => ⟨(P (n+N)).time,(P (n+N)).time_nonneg,(P (n+N)).time_lt.le⟩
  have hfield (n : ℕ) :
      (((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n))
        ⟨0,le_rfl,hD n⟩).field = (fun x => (P (n+N)).state.evolution.velocity (0,x))-u₀ := by
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((P (n+N)).state.regularity.velocity ⟨0,le_rfl,(P (n+N)).parent.T_pos.le⟩).field x-
        (U.velocity ⟨0,le_rfl,hT⟩).field x = _
    rw [hU₀,← (P (n+N)).state.regularity.velocity_match ⟨0,le_rfl,(P (n+N)).parent.T_pos.le⟩ x]
    rfl
  have hnorm (n : ℕ) :
      tensorNorm 3 ((U.restrictTime (durations n) (hD n) (hDT n)).difference
        (V n) ⟨0,le_rfl,hD n⟩) =
      derivativeSum 3 ((fun x => (P (n+N)).state.evolution.velocity (0,x))-u₀) := by
    rw [tensorNorm_eq_derivativeSum,hfield]
  have hlim : Tendsto (fun n => tensorNorm 3
      ((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n) ⟨0,le_rfl,hD n⟩))
      atTop (𝓝 0) := by
    simpa only [hnorm,Function.comp_def] using hinit.comp (tendsto_add_atTop_nat N)
  apply U.no_gradient_escape_of_initial_tendsto_varying durations hD hDT V hlim times
  have hactual (n : ℕ) : ((V n).velocity (times n)).field =
      fun x => (P (n+N)).state.evolution.velocity ((P (n+N)).time,x) :=
    funext (fun x => ((P (n+N)).state.regularity.velocity_match (times n) x).symm)
  have heq : (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) =
      fun n => (P (n+N)).activationGradient := by
    funext n
    rw [hactual]
    rfl
  rw [heq]
  exact (gradient_atTop P).comp (tendsto_add_atTop_nat N)

end EulerPacketInduction.GrowthData
