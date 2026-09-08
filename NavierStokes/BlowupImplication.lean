import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith

/-!
# Conditional blow-up and obstruction to continuous extension

The terminal inference of Proposition 11.7, independently of the claimed
Navier--Stokes construction. Positive scales approaching zero and a nonzero
limiting profile force divergent velocity norm under a negative real power.
The resulting field cannot be bounded near, or continuously extended to, the
endpoint. No existence theorem for the manuscript's profiles is assumed here.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace NavierStokes.BlowupImplication

/-- A positive scale tending to zero has a divergent negative real power. -/
theorem negative_power_tendsto_atTop {ι : Type*} {l : Filter ι}
    {q : ι → ℝ} {A : ℝ} (hA : 0 < A)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun t => q t ^ (-A)) l atTop := by
  have h := (tendsto_rpow_atTop hA).comp
    (tendsto_inv_nhdsGT_zero.comp hq)
  refine h.congr' ?_
  filter_upwards [hq.eventually self_mem_nhdsWithin] with t ht
  change (q t)⁻¹ ^ A = q t ^ (-A)
  rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]






/-- The remaining-time scale `T - t` tends to zero through positive values
as `t` approaches `T` from below. -/
theorem remaining_time_tendsto (T : ℝ) :
    Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => T) (𝓝[<] T) (𝓝 T) := tendsto_const_nhds
    simpa only [sub_self] using hconst.sub htime
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (show 0 < T - t from sub_pos.mpr ht)






end NavierStokes.BlowupImplication
