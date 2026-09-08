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

/-- The manuscript's positive scalar profile remains divergent with a vanishing
relative error. The error is inside the factor multiplied by `q ^ (-A)`. -/
theorem positive_profile_tendsto_atTop {ι : Type*} {l : Filter ι}
    {q error : ι → ℝ} {A E : ℝ} (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0)) :
    Tendsto (fun t => q t ^ (-A) * (E + error t)) l atTop := by
  have hfactor : Tendsto (fun t => E + error t) l (𝓝 E) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  exact (negative_power_tendsto_atTop hA hq).atTop_mul_pos hE hfactor

/-- A velocity norm bounded below by the positive leading profile diverges.
This directly applies when the angular component has that leading term. -/
theorem norm_tendsto_atTop_of_profile_lower_bound {ι V : Type*}
    [NormedAddCommGroup V] {l : Filter ι} {q error : ι → ℝ}
    {v : ι → V} {A E : ℝ} (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0))
    (hlower : ∀ᶠ t in l, q t ^ (-A) * (E + error t) ≤ ‖v t‖) :
    Tendsto (fun t => ‖v t‖) l atTop := by
  exact tendsto_atTop_mono' l hlower
    (positive_profile_tendsto_atTop hA hE hq herror)




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
