import Research.UnforcedRestart.Round3.MeanTopology.Main
import NavierStokes.R3.CompactTimeIntegral

/-! Fixed-support differentiation for the frozen selected activated compact velocity.
No terminal velocity trace, force-removal premise, or new witness is used. -/
noncomputable section
namespace UnforcedRestart.Round3.SelectedBridge
open NavierStokes NavierStokes.ProblemStatement
open MeanTopology Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Joint (not merely slice) regularity from the actual periodic germ on the
closed support cylinder, and the zero germ in its open complement. -/
theorem compactVelocity_smoothAt {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    ContDiffAt ℝ ∞ compactVelocity (t, x) := by
  by_cases hx : x ∈ SpatialLocalization.supportCylinder
  · have hi : x ∈ PeriodicLocalization.innerCube (1 / 4) := by
      intro i
      have hb := SpatialLocalization.supportCylinder_coordinate_bound hx i
      change |x i| < 1 - 1 / 4
      linarith
    exact (smooth_at_interior WitnessFeasibility.selected.candidate.velocity_smooth ht x).congr_of_eventuallyEq
      (compactVelocity_agreement (z := (t, x)) hi).symm
  · exact contDiffAt_const.congr_of_eventuallyEq
      (compactVelocity_zero_germ (z := (t, x)) hx)

/-- Every closed strictly interior slab has joint C¹ regularity. -/
theorem compactVelocity_contDiffOn_slab {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContDiffOn ℝ 1 compactVelocity (Icc a b ×ˢ (univ : Set Space)) := by
  intro z hz
  exact ((compactVelocity_smoothAt
    ⟨lt_of_lt_of_le ha hz.1.1, lt_of_le_of_lt hz.1.2 hb⟩ z.2).of_le
      (by norm_num)).contDiffWithinAt

/-- The support is the same fixed compact cylinder at every time, not a
separately chosen compact set for each slice. -/
theorem compactVelocity_uniform_support (r : ℝ) (x : Space)
    (hx : x ∉ SpatialLocalization.supportCylinder) : compactVelocity (r, x) = 0 :=
  compactVelocity_zero_outside r hx

/-- Differentiation under the whole-space component integral on an interior
slab, with the derivative matched to the PDE's temporalDerivative. -/
theorem compact_component_integral_hasDerivAt {a b t : ℝ}
    (ha : 0 < a) (hb : b < 1) (ht : t ∈ Ioo a b) (i : Fin 3) :
    HasDerivAt (fun r => ∫ x : Space, compactVelocity (r, x) i)
      (∫ x : Space, (temporalDerivative compactVelocity t x) i) t := by
  have hv := compactVelocity_contDiffOn_slab ha hb
  have hc : ContDiffOn ℝ 1 (fun z => compactVelocity z i)
      (Icc a b ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have h := NavierStokesR3.CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn
    SpatialLocalization.isCompact_supportCylinder hc
    (fun r _ x hx => by rw [compactVelocity_uniform_support r x hx]; rfl) ht
  have he (x : Space) : deriv (fun r => compactVelocity (r, x) i) t =
      (temporalDerivative compactVelocity t x) i := by
    have hd := NavierStokesR3.CompactTimeIntegral.hasDerivAt_time_of_contDiffOn hv ht x
    have hd' : HasDerivAt (fun r => compactVelocity (r, x))
        (temporalDerivative compactVelocity t x) t := hd.differentiableAt.hasDerivAt
    exact ((EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t hd').deriv
  simpa only [he] using h

/-- The selected bridge: zero component integral of the actual activated
compact velocity's temporal derivative at every strictly presingular time. -/
theorem selected_compact_temporal_integral_zero {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    (∫ x : Space, (temporalDerivative MeanTopology.compactVelocity t x) i) = 0 := by
  have hd := compact_component_integral_hasDerivAt
    (a := t / 2) (b := (t + 1) / 2) (t := t) (by linarith [ht.1])
    (by linarith [ht.2]) (by constructor <;> linarith [ht.1, ht.2]) i
  apply hd.unique
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact selected_compact_momentum_zero hr i

#print axioms compactVelocity_smoothAt
#print axioms compactVelocity_contDiffOn_slab
#print axioms compactVelocity_uniform_support
#print axioms compact_component_integral_hasDerivAt
#print axioms selected_compact_temporal_integral_zero
end UnforcedRestart.Round3.SelectedBridge
