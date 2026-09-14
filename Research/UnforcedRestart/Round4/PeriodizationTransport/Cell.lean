import Research.UnforcedRestart.Round4.PeriodizationTransport.Residual
import Mathlib.MeasureTheory.Group.FundamentalDomain

noncomputable section
namespace UnforcedRestart.Round4.PeriodizationTransport
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Set MeasureTheory

private def shift (k : Fin 3 → ℤ) : Coords := fun i => (k i : ℝ)
local instance : AddAction (Fin 3 → ℤ) Coords where
  vadd k y := shift k + y
  zero_vadd y := by change shift 0 + y = y; ext i; simp [shift]
  add_vadd k l y := by
    change shift (k + l) + y = shift k + (shift l + y)
    ext i
    simp [shift, add_assoc]
local instance : MeasurableVAdd (Fin 3 → ℤ) Coords where
  measurable_const_vadd _ := measurable_const.add measurable_id
  measurable_vadd_const _ := measurable_of_countable _
local instance : VAddInvariantMeasure (Fin 3 → ℤ) Coords (volume : Measure Coords) where
  measure_preimage_vadd k s _ := measure_preimage_add volume (shift k) s

private def cell : Set Coords := Set.univ.pi (fun _ => Ico (0 : ℝ) 1)
private theorem cell_domain : IsAddFundamentalDomain (Fin 3 → ℤ) cell
    (volume : Measure Coords) := by
  apply IsAddFundamentalDomain.mk' ((MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet)
  intro y
  refine ⟨(fun i => -⌊y i⌋), ?_, ?_⟩
  · intro i _
    change ((-⌊y i⌋ : ℤ) : ℝ) + y i ∈ Ico (0 : ℝ) 1
    simpa only [mem_Ico, Int.cast_neg, Int.fract, sub_eq_add_neg, add_comm] using
      And.intro (Int.fract_nonneg (y i)) (Int.fract_lt_one (y i))
  · intro k hk
    funext i
    have h : ⌊(k i : ℝ) + y i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hk i (mem_univ i))
    rw [Int.floor_intCast_add] at h
    omega

/-- Integrable lattice sums transport from the genuine closed coordinate cell.
The half-open tiling differs from that cell only on null coordinate faces. -/
theorem integral_coordinate_periodization {f : Coords → ℝ} (hf : Integrable f) :
    (∫ y in Icc (0 : Coords) 1, ∑' k : Fin 3 → ℤ, f (shift k + y)) = ∫ y, f y := by
  have he : cell =ᵐ[volume] Icc (0 : Coords) 1 := MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc
  rw [← Measure.restrict_congr_set he]
  have hm (k : Fin 3 → ℤ) : AEStronglyMeasurable (fun y => f (shift k + y))
      (volume.restrict cell) :=
    (hf.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left volume (shift k))).restrict
  have hn : (∑' k : Fin 3 → ℤ, ∫⁻ y in cell, ‖f (shift k + y)‖ₑ) ≠ ⊤ := by
    change (∑' k : Fin 3 → ℤ, ∫⁻ y in cell, ‖f (k +ᵥ y)‖ₑ) ≠ ⊤
    rw [← cell_domain.lintegral_eq_tsum'' (fun y => ‖f y‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  rw [integral_tsum hm hn]
  exact (cell_domain.integral_eq_tsum'' f hf).symm

/-- Exact component transport for bounded-support fields, with integrability
explicit rather than relying on a totalized nonintegrable integral. -/
theorem integral_periodize_component {f : VelocityField} {r : ℝ}
    (hs : PeriodicLocalization.SupportedInCube r f) (t : ℝ) (i : Fin 3)
    (hi : Integrable (fun x : Space => f (t, x) i)) :
    (∫ y in Icc (0 : Coords) 1, PeriodicLocalization.periodize f (t, toSpace y) i) =
      ∫ x : Space, f (t, x) i := by
  have hc : Integrable (fun y : Coords => f (t, toSpace y) i) :=
    (toSpace_measurePreserving.integrable_comp_emb
      toSpace.toHomeomorph.measurableEmbedding).mpr hi
  rw [← wholeSpace_integral_coordinates (fun x => f (t, x) i),
    ← integral_coordinate_periodization hc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _
  obtain ⟨N, hN⟩ := PeriodicLocalization.exists_local_latticeBox hs (t, toSpace y)
  have hz := hN.self_of_nhds
  have hsum : Summable (fun k : PeriodicLocalization.Lattice =>
      PeriodicLocalization.translate f k (t, toSpace y)) :=
    summable_of_ne_finset_zero (fun k hk => hz k hk)
  have he := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).map_tsum hsum
  change (∑' k, PeriodicLocalization.translate f k (t, toSpace y)) i = _
  change (∑' k, PeriodicLocalization.translate f k (t, toSpace y)) i =
    ∑' k, (PeriodicLocalization.translate f k (t, toSpace y)) i at he
  rw [he]
  rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun k => (PeriodicLocalization.translate f k (t, toSpace y)) i)]
  apply tsum_congr
  intro k
  have hx : toSpace y - PeriodicLocalization.lattice (-k) = toSpace (shift k + y) := by
    ext j
    simp [PeriodicLocalization.lattice, shift, toSpace, sub_eq_add_neg, add_comm]
  change f (t, toSpace y - PeriodicLocalization.lattice (-k)) i = _
  rw [hx]

/-- Integration interface for the frozen selected force; the only input is
whole-space integrability of its actual compact residual component. -/
theorem selectedCellMean_eq_compact_integral {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (i : Fin 3) (hi : Integrable (fun x : Space => compactResidual (t, x) i)) :
    selectedCellMean t i = ∫ x : Space, compactResidual (t, x) i := by
  unfold selectedCellMean
  simp_rw [selected_force_eq_periodize ht]
  exact integral_periodize_component compactResidual_supported t i hi

theorem compactResidual_component_integrable {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (i : Fin 3) : Integrable (fun x : Space => compactResidual (t, x) i) := by
  have hc : Continuous (fun x : Space => Round3.WitnessFeasibility.selected.forcing (t, x) i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      (Round3.WitnessFeasibility.selected.smooth.continuous.comp
        (continuous_const.prodMk continuous_id))
  have hi : IntegrableOn (fun x : Space => Round3.WitnessFeasibility.selected.forcing (t, x) i)
      SpatialLocalization.supportCylinder (volume : Measure Space) :=
    hc.continuousOn.integrableOn_compact SpatialLocalization.isCompact_supportCylinder
  have he : (fun x : Space => compactResidual (t, x) i) =
      SpatialLocalization.supportCylinder.indicator
        (fun x => Round3.WitnessFeasibility.selected.forcing (t, x) i) := by
    funext x
    by_cases hx : x ∈ SpatialLocalization.supportCylinder
    · rw [indicator_of_mem hx, selected_force_inner ht x]
      intro j
      have hb := SpatialLocalization.supportCylinder_coordinate_bound hx j
      dsimp
      linarith
    · rw [indicator_of_notMem hx, compactResidual_zero_outside t hx]
      rfl
  rw [he]
  exact hi.integrable_indicator SpatialLocalization.isClosed_supportCylinder.measurableSet

/-- Actual selected-field transport, with no integrability or cancellation premise. -/
theorem selected_cell_integral_transport {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Fin 3) :
    selectedCellMean t i = ∫ x : Space, compactResidual (t, x) i :=
  selectedCellMean_eq_compact_integral ht i (compactResidual_component_integrable ht i)

#print axioms compactResidual_component_integrable
#print axioms selected_cell_integral_transport
#print axioms integral_coordinate_periodization
#print axioms integral_periodize_component
#print axioms selectedCellMean_eq_compact_integral
end UnforcedRestart.Round4.PeriodizationTransport
