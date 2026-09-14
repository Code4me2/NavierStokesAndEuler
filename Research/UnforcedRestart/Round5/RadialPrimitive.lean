import Research.UnforcedRestart.Round3.CurlGeometry.Main

/-! A nonvanishing input to the proposed radial discriminator, not a force-curl
certificate. The nominal profile here is the one used by the selected assembly.
No alternative witness or effective diagonal schedule is chosen. -/
noncomputable section
namespace UnforcedRestart.Round5.RadialPrimitive
open NavierStokes Set
open scoped ContDiff

abbrev normalization : ℝ :=
  BaseExterior.nominalHeatNormalization CorrectionInitialization.ActualPrimary.nominal

/-- The actual normalization, with no assumed amplitude sign. -/
theorem normalization_pos : 0 < normalization := by
  unfold normalization BaseExterior.nominalHeatNormalization PhysicalHeatCoordinates.normalization
  exact mul_pos (HeatTailEdit.outgoingAmplitude_pos _)
    (Real.rpow_pos_of_pos (BaseExterior.nominalHeatSwitch_pos _) _)

/-- Terminal coefficient of the actual anchored heat model. -/
theorem terminal_coefficient_pos {s : ℝ} (hs : 0 < s) (z : ℝ) :
    0 < TailGaugePotential.extendedHeatCoefficient normalization
      CorrectionInitialization.ActualPrimary.h (1, (s, z)) := by
  unfold TailGaugePotential.extendedHeatCoefficient
  simp only [sub_self, mul_zero, zero_div]
  rw [HeatProfileExtension.extension_zero (by
    linarith [CorrectionInitialization.ActualPrimary.outgoing.data.h_pos])]
  exact div_pos (mul_pos normalization_pos (by positivity)) (Real.sqrt_pos.mpr (by positivity))

/-- Strict decrease follows from the source's derivative theorem, including the
anchored gauge. No totalized integral positivity argument is used. -/
theorem terminal_primitive_strictAnti :
    StrictAntiOn (fun s : ℝ => TailGaugePotential.heatPrimitive normalization
      CorrectionInitialization.ActualPrimary.h (1, (s, 0))) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _) ?_ ?_
  · intro s hs
    exact (TailGaugePotential.heatPrimitive_hasDerivAt normalization
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos 1 0 hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    rw [(TailGaugePotential.heatPrimitive_hasDerivAt normalization
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos 1 0 hs).deriv]
    exact neg_neg_of_pos (terminal_coefficient_pos hs 0)

/-- Nonzero input throughout the radial transition, not merely at a sample. -/
theorem terminal_primitive_pos {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < TailGaugePotential.heatPrimitive normalization
      CorrectionInitialization.ActualPrimary.h (1, (s, 0)) := by
  have h := terminal_primitive_strictAnti hs (show (1 : ℝ) ∈ Ioi 0 by norm_num) hs1
  simpa only [TailGaugePotential.heatPrimitive_anchor] using h

/-- Includes both endpoints required by the proposed regular ODE argument. -/
theorem transition_primitive_pos {s : ℝ} (hs : s ∈ Icc (1 / 64 : ℝ) (1 / 32)) :
    0 < TailGaugePotential.heatPrimitive normalization
      CorrectionInitialization.ActualPrimary.h (1, (s, 0)) := by
  apply terminal_primitive_pos <;> linarith [hs.1, hs.2]

#print axioms normalization_pos
#print axioms terminal_coefficient_pos
#print axioms terminal_primitive_strictAnti
#print axioms terminal_primitive_pos
#print axioms transition_primitive_pos
end UnforcedRestart.Round5.RadialPrimitive
