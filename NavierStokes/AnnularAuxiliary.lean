import NavierStokes.ParametricRadialExtension
import NavierStokes.TransportPrimitive

/-!+# Smooth auxiliary fields for an annulus

The maps constructed here agree with the physical fields on an open positive
annulus and are globally smooth. Absolute histories from the axis are not
preserved by clamping. The final section proves the correct transfer statement:
supported edit differences, including their nonlinear density integrals, are
unchanged when transplanted back to the original field.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokes.AnnularAuxiliary

noncomputable def positiveMap (a X : ℝ) : ℝ :=
  a + TransportPrimitive.cutoff (a / 2) a X * (X - a)

theorem positiveMap_contDiff (a : ℝ) : ContDiff ℝ ∞ (positiveMap a) :=
  contDiff_const.add ((TransportPrimitive.cutoff_contDiff _ _).mul
    (contDiff_id.sub contDiff_const))

theorem positiveMap_eq {a X : ℝ} (ha : 0 < a) (hX : a ≤ X) : positiveMap a X = X := by
  rw [positiveMap, TransportPrimitive.cutoff_one (by linarith) hX]
  ring

theorem positiveMap_pos {a : ℝ} (ha : 0 < a) (X : ℝ) : 0 < positiveMap a X := by
  by_cases hX : X ≤ a / 2
  · rw [positiveMap, TransportPrimitive.cutoff_zero (by linarith) hX, zero_mul, add_zero]
    exact ha
  · by_cases hXa : a ≤ X
    · rw [positiveMap_eq ha hXa]
      exact ha.trans_le hXa
    · have hc := (TransportPrimitive.cutoff_mem_Icc (a / 2) a X).2
      have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr (le_of_not_ge hXa))
      dsimp [positiveMap]
      nlinarith

noncomputable def auxiliary {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) (a : ℝ)
    (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  F (positiveMap a p.1, w.parameterMap p.2)


theorem auxiliary_eq {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) {a : ℝ} (ha : 0 < a)
    (F : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hX : a ≤ p.1) (heta : |p.2| ≤ w.inner) :
    auxiliary w a F p = F p := by
  rw [auxiliary, positiveMap_eq ha hX, w.parameterMap_eq heta]



section Transplant

variable {α E V : Type*} [AddCommGroup E] [AddCommGroup V]

/-- Transplant only the edit. The original field carries the unchanged
history between the axis and the edit window. -/
noncomputable def transplant (base aux replacement : α → E) (x : α) : E :=
  base x + (replacement x - aux x)

theorem transplant_outside {base aux replacement : α → E} {x : α}
    (hx : replacement x = aux x) : transplant base aux replacement x = base x := by
  simp only [transplant, hx, sub_self, add_zero]

theorem transplant_inside {base aux replacement : α → E} {x : α}
    (hx : base x = aux x) : transplant base aux replacement x = replacement x := by
  rw [transplant, hx]
  abel


end Transplant



end NavierStokes.AnnularAuxiliary
