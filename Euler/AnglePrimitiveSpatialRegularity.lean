import Euler.CompactParameterIntegral
import Euler.AngleMeanZeroPrimitive

/-! The actual angular primitive is jointly smooth in spatial labels and angle. -/

noncomputable section

universe u

namespace EulerAngleMeanZeroPrimitive

open Set MeasureTheory EulerCompactParameterIntegral
open scoped ContDiff

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem rawPrimitive_fixed_interval (f : ℝ → E) (θ : ℝ) :
    rawPrimitive f θ = θ • (∫ s in (0 : ℝ)..1, f (θ*s)) := by
  simpa only [rawPrimitive, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) f θ).symm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

theorem rawPrimitive_joint_contDiff (F : X × ℝ → E) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : X × ℝ => rawPrimitive (fun θ => F (p.1,θ)) p.2) := by
  have hG : ContDiff ℝ ∞ (fun z : (X × ℝ) × ℝ => F (z.1.1,z.1.2*z.2)) :=
    hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have hi := integral_contDiff 0 1 zero_le_one _ hG
  simpa only [rawPrimitive_fixed_interval, Pi.smul_def'] using contDiff_snd.smul hi

theorem primitive_joint_contDiff (P : ℝ) (hP : 0 ≤ P) (F : X × ℝ → E)
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : X × ℝ => primitive P (fun θ => F (p.1,θ)) p.2) := by
  have hr := rawPrimitive_joint_contDiff F hF
  have hm := integral_contDiff 0 P hP _ hr
  exact hr.sub (contDiff_const.smul (hm.comp contDiff_fst))

section Continuous

variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y] [LocallyCompactSpace Y]



end Continuous
end EulerAngleMeanZeroPrimitive
