import Euler.MeanDisplacementRegularity
import Euler.TransverseMomentumRegularity

/-!
# Genuine mean momentum regularity from the variational solve

Zero-initial-trace solenoidal test primitives are mapped by F into the actual
mean test space. The two original boundary terms then vanish, and the weak
identity constructs an AC representative of `Pσ F* η_t`. This is a regularity
conclusion, not an assumed momentum equation or an assumed second derivative.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution EulerMeanSolenoidal
  EulerTimeH1OperatorProduct EulerTimeWeakDerivative EulerTransverseMomentumRegularity

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The frame adjoint is the actual ordinary solenoidal projection of `F*`. -/
theorem solenoidalFrame_adjoint (t : Icc (0 : ℝ) T) :
    (solenoidalFrame T F t).adjoint =
      solenoidalSpace.orthogonalProjectionOnto.comp (F t).adjoint := by
  change ((F t).comp solenoidalSpace.subtypeL).adjoint = _
  calc
    _ = solenoidalSpace.subtypeL.adjoint.comp (F t).adjoint :=
      adjoint_comp _ _
    _ = _ := congrArg (fun A : L2 →L[ℝ] solenoidalSpace => A.comp (F t).adjoint)
      (Submodule.adjoint_subtypeL solenoidalSpace)


/-- The exact mean variational identity determines the weak derivative of its
actual projected momentum after the trace-zero test restriction. -/
theorem meanMomentum_weak
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
    (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (hu : ∀ w : meanDerivatives T hT FInv,
      ⟪(u : TimeLp T L2), (w : TimeLp T L2)⟫_ℝ-
        ⟪timeMultiplier T hT H (meanPrimitive T hT FInv u), meanPrimitive T hT FInv w⟫_ℝ+
        ⟪M0 (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ+
        L*⟪A (meanTrace T hT FInv u), meanTrace T hT FInv w⟫_ℝ =
        -⟪f, meanPrimitive T hT FInv w⟫_ℝ)
    (v : TimeLp T solenoidalSpace) (hv : initialTrace T hT v = 0) :
    ⟪momentum T hT (solenoidalFrame T F) (u : TimeLp T L2), v⟫_ℝ =
      -⟪momentumForcing T hT (solenoidalFrame T F) (solenoidalFrame T F') H
        (u : TimeLp T L2) f, primitiveTimeLp T hT v⟫_ℝ := by
  apply momentum_weak_of_product_tests T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) H (u : TimeLp T L2) f v
  have h := hu (meanTestMap T hT FInv F F' hF hInv v)
  simpa only [meanTestMap_trace_zero T hT FInv F F' hF hInv v hv,
    inner_zero_right, mul_zero, add_zero, meanPrimitive, comp_apply,
    Submodule.subtypeL_apply, meanTestMap_coe] using h



end EulerMeanVariationalInverse
