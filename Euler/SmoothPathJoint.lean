import Euler.SmoothPathTimeJets
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Joint time-space differentiability of a genuine smooth family of
continuous paths, and the actual mixed derivative of its spatial Jacobian. -/

noncomputable section


open scoped ContDiff Topology

namespace EulerSmoothPathJoint

open Set Filter EulerVolterraConvolution EulerSmoothPathTimeJets

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T,V))

def timeSlice (t : ℝ) (x : E) : V := extendPath T hT (f x) t

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem timeSlice_joint_continuous (hf : Continuous f) :
    Continuous (Function.uncurry (timeSlice T hT f)) := by
  unfold timeSlice extendPath
  fun_prop

def spatialDerivative (x : E) : C(Icc (0 : ℝ) T,E →L[ℝ] V) :=
  ((continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
    ℝ (Icc (0 : ℝ) T)) (jetFamily T f 1 x)

theorem spatialDerivative_contDiff (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spatialDerivative T f) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,E [×1]→L[ℝ] V)) (F := C(Icc (0 : ℝ) T,E →L[ℝ] V))
    ((continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
      ℝ (Icc (0 : ℝ) T))).comp (jetFamily_contDiff T f hf 1)



def jointDerivative (t : ℝ) (x : E) : (ℝ × E) →L[ℝ] V :=
  (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q t x)).coprod
    (timeSlice T hT (spatialDerivative T f) t x)

theorem jointDerivative_continuous (hf : ContDiff ℝ ∞ f) (hq : Continuous q) :
    Continuous (Function.uncurry (jointDerivative T hT f q)) := by
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
    (timeSlice_joint_continuous T hT q hq)).continuousLinearMapCoprod
      (timeSlice_joint_continuous T hT (spatialDerivative T f)
        (spatialDerivative_contDiff T f hf).continuous)

variable (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)




end EulerSmoothPathJoint
