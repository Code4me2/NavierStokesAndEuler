import Euler.MeanVariationalInverse
import Euler.TimeH1OperatorProduct

/-!
# Genuine H¹ label displacements and mean variational tests

The mean Hilbert model uses derivatives of the physical displacement.  A C¹
inverse deformation converts its terminal primitive to an actual H¹ solenoidal
label path, with a constructed Bochner L² derivative.  Conversely, each genuine
solenoidal terminal primitive yields an admissible physical test through F.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set Filter InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerTimeH1OperatorProduct
  EulerMeanSolenoidal EulerVolterraConvolution
open scoped Topology

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv FInv' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))




variable (hFInv : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT FInv) (FInv' t) (Icc (0 : ℝ) T) t)







variable (F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- Restrict the physical deformation to actual solenoidal label fields. -/
def solenoidalFrame : C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) :=
  ⟨fun t => (F t).comp solenoidalSpace.subtypeL,
    F.continuous.clm_comp continuous_const⟩

/-- Differentiating the restricted frame is literal bounded-map composition. -/
theorem solenoidalFrame_hasDerivWithinAt
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t) :
    ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT (solenoidalFrame T F))
        (solenoidalFrame T F' t) (Icc (0 : ℝ) T) t := by
  intro t
  have h := (hF t).clm_comp
    (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) solenoidalSpace.subtypeL)
  change HasDerivWithinAt (fun s => (extendPath T hT F s).comp solenoidalSpace.subtypeL)
    ((F' t).comp solenoidalSpace.subtypeL) (Icc (0 : ℝ) T) t
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using h

variable (hF : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)

include hF hInv in
/-- Every solenoidal terminal H¹ path supplies an admissible physical test. -/
theorem productDerivative_mem_mean (v : TimeLp T solenoidalSpace) :
    productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F') v ∈
      meanDerivatives T hT FInv := by
  intro t
  rw [terminalPrimitive_productDerivative T hT (solenoidalFrame T F)
    (solenoidalFrame T F') (solenoidalFrame_hasDerivWithinAt T hT F F' hF) v t]
  change FInv t (F t ((terminalPrimitive T hT v t : solenoidalSpace) : L2)) ∈ solenoidalSpace
  rw [hInv]
  exact (terminalPrimitive T hT v t).property

/-- A genuine bounded map from solenoidal label derivatives to admissible mean tests. -/
def meanTestMap : TimeLp T solenoidalSpace →L[ℝ] meanDerivatives T hT FInv :=
  (productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F')).codRestrict
    (meanDerivatives T hT FInv) (productDerivative_mem_mean T hT FInv F F' hF hInv)

/-- The test derivative is the actual product-rule L² field. -/
@[simp] theorem meanTestMap_coe (v : TimeLp T solenoidalSpace) :
    (meanTestMap T hT FInv F F' hF hInv v : TimeLp T L2) =
      productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F') v := rfl

/-- Its displacement primitive is the actual physical test `F b`. -/
theorem meanTestMap_primitive (v : TimeLp T solenoidalSpace) :
    meanPrimitive T hT FInv (meanTestMap T hT FInv F F' hF hInv v) =
      timeMultiplier T hT (solenoidalFrame T F) (primitiveTimeLp T hT v) :=
  primitiveTimeLp_productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) v

/-- The initial trace of the physical test is exactly `F(0) b(0)`. -/
theorem meanTestMap_trace (v : TimeLp T solenoidalSpace) :
    meanTrace T hT FInv (meanTestMap T hT FInv F F' hF hInv v) =
      F ⟨0, le_rfl, hT⟩ ((initialTrace T hT v : solenoidalSpace) : L2) :=
  initialTrace_productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) v

/-- Therefore zero-endpoint label tests remove both actual initial boundary terms. -/
theorem meanTestMap_trace_zero (v : TimeLp T solenoidalSpace) (hv : initialTrace T hT v = 0) :
    meanTrace T hT FInv (meanTestMap T hT FInv F F' hF hInv v) = 0 := by
  rw [meanTestMap_trace T hT FInv F F' hF hInv v, hv]
  exact map_zero _

end EulerMeanVariationalInverse
