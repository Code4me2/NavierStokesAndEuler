import Euler.MeanStrongInverse
import Euler.TimeH1FieldProduct

/-!
# The actual mean velocity and pressure-gradient residual

From a genuine strong mean evolution, construct B=F z_t in Bochner L², its
actual time derivative, and the residual f-B_t-MB. Its F-adjoint transform is
in the ordinary L² gradient space by the proved strong projected equation.
-/

noncomputable section


namespace EulerMeanVariationalInverse.StrongMeanEvolution

open MeasureTheory Set EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerVolterraConvolution EulerTimeH1FieldProduct

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The actual physical velocity B=F z_t as a Bochner L² field. -/
def velocityField : TimeLp T L2 :=
  timeMultiplier T hT (solenoidalFrame T F) s.velocityLp

/-- The actual continuous physical-velocity representative. -/
def physicalPath : ℝ → L2 := fun t => extendPath T hT F t (s.velocity t : L2)

/-- The product-rule candidate for B_t, constructed in actual Bochner L². -/
def velocityDerivative : TimeLp T L2 :=
  fieldProductDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    s.velocityLp s.acceleration

/-- This field really is B_t, and B has an actual absolutely continuous representative. -/
theorem physical_h1
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t) :
    AbsolutelyContinuousOnInterval s.physicalPath 0 T ∧
      (s.velocityField : ℝ → L2) =ᵐ[timeMeasure T] s.physicalPath ∧
      ∀ᵐ t ∂timeMeasure T, HasDerivAt s.physicalPath (s.velocityDerivative t) t :=
  fieldProduct_h1 T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    (solenoidalFrame_hasDerivWithinAt T hT F F₁ hF) s.velocityLp s.acceleration
    s.velocity s.velocity_ac s.velocity_ae s.velocity_derivative







/-- The initial physical velocity is exactly the source's localized boundary value. -/
theorem physicalPath_initial
    (hF₀ : F ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2) :
    s.physicalPath 0 = L • A (s.label 0 : L2) := by
  change F (projIcc 0 T hT 0) (s.velocity 0 : L2) = _
  rw [projIcc_of_mem hT ⟨le_rfl, hT⟩, hF₀, ContinuousLinearMap.id_apply]
  exact s.initial_velocity

end EulerMeanVariationalInverse.StrongMeanEvolution
