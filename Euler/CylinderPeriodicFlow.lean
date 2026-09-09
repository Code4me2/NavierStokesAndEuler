import Euler.CylinderCoverDescent
import Euler.BoundedFlowContinuity

/-! The actual flow of a periodic cover velocity descends to a genuine
continuous cylinder flow with two-sided inverse.

Merged in from the former module `Euler.BoundedFlowPeriodicity`: `flow_add_eq`.
-/

/-! Periodicity of the prescribed velocity gives exact translation
equivariance of the constructed global flow, by ODE uniqueness. -/

noncomputable section

namespace EulerBoundedLipschitzFlow.Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)

theorem flow_add_eq (c : E) (hc : ∀ t x, V.velocity t (x+c)=V.velocity t x)
    (s t : ℝ) (x : E) : V.flow s t (x+c)=V.flow s t x+c := by
  have h := V.flow_unique s (x+c) (fun r => V.flow s r x+c)
    (fun r => by simpa only [hc] using (V.flow_hasDerivAt s r x).add_const c)
    (by rw [V.flow_initial])
  exact (congrFun h t).symm

end EulerBoundedLipschitzFlow.Data
end

noncomputable section

namespace EulerCylinderPeriodicFlow

open Set Function MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent

variable (P : ℝ) [Fact (0 < P)] (V : EulerBoundedLipschitzFlow.Data LiftTangent)
  (hV : ∀ (c : AddSubgroup.zmultiples P) t z,
    V.velocity t (z.1,(c : ℝ)+z.2)=V.velocity t z)

include hV in
omit [Fact (0 < P)] in
theorem flow_deck (s t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    V.flow s t (z.1,(c : ℝ)+z.2) = ((V.flow s t z).1,(c : ℝ)+(V.flow s t z).2) := by
  have shift (w : LiftTangent) : w+(0,(c : ℝ)) = (w.1,(c : ℝ)+w.2) := by
    apply Prod.ext <;> simp [add_comm]
  have hp : ∀ r w, V.velocity r (w+(0,(c : ℝ)))=V.velocity r w := by
    intro r w
    rw [shift]
    exact hV c r w
  simpa only [shift] using V.flow_add_eq (0,(c : ℝ)) hp s t z

def flow (s t : ℝ) : LiftDomain P → LiftDomain P := descendMap P (V.flow s t)









include hV in
theorem flow_measurePreserving (s t : ℝ) (hf : MeasurePreserving (V.flow s t) volume volume) :
    MeasurePreserving (flow P V s t) (liftMeasure P) (liftMeasure P) :=
  descendMap_measurePreserving P (V.flow s t) (flow_deck P V hV s t) hf

end EulerCylinderPeriodicFlow
