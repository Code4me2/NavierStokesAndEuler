import Euler.PacketCrossProduct
import Euler.AngleMeanZeroPrimitive

/-! The vector potential Q of a tangent, mean-zero, periodic high coefficient. -/

noncomputable section

namespace EulerPacketAngularPotential

open EulerSmoothLimit EulerPacketCrossProduct EulerAngleMeanZeroPrimitive
  MeasureTheory Set InnerProductSpace

def potential (P : ℝ) (m : Space) (A : ℝ → Space) : ℝ → Space :=
  primitive P (fun θ => potentialMultiplier m (A θ))

theorem potential_hasDerivAt (P : ℝ) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) (θ : ℝ) :
    HasDerivAt (potential P m A) (potentialMultiplier m (A θ)) θ :=
  primitive_hasDerivAt P _ ((potentialMultiplier m).continuous.comp hA) θ


theorem potential_periodic (P : ℝ) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) (hper : Function.Periodic A P)
    (hmean : ∫ θ in 0..P, A θ=0) : Function.Periodic (potential P m A) P := by
  apply primitive_periodic P _ ((potentialMultiplier m).continuous.comp hA)
  · intro θ
    exact congrArg (potentialMultiplier m) (hper θ)
  · simp only [Function.comp_def]
    rw [(potentialMultiplier m).intervalIntegral_comp_comm (hA.intervalIntegrable 0 P),
      hmean, map_zero]


theorem potential_zero (P : ℝ) (m : Space) :
    potential P m (fun _ => 0)=fun _ => 0 := by
  funext θ
  simp [potential, primitive, rawPrimitive]



end EulerPacketAngularPotential
