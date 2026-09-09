import Euler.PacketCylinderBoundTransfer

/-! Genuine time-derivative witnesses are unique, including at both endpoints. -/

namespace EulerPacketCylinderField.TimeDerivative

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketPointJets

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T}
  {raw raw₁ raw₂ : VectorField} {G H : Field P T raw}
  {G₁ : Field P T raw₁} {H₁ : Field P T raw₂}

theorem raw_eq (hG : TimeDerivative hT.le G G₁) (hH : TimeDerivative hT.le H H₁)
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) : raw₁ (t,(x,θ)) = raw₂ (t,(x,θ)) :=
  (G.slicedJet_temporal hT G₁ hG t x θ).symm.trans (H.slicedJet_temporal hT H₁ hH t x θ)


end EulerPacketCylinderField.TimeDerivative
