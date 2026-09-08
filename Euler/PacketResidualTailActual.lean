import Euler.PacketResidualTailFields
import Euler.PacketSourceRegularity

/-!
The actual sliced momentum coefficient equals the tail decomposition using
only finite velocity regularity. No regularity of the lower scalar pressures
is needed, because their coefficients are already outside the tail support.
-/

noncomputable section

namespace EulerPacketProfileRecursion

open Set EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades EulerPacketResidual

theorem slicedJet_assembledVelocity_finite (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain)
    (hA : ∀ i ≤ N, SliceDifferentiable O.interval (a i).high z)
    (hB : ∀ i ≤ N, SliceDifferentiable O.interval (a i).mean z)
    (hC : ∀ i ≤ N, SliceDifferentiable O.interval (a i).corrector z) (i : ℕ) :
    slicedJet O.interval (assembledVelocity N a i) z = assembledJets O N a z i := by
  unfold assembledVelocity
  rw [slicedJet_assemble O.interval N i _ _ z
    (fun j hj => (hA j hj).add (hB j hj)) hC]
  change truncate N (fun j => slicedJet O.interval ((a j).high+(a j).mean) z) i + _ =
    truncate N (fun j => slicedJet O.interval (a j).high z+slicedJet O.interval (a j).mean z) i + _
  by_cases hi : i ≤ N
  · rw [truncate_of_le _ _ _ hi,truncate_of_le _ _ _ hi,slicedJet_add (hA i hi) (hB i hi)]
  · rw [truncate_of_gt _ _ _ (by omega),truncate_of_gt _ _ _ (by omega)]



end EulerPacketProfileRecursion

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {N : ℕ} {a : ℕ → Profile} {S : Set Space}



end EulerPacketCylinderField.ProfileRegularity
