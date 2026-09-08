import Euler.PacketUniformFrequencyMargin
import Euler.PhysicalChildSourceBound
import Euler.PacketTerminalDatum

/-! The only eventual frequency conditions left after the uniform source
cost comparison form one fixed, parent-independent numerical record. -/

noncomputable section

namespace EulerPacketSourceFrequency

open Filter EulerPacketCorrectionScalar EulerPacketTerminalDatum
  EulerPacketParentLabelBounds EulerSobolevSourceExponent

structure UniversalFrequency (k : ℝ) : Prop where
  four : 4 ≤ k
  expansion_bound : 64 ≤ expansion k
  log_bound : 1 ≤ Real.log k
  delta_bound : delta (expansion k) ≤ k^(-(3 : ℝ))
  root_bound : 16 ≤ k^(1/4 : ℝ)
  trace_bound : max 71 (Real.sqrt (2/period+2*period)) ≤ k^(1/24 : ℝ)
  child_bound : 69 ≤ k
  embedding_bound : 2+45*embeddingCost ≤ k
  derivative_bound : fixedCost 6 ≤ k

theorem universal_frequency_eventually : ∀ᶠ k : ℝ in atTop, UniversalFrequency k := by
  filter_upwards [universal_margin_eventually (Real.sqrt (2/period+2*period)),
    eventually_ge_atTop (69 : ℝ),eventually_ge_atTop (2+45*embeddingCost),
    eventually_ge_atTop (fixedCost 6)] with k h hk he hd
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,hk,he,hd⟩


namespace UniversalFrequency

variable {k : ℝ} (h : UniversalFrequency k)

include h

theorem one_le : 1 ≤ k := by linarith [h.four]
theorem pos : 0 < k := zero_lt_one.trans_le h.one_le

end UniversalFrequency
end EulerPacketSourceFrequency
