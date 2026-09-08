import Euler.PacketCorrectionRapidDecay

/-! The literal correction target and a fixed inverse-frequency packet
amplitude give the small lifted velocity required by the finite flow
bootstrap. All source constants remain fixed as frequency increases. -/

noncomputable section

namespace EulerPacketSourceFrequency

open Real Filter EulerPacketCorrectionScalar
open scoped Topology

def liftedAmplitude (C E k : ℝ) : ℝ := C/k + E*delta (expansion k)





end EulerPacketSourceFrequency
