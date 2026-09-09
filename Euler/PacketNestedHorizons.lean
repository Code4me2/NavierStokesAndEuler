import Euler.PacketBaseGuardScales
import Euler.PacketSourceScaleGuards

/-! The literal activation times and nested horizons in (38). The same
positive initial time interval is available to every finite packet state. -/

noncomputable section

namespace EulerPacketNestedHorizons

open Finset Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleGuards EulerPacketBaseGuardScales

def stepLength (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  scaleSequence J X (n+1)/sqrt (β n*a n*previousShear J X n)

def activationTime (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, stepLength J X a β i


@[simp] theorem activationTime_zero (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) :
    activationTime J X a β 0=0 := by simp [activationTime]

theorem activationTime_succ (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) :
    activationTime J X a β (n+1)=activationTime J X a β n+stepLength J X a β n := sum_range_succ _ n


variable (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X) (a β : ℕ → ℝ)
  (ha : ∀ n, 1/2 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
  (hβ : ∀ n, 1/2 ≤ β n*scaleSequence J X n^2)
  (hβ₂ : ∀ n, β n*scaleSequence J X n^2 ≤ 2)















end EulerPacketNestedHorizons
