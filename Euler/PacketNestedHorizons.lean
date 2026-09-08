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

def horizonTime (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  activationTime J X a β n+2*timeWidth J X n

@[simp] theorem activationTime_zero (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) :
    activationTime J X a β 0=0 := by simp [activationTime]

theorem activationTime_succ (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) :
    activationTime J X a β (n+1)=activationTime J X a β n+stepLength J X a β n := by
  exact sum_range_succ _ n

@[simp] theorem horizonTime_zero (J : ℕ) {X : ℝ} (hX : 0 < X) (a β : ℕ → ℝ) :
    horizonTime J X a β 0=baseHorizon J X := by
  rw [horizonTime,activationTime_zero,zero_add,baseHorizon_eq_timeWidth J hX]

variable (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X) (a β : ℕ → ℝ)
  (ha : ∀ n, 1/2 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
  (hβ : ∀ n, 1/2 ≤ β n*scaleSequence J X n^2)
  (hβ₂ : ∀ n, β n*scaleSequence J X n^2 ≤ 2)

include hJ hX ha ha₂ hβ hβ₂ in
theorem stepLength_bounds (n : ℕ) :
    timeWidth J X n/6 ≤ stepLength J X a β n ∧
      stepLength J X a β n ≤ 2*timeWidth J X n/3 := by
  have hx := quadratic_growth_pos J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  exact activation_time_bounds (ha n) (ha₂ n) (previousShear_pos J hX n)
    (hx n) (hx (n+1)).le (hβ n) (hβ₂ n)

include hJ hX ha ha₂ hβ hβ₂ in
theorem stepLength_pos (n : ℕ) : 0 < stepLength J X a β n :=
  lt_of_lt_of_le (div_pos (timeWidth_pos J hJ hX n) (by norm_num))
    (stepLength_bounds J hJ X hX a β ha ha₂ hβ hβ₂ n).1

include hJ hX ha ha₂ hβ hβ₂ in
theorem activationTime_strictMono : StrictMono (activationTime J X a β) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [activationTime_succ]
  exact lt_add_of_pos_right _ (stepLength_pos J hJ X hX a β ha ha₂ hβ hβ₂ n)


include hJ hX ha ha₂ hβ hβ₂ in
theorem activationTime_pos {n : ℕ} (hn : 0 < n) : 0 < activationTime J X a β n := by
  simpa only [activationTime_zero] using
    activationTime_strictMono J hJ X hX a β ha ha₂ hβ hβ₂ hn










end EulerPacketNestedHorizons
