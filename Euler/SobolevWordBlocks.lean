import Euler.SobolevRestriction
import Euler.SobolevHeat

/-! Bounded actual derivative-word blocks on the complete Sobolev scale. -/

noncomputable section

namespace EulerSobolevWordBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSobolevHeat EulerGaussianCylinderHeat EulerPressureSpatialRegularity
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A derivative word as an actual bounded map H^(q+n)→Hq, with its literal differentiation order. -/
def wordBlock (q : ℕ) : (n : ℕ) → (Fin n → Fin 4) →
    SobolevSpace period (q + n) →L[ℝ] SobolevSpace period q
  | 0, _ => ContinuousLinearMap.id ℝ (SobolevSpace period q)
  | n + 1, w => (wordBlock q n (Fin.init w)).comp (derivativeOperator period (q + n) (w (Fin.last n)))


/-- The field underlying a derivative block is exactly its genuine derivative-word coordinate. -/
theorem wordBlock_value (q n : ℕ) (w : Fin n → Fin 4) (u : SobolevSpace period (q + n)) :
    value period (wordBlock period q n w u) = word period u (by omega : n ≤ q + n) w := by
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    rfl
  | succ n ih =>
    change value period (wordBlock period q n (Fin.init w)
      (derivativeOperator period (q+n) (w (Fin.last n)) u)) = _
    rw [ih]
    change u.val ⟨⟨n+1, _⟩, Fin.snoc (Fin.init w) (w (Fin.last n))⟩ = _
    rw [Fin.snoc_init_self]
    rfl




end EulerSobolevWordBlocks
